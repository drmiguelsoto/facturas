"""
facturas-sync — Servidor de conciliación de CFDI del Dr. Miguel Soto.

- Guarda la e.firma CIFRADA (Fernet, llave en la variable MASTER_KEY) en el volumen.
- Todos los días se conecta al servicio oficial de Descarga Masiva del SAT,
  baja CFDI emitidos y recibidos + metadata de cancelados, y los guarda en SQLite.
- Expone una API protegida con login de Google (sólo correos en ALLOWED_EMAILS)
  que consume facturas.miguelsotomd.com.

La e.firma sólo se usa para AUTENTICARSE y descargar. Este servidor no timbra,
no cancela ni firma ningún documento.
"""
import base64
import datetime as dt
import io
import json
import logging
import os
import sqlite3
import threading
import time
import zipfile
from contextlib import contextmanager
from zoneinfo import ZoneInfo

from cryptography import x509
from cryptography.fernet import Fernet, InvalidToken
from fastapi import Depends, FastAPI, File, Form, HTTPException, Request, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, Response
from google.auth.transport import requests as g_requests
from google.oauth2 import id_token as g_id_token
from lxml import etree

from cfdiclient import (
    Autenticacion,
    DescargaMasiva,
    Fiel,
    SolicitaDescargaEmitidos,
    SolicitaDescargaRecibidos,
    VerificaSolicitudDescarga,
)

# ---------------------------------------------------------------- config
DATA_DIR = os.environ.get("DATA_DIR", "/data")
DB_PATH = os.path.join(DATA_DIR, "facturas.db")
FIEL_PATH = os.path.join(DATA_DIR, "fiel.enc")
MASTER_KEY = os.environ.get("MASTER_KEY", "")
GOOGLE_CLIENT_ID = os.environ.get(
    "GOOGLE_CLIENT_ID",
    "634352012698-b47t3ed3tvd4d1g7l30l68bd6e5s0ri4.apps.googleusercontent.com",
)
ALLOWED_EMAILS = {
    e.strip().lower()
    for e in os.environ.get(
        "ALLOWED_EMAILS",
        "miguelitosotomd@gmail.com,miguelsotomd@gmail.com,miguelsotouniverse@gmail.com",
    ).split(",")
    if e.strip()
}
ALLOWED_ORIGINS = [
    o.strip()
    for o in os.environ.get(
        "ALLOWED_ORIGINS",
        "https://facturas.miguelsotomd.com,http://facturas.miguelsotomd.com",
    ).split(",")
    if o.strip()
]
TZ = ZoneInfo("America/Mexico_City")
SYNC_HOUR = int(os.environ.get("SYNC_HOUR", "4"))  # 4:00 am CDMX
CHECK_EVERY = int(os.environ.get("CHECK_EVERY_SECONDS", "600"))
BACKFILL_FROM = os.environ.get("BACKFILL_FROM", "")  # ej. 2025-01-01

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("facturas")
os.makedirs(DATA_DIR, exist_ok=True)

# ---------------------------------------------------------------- base de datos
SCHEMA = """
CREATE TABLE IF NOT EXISTS cfdi(
  uuid TEXT PRIMARY KEY, rfc_dueno TEXT, data TEXT NOT NULL, xml TEXT NOT NULL,
  origen TEXT, creado TEXT
);
CREATE TABLE IF NOT EXISTS estatus(
  uuid TEXT PRIMARY KEY, estatus TEXT, fecha_cancelacion TEXT, actualizado TEXT
);
CREATE TABLE IF NOT EXISTS solicitudes(
  id TEXT PRIMARY KEY, rfc TEXT, direccion TEXT, tipo TEXT, desde TEXT, hasta TEXT,
  estado TEXT, mensaje TEXT, numero INTEGER, creado TEXT, actualizado TEXT
);
CREATE TABLE IF NOT EXISTS eventos(
  id INTEGER PRIMARY KEY AUTOINCREMENT, fecha TEXT, nivel TEXT, mensaje TEXT
);
CREATE TABLE IF NOT EXISTS kv(k TEXT PRIMARY KEY, v TEXT);
"""
_db_lock = threading.RLock()


@contextmanager
def db():
    with _db_lock:
        con = sqlite3.connect(DB_PATH, timeout=30)
        con.row_factory = sqlite3.Row
        try:
            yield con
            con.commit()
        finally:
            con.close()


with db() as c:
    c.executescript(SCHEMA)


def now_iso():
    return dt.datetime.now(TZ).isoformat(timespec="seconds")


def kv_get(k, default=None):
    with db() as c:
        r = c.execute("SELECT v FROM kv WHERE k=?", (k,)).fetchone()
    return json.loads(r["v"]) if r else default


def kv_set(k, v):
    with db() as c:
        c.execute("INSERT OR REPLACE INTO kv(k,v) VALUES(?,?)", (k, json.dumps(v)))


def evento(msg, nivel="info"):
    log.log(logging.WARNING if nivel != "info" else logging.INFO, msg)
    with db() as c:
        c.execute("INSERT INTO eventos(fecha,nivel,mensaje) VALUES(?,?,?)", (now_iso(), nivel, msg))
        c.execute("DELETE FROM eventos WHERE id NOT IN (SELECT id FROM eventos ORDER BY id DESC LIMIT 300)")


# ---------------------------------------------------------------- lectura de CFDI
def _ln(el):
    return etree.QName(el).localname


def _kids(el, name):
    return [c for c in (el if el is not None else []) if isinstance(c.tag, str) and _ln(c) == name]


def _kid(el, name):
    k = _kids(el, name)
    return k[0] if k else None


def _num(v):
    try:
        return float(v or 0)
    except ValueError:
        return 0.0


def parse_cfdi(raw: bytes):
    """Devuelve el CFDI con las mismas llaves que usa la app web."""
    i = raw.find(b"<")
    if i < 0:
        return None
    try:
        r = etree.fromstring(raw[i:], parser=etree.XMLParser(resolve_entities=False, no_network=True, huge_tree=True))
    except etree.XMLSyntaxError:
        return None
    if _ln(r) != "Comprobante":
        return None
    comp = _kid(r, "Complemento")
    tfd = None
    if comp is not None:
        for el in comp.iter():
            if isinstance(el.tag, str) and _ln(el) == "TimbreFiscalDigital":
                tfd = el
                break
    if tfd is None:
        return None
    em, rc = _kid(r, "Emisor"), _kid(r, "Receptor")
    g = r.get
    conceptos = [c.get("Descripcion") for c in _kids(_kid(r, "Conceptos"), "Concepto") if c.get("Descripcion")]
    rel = []
    for cr in _kids(r, "CfdiRelacionados"):
        for x in _kids(cr, "CfdiRelacionado"):
            rel.append({"tipo": cr.get("TipoRelacion"), "uuid": (x.get("UUID") or "").upper()})
    pagos, nomina = [], 0.0
    if comp is not None:
        for el in comp.iter():
            if not isinstance(el.tag, str):
                continue
            n = _ln(el)
            if n == "Pago":
                fecha = (el.get("FechaPago") or "")[:10]
                for d in _kids(el, "DoctoRelacionado"):
                    pagos.append({"uuid": (d.get("IdDocumento") or "").upper(), "imp": _num(d.get("ImpPagado")),
                                  "fecha": fecha, "forma": el.get("FormaDePagoP")})
            elif n == "Nomina":
                nomina = _num(el.get("TotalPercepciones"))
    return {
        "uuid": tfd.get("UUID").upper(), "fecha": (g("Fecha") or "")[:10], "tipo": g("TipoDeComprobante"),
        "serie": g("Serie") or "", "folio": g("Folio") or "", "moneda": g("Moneda"), "tc": _num(g("TipoCambio")) or 1,
        "subtotal": _num(g("SubTotal")), "descuento": _num(g("Descuento")), "total": _num(g("Total")),
        "metodo": g("MetodoPago") or "", "forma": g("FormaPago") or "",
        "emRfc": (em.get("Rfc") if em is not None else "").upper(), "emNom": em.get("Nombre") if em is not None else "",
        "emReg": em.get("RegimenFiscal") if em is not None else "",
        "rcRfc": (rc.get("Rfc") if rc is not None else "").upper(), "rcNom": rc.get("Nombre") if rc is not None else "",
        "rcReg": rc.get("RegimenFiscalReceptor") if rc is not None else "", "uso": rc.get("UsoCFDI") if rc is not None else "",
        "conceptos": " · ".join(conceptos[:6]), "rel": rel, "pagos": pagos, "nomina": nomina,
    }


def guardar_xmls(blobs, rfc_dueno, origen):
    """blobs: iterable de bytes XML. Devuelve (leidos, nuevos, errores)."""
    leidos = nuevos = errores = 0
    with db() as c:
        for raw in blobs:
            d = parse_cfdi(raw)
            if not d:
                errores += 1
                continue
            leidos += 1
            existe = c.execute("SELECT 1 FROM cfdi WHERE uuid=?", (d["uuid"],)).fetchone()
            c.execute(
                "INSERT OR REPLACE INTO cfdi(uuid,rfc_dueno,data,xml,origen,creado) VALUES(?,?,?,?,?,COALESCE((SELECT creado FROM cfdi WHERE uuid=?),?))",
                (d["uuid"], rfc_dueno, json.dumps(d, ensure_ascii=False), raw.decode("utf-8", "replace"), origen, d["uuid"], now_iso()),
            )
            if not existe:
                nuevos += 1
    return leidos, nuevos, errores


def xmls_de_zip(data: bytes):
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for n in z.namelist():
            if n.lower().endswith(".xml"):
                yield z.read(n)


def guardar_metadata_zip(data: bytes):
    """Metadata del SAT: archivos .txt separados por '~' con encabezado."""
    n = 0
    with zipfile.ZipFile(io.BytesIO(data)) as z, db() as c:
        for name in z.namelist():
            if not name.lower().endswith(".txt"):
                continue
            lines = z.read(name).decode("utf-8", "replace").lstrip("﻿").splitlines()
            if not lines:
                continue
            head = [h.strip().lower() for h in lines[0].split("~")]
            iu, ie = head.index("uuid"), head.index("estatus")
            ifc = head.index("fechacancelacion") if "fechacancelacion" in head else None
            for ln in lines[1:]:
                p = ln.split("~")
                if len(p) <= max(iu, ie):
                    continue
                c.execute(
                    "INSERT OR REPLACE INTO estatus(uuid,estatus,fecha_cancelacion,actualizado) VALUES(?,?,?,?)",
                    (p[iu].strip().upper(), "Vigente" if p[ie].strip() == "1" else "Cancelado",
                     (p[ifc].strip() if ifc is not None and ifc < len(p) else "") or None, now_iso()),
                )
                n += 1
    return n


# ---------------------------------------------------------------- e.firma cifrada
def _fernet():
    if len(MASTER_KEY) < 16:
        raise HTTPException(500, "Falta la variable MASTER_KEY (mínimo 16 caracteres) en el servidor.")
    import hashlib
    # MASTER_KEY puede ser cualquier frase larga; se deriva una llave Fernet de 32 bytes.
    return Fernet(base64.urlsafe_b64encode(hashlib.sha256(MASTER_KEY.encode()).digest()))


def fiel_info_de_cer(cer_der: bytes):
    cert = x509.load_der_x509_certificate(cer_der)
    rfc = ""
    for attr in cert.subject:
        # El SAT pone el RFC en x500UniqueIdentifier (2.5.4.45): "RFC / CURP"
        if attr.oid.dotted_string == "2.5.4.45":
            rfc = attr.value.split("/")[0].strip()
    nombre = next((a.value for a in cert.subject if a.oid.dotted_string == "2.5.4.3"), "")
    return {
        "rfc": rfc.upper(),
        "nombre": nombre,
        "vence": cert.not_valid_after_utc.astimezone(TZ).date().isoformat(),
        "serie": format(cert.serial_number, "x"),
    }


def cargar_fiel():
    if not os.path.exists(FIEL_PATH):
        return None, None
    try:
        payload = json.loads(_fernet().decrypt(open(FIEL_PATH, "rb").read()))
    except (InvalidToken, ValueError):
        evento("No se pudo descifrar la e.firma guardada (¿cambió MASTER_KEY?).", "error")
        return None, None
    cer = base64.b64decode(payload["cer"])
    key = base64.b64decode(payload["key"])
    return Fiel(cer, key, payload["pwd"]), fiel_info_de_cer(cer)


# ---------------------------------------------------------------- SAT: solicitudes
def _token(fiel):
    return Autenticacion(fiel).obtener_token()


def crear_solicitud(fiel, rfc, direccion, tipo, desde: dt.datetime, hasta: dt.datetime, token=None):
    token = token or _token(fiel)
    estado = "Vigente" if tipo == "CFDI" else "Cancelado"
    kw = dict(token=token, rfc_solicitante=rfc, fecha_inicial=desde, fecha_final=hasta,
              tipo_solicitud=tipo, estado_comprobante=estado)
    if direccion == "emitidas":
        res = SolicitaDescargaEmitidos(fiel, timeout=60).solicitar_descarga(rfc_emisor=rfc, **kw)
    else:
        res = SolicitaDescargaRecibidos(fiel, timeout=60).solicitar_descarga(rfc_receptor=rfc, **kw)
    sid, cod, msg = res.get("id_solicitud"), res.get("cod_estatus"), res.get("mensaje")
    rango = f"{desde:%Y-%m-%d} a {hasta:%Y-%m-%d}"
    if cod != "5000" or not sid:
        evento(f"SAT rechazó solicitud {tipo} {direccion} {rango}: {cod} {msg}", "warn")
        return None
    with db() as c:
        c.execute(
            "INSERT OR REPLACE INTO solicitudes(id,rfc,direccion,tipo,desde,hasta,estado,mensaje,numero,creado,actualizado) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
            (sid, rfc, direccion, tipo, desde.isoformat(), hasta.isoformat(), "pendiente", msg, None, now_iso(), now_iso()),
        )
    evento(f"Solicitud {tipo} {direccion} {rango} aceptada por el SAT.")
    return sid


def _ventanas(desde: dt.datetime, hasta: dt.datetime, dias=31):
    """Parte rangos largos en ventanas mensuales para no topar límites del SAT."""
    a = desde
    while a < hasta:
        b = min(a + dt.timedelta(days=dias) - dt.timedelta(seconds=1), hasta)
        yield a, b
        a = b + dt.timedelta(seconds=1)


def solicitar_rango(fiel, rfc, desde, hasta, incluir_metadata=True):
    token = _token(fiel)
    ok = 0
    for a, b in _ventanas(desde, hasta):
        for d in ("emitidas", "recibidas"):
            ok += bool(crear_solicitud(fiel, rfc, d, "CFDI", a, b, token))
    if incluir_metadata:
        for d in ("emitidas", "recibidas"):
            ok += bool(crear_solicitud(fiel, rfc, d, "Metadata", desde, hasta, token))
    return ok


def verificar_pendientes(fiel, rfc):
    with db() as c:
        pend = [dict(r) for r in c.execute("SELECT * FROM solicitudes WHERE estado='pendiente' AND rfc=?", (rfc,))]
    if not pend:
        return 0
    token = _token(fiel)
    hechas = 0
    for s in pend:
        try:
            v = VerificaSolicitudDescarga(fiel, timeout=60).verificar_descarga(token, rfc, s["id"])
        except Exception as e:  # red del SAT intermitente
            evento(f"No se pudo verificar {s['id']}: {e}", "warn")
            continue
        est = str(v.get("estado_solicitud") or "")
        cod_sol = str(v.get("codigo_estado_solicitud") or "")
        if est in ("1", "2"):
            continue
        nuevo_estado, numero = "error", int(v.get("numero_cfdis") or 0)
        if est == "3":
            total_nuevos = 0
            for pid in v.get("paquetes") or []:
                r = DescargaMasiva(fiel, timeout=120).descargar_paquete(token, rfc, pid)
                if not r.get("paquete_b64"):
                    evento(f"Paquete {pid} vacío: {r.get('cod_estatus')} {r.get('mensaje')}", "warn")
                    continue
                data = base64.b64decode(r["paquete_b64"])
                if s["tipo"] == "CFDI":
                    _, nuevos, _ = guardar_xmls(xmls_de_zip(data), rfc, "sat-ws")
                    total_nuevos += nuevos
                else:
                    guardar_metadata_zip(data)
            nuevo_estado = "terminada"
            if s["tipo"] == "CFDI":
                evento(f"Descargadas {numero} {s['direccion']} ({total_nuevos} nuevas) {s['desde'][:10]} a {s['hasta'][:10]}.")
        elif cod_sol == "5004":  # "No se encontró la información": rango sin facturas
            nuevo_estado = "sin_datos"
        else:
            nuevo_estado = "vencida" if est == "6" else "error"
            evento(f"Solicitud {s['tipo']} {s['direccion']} terminó con estado {est} ({cod_sol}) {v.get('mensaje')}", "warn")
        with db() as c:
            c.execute("UPDATE solicitudes SET estado=?, mensaje=?, numero=?, actualizado=? WHERE id=?",
                      (nuevo_estado, v.get("mensaje"), numero, now_iso(), s["id"]))
        hechas += 1
    return hechas


# ---------------------------------------------------------------- ciclo automático
_sync_lock = threading.Lock()


def ciclo(forzar_diario=False):
    if not _sync_lock.acquire(blocking=False):
        return
    try:
        fiel, info = cargar_fiel()
        if not fiel:
            return
        rfc = info["rfc"]
        ahora = dt.datetime.now(TZ).replace(tzinfo=None, microsecond=0)
        hoy = ahora.date().isoformat()

        # 1) Primera carga: desde el 1 de enero (o BACKFILL_FROM)
        if not kv_get(f"backfill:{rfc}"):
            desde = dt.datetime.fromisoformat(BACKFILL_FROM) if BACKFILL_FROM else dt.datetime(ahora.year, 1, 1)
            evento(f"Primera carga desde {desde:%Y-%m-%d} para {rfc}.")
            if solicitar_rango(fiel, rfc, desde, ahora - dt.timedelta(minutes=5)):
                kv_set(f"backfill:{rfc}", hoy)
                kv_set(f"diario:{rfc}", hoy)
            else:
                evento("El SAT no aceptó ninguna solicitud de la primera carga; se reintenta en el siguiente ciclo.", "warn")

        # 2) Diario a las SYNC_HOUR: últimos 7 días de CFDI + cancelados del año
        elif forzar_diario or (kv_get(f"diario:{rfc}") != hoy and ahora.hour >= SYNC_HOUR):
            desde = ahora - dt.timedelta(days=7)
            evento("Sincronización diaria con el SAT.")
            token = _token(fiel)
            for d in ("emitidas", "recibidas"):
                crear_solicitud(fiel, rfc, d, "CFDI", desde.replace(hour=0, minute=0, second=0), ahora - dt.timedelta(minutes=5), token)
            inicio_meta = dt.datetime(ahora.year - (1 if ahora.month == 1 else 0), 1, 1)
            for d in ("emitidas", "recibidas"):
                crear_solicitud(fiel, rfc, d, "Metadata", inicio_meta, ahora - dt.timedelta(minutes=5), token)
            kv_set(f"diario:{rfc}", hoy)

        # 3) Revisar y bajar lo que el SAT ya tenga listo
        if verificar_pendientes(fiel, rfc):
            kv_set("ultima_descarga", now_iso())
    except Exception as e:
        evento(f"Error en sincronización: {e}", "error")
    finally:
        _sync_lock.release()


def _loop():
    time.sleep(20)
    while True:
        ciclo()
        time.sleep(CHECK_EVERY)


threading.Thread(target=_loop, daemon=True).start()

# ---------------------------------------------------------------- API
app = FastAPI(title="facturas-sync", docs_url=None, redoc_url=None)
app.add_middleware(
    CORSMiddleware, allow_origins=ALLOWED_ORIGINS, allow_methods=["*"],
    allow_headers=["Authorization", "Content-Type"], max_age=3600,
)
_g_req = g_requests.Request()


def usuario(request: Request):
    h = request.headers.get("Authorization", "")
    if not h.startswith("Bearer "):
        raise HTTPException(401, "Inicia sesión con Google.")
    try:
        info = g_id_token.verify_oauth2_token(h[7:], _g_req, GOOGLE_CLIENT_ID)
    except Exception:
        raise HTTPException(401, "Sesión vencida. Vuelve a iniciar sesión.")
    email = (info.get("email") or "").lower()
    if not info.get("email_verified") or email not in ALLOWED_EMAILS:
        raise HTTPException(403, f"{email} no tiene acceso a esta app.")
    return email


@app.get("/health")
def health():
    return {"ok": True}


@app.get("/api/config")
def config():
    return {"google_client_id": GOOGLE_CLIENT_ID}


@app.get("/api/status")
def status(email=Depends(usuario)):
    _, info = cargar_fiel()
    with db() as c:
        n = c.execute("SELECT COUNT(*) n FROM cfdi").fetchone()["n"]
        sol = [dict(r) for r in c.execute("SELECT direccion,tipo,desde,hasta,estado,numero,mensaje,actualizado FROM solicitudes ORDER BY creado DESC LIMIT 30")]
        ev = [dict(r) for r in c.execute("SELECT fecha,nivel,mensaje FROM eventos ORDER BY id DESC LIMIT 15")]
        pend = c.execute("SELECT COUNT(*) n FROM solicitudes WHERE estado='pendiente'").fetchone()["n"]
    vence_en = None
    if info:
        vence_en = (dt.date.fromisoformat(info["vence"]) - dt.datetime.now(TZ).date()).days
    return {
        "usuario": email, "fiel": info, "fiel_vence_en_dias": vence_en, "cfdi": n, "pendientes": pend,
        "ultima_descarga": kv_get("ultima_descarga"), "ultimo_diario": kv_get(f"diario:{info['rfc']}") if info else None,
        "solicitudes": sol, "eventos": ev, "hora_sync": SYNC_HOUR,
    }


@app.get("/api/cfdi")
def lista_cfdi(email=Depends(usuario)):
    with db() as c:
        est = {r["uuid"]: (r["estatus"], r["fecha_cancelacion"]) for r in c.execute("SELECT * FROM estatus")}
        out = []
        for r in c.execute("SELECT data FROM cfdi"):
            d = json.loads(r["data"])
            e = est.get(d["uuid"])
            d["estatus"] = e[0] if e else "Vigente"
            d["cancelado_en"] = e[1] if e else None
            out.append(d)
    return JSONResponse(out, headers={"Cache-Control": "no-store"})


@app.get("/api/xml/{uuid}")
def xml(uuid: str, email=Depends(usuario)):
    with db() as c:
        r = c.execute("SELECT xml FROM cfdi WHERE uuid=?", (uuid.upper(),)).fetchone()
    if not r:
        raise HTTPException(404, "No encontrado")
    return Response(r["xml"], media_type="application/xml",
                    headers={"Content-Disposition": f'attachment; filename="{uuid.upper()}.xml"'})


@app.post("/api/upload")
async def upload(files: list[UploadFile] = File(...), email=Depends(usuario)):
    _, info = cargar_fiel()
    rfc = info["rfc"] if info else ""
    tot = [0, 0, 0]
    for f in files:
        data = await f.read()
        name = (f.filename or "").lower()
        try:
            blobs = list(xmls_de_zip(data)) if name.endswith(".zip") else [data]
        except zipfile.BadZipFile:
            tot[2] += 1
            continue
        r = guardar_xmls(blobs, rfc, "manual")
        tot = [a + b for a, b in zip(tot, r)]
    evento(f"{email} cargó {tot[0]} XML a mano ({tot[1]} nuevos).")
    return {"leidos": tot[0], "nuevos": tot[1], "errores": tot[2]}


@app.post("/api/fiel")
async def subir_fiel(cer: UploadFile = File(...), key: UploadFile = File(...), password: str = Form(...),
                     email=Depends(usuario)):
    cer_der, key_der = await cer.read(), await key.read()
    try:
        info = fiel_info_de_cer(cer_der)
    except Exception:
        raise HTTPException(400, "El archivo .cer no es un certificado válido.")
    try:
        fiel = Fiel(cer_der, key_der, password)
    except Exception:
        raise HTTPException(400, "La contraseña no abre el archivo .key (o el .key no corresponde).")
    if info["vence"] < dt.datetime.now(TZ).date().isoformat():
        raise HTTPException(400, f"Esta e.firma venció el {info['vence']}. Hay que renovarla en el SAT.")
    try:
        _token(fiel)
    except Exception as e:
        raise HTTPException(400, f"El SAT no aceptó la e.firma: {e}")
    blob = _fernet().encrypt(json.dumps({
        "cer": base64.b64encode(cer_der).decode(), "key": base64.b64encode(key_der).decode(), "pwd": password,
    }).encode())
    tmp = FIEL_PATH + ".tmp"
    with open(tmp, "wb") as fh:
        fh.write(blob)
    os.replace(tmp, FIEL_PATH)
    evento(f"{email} cargó la e.firma de {info['rfc']} (vence {info['vence']}).")
    threading.Thread(target=ciclo, daemon=True).start()
    return {"ok": True, "fiel": info}


@app.delete("/api/fiel")
def borrar_fiel(email=Depends(usuario)):
    if os.path.exists(FIEL_PATH):
        os.remove(FIEL_PATH)
    evento(f"{email} borró la e.firma del servidor.", "warn")
    return {"ok": True}


@app.post("/api/sync")
def sync_ahora(email=Depends(usuario)):
    fiel, _ = cargar_fiel()
    if not fiel:
        raise HTTPException(400, "Primero carga la e.firma.")
    threading.Thread(target=ciclo, kwargs={"forzar_diario": True}, daemon=True).start()
    return {"ok": True, "mensaje": "Solicitud enviada al SAT. Las facturas llegan en minutos u horas, según el SAT."}


# ---------------------------------------------------------------- verificar antes de pagar
LISTA_69B_URL = os.environ.get(
    "LISTA_69B_URL", "http://omawww.sat.gob.mx/cifras_sat/Documents/Listado_Completo_69-B.csv"
)
LISTA_69B_PATH = os.path.join(DATA_DIR, "lista69b.json")
_69b_lock = threading.Lock()
_69b_mem = {"fecha": None, "rfcs": {}}


def lista_69b():
    """Lista 69-B (EFOS) del SAT, cacheada 24 h en el volumen. Devuelve (dict rfc->situacion, fecha)."""
    import requests
    with _69b_lock:
        if not _69b_mem["fecha"] and os.path.exists(LISTA_69B_PATH):
            try:
                _69b_mem.update(json.load(open(LISTA_69B_PATH)))
            except Exception:
                pass
        fresca = _69b_mem["fecha"] and (dt.datetime.now(TZ) - dt.datetime.fromisoformat(_69b_mem["fecha"])).total_seconds() < 86400
        if fresca:
            return _69b_mem["rfcs"], _69b_mem["fecha"]
        try:
            r = requests.get(LISTA_69B_URL, timeout=60)
            r.raise_for_status()
            txt = r.content.decode("latin-1")
            rfcs = {}
            col_rfc = col_sit = None
            for line in txt.splitlines():
                cols = [c.strip().strip('"') for c in line.split(",")]
                low = [c.lower() for c in cols]
                if col_rfc is None:
                    if "rfc" in low:
                        col_rfc = low.index("rfc")
                        col_sit = next((i for i, c in enumerate(low) if c.startswith("situaci")), None)
                    continue
                if len(cols) > col_rfc and len(cols[col_rfc]) in (12, 13):
                    rfcs[cols[col_rfc].upper()] = cols[col_sit] if col_sit is not None and col_sit < len(cols) else "En lista"
            if len(rfcs) > 1000:
                _69b_mem.update({"fecha": now_iso(), "rfcs": rfcs})
                json.dump(_69b_mem, open(LISTA_69B_PATH, "w"))
                evento(f"Lista 69-B del SAT actualizada ({len(rfcs)} RFC).")
            else:
                evento("La lista 69-B descargada vino incompleta; se conserva la anterior.", "warn")
        except Exception as e:
            evento(f"No se pudo descargar la lista 69-B: {e}", "warn")
        return _69b_mem["rfcs"], _69b_mem["fecha"]


def consulta_estado_sat(rfc_emisor, rfc_receptor, total_str, uuid):
    """Servicio público de verificación de CFDI del SAT (el mismo del código QR)."""
    import requests
    from xml.sax.saxutils import escape
    expr = f"?re={escape(rfc_emisor)}&rr={escape(rfc_receptor)}&tt={escape(total_str)}&id={escape(uuid)}"
    body = ('<soapenv:Envelope xmlns:soapenv="http://schemas.xmlsoap.org/soap/envelope/" xmlns:tem="http://tempuri.org/">'
            '<soapenv:Header/><soapenv:Body><tem:Consulta><tem:expresionImpresa><![CDATA[' + expr +
            ']]></tem:expresionImpresa></tem:Consulta></soapenv:Body></soapenv:Envelope>')
    r = requests.post(
        "https://consultaqr.facturaelectronica.sat.gob.mx/ConsultaCFDIService.svc", data=body.encode(),
        headers={"Content-Type": 'text/xml;charset="utf-8"', "SOAPAction": "http://tempuri.org/IConsultaCFDIService/Consulta"},
        timeout=30,
    )
    r.raise_for_status()
    root = etree.fromstring(r.content)
    out = {}
    for el in root.iter():
        if isinstance(el.tag, str) and _ln(el) in ("CodigoEstatus", "Estado", "EsCancelable", "EstatusCancelacion", "ValidacionEFOS"):
            out[_ln(el)] = (el.text or "").strip()
    return out


def verificar_xml(raw: bytes, rfc_mio: str):
    d = parse_cfdi(raw)
    if not d:
        return {"ok": False, "error": "No es un XML de factura (CFDI) válido. Necesito el .xml, no el PDF."}
    root = etree.fromstring(raw[raw.find(b"<"):])
    total_str = root.get("Total") or str(d["total"])
    checks = []

    def chk(nivel, titulo, detalle=""):
        checks.append({"nivel": nivel, "titulo": titulo, "detalle": detalle})

    # 1) ¿Existe en el SAT y está vigente?
    sat = None
    try:
        sat = consulta_estado_sat(d["emRfc"], d["rcRfc"], total_str, d["uuid"])
        est = (sat.get("Estado") or "").lower()
        if est == "vigente":
            chk("ok", "Registrada en el SAT y vigente", sat.get("CodigoEstatus", ""))
        elif est == "cancelado":
            chk("bad", "El SAT la reporta CANCELADA", "No la pagues: pide al proveedor la factura que la sustituye.")
        else:
            chk("pend", "El SAT todavía no la encuentra",
                "Si se timbró hace poco puede tardar hasta 72 h en aparecer. Si pasan más de 3 días, es falsa o tiene datos alterados.")
    except Exception as e:
        chk("pend", "No se pudo consultar al SAT en este momento", f"Intenta de nuevo en unos minutos. ({e})")

    # 2) Lista negra 69-B
    rfcs69, fecha69 = lista_69b()
    sit = rfcs69.get(d["emRfc"])
    if sit:
        s = sit.lower()
        if "desvirt" in s or "favorable" in s:
            chk("warn", f"El proveedor estuvo en la lista 69-B ({sit})", "Salió de la lista; normalmente sí es deducible. Confírmalo con tu contador.")
        else:
            chk("bad", f"Proveedor en la lista negra 69-B del SAT: {sit}",
                "Facturas de empresas fantasma (EFOS): no son deducibles y te pueden generar problemas con el SAT. No pagues sin hablar con tu contador.")
    elif fecha69:
        chk("ok", "El proveedor no está en la lista negra 69-B", f"Lista del SAT consultada el {fecha69[:10]}.")
    else:
        chk("pend", "No se pudo revisar la lista 69-B del SAT", "Intenta de nuevo más tarde.")

    # 3) A quién está facturada
    if rfc_mio and d["rcRfc"] != rfc_mio:
        chk("bad", f"Está facturada a otro RFC ({d['rcRfc']})", f"Tu RFC es {rfc_mio}. Pide que la refacturen a tu nombre.")
    else:
        chk("ok", "Facturada a tu RFC", d["rcRfc"])
    if d["rcReg"] and d["rcReg"] not in ("612", "626"):
        chk("bad", f"Régimen equivocado ({d['rcReg']})", "Debe ir a tu régimen 612 (actividades empresariales y profesionales). Pide que la refacturen.")
    else:
        chk("ok", "Régimen correcto", d["rcReg"] or "")

    # 4) Uso del CFDI
    uso = d["uso"] or ""
    if uso == "S01":
        chk("bad", "Uso S01: sin efectos fiscales", "Así NO es deducible. Pide que la refacturen con uso G03.")
    elif re_uso_ok(uso):
        chk("ok", f"Uso {uso} deducible para tu actividad", "")
    elif uso.startswith("D"):
        chk("warn", f"Uso {uso}: deducción personal", "Sirve en tu declaración anual, no como gasto del consultorio. Si es gasto del consultorio, pide uso G03.")
    else:
        chk("warn", f"Uso {uso} poco común", "Confírmalo con tu contador.")

    # 5) Forma y método de pago
    if d["forma"] == "01" and d["total"] > 2000:
        chk("bad", "Dice pago en EFECTIVO por más de $2,000", "Así no es deducible. Paga por transferencia o tarjeta y pide que la factura lo diga.")
    if d["metodo"] == "PUE":
        mes = d["fecha"][:7]
        chk("info" if mes == dt.datetime.now(TZ).strftime("%Y-%m") else "bad",
            "Pago en una sola exhibición (PUE)",
            f"Págala dentro del mismo mes en que se emitió ({mes}). Si la pagas después, debió venir en PPD con complemento de pago.")
    elif d["metodo"] == "PPD":
        chk("warn", "Pago en parcialidades o diferido (PPD)",
            "Después de pagar, el proveedor DEBE mandarte el complemento de pago; sin él no es deducible.")

    # 6) ¿Ya la tenemos?
    with db() as c:
        ya = c.execute("SELECT origen, creado FROM cfdi WHERE uuid=?", (d["uuid"],)).fetchone()
    if ya:
        chk("ok", "Ya está en tu sistema", f"Descargada el {ya['creado'][:10]}.")

    niveles = {x["nivel"] for x in checks}
    peor = next((n for n in ("bad", "pend", "warn") if n in niveles), "ok")
    veredicto = {"ok": "Puedes pagarla", "warn": "Puedes pagarla, con las precauciones marcadas",
                 "pend": "Falta confirmar con el SAT: vuelve a verificar antes de pagar",
                 "bad": "No la pagues todavía"}[peor]
    return {"ok": True, "veredicto": veredicto, "nivel": peor, "cfdi": d, "sat": sat, "checks": checks}


def re_uso_ok(uso):
    import re
    return bool(re.match(r"^(G0[1-3]|I0[1-8])$", uso or ""))


@app.post("/api/verificar")
async def verificar(files: list[UploadFile] = File(...), email=Depends(usuario)):
    _, info = cargar_fiel()
    rfc = info["rfc"] if info else ""
    res = []
    for f in files:
        data = await f.read()
        name = (f.filename or "").lower()
        if name.endswith(".zip"):
            try:
                blobs = list(xmls_de_zip(data))
            except zipfile.BadZipFile:
                res.append({"ok": False, "archivo": f.filename, "error": "ZIP dañado."})
                continue
        elif name.endswith(".pdf"):
            res.append({"ok": False, "archivo": f.filename, "error": "Es el PDF. Para verificar necesito el archivo .xml de la factura."})
            continue
        else:
            blobs = [data]
        for b in blobs:
            r = verificar_xml(b, rfc)
            r["archivo"] = f.filename
            res.append(r)
    evento(f"{email} verificó {len(res)} factura(s) antes de pagar.")
    return res
