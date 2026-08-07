#!/usr/bin/env python3
"""
Flux BVB — monitor de știri pentru H2O, FP, TLV, SNP, SNG.

Ce face la fiecare rulare:
  1. citește sursele (Google News RSS pe fiecare companie, RSS-urile publicațiilor,
     plus rapoartele curente de pe bvb.ro)
  2. compară cu ce a văzut deja și păstrează doar ce e nou
  3. rescrie flux.html, ca pagina să fie proaspătă de fiecare dată când o deschizi
  4. trimite noutățile pe Telegram și pe e-mail

Fără dependențe externe: doar biblioteca standard Python 3.9+.

    python3 flux_bvb.py --test      verifică ce surse răspund
    python3 flux_bvb.py             rulare normală
    python3 flux_bvb.py --open      rulare + deschide pagina
    python3 flux_bvb.py --no-notify doar regenerează pagina
"""

from __future__ import annotations

import argparse
import hashlib
import html as htmlmod
import json
import os
import re
import smtplib
import ssl
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import parsedate_to_datetime
from pathlib import Path
from xml.etree import ElementTree

# --------------------------------------------------------------------------- #
# Configurare
# --------------------------------------------------------------------------- #

HERE = Path(__file__).resolve().parent
CONFIG_PATH = HERE / "config.json"
STATE_PATH = HERE / "state.json"
TEMPLATE_PATH = HERE / "flux_template.html"
OUTPUT_PATH = HERE / "flux.html"

UA = "Mozilla/5.0 (compatible; FluxBVB/1.0; monitor personal de știri)"
TIMEOUT = 25

TICKERS = [
    {"s": "H2O", "nume": "Hidroelectrica",      "cauta": "Hidroelectrica"},
    {"s": "FP",  "nume": "Fondul Proprietatea", "cauta": "Fondul Proprietatea"},
    {"s": "TLV", "nume": "Banca Transilvania",  "cauta": "Banca Transilvania"},
    {"s": "SNP", "nume": "OMV Petrom",          "cauta": "OMV Petrom"},
    {"s": "SNG", "nume": "Romgaz",              "cauta": "Romgaz"},
]

# RSS-uri de publicații. Scriptul le încearcă pe toate și le ignoră tăcut pe
# cele care nu răspund — adaugă sau șterge liber.
FEEDURI_GENERALE = [
    # Ziarul Financiar - tiparul real e /rss/<sectiune>, confirmat in cataloage publice
    ("Ziarul Financiar", "https://www.zf.ro/rss.xml"),
    ("ZF Burse", "https://www.zf.ro/rss/burse-fonduri-mutuale"),
    ("ZF Banci", "https://www.zf.ro/rss/banci-si-asigurari"),
    ("ZF Energie", "https://www.zf.ro/rss/companii/energie"),
    ("ZF Piata energiei", "https://www.zf.ro/rss/piata-energiei"),
    ("ZF 24", "https://www.zf.ro/rss/zf-24"),
    # Ziare.com - sectiuni numerice
    ("Ziare.com business", "https://www.ziare.com/rss/business.xml"),
    ("Ziare.com companii", "https://www.ziare.com/rss/47.xml"),
    ("Ziare.com investitii", "https://www.ziare.com/rss/48.xml"),
    # Restul presei economice
    ("HotNews economie", "https://www.hotnews.ro/rss/economie"),
    ("Mediafax economic", "https://www.mediafax.ro/economic.xml"),
    ("Stirile ProTV economie", "https://rss.stirileprotv.ro/stiri/economie/"),
    ("Capital", "https://www.capital.ro/usr/rss/index20.xml"),
    # Fluxuri WordPress (tiparul /feed)
    ("Economedia", "https://economedia.ro/feed"),
    ("Curs de Guvernare", "https://cursdeguvernare.ro/feed"),
    ("Financial Intelligence", "https://financialintelligence.ro/feed"),
    ("Profit.ro", "https://www.profit.ro/feed"),
    ("Bursa.ro", "https://www.bursa.ro/feed"),
    ("Wall-Street.ro", "https://www.wall-street.ro/feed"),
]

CATEGORII = [
    ("Dividende",    r"dividend|ex-date|data plat|randament|rascumpar|buyback|actiuni gratuite"),
    ("Rezultate",    r"profit|rezultate|raport (trimestrial|semestrial|anual)|cifra de afaceri|ebitda|venituri|marja"),
    ("Reglementare", r"anre|asf|consiliul concurent|amend|lege|ordonant|impozit|taxa|plafonar|reglementar|instant|proces|sanctiun"),
    ("Tranzactii",   r"achizit|preluare|vanzare de|fuziune|tranzacti|participat|pachet de actiuni|oferta publica|vinde|cumpar|cumper|achizitie"),
    ("Analiza",      r"analist|analiz|pret tinta|rating|recomandare|evaluare|target|fitch|moody|s&p|upgrade|downgrade"),
    ("Guvernanta",   r"\baga\b|agoa|agea|adunare|consiliu|director|ceo|mandat|convocare|actionariat|actionar"),
    ("Operational",  r"producti|investit|capacitat|proiect|foraj|sonda|platform|centrala|retehnolog|contract|livrare"),
    ("Piata",        r"bvb|bursa|indice|bet|sedint|rulaj|lichiditate|cotati|inchide|actiunile"),
]

# Etichetele afisate in pagina folosesc diacritice; tiparele de mai sus, nu.
AFISAT = {"Tranzactii": "Tranzac\u021bii", "Analiza": "Analiz\u0103",
          "Guvernanta": "Guvernan\u021b\u0103", "Operational": "Opera\u021bional",
          "Piata": "Pia\u021b\u0103"}

POZITIV = r"creste|crestere|urca|record|maxim|avans|castig|majorare|aprobat|finalizat|upgrade|depase|dubl|solid|puternic"
NEGATIV = r"scade|scadere|coboara|pierde|pierdere|minim|declin|corecti|downgrade|intarzier|slab|presiune"

# Cuvinte care decid singure tonul, indiferent de restul textului: fara ele,
# "amenda record" iese neutru, fiindca "record" anuleaza "amenda".
DECISIV_NEGATIV = (r"amend|sanctiun|anchet|dosar penal|insolvent|faliment|"
                   r"revocat|suspendat|respins|litigi|prejudici|demis|blocat")

_DIACRITICE = str.maketrans("ăâîșşțţĂÂÎȘŞȚŢ",
                            "aaissttAAISSTT")


def fara_diacritice(text: str) -> str:
    """Presa romaneasca scrie inconsecvent cu si fara diacritice; normalizam
    ca tiparele sa prinda ambele variante."""
    return text.translate(_DIACRITICE)


# --------------------------------------------------------------------------- #
# Utilitare
# --------------------------------------------------------------------------- #


def log(msg: str, quiet: bool = False) -> None:
    if not quiet:
        print(f"[{datetime.now():%H:%M:%S}] {msg}", flush=True)


def http_get(url: str, timeout: int = TIMEOUT) -> bytes:
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "application/rss+xml, application/xml, text/xml, text/html;q=0.9",
        "Accept-Language": "ro-RO,ro;q=0.9,en;q=0.8",
    })
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def curata(text: str) -> str:
    """Scoate tagurile HTML și normalizează spațiile."""
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = htmlmod.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def cheie(ticker: str, titlu: str) -> str:
    """Amprentă stabilă pentru deduplicare — aceeași știre din surse diferite
    are, de obicei, titluri aproape identice."""
    t = re.sub(r"[^a-z0-9 ]", "", fara_diacritice(titlu).lower())
    t = re.sub(r"\s+", " ", t).strip()[:90]
    return hashlib.sha1(f"{ticker}|{t}".encode("utf-8")).hexdigest()[:16]


def clasifica(titlu: str, rezumat: str) -> tuple[str, str, int]:
    text = fara_diacritice(f"{titlu} {rezumat}").lower()
    categorie = "Piata"
    for nume, tipar in CATEGORII:
        if re.search(tipar, text):
            categorie = nume
            break
    poz = len(re.findall(POZITIV, text))
    neg = len(re.findall(NEGATIV, text))
    if re.search(DECISIV_NEGATIV, text):
        sentiment = "negative"
    else:
        sentiment = "positive" if poz > neg else "negative" if neg > poz else "neutral"
    impact = 3
    if categorie in ("Dividende", "Rezultate", "Reglementare"):
        impact += 1
    if categorie == "Piata":
        impact -= 1
    return AFISAT.get(categorie, categorie), sentiment, max(1, min(5, impact))


def data_iso(valoare: str | None) -> str:
    if valoare:
        try:
            return parsedate_to_datetime(valoare).astimezone(timezone.utc).date().isoformat()
        except Exception:
            m = re.search(r"(\d{4})-(\d{2})-(\d{2})", valoare)
            if m:
                return m.group(0)
            m = re.search(r"(\d{2})[./](\d{2})[./](\d{4})", valoare)
            if m:
                return f"{m.group(3)}-{m.group(2)}-{m.group(1)}"
    return datetime.now(timezone.utc).date().isoformat()


# --------------------------------------------------------------------------- #
# Surse
# --------------------------------------------------------------------------- #


def parseaza_rss(continut: bytes, sursa_implicita: str) -> list[dict]:
    """Acceptă atât RSS 2.0 cât și Atom."""
    try:
        radacina = ElementTree.fromstring(continut)
    except ElementTree.ParseError:
        return []

    ns = {"atom": "http://www.w3.org/2005/Atom"}
    iesire: list[dict] = []

    for item in radacina.iter():
        eticheta = item.tag.split("}")[-1]
        if eticheta not in ("item", "entry"):
            continue

        def camp(*nume: str) -> str:
            for n in nume:
                el = item.find(n)
                if el is None:
                    el = item.find(f"atom:{n}", ns)
                if el is not None:
                    if el.text and el.text.strip():
                        return el.text.strip()
                    if el.get("href"):
                        return el.get("href", "")
            return ""

        titlu = curata(camp("title"))
        if not titlu:
            continue
        link = camp("link", "guid")
        rezumat = curata(camp("description", "summary", "content"))[:400]
        publicat = camp("pubDate", "published", "updated")
        sursa = curata(camp("source")) or sursa_implicita

        # Google News pune " - Publicația" la coada titlului
        if sursa_implicita == "Google News":
            taie = titlu.rfind(" - ")
            if taie > 25:
                sursa = titlu[taie + 3:]
                titlu = titlu[:taie]

        iesire.append({
            "titlu": titlu,
            "link": link,
            "rezumat": rezumat,
            "data": data_iso(publicat),
            "sursa": sursa,
        })
    return iesire


def google_news(interogare: str) -> list[dict]:
    url = ("https://news.google.com/rss/search?q="
           + urllib.parse.quote(f'"{interogare}"')
           + "&hl=ro&gl=RO&ceid=RO:ro")
    return parseaza_rss(http_get(url), "Google News")


def rapoarte_bvb(simbol: str) -> list[dict]:
    """Rapoartele curente de pe pagina emitentului. Best effort: dacă BVB
    își schimbă structura paginii, funcția returnează listă goală în loc
    să oprească rularea."""
    url = ("https://bvb.ro/FinancialInstruments/Details/"
           f"FinancialInstrumentsDetails.aspx?s={simbol}")
    try:
        pagina = http_get(url).decode("utf-8", "replace")
    except Exception:
        return []

    iesire: list[dict] = []
    # Titlurile rapoartelor apar ca linkuri către /FinancialInstruments/SelectedData/NewsItem/...
    tipar = re.compile(
        r'href="(?P<href>[^"]*NewsItem[^"]*)"[^>]*>(?P<titlu>[^<]{10,300})</a>',
        re.I)
    for m in tipar.finditer(pagina):
        titlu = curata(m.group("titlu"))
        if not titlu:
            continue
        href = htmlmod.unescape(m.group("href"))
        if href.startswith("/"):
            href = "https://bvb.ro" + href
        iesire.append({
            "titlu": titlu,
            "link": href,
            "rezumat": "",
            "data": datetime.now(timezone.utc).date().isoformat(),
            "sursa": "Raport BVB",
        })
        if len(iesire) >= 30:
            break
    return iesire


def potrivit(item: dict, tk: dict) -> bool:
    text = fara_diacritice(f"{item['titlu']} {item['rezumat']}").lower()
    nume = fara_diacritice(tk["nume"]).lower()
    if nume in text:
        return True
    # simbolul, dar numai ca și cuvânt de sine stătător, ca să nu prindă „SNP" din alt context
    return bool(re.search(rf"\b{tk['s'].lower()}\b", text))


def aduna(quiet: bool = False) -> tuple[list[dict], list[str]]:
    """Returnează (știri, jurnal_diagnostic)."""
    jurnal: list[str] = []
    brute: list[tuple[str, dict]] = []   # (ticker, item)

    for tk in TICKERS:
        try:
            gasite = google_news(tk["cauta"])
            jurnal.append(f"OK   Google News · {tk['s']} · {len(gasite)} titluri")
            brute += [(tk["s"], it) for it in gasite]
        except Exception as e:
            jurnal.append(f"EROARE Google News · {tk['s']} · {e}")
        time.sleep(1.0)  # politicos față de server

        try:
            rap = rapoarte_bvb(tk["s"])
            if rap:
                jurnal.append(f"OK   bvb.ro · {tk['s']} · {len(rap)} rapoarte")
            else:
                jurnal.append(f"GOL  bvb.ro · {tk['s']} · nimic extras (pagina s-a schimbat?)")
            brute += [(tk["s"], it) for it in rap]
        except Exception as e:
            jurnal.append(f"EROARE bvb.ro · {tk['s']} · {e}")
        time.sleep(1.0)

    for nume, url in FEEDURI_GENERALE:
        try:
            gasite = parseaza_rss(http_get(url), nume)
            atins = 0
            for it in gasite:
                for tk in TICKERS:
                    if potrivit(it, tk):
                        brute.append((tk["s"], it))
                        atins += 1
                        break
            jurnal.append(f"OK   {nume} · {len(gasite)} titluri, {atins} relevante")
        except Exception as e:
            jurnal.append(f"EROARE {nume} · {type(e).__name__}")
        time.sleep(0.6)

    # dedupe + normalizare în formatul folosit de pagină
    vazute: set[str] = set()
    stiri: list[dict] = []
    for ticker, it in brute:
        k = cheie(ticker, it["titlu"])
        if k in vazute:
            continue
        vazute.add(k)
        categorie, sentiment, impact = clasifica(it["titlu"], it["rezumat"])
        stiri.append({
            "id": k,
            "t": ticker,
            "d": it["data"],
            "h": it["titlu"],
            "s": it["rezumat"][:240],
            "src": it["sursa"],
            "c": categorie,
            "sent": sentiment,
            "i": impact,
            "u": it["link"],
        })

    stiri.sort(key=lambda x: (x["d"], x["i"]), reverse=True)
    return stiri, jurnal


# --------------------------------------------------------------------------- #
# Stare, pagină, notificări
# --------------------------------------------------------------------------- #


def incarca_stare() -> dict:
    if STATE_PATH.exists():
        try:
            return json.loads(STATE_PATH.read_text(encoding="utf-8"))
        except Exception:
            pass
    return {"vazute": {}}


def salveaza_stare(stare: dict) -> None:
    limita = (datetime.now(timezone.utc) - timedelta(days=120)).isoformat()
    stare["vazute"] = {k: v for k, v in stare["vazute"].items() if v > limita}
    STATE_PATH.write_text(json.dumps(stare, ensure_ascii=False), encoding="utf-8")


def scrie_pagina(stiri: list[dict], cfg: dict, iesire: Path | None = None) -> Path:
    if not TEMPLATE_PATH.exists():
        raise SystemExit(f"Lipsește șablonul: {TEMPLATE_PATH}")
    sablon = TEMPLATE_PATH.read_text(encoding="utf-8")

    pastreaza = int(cfg.get("stiri_in_pagina", 250))
    date = {
        "generat": datetime.now(timezone.utc).isoformat(),
        "stiri": stiri[:pastreaza],
    }
    # dividendele și termenele rămân cele din șablon dacă nu sunt definite în config
    for camp in ("dividende", "termene"):
        if cfg.get(camp):
            date[camp] = cfg[camp]

    payload = json.dumps(date, ensure_ascii=False).replace("</", "<\\/")
    pagina = sablon.replace("window.FLUX_DATA=null;/*__FLUX_DATA__*/",
                            f"window.FLUX_DATA={payload};")
    tinta = iesire or OUTPUT_PATH
    tinta.parent.mkdir(parents=True, exist_ok=True)
    tinta.write_text(pagina, encoding="utf-8")
    return tinta


def text_telegram(noi: list[dict], url_public: str = "") -> str:
    cap = f"<b>Flux BVB</b> — {len(noi)} știri noi"
    if url_public:
        cap += f'\n<a href="{htmlmod.escape(url_public)}">deschide pagina</a>'
    linii = [cap + "\n"]
    for tk in TICKERS:
        ale_lui = [x for x in noi if x["t"] == tk["s"]]
        if not ale_lui:
            continue
        linii.append(f"\n<b>{tk['s']}</b> · {htmlmod.escape(tk['nume'])}")
        for x in ale_lui[:6]:
            semn = {"positive": "▲", "negative": "▼"}.get(x["sent"], "•")
            titlu = htmlmod.escape(x["h"][:150])
            if x["u"]:
                linii.append(f'{semn} <a href="{htmlmod.escape(x["u"])}">{titlu}</a>'
                             f'\n   <i>{htmlmod.escape(x["src"])} · {x["c"]}</i>')
            else:
                linii.append(f'{semn} {titlu}\n   <i>{htmlmod.escape(x["src"])} · {x["c"]}</i>')
        if len(ale_lui) > 6:
            linii.append(f"   <i>… și încă {len(ale_lui) - 6}</i>")
    return "\n".join(linii)


def trimite_telegram(cfg: dict, mesaj: str, quiet: bool) -> None:
    token = cfg.get("telegram", {}).get("token") or os.getenv("FLUX_TG_TOKEN")
    chat = cfg.get("telegram", {}).get("chat_id") or os.getenv("FLUX_TG_CHAT")
    if not token or not chat:
        log("Telegram: neconfigurat, sar peste", quiet)
        return
    # Telegram taie la 4096 de caractere
    bucati = [mesaj[i:i + 3800] for i in range(0, len(mesaj), 3800)] or [mesaj]
    for bucata in bucati:
        date = urllib.parse.urlencode({
            "chat_id": chat,
            "text": bucata,
            "parse_mode": "HTML",
            "disable_web_page_preview": "true",
        }).encode()
        try:
            req = urllib.request.Request(
                f"https://api.telegram.org/bot{token}/sendMessage",
                data=date, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
                raspuns = json.loads(r.read())
            if not raspuns.get("ok"):
                log(f"Telegram: {raspuns}", quiet)
        except Exception as e:
            log(f"Telegram EROARE: {e}", quiet)
            return
    log(f"Telegram: trimis ({len(bucati)} mesaj/e)", quiet)


def html_email(noi: list[dict], cale_pagina: Path, url_public: str = "") -> str:
    p = ['<div style="font-family:-apple-system,Segoe UI,Roboto,sans-serif;'
         'max-width:640px;color:#12313A">',
         f'<h2 style="font-size:19px;margin:0 0 4px">Flux BVB — {len(noi)} știri noi</h2>',
         f'<p style="color:#7EA3AA;font-size:12px;margin:0 0 18px">'
         f'{datetime.now():%d.%m.%Y %H:%M} · pagina completă: '
         f'<a href="{htmlmod.escape(url_public or cale_pagina.as_uri())}">'
         f'{htmlmod.escape(url_public or cale_pagina.as_uri())}</a></p>']
    for tk in TICKERS:
        ale_lui = [x for x in noi if x["t"] == tk["s"]]
        if not ale_lui:
            continue
        p.append(f'<h3 style="font-size:14px;margin:18px 0 6px;padding-bottom:4px;'
                 f'border-bottom:1px solid #DDE7E8">{tk["s"]} · {htmlmod.escape(tk["nume"])}</h3>')
        for x in ale_lui:
            culoare = {"positive": "#1F9D63", "negative": "#C4483F"}.get(x["sent"], "#7EA3AA")
            titlu = htmlmod.escape(x["h"])
            titlu = (f'<a href="{htmlmod.escape(x["u"])}" style="color:#12313A;'
                     f'text-decoration:none">{titlu}</a>') if x["u"] else titlu
            p.append(f'<div style="margin:0 0 12px;padding-left:9px;'
                     f'border-left:3px solid {culoare}">'
                     f'<div style="font-size:14px;font-weight:600;line-height:1.35">{titlu}</div>'
                     + (f'<div style="font-size:12.5px;color:#4A6B72;margin-top:3px">'
                        f'{htmlmod.escape(x["s"])}</div>' if x["s"] else "")
                     + f'<div style="font-size:11px;color:#8AA5AB;margin-top:3px">'
                       f'{htmlmod.escape(x["src"])} · {x["c"]} · {x["d"]}</div></div>')
    p.append('<p style="font-size:11px;color:#8AA5AB;margin-top:22px">'
             'Categoriile și sentimentul sunt atribuite automat, după cuvinte-cheie. '
             'Nu sunt recomandări de investiție.</p></div>')
    return "".join(p)


def trimite_email(cfg: dict, subiect: str, corp_html: str, quiet: bool) -> None:
    e = cfg.get("email", {})
    gazda = e.get("smtp_host") or os.getenv("FLUX_SMTP_HOST")
    user = e.get("user") or os.getenv("FLUX_SMTP_USER")
    parola = e.get("parola") or os.getenv("FLUX_SMTP_PASS")
    catre = e.get("catre") or os.getenv("FLUX_MAIL_TO")
    if not (gazda and user and parola and catre):
        log("E-mail: neconfigurat, sar peste", quiet)
        return

    port = int(e.get("smtp_port", 587))
    msg = EmailMessage()
    msg["Subject"] = subiect
    msg["From"] = e.get("de_la", user)
    msg["To"] = catre
    msg.set_content(re.sub(r"<[^>]+>", " ", corp_html))
    msg.add_alternative(corp_html, subtype="html")

    try:
        ctx = ssl.create_default_context()
        if port == 465:
            with smtplib.SMTP_SSL(gazda, port, context=ctx, timeout=TIMEOUT) as s:
                s.login(user, parola)
                s.send_message(msg)
        else:
            with smtplib.SMTP(gazda, port, timeout=TIMEOUT) as s:
                s.starttls(context=ctx)
                s.login(user, parola)
                s.send_message(msg)
        log(f"E-mail: trimis către {catre}", quiet)
    except Exception as ex:
        log(f"E-mail EROARE: {ex}", quiet)


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #


def incarca_config() -> dict:
    if CONFIG_PATH.exists():
        try:
            return json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
        except Exception as e:
            raise SystemExit(f"config.json invalid: {e}")
    return {}


def main() -> int:
    ap = argparse.ArgumentParser(description="Monitor de știri BVB")
    ap.add_argument("--test", action="store_true", help="verifică sursele și ieși")
    ap.add_argument("--no-notify", action="store_true", help="nu trimite nimic")
    ap.add_argument("--open", action="store_true", help="deschide pagina la final")
    ap.add_argument("--quiet", action="store_true", help="fără mesaje în consolă")
    ap.add_argument("--reset", action="store_true", help="uită tot istoricul de deduplicare")
    ap.add_argument("--out", metavar="CALE", default=None,
                    help="unde se scrie pagina (implicit flux.html; pentru Pages: public/index.html)")
    args = ap.parse_args()

    cfg = incarca_config()

    if args.reset and STATE_PATH.exists():
        STATE_PATH.unlink()
        log("Stare ștearsă.", args.quiet)

    log("Citesc sursele…", args.quiet)
    stiri, jurnal = aduna(args.quiet)

    if args.test:
        print("\n--- diagnostic surse ---")
        for linie in jurnal:
            print(" ", linie)
        print(f"\n  total știri unice: {len(stiri)}")
        for tk in TICKERS:
            print(f"    {tk['s']}: {sum(1 for x in stiri if x['t'] == tk['s'])}")
        return 0

    print("--- surse ---", flush=True)
    for linie in jurnal:
        print("  " + linie, flush=True)

    stare = incarca_stare()
    acum = datetime.now(timezone.utc).isoformat()
    noi = [x for x in stiri if x["id"] not in stare["vazute"]]
    prima_rulare = not stare["vazute"]

    for x in stiri:
        stare["vazute"].setdefault(x["id"], acum)
    salveaza_stare(stare)

    if stiri:
        proaspete = sum(1 for x in stiri
                        if x["d"] >= (datetime.now(timezone.utc) - timedelta(days=1)).date().isoformat())
        print(f"--- {len(stiri)} stiri unice | cea mai recenta: {stiri[0]['d']} | "
              f"din ultimele 24h: {proaspete}", flush=True)
        for tk in TICKERS:
            ale = [x for x in stiri if x["t"] == tk["s"]]
            print(f"      {tk['s']}: {len(ale)}" + (f" (cea mai noua {ale[0]['d']})" if ale else ""),
                  flush=True)
    else:
        print("--- ATENTIE: zero stiri. Toate sursele au esuat.", flush=True)

    cale = scrie_pagina(stiri, cfg, Path(args.out) if args.out else None)
    log(f"Pagină scrisă: {cale}  ({len(stiri)} știri, {len(noi)} noi)", args.quiet)

    if noi and not args.no_notify:
        if prima_rulare:
            log("Prima rulare — nu trimit notificări pentru istoricul inițial.", args.quiet)
        else:
            url_pub = cfg.get("url_public") or os.getenv("FLUX_URL_PUBLIC", "")
            trimite_telegram(cfg, text_telegram(noi, url_pub), args.quiet)
            subiect = (f"Flux BVB · {len(noi)} știri noi · "
                       + ", ".join(sorted({x['t'] for x in noi})))
            url_pub = cfg.get("url_public") or os.getenv("FLUX_URL_PUBLIC", "")
            trimite_email(cfg, subiect, html_email(noi, cale, url_pub), args.quiet)
    elif not noi:
        log("Nimic nou de la ultima verificare.", args.quiet)

    if args.open:
        webbrowser.open(cale.as_uri())
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
