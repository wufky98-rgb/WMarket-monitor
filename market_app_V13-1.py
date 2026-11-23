# -*- coding: utf-8 -*-
"""
market_app_V13-1.py – Market Monitor jako webová aplikace (styl TradingView / Trading 212)

Python na pozadí stahuje ceny (Yahoo Finance) a zprávy (Google News + Yahoo),
prohlížeč zobrazuje tmavý dashboard s grafy. Vše běží jen u tebe na počítači.

Spuštění:   dvojklik na spustit_app.bat  (nebo: py market_app_V13-1.py)
            macOS: dvojklik na spustit_mac.command  (nebo: python3 market_app_V13-1.py)      (otevře se prohlížeč na http://localhost:8050)
Zastavení:  Ctrl + C v okně konzole
Knihovny:   py -m pip install yfinance feedparser requests
"""

import calendar
import hashlib
import hmac
import json
import logging
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
import urllib.parse
import webbrowser
from collections import deque
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ============================================================================
#  NASTAVENÍ
# ============================================================================

VERZE = "V13-1"                # V13-1: menu intervalu a seancí se otevírá přes graf (nebylo oříznuté)
                               # V13: šéfovy tipy na grafu (✓/✗), volba intervalu svíček, řazení watchlistu, bez kalendáře
                               # V12: SMC bot + kreslení SMC, 13 nových zdrojů zpráv, obchodní hodiny
                               # V11: 5. bot Scenárista – scénáře z grafu (úrovně, pivoty, ATR)
                               # V10: AI tým – 4 boti debatují (Groq), verdikt pod ukazatelem
                               # V9: webová verze (Render), přihlášení heslem, mobilní rozložení
                               # V8: Technická analýza, obchodní seance, nové zdroje zpráv (Reuters, EIA, Fed), kalendář ForexFactory
                               # V7: čitelný 1D graf (5min svíčky), oprava „plochých“ forex svíček, zprávy EUR/USD
                               # V6: ikony aktiv vlevo ve watchlistu a v hlavičce
                               # V5: oprava falešné svíčky na konci grafu, reset měřítka grafu při přepnutí
                               # V4: podpora macOS (spouštěč + aktualizace na Macu)
                               # V3: tlačítko pro automatickou aktualizaci (GitHub Releases)
                               # V2: kategorie v rámečcích (sbalitelné), oprava 1D grafu o víkendu, filtr zpráv
                               # V1: live grafy, BTC + stříbro, kategorie, zprávy à 5 min

PORT = 8050                    # port aplikace (když je obsazený, zkusí se další)
CENY_KAZDYCH_S = 60            # jak často obnovovat ceny (sekundy)
ZPRAVY_KAZDYCH_MIN = 5       # jak často hledat nové zprávy (minuty)
SKOK_OKNO_MIN = 15             # „skok“ = změna ceny za posledních X minut
MAX_STARI_ZPRAVY_HODIN = 48

# --- DALŠÍ ZDROJE ZPRÁV ---
#  typ "rss" = přímý RSS kanál webu (nejspolehlivější)
#  typ "web" = web prohledaný přes Google News (pro weby bez RSS, např. Reuters)
#  aktiva    = "vse" nebo seznam id aktiv (nvda, sndk, btc, eurusd, gold, silver, oil)
#  dotaz     = (jen u "web") co hledat; bez něj se použije dotaz daného aktiva
#  vse_zpravy= True → nefiltrovat podle klíčových slov a brát zprávy až 7 dní staré
#  ua        = (volitelné) vlastní User-Agent – SEC ho vyžaduje
#  Jestli nějaký zdroj nefunguje, uvidíš to v aplikaci: Zprávy → dole „Stav zdrojů“.
ZDROJE_ZPRAV = [
    {"typ": "web", "domena": "reuters.com", "nazev": "Reuters", "aktiva": "vse"},
    {"typ": "rss", "url": "https://www.eia.gov/about/new/WNtest3.php", "nazev": "EIA",
     "aktiva": ["oil"], "vse_zpravy": True},
    {"typ": "rss", "url": "https://www.eia.gov/rss/todayinenergy.xml", "nazev": "EIA – Today in Energy",
     "aktiva": ["oil"], "vse_zpravy": True},
    {"typ": "rss", "url": "https://www.federalreserve.gov/feeds/press_monetary.xml", "nazev": "Federal Reserve",
     "aktiva": ["eurusd", "gold", "silver"], "vse_zpravy": True},
    {"typ": "rss", "url": "https://www.federalreserve.gov/feeds/speeches.xml", "nazev": "Federal Reserve – projevy",
     "aktiva": ["eurusd", "gold"], "vse_zpravy": True},
    {"typ": "web", "domena": "frbsf.org", "nazev": "Fed San Francisco", "dotaz": "economy OR inflation OR rates",
     "aktiva": ["eurusd", "gold"], "vse_zpravy": True},
    # ---- V12: nové zdroje ----
    # Ropa
    {"typ": "rss", "url": "https://oilprice.com/rss/main", "nazev": "OilPrice.com", "aktiva": ["oil"]},
    {"typ": "web", "domena": "rigzone.com", "nazev": "Rigzone", "dotaz": "oil", "aktiva": ["oil"]},
    # Zlato a stříbro
    {"typ": "web", "domena": "kitco.com", "nazev": "Kitco", "aktiva": ["gold", "silver"]},
    # EUR/USD a centrální banky
    {"typ": "rss", "url": "https://www.ecb.europa.eu/rss/press.html", "nazev": "ECB",
     "aktiva": ["eurusd"], "vse_zpravy": True},
    {"typ": "web", "domena": "fxstreet.com", "nazev": "FXStreet", "aktiva": ["eurusd", "gold"]},
    {"typ": "rss", "url": "https://www.bls.gov/feed/bls_latest.rss", "nazev": "US Bureau of Labor Statistics",
     "aktiva": ["eurusd", "gold", "silver"], "vse_zpravy": True,
     "ua": "MarketMonitor/1.0 (personal app; contact: marketmonitor@example.com)"},
    # Akcie
    {"typ": "rss", "url": "https://www.cnbc.com/id/100003114/device/rss/rss.html", "nazev": "CNBC",
     "aktiva": ["nvda", "sndk"]},
    {"typ": "web", "domena": "marketwatch.com", "nazev": "MarketWatch", "aktiva": ["nvda", "sndk"]},
    {"typ": "rss", "url": "https://www.sec.gov/cgi-bin/browse-edgar?action=getcompany&CIK=NVDA&type=8-K&count=20&output=atom",
     "nazev": "SEC EDGAR – NVIDIA", "aktiva": ["nvda"], "vse_zpravy": True,
     "ua": "MarketMonitor/1.0 (personal app; contact: marketmonitor@example.com)"},
    {"typ": "rss", "url": "https://www.sec.gov/cgi-bin/browse-edgar?action=getcompany&CIK=SNDK&type=8-K&count=20&output=atom",
     "nazev": "SEC EDGAR – SanDisk", "aktiva": ["sndk"], "vse_zpravy": True,
     "ua": "MarketMonitor/1.0 (personal app; contact: marketmonitor@example.com)"},
    # Bitcoin
    {"typ": "rss", "url": "https://www.coindesk.com/arc/outboundfeeds/rss/", "nazev": "CoinDesk", "aktiva": ["btc"]},
    {"typ": "rss", "url": "https://cointelegraph.com/rss", "nazev": "Cointelegraph", "aktiva": ["btc"]},
    {"typ": "rss", "url": "https://decrypt.co/feed", "nazev": "Decrypt", "aktiva": ["btc"]},
    {"typ": "rss", "url": "https://www.theblock.co/rss.xml", "nazev": "The Block", "aktiva": ["btc"]},
]

# --- EKONOMICKÝ KALENDÁŘ (ForexFactory, veřejný týdenní feed) ---
KALENDAR_URL = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"
KALENDAR_MENY = ["USD", "EUR"]            # které měny zobrazit (např. přidej "GBP", "JPY", "CNY")
KALENDAR_DOPAD = ["High", "Medium"]       # High / Medium / Low / Holiday
KALENDAR_KAZDYCH_MIN = 60
KALENDAR_ZAPNUTO = False                  # V13: kalendář vypnutý (ForexFactory často odmítá – „429 Too Many Requests“)
OTEVRIT_PROHLIZEC = True

# --- WEBOVÁ VERZE (běh na serveru, např. Render.com) ---
# Na serveru se spouští s parametrem --server (nebo automaticky na Renderu).
# Heslo se NEpíše sem – nastavuje se na serveru jako proměnná prostředí MM_HESLO.
SERVER_MODE = "--server" in sys.argv or bool(os.environ.get("RENDER"))
HESLO = os.environ.get("MM_HESLO", "")

# --- AI TÝM (4 boti přes Groq – zdarma) ---
# Klíč získáš na console.groq.com → API Keys.  NIKDY ho nepiš do tohoto souboru!
#  • Web (Render): Environment → přidej proměnnou GROQ_API_KEY
#  • PC: vytvoř vedle aplikace soubor groq_klic.txt a vlož do něj klíč (tento soubor NENAHRÁVEJ na GitHub)
GROQ_MODEL = os.environ.get("GROQ_MODEL", "openai/gpt-oss-120b")
DEBATA_PLATNOST_MIN = 15       # jak dlouho platí výsledek debaty, než jde spustit znovu bez „Znovu“
HTTP_TIMEOUT = 15

# --- AUTOMATICKÉ AKTUALIZACE ---
# GitHub repozitář, kde vydáváš nové verze (záložka Releases), ve tvaru "uzivatel/repozitar".
# Prázdné = aktualizace vypnuté.  Návod je v odpovědi od Clauda / v souboru vytvor_exe.bat.
UPDATE_REPO = ""
UPDATE_KONTROLA_MIN = 30       # jak často hledat novou verzi (minuty)

# kat = kategorie pro záložky ve watchlistu: "akcie", "krypto", "forex", "komodity"
# Nové aktivum přidáš zkopírováním jednoho řádku a úpravou hodnot.
AKTIVA = [
    # --- Akcie ---
    # "barva" = barva kulatého odznaku s písmenem (jen pro aktiva bez vlastní ikony)
    {"id": "nvda",   "barva": "#76b900", "kat": "akcie",    "nazev": "NVIDIA",   "popis": "NVIDIA Corp.",     "tickers": ["NVDA"],
     "alert_den": 3.0, "alert_skok": 1.0,  "dotaz": "Nvidia stock",        "desetinna": 2, "mena": "USD",
     "slova": ["nvidia", "nvda"]},
    {"id": "sndk",   "barva": "#e4002b", "kat": "akcie",    "nazev": "SanDisk",  "popis": "SanDisk Corp.",    "tickers": ["SNDK", "WDC"],
     "alert_den": 4.0, "alert_skok": 1.5,  "dotaz": "SanDisk stock",       "desetinna": 2, "mena": "USD",
     "slova": ["sandisk", "sndk", "western digital", "nand", "flash memory", "memory chip"]},
    # --- Krypto ---
    {"id": "btc",    "kat": "krypto",   "nazev": "Bitcoin",  "popis": "Bitcoin / USD",    "tickers": ["BTC-USD"],
     "alert_den": 4.0, "alert_skok": 1.5,  "dotaz": "Bitcoin price",       "desetinna": 2, "mena": "USD",
     "slova": ["bitcoin", "btc", "crypto"]},
    # --- Forex ---
    {"id": "eurusd", "kat": "forex",    "nazev": "EUR/USD",  "popis": "Euro / US Dollar", "tickers": ["EURUSD=X"],
     "alert_den": 0.6, "alert_skok": 0.25, "dotaz": "EURUSD OR \"euro dollar\" OR \"EUR/USD\"", "desetinna": 5, "mena": "",
     "slova": ["euro", "eur/usd", "eurusd", "eur ", "dollar", "ecb", "fed", "forex", "currenc", "exchange rate", "lagarde", "powell"]},
    # --- Komodity ---
    {"id": "gold",   "kat": "komodity", "nazev": "Zlato",    "popis": "Gold Futures",     "tickers": ["GC=F"],
     "alert_den": 1.5, "alert_skok": 0.5,  "dotaz": "gold price",          "desetinna": 2, "mena": "USD",
     "slova": ["gold"]},
    {"id": "silver", "kat": "komodity", "nazev": "Stříbro",  "popis": "Silver Futures",   "tickers": ["SI=F"],
     "alert_den": 2.5, "alert_skok": 0.8,  "dotaz": "silver price",        "desetinna": 3, "mena": "USD",
     "slova": ["silver"]},
    {"id": "oil",    "kat": "komodity", "nazev": "Ropa WTI", "popis": "Crude Oil WTI",    "tickers": ["CL=F"],
     "alert_den": 2.5, "alert_skok": 1.0,  "dotaz": "WTI crude oil price", "desetinna": 2, "mena": "USD",
     "slova": ["oil", "crude", "opec", "brent", "wti"]},
]

# Obchodní hodiny podle kategorie (u aktiva jde přepsat klíčem "hodiny"):
#  "futures" (CME), "us_akcie" (burza USA), "forex", "krypto" (24/7)
VYCHOZI_HODINY = {"akcie": "us_akcie", "krypto": "krypto", "forex": "forex", "komodity": "futures"}

ROZSAHY = {  # tlačítko -> (period, interval) pro yfinance
    "1D": ("5d", "5m"), "5D": ("5d", "15m"), "1M": ("1mo", "60m"),
    "6M": ("6mo", "1d"), "1R": ("1y", "1d"), "5R": ("5y", "1wk"),
}

# Interval svíček (volba ⏱ v grafu): tlačítko -> (interval u Yahoo, sloučit na, délka v s; 0 = denní a delší)
# Yahoo nemá 10 min ani 4 h – skládají se z 5min a hodinových svíček.
INTERVALY = {
    "1m": ("1m", None, 60), "5m": ("5m", None, 300), "10m": ("5m", "10min", 600),
    "15m": ("15m", None, 900), "30m": ("30m", None, 1800), "1h": ("60m", None, 3600),
    "4h": ("60m", "4h", 14400), "1d": ("1d", None, 0), "1wk": ("1wk", None, 0), "1mo": ("1mo", None, 0),
}
VYCHOZI_IV = {"1D": "5m", "5D": "15m", "1M": "1h", "6M": "1d", "1R": "1d", "5R": "1wk"}


def perioda(rozsah: str, iv: str) -> str:
    """Jak daleko do minulosti stahovat – s ohledem na limity Yahoo
    (1min data jen ~7 dní, 5–30min jen ~60 dní, hodinová ~2 roky)."""
    yi = INTERVALY[iv][0]
    zaklad = {"1D": "5d", "5D": "5d", "1M": "1mo", "6M": "6mo", "1R": "1y", "5R": "5y"}[rozsah]
    if yi == "1m":
        return "5d" if rozsah in ("1D", "5D") else "7d"
    if yi in ("5m", "15m", "30m"):
        return zaklad if rozsah in ("1D", "5D", "1M") else "60d"
    if yi == "60m":
        return zaklad if rozsah != "5R" else "730d"
    if yi == "1d" and rozsah in ("1D", "5D"):
        return "1mo"
    if yi == "1wk" and rozsah in ("1D", "5D", "1M"):
        return "6mo"
    if yi == "1mo" and rozsah in ("1D", "5D", "1M", "6M"):
        return "2y"
    return zaklad

# ============================================================================

try:
    import yfinance as yf
    import feedparser
    import requests
    import pandas as pd
except ImportError as e:
    print(f"Chybí knihovna: {e.name}")
    print("Nainstaluj:  py -m pip install yfinance feedparser requests")
    input("Stiskni Enter pro ukončení…")
    sys.exit(1)

logging.getLogger("yfinance").setLevel(logging.CRITICAL)

YF_LOCK = threading.Lock()          # yfinance není úplně thread-safe
STAV_LOCK = threading.Lock()
STAV = {
    "aktualizovano": None,
    "zpravy_aktualizovano": None,
    "kotace": {},                   # id -> dict
    "zpravy": {},                   # id -> list
}
HISTORIE_CEN = {a["id"]: deque(maxlen=600) for a in AKTIVA}   # (ts, cena) pro detekci skoků
ZVOLENY_TICKER = {}
CACHE_GRAFU = {}                    # (id, rozsah) -> (ts, data)


# ----------------------------------------------------------------------------
#  Ceny
# ----------------------------------------------------------------------------

def ocisti_intraday(df, sekund: int):
    """Yahoo na konec minutových dat přidává řádek s aktuální/vypořádací cenou
    (čas mimo celou minutu, např. 22:59:58). Není to skutečná svíčka – na grafu
    pak vznikne falešný „spike“. Takové řádky zahodíme."""
    if df is None or df.empty:
        return df
    ts = [int(i.timestamp()) for i in df.index]
    ok = [t % 60 == 0 for t in ts]
    if len(ts) >= 2 and ok[-1] and ts[-1] - ts[-2] < sekund:
        ok[-1] = False      # poslední řádek uvnitř předchozí svíčky
    return df[ok]


def stahni_kotaci(a: dict) -> dict | None:
    kandidati = [ZVOLENY_TICKER[a["id"]]] if a["id"] in ZVOLENY_TICKER else a["tickers"]
    for ticker in kandidati:
        try:
            with YF_LOCK:
                t = yf.Ticker(ticker)
                den = t.history(period="7d", interval="1d", auto_adjust=False).dropna(subset=["Close"])
                if len(den) < 2:
                    continue
                intra = ocisti_intraday(t.history(period="5d", interval="5m").dropna(subset=["Close"]), 300)
                if not intra.empty:   # posledních 24 h obchodování (i o víkendu)
                    intra = intra[intra.index >= intra.index[-1] - pd.Timedelta(hours=24)]
        except Exception:
            continue

        posledni = den.iloc[-1]
        predchozi = float(den["Close"].iloc[-2])
        if not intra.empty:
            cena = float(intra["Close"].iloc[-1])
            cas = int(intra.index[-1].timestamp())
            spark = [round(float(x), 6) for x in intra["Close"].tolist()]
        else:
            cena = float(posledni["Close"])
            cas = int(den.index[-1].timestamp())
            spark = [round(float(x), 6) for x in den["Close"].tolist()]
        if len(spark) > 80:  # zředit pro mini graf
            krok = len(spark) / 80
            spark = [spark[int(i * krok)] for i in range(80)] + [spark[-1]]

        ZVOLENY_TICKER[a["id"]] = ticker
        zmena = cena - predchozi
        return {
            "ticker": ticker,
            "cena": cena,
            "predchozi": predchozi,
            "zmena": zmena,
            "zmena_pct": zmena / predchozi * 100 if predchozi else 0.0,
            "open": float(posledni["Open"]),
            "high": max(float(posledni["High"]), cena),
            "low": min(float(posledni["Low"]), cena),
            "objem": int(posledni["Volume"]) if posledni["Volume"] == posledni["Volume"] else 0,
            "cas": cas,
            "spark": spark,
        }
    return None


def obnov_ceny() -> None:
    ted = time.time()
    for a in AKTIVA:
        k = stahni_kotaci(a)
        if k is None:
            continue
        hist = HISTORIE_CEN[a["id"]]
        hist.append((ted, k["cena"]))

        upozorneni = []
        if abs(k["zmena_pct"]) >= a["alert_den"]:
            upozorneni.append({"typ": "den", "hodnota": round(k["zmena_pct"], 2),
                               "text": f"Výrazný denní pohyb {k['zmena_pct']:+.2f} %"})
        # skok za posledních SKOK_OKNO_MIN minut
        stara = [c for (t, c) in hist if ted - t >= SKOK_OKNO_MIN * 60 - 30]
        if stara:
            ref = stara[-1]
            skok = (k["cena"] - ref) / ref * 100 if ref else 0
            k["skok_pct"] = skok
            if abs(skok) >= a["alert_skok"]:
                smer = "nahoru" if skok > 0 else "dolů"
                upozorneni.append({"typ": "skok", "hodnota": round(skok, 2),
                                   "text": f"Skok {smer} {skok:+.2f} % za {SKOK_OKNO_MIN} min"})
        else:
            k["skok_pct"] = None
        k["upozorneni"] = upozorneni
        with STAV_LOCK:
            STAV["kotace"][a["id"]] = k
    with STAV_LOCK:
        STAV["aktualizovano"] = int(time.time())


# ----------------------------------------------------------------------------
#  Zprávy
# ----------------------------------------------------------------------------

def klic_zpravy(titulek: str) -> str:
    t = titulek.lower()
    if " - " in t:
        t = t.rsplit(" - ", 1)[0]
    return "".join(ch for ch in t if ch.isalnum())[:120]


def zpravy_google(dotaz: str) -> list[dict]:
    url = ("https://news.google.com/rss/search?q=" + urllib.parse.quote(f"{dotaz} when:2d")
           + "&hl=en-US&gl=US&ceid=US:en")
    try:
        r = requests.get(url, timeout=HTTP_TIMEOUT, headers={"User-Agent": "Mozilla/5.0"})
        feed = feedparser.parse(r.content)
    except Exception:
        return []
    out = []
    for e in feed.entries[:25]:
        ts = None
        try:
            dt = parsedate_to_datetime(e.get("published", ""))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            ts = int(dt.timestamp())
        except Exception:
            pass
        zdroj = e.source.get("title", "") if "source" in e and hasattr(e.source, "get") else ""
        titulek = e.get("title", "").strip()
        if zdroj and titulek.endswith(" - " + zdroj):
            titulek = titulek[: -len(" - " + zdroj)]
        out.append({"titulek": titulek, "odkaz": e.get("link", ""),
                    "zdroj": zdroj or "Google News", "ts": ts})
    return out


ZDROJE_STAV = {}                  # název zdroje -> {ok, pocet, chyba, cas}


def _zapis_stav(nazev: str, ok: bool, pocet: int = 0, chyba: str = "") -> None:
    ZDROJE_STAV[nazev] = {"ok": ok, "pocet": pocet, "chyba": chyba[:120], "cas": int(time.time())}


def zpravy_rss(url: str, nazev: str, ua: str | None = None) -> list[dict]:
    try:
        r = requests.get(url, timeout=HTTP_TIMEOUT, headers={"User-Agent": ua or "Mozilla/5.0 (MarketMonitor)"})
        if getattr(r, "status_code", 200) >= 400:
            _zapis_stav(nazev, False, 0, f"HTTP {r.status_code} (web blokuje přístup)")
            return []
        feed = feedparser.parse(r.content)
    except Exception as e:
        _zapis_stav(nazev, False, 0, str(e))
        return []
    out = []
    for e in feed.entries[:25]:
        ts = None
        for pole in ("published_parsed", "updated_parsed"):
            if e.get(pole):
                try:
                    ts = int(calendar.timegm(e[pole]))
                    break
                except Exception:
                    pass
        titulek = (e.get("title") or "").strip()
        if titulek:
            out.append({"titulek": titulek, "odkaz": e.get("link", ""), "zdroj": nazev, "ts": ts})
    _zapis_stav(nazev, bool(out), len(out), "" if out else "kanál je prázdný nebo nečitelný")
    return out


def zpravy_z_webu(z: dict, dotaz: str) -> list[dict]:
    q = f'{z.get("dotaz") or dotaz} site:{z["domena"]}'
    vysledek = zpravy_google(q)
    for v in vysledek:
        v["zdroj"] = v["zdroj"] if v["zdroj"] and v["zdroj"] != "Google News" else z["nazev"]
    predtim = ZDROJE_STAV.get(z["nazev"], {})
    if vysledek or not predtim.get("ok"):       # u webů hledaných pro víc aktiv stačí jeden úspěch
        _zapis_stav(z["nazev"], bool(vysledek), len(vysledek) + (predtim.get("pocet", 0) if predtim.get("ok") else 0),
                    "" if vysledek else "Google News nic nenašel")
    return vysledek


def zpravy_yahoo(ticker: str) -> list[dict]:
    try:
        with YF_LOCK:
            polozky = yf.Ticker(ticker).news or []
    except Exception:
        return []
    out = []
    for p in polozky[:20]:
        c = p.get("content", p)
        titulek = (c.get("title") or "").strip()
        if not titulek:
            continue
        odkaz = c["canonicalUrl"].get("url", "") if isinstance(c.get("canonicalUrl"), dict) else ""
        odkaz = odkaz or c.get("link", "")
        zdroj = c["provider"].get("displayName", "") if isinstance(c.get("provider"), dict) else ""
        zdroj = zdroj or c.get("publisher", "") or "Yahoo Finance"
        ts = None
        try:
            if c.get("pubDate"):
                ts = int(datetime.fromisoformat(c["pubDate"].replace("Z", "+00:00")).timestamp())
            elif c.get("providerPublishTime"):
                ts = int(c["providerPublishTime"])
        except Exception:
            pass
        out.append({"titulek": titulek, "odkaz": odkaz, "zdroj": zdroj, "ts": ts})
    return out


def obnov_zpravy() -> None:
    hranice = time.time() - MAX_STARI_ZPRAVY_HODIN * 3600
    hranice_primo = time.time() - 7 * 86400
    rss_cache = {}
    for z in ZDROJE_ZPRAV:                     # stav webových zdrojů se počítá znovu při každé obnově
        if z["typ"] == "web":
            ZDROJE_STAV.pop(z["nazev"], None)
    for a in AKTIVA:
        vse = zpravy_google(a["dotaz"])
        ticker = ZVOLENY_TICKER.get(a["id"], a["tickers"][0])
        vse += zpravy_yahoo(ticker)
        primo = []                       # zprávy z oficiálních zdrojů – bez filtru slov
        for z in ZDROJE_ZPRAV:
            if z.get("aktiva") != "vse" and a["id"] not in z.get("aktiva", []):
                continue
            if z["typ"] == "rss":
                if z["url"] not in rss_cache:
                    rss_cache[z["url"]] = zpravy_rss(z["url"], z["nazev"], z.get("ua"))
                polozky = [dict(p) for p in rss_cache[z["url"]]]
            else:
                polozky = zpravy_z_webu(z, a["dotaz"])
            (primo if z.get("vse_zpravy") else vse).extend(polozky)
        vse = [z for z in vse if z["titulek"] and (z["ts"] is None or z["ts"] >= hranice)]
        slova = a.get("slova")
        if slova:  # jen zprávy, které se aktiva opravdu týkají
            filtr = [z for z in vse if any(w in z["titulek"].lower() for w in slova)]
            vse = filtr if filtr else vse   # když filtr nic nenechá, radši ukázat aspoň něco
        vse += [z for z in primo if z["titulek"] and (z["ts"] is None or z["ts"] >= hranice_primo)]
        vse.sort(key=lambda z: z["ts"] or 0, reverse=True)
        vysledek, videno = [], set()
        for z in vse:
            k = klic_zpravy(z["titulek"])
            if not k or k in videno:
                continue
            if not z["odkaz"].startswith(("http://", "https://")):
                z["odkaz"] = ""
            videno.add(k)
            z["id"] = k
            vysledek.append(z)
            if len(vysledek) >= 30:
                break
        if vysledek:
            with STAV_LOCK:
                STAV["zpravy"][a["id"]] = vysledek
    with STAV_LOCK:
        STAV["zpravy_aktualizovano"] = int(time.time())


KALENDAR = {"udalosti": [], "aktualizovano": None, "chyba": None}


def obnov_kalendar() -> None:
    try:
        r = requests.get(KALENDAR_URL, timeout=HTTP_TIMEOUT, headers={"User-Agent": "Mozilla/5.0 (MarketMonitor)"})
        r.raise_for_status()
        data = r.json()
        udalosti = []
        for u in data:
            if u.get("country") not in KALENDAR_MENY or u.get("impact") not in KALENDAR_DOPAD:
                continue
            try:
                ts = int(datetime.fromisoformat(u["date"]).timestamp())
            except Exception:
                continue
            udalosti.append({"id": f'{u.get("country")}|{u.get("title")}|{ts}', "nazev": u.get("title", ""),
                             "mena": u.get("country"), "dopad": u.get("impact"), "ts": ts,
                             "prognoza": u.get("forecast") or "", "predchozi": u.get("previous") or "",
                             "skutecnost": u.get("actual") or ""})
        udalosti.sort(key=lambda x: x["ts"])
        KALENDAR.update(udalosti=udalosti, aktualizovano=int(time.time()), chyba=None)
    except Exception as e:
        KALENDAR.update(chyba=str(e)[:200], aktualizovano=int(time.time()))


# ----------------------------------------------------------------------------
#  Historie pro graf
# ----------------------------------------------------------------------------

# ----------------------------------------------------------------------------
#  LIVE ceny – Yahoo WebSocket stream (zdarma), záloha = dotaz každých 10 s
# ----------------------------------------------------------------------------

LIVE_POLL_S = 10               # záložní obnova vybraného aktiva (s), když stream nejede
LIVE = {}                      # ticker -> {"cena", "ts", "zdroj"}
LIVE_LOCK = threading.Lock()
LIVE_STAV = {"rezim": "start"}
POLL_CACHE = {}


def _live_zprava(msg) -> None:
    try:
        sym, cena = msg.get("id"), msg.get("price")
        if not sym or cena is None:
            return
        t = msg.get("time")
        ts = float(t) / 1000 if t else time.time()
        if ts > time.time() + 60:      # pojistka proti divnému formátu času
            ts = time.time()
        with LIVE_LOCK:
            LIVE[sym] = {"cena": float(cena), "ts": ts, "zdroj": "stream"}
    except Exception:
        pass


def live_stream() -> None:
    if not hasattr(yf, "WebSocket"):
        LIVE_STAV["rezim"] = "poll"
        print("[live] tato verze yfinance nemá WebSocket – používám obnovu každých "
              f"{LIVE_POLL_S} s (aktualizuj: py -m pip install -U yfinance)")
        return
    while True:
        try:
            tickers = sorted({ZVOLENY_TICKER.get(a["id"], a["tickers"][0]) for a in AKTIVA})
            try:
                ws = yf.WebSocket(verbose=False)
            except TypeError:
                ws = yf.WebSocket()
            ws.subscribe(tickers)
            LIVE_STAV["rezim"] = "stream"
            print(f"\n[{datetime.now():%H:%M:%S}] live stream připojen")
            ws.listen(_live_zprava)    # blokuje, dokud spojení běží
        except Exception as e:
            print(f"[live] stream odpojen ({e}) – zkusím znovu za 15 s")
        LIVE_STAV["rezim"] = "poll"
        time.sleep(15)


def live_cena(aid: str) -> dict | None:
    a = next((x for x in AKTIVA if x["id"] == aid), None)
    if a is None:
        return None
    ticker = ZVOLENY_TICKER.get(aid, a["tickers"][0])
    with LIVE_LOCK:
        l = LIVE.get(ticker)
    if l and l["zdroj"] == "stream" and time.time() - l["ts"] < 90:
        return l
    c = POLL_CACHE.get(ticker)
    if c and time.time() - c[0] < LIVE_POLL_S:
        return c[1] or l
    vysledek = None
    try:
        with YF_LOCK:
            df = ocisti_intraday(yf.Ticker(ticker).history(period="5d", interval="1m").dropna(subset=["Close"]), 60)
        if not df.empty:
            vysledek = {"cena": float(df["Close"].iloc[-1]),
                        "ts": float(df.index[-1].timestamp()), "zdroj": "poll"}
    except Exception:
        pass
    POLL_CACHE[ticker] = (time.time(), vysledek)
    if vysledek and (not l or vysledek["ts"] >= l["ts"]):
        with LIVE_LOCK:
            LIVE[ticker] = vysledek
        return vysledek
    return l


def s_live_cenou(k: dict | None) -> dict | None:
    """Do kotace z historie dosadí novější live cenu (pokud existuje)."""
    if not k:
        return k
    with LIVE_LOCK:
        l = LIVE.get(k["ticker"])
    if not l or l["ts"] <= k["cas"]:
        return k
    k = dict(k)
    c = l["cena"]
    k["cena"] = c
    k["zmena"] = c - k["predchozi"]
    k["zmena_pct"] = k["zmena"] / k["predchozi"] * 100 if k["predchozi"] else 0.0
    k["high"], k["low"] = max(k["high"], c), min(k["low"], c)
    k["cas"] = int(l["ts"])
    return k


# ----------------------------------------------------------------------------
#  Technická analýza (podobně jako „Technicals“ na TradingView)
# ----------------------------------------------------------------------------

TECH_TF = {"1H": ("60d", "60m"), "1D": ("2y", "1d"), "1T": ("10y", "1wk")}
TECH_CACHE = {}


def _cislo(v):
    try:
        v = float(v)
        return None if v != v else round(v, 6)   # NaN -> None
    except Exception:
        return None


def _stitek(r: float) -> str:
    if r >= 0.5:
        return "Silný nákup"
    if r >= 0.1:
        return "Nákup"
    if r > -0.1:
        return "Neutrální"
    if r > -0.5:
        return "Prodej"
    return "Silný prodej"


def technicka_analyza(aid: str, tf: str) -> dict:
    klic = (aid, tf)
    if klic in TECH_CACHE and time.time() - TECH_CACHE[klic][0] < 120:
        return TECH_CACHE[klic][1]
    a = next((x for x in AKTIVA if x["id"] == aid), None)
    if a is None or tf not in TECH_TF:
        return {"chyba": "Neznámé aktivum"}
    period, interval = TECH_TF[tf]
    ticker = ZVOLENY_TICKER.get(aid, a["tickers"][0])
    try:
        with YF_LOCK:
            df = yf.Ticker(ticker).history(period=period, interval=interval, auto_adjust=False)
        df = df.dropna(subset=["Close", "High", "Low"])
        if interval.endswith("m"):
            df = ocisti_intraday(df, 3600)
    except Exception as e:
        return {"chyba": f"Data se nepodařilo stáhnout ({e})"}
    if len(df) < 40:
        return {"chyba": "Málo dat pro výpočet"}

    c, h, l = df["Close"], df["High"], df["Low"]
    cena = float(c.iloc[-1])
    nic = lambda s: s.replace(0, float("nan"))

    # --- klouzavé průměry: cena nad průměrem = nákup, pod = prodej
    prumery = []
    for n in (10, 20, 30, 50, 100, 200):
        if len(c) < n:
            continue
        for nazev, hodn in (("EMA", c.ewm(span=n, adjust=False).mean().iloc[-1]),
                            ("SMA", c.rolling(n).mean().iloc[-1])):
            hodn = _cislo(hodn)
            sig = 0 if hodn is None else (1 if cena > hodn else -1 if cena < hodn else 0)
            prumery.append({"nazev": f"{nazev} ({n})", "hodnota": hodn, "signal": sig})

    # --- oscilátory
    osc = []

    def pridej(nazev, hodn, sig):
        hodn = _cislo(hodn)
        osc.append({"nazev": nazev, "hodnota": hodn, "signal": 0 if hodn is None else sig})

    d = c.diff()
    up = d.clip(lower=0).ewm(alpha=1 / 14, adjust=False).mean()
    dn = (-d.clip(upper=0)).ewm(alpha=1 / 14, adjust=False).mean()
    rsi = 100 - 100 / (1 + up / nic(dn))
    r, rp = rsi.iloc[-1], rsi.iloc[-2]
    pridej("RSI (14)", r, 1 if r < 30 and r > rp else -1 if r > 70 and r < rp else 0)

    ll, hh = l.rolling(14).min(), h.rolling(14).max()
    k = (100 * (c - ll) / nic(hh - ll)).rolling(3).mean()
    kd = k.rolling(3).mean()
    kk, dd = k.iloc[-1], kd.iloc[-1]
    pridej("Stochastic %K (14, 3, 3)", kk,
           1 if kk < 20 and dd < 20 and kk > dd else -1 if kk > 80 and dd > 80 and kk < dd else 0)

    tp = (h + l + c) / 3
    md = tp.rolling(20).apply(lambda x: abs(x - x.mean()).mean(), raw=True)
    cci = (tp - tp.rolling(20).mean()) / nic(0.015 * md)
    ci, cp = cci.iloc[-1], cci.iloc[-2]
    pridej("CCI (20)", ci, 1 if ci < -100 and ci > cp else -1 if ci > 100 and ci < cp else 0)

    mp = (h + l) / 2
    ao = mp.rolling(5).mean() - mp.rolling(34).mean()
    ai, ap = ao.iloc[-1], ao.iloc[-2]
    pridej("Awesome Oscillator", ai, 1 if ai > 0 and ai > ap else -1 if ai < 0 and ai < ap else 0)

    mom = c - c.shift(10)
    mi, mpv = mom.iloc[-1], mom.iloc[-2]
    pridej("Momentum (10)", mi, 1 if mi > mpv else -1 if mi < mpv else 0)

    macd = c.ewm(span=12, adjust=False).mean() - c.ewm(span=26, adjust=False).mean()
    sigl = macd.ewm(span=9, adjust=False).mean()
    pridej("MACD (12, 26)", macd.iloc[-1], 1 if macd.iloc[-1] > sigl.iloc[-1] else -1 if macd.iloc[-1] < sigl.iloc[-1] else 0)

    wr = -100 * (hh - c) / nic(hh - ll)
    wi, wp = wr.iloc[-1], wr.iloc[-2]
    pridej("Williams %R (14)", wi, 1 if wi < -80 and wi > wp else -1 if wi > -20 and wi < wp else 0)

    def souhrn(polozky):
        sig = [p["signal"] for p in polozky]
        r = sum(sig) / len(sig) if sig else 0.0
        return {"rating": round(r, 3), "stitek": _stitek(r),
                "nakup": sig.count(1), "neutral": sig.count(0), "prodej": sig.count(-1)}

    sp, so = souhrn(prumery), souhrn(osc)
    celkem = (sp["rating"] + so["rating"]) / 2
    vysledek = {"tf": tf, "rating": round(celkem, 3), "stitek": _stitek(celkem),
                "prumery": sp, "oscilatory": so, "detail_prumery": prumery, "detail_oscilatory": osc,
                "cas": int(df.index[-1].timestamp()), "svicek": len(df)}
    TECH_CACHE[klic] = (time.time(), vysledek)
    return vysledek


# ----------------------------------------------------------------------------
#  AI TÝM – 4 boti debatují (Groq, OpenAI-kompatibilní API)
# ----------------------------------------------------------------------------

GROQ_URL = os.environ.get("GROQ_URL", "https://api.groq.com/openai/v1/chat/completions")
DEBATY = {}                       # id aktiva -> stav debaty
DEBATA_LOCK = threading.Lock()    # jen jedna debata najednou (šetří limit)

BOTI = {
    "analytik": {"jmeno": "Analytik", "ikona": "📊"},
    "zpravar":  {"jmeno": "Zpravodaj", "ikona": "📰"},
    "smc":      {"jmeno": "SMC bot", "ikona": "🧠"},
    "scen":     {"jmeno": "Scenárista", "ikona": "🔭"},
    "risk":     {"jmeno": "Risk manažer", "ikona": "🛡️"},
    "sef":      {"jmeno": "Šéf", "ikona": "👔"},
}
SPOLECNE = ("Jsi člen týmu 4 AI analytiků v aplikaci Market Monitor. Odpovídej VŽDY česky, stručně a konkrétně, "
            "používej čísla z dodaných dat a nic si nevymýšlej – když něco nevíš, řekni to. "
            "Jde o vzdělávací analýzu, ne o investiční doporučení.")


def groq_klic() -> str:
    klic = os.environ.get("GROQ_API_KEY", "").strip()
    if klic:
        return klic
    try:
        p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "groq_klic.txt")
        with open(p, encoding="utf-8") as f:
            return f.read().strip()
    except Exception:
        return ""


def groq_chat(system: str, user: str, max_tokens: int = 600) -> str:
    klic = groq_klic()
    telo = {"model": GROQ_MODEL, "temperature": 0.5, "max_tokens": max_tokens, "reasoning_effort": "low",
            "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}]}
    for pokus in range(5):
        r = requests.post(GROQ_URL, json=telo, timeout=90,
                          headers={"Authorization": f"Bearer {klic}", "Content-Type": "application/json"})
        if r.status_code == 429:                        # limit za minutu – počkat a zkusit znovu
            try:
                cekej = float(r.headers.get("retry-after", "10"))
            except ValueError:
                cekej = 10
            time.sleep(min(max(cekej, 2), 40) + 1)
            continue
        if r.status_code == 400 and "reasoning_effort" in r.text and "reasoning_effort" in telo:
            telo.pop("reasoning_effort")                # model tenhle parametr nezná
            continue
        if r.status_code == 401:
            raise RuntimeError("Groq odmítl klíč (401) – zkontroluj GROQ_API_KEY.")
        if r.status_code >= 400:
            raise RuntimeError(f"Groq chyba {r.status_code}: {r.text[:200]}")
        obsah = (r.json()["choices"][0]["message"].get("content") or "").strip()
        if obsah:
            return obsah
        telo["max_tokens"] = int(telo["max_tokens"] * 1.6)   # odpověď se nevešla – zkusit s větším limitem
    raise RuntimeError("Groq je teď přetížený nebo jsi vyčerpal limit. Zkus to za pár minut.")


def _pct(a, b):
    return (a - b) / b * 100 if b else 0.0


def kontext_debaty(a: dict) -> dict:
    """Připraví stručná data pro boty (co nejméně tokenů)."""
    d = a["desetinna"]
    k = s_live_cenou(STAV["kotace"].get(a["id"])) or {}
    radky = [f"Aktivum: {a['nazev']} ({k.get('ticker', a['tickers'][0])}), {a['popis']}"]
    if k:
        radky.append(f"Cena {k['cena']:.{d}f}, dnes {k['zmena_pct']:+.2f} % (otevření {k['open']:.{d}f}, "
                     f"max {k['high']:.{d}f}, min {k['low']:.{d}f}, předch. zavření {k['predchozi']:.{d}f})")
    try:
        den = historie(a["id"], "6M")
        if len(den) > 22:
            c = [b["close"] for b in den]
            radky.append(f"Výkon: 5 dní {_pct(c[-1], c[-6]):+.1f} %, 1 měsíc {_pct(c[-1], c[-22]):+.1f} %, "
                         f"6 měsíců {_pct(c[-1], c[0]):+.1f} %; 6M max {max(b['high'] for b in den):.{d}f}, "
                         f"6M min {min(b['low'] for b in den):.{d}f}")
    except Exception:
        pass
    zaklad = "\n".join(radky)

    tech = []
    for tf, nazev in (("1H", "hodinový"), ("1D", "denní"), ("1T", "týdenní")):
        t = technicka_analyza(a["id"], tf)
        if t.get("chyba"):
            continue
        ind = {x["nazev"]: x for x in t["detail_oscilatory"] + t["detail_prumery"]}
        def hv(n):
            x = ind.get(n)
            return "—" if not x or x["hodnota"] is None else f"{x['hodnota']:.2f}"
        tech.append(f"{nazev} graf: celkem {t['stitek']} (oscilátory {t['oscilatory']['stitek']}, "
                    f"průměry {t['prumery']['stitek']} – nákup {t['prumery']['nakup']}/prodej {t['prumery']['prodej']}); "
                    f"RSI {hv('RSI (14)')}, MACD {hv('MACD (12, 26)')}, SMA50 {hv('SMA (50)')}, SMA200 {hv('SMA (200)')}")
    technika = zaklad + "\n" + "\n".join(tech)

    zpr, na_zdroj = [], {}                       # max 3 zprávy z jednoho zdroje, ať je pohled pestrý
    for z in STAV["zpravy"].get(a["id"], []):
        if na_zdroj.get(z["zdroj"], 0) < 3:
            zpr.append(z)
            na_zdroj[z["zdroj"]] = na_zdroj.get(z["zdroj"], 0) + 1
        if len(zpr) >= 14:
            break
    ted = time.time()
    def stari(ts):
        if not ts:
            return "?"
        h = (ted - ts) / 3600
        return f"{h:.0f} h" if h >= 1 else f"{h * 60:.0f} min"
    zpravy = "\n".join(f"- [{z['zdroj']}, před {stari(z.get('ts'))}] {z['titulek']}" for z in zpr) or "(žádné zprávy)"
    meny = ["USD"] + (["EUR"] if a["id"] == "eurusd" else [])
    kal = [u for u in KALENDAR.get("udalosti", []) if u["mena"] in meny and ted - 3600 < u["ts"] < ted + 48 * 3600]
    kalendar = "\n".join(
        f"- {'před' if u['ts'] < ted else 'za'} {abs(u['ts'] - ted) / 3600:.1f} h: {u['mena']} {u['nazev']} ({u['dopad']})"
        + (f", prognóza {u['prognoza']}" if u["prognoza"] else "") + (f", skutečnost {u['skutecnost']}" if u["skutecnost"] else "")
        for u in kal[:8]) or "(žádné důležité události v příštích 48 h)"
    return {"zaklad": zaklad, "technika": technika, "zpravy": zpravy, "kalendar": kalendar,
            "urovne": urovne_grafu(a), "smc": smc_text(a)}


# ----------------------------------------------------------------------------
#  SMC – Smart Money Concepts (swingy, BOS/CHoCH, likvidita, síla trendu)
# ----------------------------------------------------------------------------

def _atr(bars: list[dict], n: int = 14) -> float:
    tr = [max(b["high"] - b["low"], abs(b["high"] - a["close"]), abs(b["low"] - a["close"]))
          for a, b in zip(bars[-n - 1:-1], bars[-n:])]
    return sum(tr) / len(tr) if tr else 0.0


def smc_analyza(bars: list[dict], n: int | None = None) -> dict | None:
    """Spočítá tržní strukturu ze svíček (surové časy UTC).
    n = kolik svíček na každou stranu musí být nižších/vyšších, aby šlo o swing
    (víc svíček → bere jen důležitější swingy)."""
    if n is None:
        n = max(3, min(8, len(bars) // 60))
    if len(bars) < 2 * n + 20:
        return None
    atr = _atr(bars) or (bars[-1]["close"] * 0.002)
    cena = bars[-1]["close"]

    # 1) swingové vrcholy a dna (fraktál ±n svíček), střídavě H / L
    kandidati = []
    for i in range(n, len(bars) - n):
        okno = bars[i - n:i + n + 1]
        if bars[i]["high"] == max(b["high"] for b in okno):
            kandidati.append({"typ": "H", "i": i, "t": bars[i]["time"], "cena": bars[i]["high"]})
        if bars[i]["low"] == min(b["low"] for b in okno):
            kandidati.append({"typ": "L", "i": i, "t": bars[i]["time"], "cena": bars[i]["low"]})
    swingy = []
    for s in kandidati:
        if swingy and swingy[-1]["typ"] == s["typ"]:
            if (s["typ"] == "H" and s["cena"] > swingy[-1]["cena"]) or (s["typ"] == "L" and s["cena"] < swingy[-1]["cena"]):
                swingy[-1] = s
        else:
            swingy.append(s)
    posl = {"H": None, "L": None}
    for s in swingy:
        p = posl[s["typ"]]
        if s["typ"] == "H":
            s["stitek"] = "HH" if p is not None and s["cena"] > p else ("LH" if p is not None else "H")
        else:
            s["stitek"] = "HL" if p is not None and s["cena"] > p else ("LL" if p is not None else "L")
        posl[s["typ"]] = s["cena"]

    # 2) zlomy struktury – BOS (pokračování) a CHoCH (změna charakteru)
    trend, zlomy = None, []
    potvrzene = {"H": None, "L": None}
    si = 0
    for i, b in enumerate(bars):
        while si < len(swingy) and swingy[si]["i"] + n <= i:
            sw = dict(swingy[si])
            sw["prolomen"] = False
            potvrzene[sw["typ"]] = sw
            si += 1
        h, l = potvrzene["H"], potvrzene["L"]
        if h and not h["prolomen"] and b["close"] > h["cena"]:
            zlomy.append({"typ": "BOS" if trend in (None, "up") else "CHoCH", "smer": "up",
                          "cena": h["cena"], "t1": h["t"], "t2": b["time"], "i": i})
            h["prolomen"], trend = True, "up"
        if l and not l["prolomen"] and b["close"] < l["cena"]:
            zlomy.append({"typ": "BOS" if trend in (None, "down") else "CHoCH", "smer": "down",
                          "cena": l["cena"], "t1": l["t"], "t2": b["time"], "i": i})
            l["prolomen"], trend = True, "down"

    # 3) likvidita – neprolomené swingy nad/pod cenou, stejné vrcholy/dna (EQH/EQL), sweepy
    tol = max(cena * 0.001, atr * 0.15)
    nad = [s for s in swingy if s["typ"] == "H" and s["cena"] > cena
           and all(x["close"] <= s["cena"] for x in bars[s["i"] + 1:])]
    pod = [s for s in swingy if s["typ"] == "L" and s["cena"] < cena
           and all(x["close"] >= s["cena"] for x in bars[s["i"] + 1:])]
    likvidita = []
    for skup, typ, eq in ((nad, "BSL", "EQH"), (pod, "SSL", "EQL")):
        skup = sorted(skup, key=lambda s: abs(s["cena"] - cena))[:6]
        pouzite = set()
        for a_ in skup:
            pary = [b_ for b_ in skup if b_ is not a_ and abs(b_["cena"] - a_["cena"]) <= tol]
            if pary and id(a_) not in pouzite:
                cl = [a_] + pary
                pouzite.update(id(x) for x in cl)
                uroven = max(x["cena"] for x in cl) if typ == "BSL" else min(x["cena"] for x in cl)
                likvidita.append({"typ": eq, "strana": typ, "cena": uroven, "t1": min(x["t"] for x in cl)})
        for a_ in skup[:2]:
            if id(a_) not in pouzite:
                likvidita.append({"typ": typ, "strana": typ, "cena": a_["cena"], "t1": a_["t"]})
    vyber = []                                     # jen 2 nejbližší úrovně na každé straně
    for strana in ("BSL", "SSL"):
        vyber += sorted((x for x in likvidita if x["strana"] == strana), key=lambda x: abs(x["cena"] - cena))[:2]
    likvidita = vyber
    sweepy = []
    for i in range(max(n + 1, len(bars) - 30), len(bars)):
        b = bars[i]
        for s in swingy:
            if s["i"] + n >= i:
                continue
            if s["typ"] == "H" and b["high"] > s["cena"] and b["close"] < s["cena"] and i - s["i"] < 120:
                sweepy.append({"strana": "BSL", "cena": s["cena"], "t": b["time"], "i": i})
            if s["typ"] == "L" and b["low"] < s["cena"] and b["close"] > s["cena"] and i - s["i"] < 120:
                sweepy.append({"strana": "SSL", "cena": s["cena"], "t": b["time"], "i": i})
    jedinecne = {}
    for x in sweepy:                                # stejná úroveň vybraná víckrát → jen poslední
        jedinecne[(x["strana"], round(x["cena"], 6))] = x
    sweepy = sorted(jedinecne.values(), key=lambda x: x["i"])[-3:]

    # 4) síla trendu (-100 medvědí … +100 býčí)
    stitky = [s["stitek"] for s in swingy[-6:]]
    skore = 18 * (stitky.count("HH") + stitky.count("HL") - stitky.count("LH") - stitky.count("LL"))
    if zlomy:
        skore += 25 if zlomy[-1]["smer"] == "up" else -25
    if len(bars) > 20:
        skore += max(-25, min(25, (cena - bars[-21]["close"]) / atr * 8))
    skore = int(max(-100, min(100, skore)))
    if abs(skore) < 20:
        sila = "bez jasného trendu (range)"
    else:
        sila = ("silný " if abs(skore) >= 60 else "mírný ") + ("býčí" if skore > 0 else "medvědí")
    return {"swingy": swingy[-24:], "zlomy": zlomy[-4:], "likvidita": likvidita, "sweepy": sweepy,
            "trend": trend, "skore": skore, "sila": sila, "atr": atr, "cena": cena,
            "posledni_cas": bars[-1]["time"]}


def smc_text(a: dict) -> str:
    """Popis SMC pro AI bota – hodinový a 15minutový graf."""
    d = a["desetinna"]
    f = lambda v: f"{v:.{d}f}"
    vystup = []
    for rozsah, nazev in (("1M", "Hodinový graf (H1)"), ("5D", "15minutový graf (M15)")):
        try:
            sm = smc_analyza(historie(a["id"], rozsah))
        except Exception:
            sm = None
        if not sm:
            continue
        radky = [f"{nazev}: struktura {sm['sila']} (skóre {sm['skore']:+d}), "
                 f"poslední zlom: {(sm['zlomy'][-1]['typ'] + ' ' + ('nahoru' if sm['zlomy'][-1]['smer'] == 'up' else 'dolů') + ' přes ' + f(sm['zlomy'][-1]['cena'])) if sm['zlomy'] else 'žádný'}"]
        radky.append("Poslední swingy: " + ", ".join(f"{s['stitek']} {f(s['cena'])}" for s in sm["swingy"][-6:]))
        if sm["likvidita"]:
            radky.append("Likvidita: " + ", ".join(
                f"{x['typ']} {f(x['cena'])} ({'nad cenou' if x['strana'] == 'BSL' else 'pod cenou'})" for x in sm["likvidita"]))
        if sm["sweepy"]:
            radky.append("Nedávné sweepy likvidity: " + ", ".join(
                f"{'nad' if x['strana'] == 'BSL' else 'pod'} {f(x['cena'])} (před {len(historie(a['id'], rozsah)) - 1 - x['i']} svíčkami)"
                for x in sm["sweepy"]))
        vystup.append("\n".join(radky))
    return "\n\n".join(vystup) or "(SMC data nejsou k dispozici)"


def urovne_grafu(a: dict) -> str:
    """Spočítá důležité cenové úrovně z grafu pro Scenáristu."""
    d = a["desetinna"]
    f = lambda v: f"{v:.{d}f}"
    radky = []
    try:
        den = historie(a["id"], "6M")
        if len(den) >= 22:
            cena = den[-1]["close"]
            p = den[-2]                                   # předchozí celý den
            P = (p["high"] + p["low"] + p["close"]) / 3
            rng = p["high"] - p["low"]
            radky.append(f"Pivoty (z předchozího dne): R2 {f(P + rng)}, R1 {f(2 * P - p['low'])}, P {f(P)}, "
                         f"S1 {f(2 * P - p['high'])}, S2 {f(P - rng)}")
            tr = [max(b["high"] - b["low"], abs(b["high"] - a0["close"]), abs(b["low"] - a0["close"]))
                  for a0, b in zip(den[-15:-1], den[-14:])]
            atr = sum(tr) / len(tr)
            radky.append(f"Průměrný denní pohyb (ATR 14): {f(atr)} ({atr / cena * 100:.1f} % ceny)")
            radky.append(f"20denní max {f(max(b['high'] for b in den[-20:]))}, 20denní min {f(min(b['low'] for b in den[-20:]))}; "
                         f"6M max {f(max(b['high'] for b in den))}, 6M min {f(min(b['low'] for b in den))}")
    except Exception:
        pass
    try:
        hod = historie(a["id"], "1M")                     # hodinové svíčky ~1 měsíc
        if len(hod) > 30:
            cena = hod[-1]["close"]
            vrcholy, dna = [], []
            for i in range(5, len(hod) - 5):
                okno = hod[i - 5:i + 6]
                if hod[i]["high"] == max(b["high"] for b in okno):
                    vrcholy.append(hod[i]["high"])
                if hod[i]["low"] == min(b["low"] for b in okno):
                    dna.append(hod[i]["low"])
            def sluc(urovne):              # sloučit téměř stejné úrovně (do 0,15 % ceny)
                out = []
                for v in urovne:
                    if not out or abs(v - out[-1]) > cena * 0.0015:
                        out.append(v)
                return out
            nad = sluc(sorted(v for v in vrcholy + dna if v > cena))[:3]
            pod = sluc(sorted((v for v in vrcholy + dna if v < cena), reverse=True))[:3]
            radky.append("Odpory nad cenou (swingy z hodinového grafu): " + (", ".join(f(v) for v in nad) or "žádné"))
            radky.append("Podpory pod cenou (swingy z hodinového grafu): " + (", ".join(f(v) for v in pod) or "žádné"))
    except Exception:
        pass
    try:
        d24 = historie(a["id"], "1D")
        if d24:
            radky.append(f"Posledních 24 h: max {f(max(b['high'] for b in d24))}, min {f(min(b['low'] for b in d24))}, "
                         f"otevření {f(d24[0]['open'])}")
    except Exception:
        pass
    return "\n".join(radky) or "(úrovně se nepodařilo spočítat)"


def _pridej(aid: str, bot: str, text: str, kolo: int = 1) -> None:
    with STAV_LOCK:
        DEBATY[aid]["zpravy"].append({"bot": bot, **BOTI[bot], "text": text, "kolo": kolo})


def _postoj(text: str) -> str:
    m = re.search(r"POSTOJ\s*:\s*([A-ZÁČĎÉĚÍŇÓŘŠŤÚŮÝŽ ]+)", text.upper())
    return m.group(1).strip() if m else ""


def _cena_z_textu(text: str, blizko: float) -> float | None:
    """Vytáhne cenu z textu jako „3 636,50“, „3,636.5“ nebo „1,0974“ – vybere výklad nejbližší aktuální ceně."""
    m = re.search(r"\d[\d\s\u00a0.,]*", text)
    if not m:
        return None
    x = re.sub(r"[\s\u00a0]", "", m.group(0)).rstrip(".,")
    kandidati = []
    if "," in x and "." in x:
        kandidati.append(x.replace(",", ""))
    elif "," in x:
        kandidati += [x.replace(",", "."), x.replace(",", "")]
    else:
        kandidati.append(x)
    hodnoty = []
    for k in kandidati:
        try:
            hodnoty.append(float(k))
        except ValueError:
            pass
    return min(hodnoty, key=lambda v: abs(v - blizko)) if hodnoty else None


def scenare_z_textu(text: str) -> list[dict]:
    vysledek = []
    for radek in text.splitlines():
        r = radek.strip().lstrip("-*• ").strip()
        for znak, typ in (("🟢", "up"), ("⚪", "side"), ("🔴", "down")):
            if r.startswith(znak):
                obsah = r[len(znak):].strip()
                m = re.search(r"(\d{1,3})\s*%", obsah)
                nazev, _, popis = obsah.partition(":")
                vysledek.append({"typ": typ, "pst": int(m.group(1)) if m else None,
                                 "nazev": re.sub(r"\s*\(.*?\)\s*", "", nazev).strip() or obsah[:20],
                                 "popis": popis.strip() or obsah})
    return vysledek


def spust_debatu(aid: str) -> None:
    a = next((x for x in AKTIVA if x["id"] == aid), None)
    if a is None:
        return
    if not DEBATA_LOCK.acquire(blocking=False):
        with STAV_LOCK:
            DEBATY[aid] = {"stav": "chyba", "chyba": "Právě běží jiná debata – zkus to za chvilku.", "zpravy": []}
        return
    try:
        with STAV_LOCK:
            DEBATY[aid] = {"stav": "bezi", "krok": "Připravuji data…", "zpravy": [], "start": int(time.time())}
        kx = kontext_debaty(a)
        konec = "Na konec napiš samostatný řádek: POSTOJ: NÁKUP / PRODEJ / NEUTRÁLNÍ (jistota X %)."

        DEBATY[aid]["krok"] = "📊 Analytik studuje grafy…"
        t_an = groq_chat(SPOLECNE + " Jsi ANALYTIK: hodnotíš jen technickou analýzu, trend, indikátory a cenové úrovně. "
                         "Max 90 slov. " + konec, kx["technika"])
        _pridej(aid, "analytik", t_an)

        DEBATY[aid]["krok"] = "🧠 SMC bot čte strukturu trhu…"
        t_smc = groq_chat(SPOLECNE + " Jsi SMC BOT (Smart Money Concepts): čti tržní strukturu – swingy (HH/HL/LH/LL), "
                          "BOS a CHoCH, likviditu (BSL/SSL, EQH/EQL), sweepy likvidity a sílu trendu. Řekni, kdo má kontrolu "
                          "(kupci/prodejci), kde leží likvidita, kterou trh pravděpodobně půjde vybrat, a jestli už byla "
                          "vybrána. Porovnej H1 a M15. Max 100 slov. " + konec,
                          kx["zaklad"] + "\n\nSMC DATA:\n" + kx["smc"], 650)
        _pridej(aid, "smc", t_smc)

        DEBATY[aid]["krok"] = "🔭 Scenárista prochází graf a hledá scénáře…"
        t_sc = groq_chat(SPOLECNE + " Jsi SCENÁRISTA: projdi graf a cenové úrovně a popiš všechny realistické scénáře. "
                         "U každého uveď cenovou úroveň, která ho spustí (průraz/odraz), cíl a pravděpodobnost v %; "
                         "součet pravděpodobností = 100 %. Pak řekni svůj názor týmu. Odpověz PŘESNĚ v tomto formátu:\n"
                         "🟢 Růst (X %): <spouštěč a cíl, max 20 slov>\n"
                         "⚪ Do strany (X %): <rozmezí, max 20 slov>\n"
                         "🔴 Pokles (X %): <spouštěč a cíl, max 20 slov>\n"
                         "NÁZOR: <nejpravděpodobnější scénář a proč, max 35 slov>\n" + konec,
                         kx["technika"] + "\n\nCENOVÉ ÚROVNĚ:\n" + kx["urovne"]
                         + "\n\nZÁVĚR SMC BOTA (stav na něm své scénáře):\n" + t_smc, 750)
        _pridej(aid, "scen", t_sc)

        DEBATY[aid]["krok"] = "📰 Zpravodaj čte zprávy…"
        t_zp = groq_chat(SPOLECNE + " Jsi ZPRAVODAJ: hodnotíš jen zprávy – sentiment, co trh hýbe a jaké důležité "
                         "události (Fed, inflace, zprávy firem) zprávy zmiňují. Max 90 slov. " + konec,
                         kx["zaklad"] + "\n\nZPRÁVY:\n" + kx["zpravy"])
        _pridej(aid, "zpravar", t_zp)

        DEBATY[aid]["krok"] = "🛡️ Risk manažer hledá rizika…"
        t_ri = groq_chat(SPOLECNE + " Jsi RISK MANAŽER: kriticky prověř názory kolegů, hledej rizika (volatilita, "
                         "blížící se události, rozpory mezi signály, přepálený trh) a oponuj tomu, kdo je moc sebejistý. "
                         "Max 90 slov. " + konec,
                         kx["zaklad"]
                         + f"\n\nANALYTIK:\n{t_an}\n\nSMC BOT:\n{t_smc}\n\nSCENÁRISTA:\n{t_sc}\n\nZPRAVODAJ:\n{t_zp}")
        _pridej(aid, "risk", t_ri)

        DEBATY[aid]["krok"] = "💬 Boti si odpovídají…"
        t_an2 = groq_chat(SPOLECNE + " Jsi ANALYTIK. Krátce (max 45 slov) zareaguj na kolegy: s čím souhlasíš, "
                          "v čem se mýlí, a jestli měníš názor. " + konec,
                          f"Tvůj názor:\n{t_an}\n\nSMC BOT:\n{t_smc}\n\nSCENÁRISTA:\n{t_sc}\n\nZPRAVODAJ:\n{t_zp}"
                          f"\n\nRISK MANAŽER:\n{t_ri}", 450)
        _pridej(aid, "analytik", t_an2, 2)
        t_zp2 = groq_chat(SPOLECNE + " Jsi ZPRAVODAJ. Krátce (max 45 slov) zareaguj na kolegy: s čím souhlasíš, "
                          "v čem se mýlí, a jestli měníš názor. " + konec,
                          f"Tvůj názor:\n{t_zp}\n\nANALYTIK:\n{t_an2}\n\nRISK MANAŽER:\n{t_ri}", 450)
        _pridej(aid, "zpravar", t_zp2, 2)

        DEBATY[aid]["krok"] = "👔 Šéf rozhoduje…"
        t_sef = groq_chat(SPOLECNE + " Jsi ŠÉF týmu. Zvaž argumenty všech, vysvětli, komu dáváš za pravdu a proč, a rozhodni. "
                          "Urči i cenový CÍL a STOP z úrovní SMC a scénářů: u nákupu je cíl NAD aktuální cenou a stop POD ní, "
                          "u prodeje naopak; u Neutrální napiš u cíle i stopu pomlčku. "
                          "Odpověz PŘESNĚ v tomto formátu (5 řádků):\n"
                          "VERDIKT: <Silný nákup | Nákup | Neutrální | Prodej | Silný prodej>\n"
                          "JISTOTA: <číslo 0-100>\n"
                          "CÍL: <cena>\n"
                          "STOP: <cena>\n"
                          "SHRNUTÍ: <2–3 věty, max 60 slov>",
                          kx["zaklad"] + "\nCENOVÉ ÚROVNĚ:\n" + kx["urovne"] + f"\n\nANALYTIK:\n{t_an}\n{t_an2}\n\nSMC BOT:\n{t_smc}\n\nSCENÁRISTA:\n{t_sc}"
                          f"\n\nZPRAVODAJ:\n{t_zp}\n{t_zp2}"
                          f"\n\nRISK MANAŽER:\n{t_ri}", 500)
        _pridej(aid, "sef", t_sef)

        verdikty = ["Silný nákup", "Silný prodej", "Nákup", "Prodej", "Neutrální"]
        m = re.search(r"VERDIKT\s*:\s*(.+)", t_sef, re.I)
        verdikt = next((v for v in verdikty if m and v.lower() in m.group(1).lower()), "Neutrální")
        m = re.search(r"JISTOTA\s*:\s*(\d+)", t_sef, re.I)
        jistota = max(0, min(100, int(m.group(1)))) if m else None
        m = re.search(r"SHRNUTÍ\s*:\s*(.+)", t_sef, re.I | re.S)
        shrnuti = (m.group(1).strip() if m else t_sef)[:600]
        k_ted = s_live_cenou(STAV["kotace"].get(aid)) or {}
        cena_ted = k_ted.get("cena")
        cil = stop = None
        if cena_ted and verdikt != "Neutrální":
            m = re.search(r"C[ÍI]L\s*:\s*([^\n]+)", t_sef, re.I)
            cil = _cena_z_textu(m.group(1), cena_ted) if m else None
            m = re.search(r"STOP\s*:\s*([^\n]+)", t_sef, re.I)
            stop = _cena_z_textu(m.group(1), cena_ted) if m else None
            nakup = "nákup" in verdikt.lower()
            ok = cil and stop and ((stop < cena_ted < cil) if nakup else (cil < cena_ted < stop))
            if not ok or abs(cil - cena_ted) / cena_ted > 0.25 or abs(stop - cena_ted) / cena_ted > 0.25:
                cil = stop = None                       # nesmyslné úrovně raději zahodit
        with STAV_LOCK:
            DEBATY[aid].update(stav="hotovo", verdikt=verdikt, jistota=jistota, shrnuti=shrnuti,
                               cas=int(time.time()), krok="", cena=cena_ted, cil=cil, stop=stop,
                               scenare=scenare_z_textu(t_sc),
                               postoje={"analytik": _postoj(t_an2) or _postoj(t_an), "smc": _postoj(t_smc), "scen": _postoj(t_sc),
                                        "zpravar": _postoj(t_zp2) or _postoj(t_zp), "risk": _postoj(t_ri)})
    except Exception as e:
        with STAV_LOCK:
            DEBATY.setdefault(aid, {"zpravy": []}).update(stav="chyba", chyba=str(e)[:300], krok="")
    finally:
        DEBATA_LOCK.release()


def stav_debaty(aid: str) -> dict:
    with STAV_LOCK:
        d = dict(DEBATY.get(aid) or {"stav": "nic", "zpravy": []})
        d["zpravy"] = list(d.get("zpravy", []))
    d["klic"] = bool(groq_klic())
    d["model"] = GROQ_MODEL
    d["platnost_min"] = DEBATA_PLATNOST_MIN
    return d


def historie(aid: str, rozsah: str, iv: str | None = None) -> list[dict]:
    if iv not in INTERVALY:
        iv = VYCHOZI_IV.get(rozsah, "1d")
    klic = (aid, rozsah, iv)
    if klic in CACHE_GRAFU and time.time() - CACHE_GRAFU[klic][0] < 55:
        return CACHE_GRAFU[klic][1]
    a = next((x for x in AKTIVA if x["id"] == aid), None)
    if a is None or rozsah not in ROZSAHY:
        return []
    interval, sloucit, delka = INTERVALY[iv]
    period = perioda(rozsah, iv)
    ticker = ZVOLENY_TICKER.get(aid, a["tickers"][0])
    try:
        with YF_LOCK:
            df = yf.Ticker(ticker).history(period=period, interval=interval, auto_adjust=False)
        sekund = {"1m": 60, "5m": 300, "15m": 900, "30m": 1800, "60m": 3600}.get(interval)
        if sekund:
            df = ocisti_intraday(df.dropna(subset=["Close"]), sekund)
        if sloucit and not df.empty:            # 10 min / 4 h – složit z menších svíček
            df = df.dropna(subset=["Close"]).resample(sloucit, label="left", closed="left").agg(
                {"Open": "first", "High": "max", "Low": "min", "Close": "last", "Volume": "sum"}).dropna(subset=["Close"])
        if rozsah == "1D" and delka:
            df = df.dropna(subset=["Close"])
            if not df.empty:   # posledních 24 h obchodování – o víkendu ukáže poslední seanci
                df = df[df.index >= df.index[-1] - pd.Timedelta(hours=24)]
    except Exception:
        return []
    body = {}
    for idx, r in df.iterrows():
        o, h, l, c = r.get("Open"), r.get("High"), r.get("Low"), r.get("Close")
        if any(v != v or v is None for v in (o, h, l, c)):  # NaN
            continue
        v = r.get("Volume", 0)
        body[int(idx.timestamp())] = {
            "time": int(idx.timestamp()), "open": float(o), "high": float(h),
            "low": float(l), "close": float(c), "volume": int(v) if v == v else 0,
        }
    data = [body[k] for k in sorted(body)][-3000:]
    if interval.endswith("m"):
        # Forex u Yahoo má často „ploché“ svíčky (open = high = low = close).
        # Takovou svíčku dopočítáme: open = předchozí close → vznikne normální tělo.
        for i in range(1, len(data)):
            b = data[i]
            if b["high"] == b["low"]:
                o = data[i - 1]["close"]
                b["open"] = o
                b["high"] = max(b["high"], o, b["close"])
                b["low"] = min(b["low"], o, b["close"])
    CACHE_GRAFU[klic] = (time.time(), data)
    return data


# ----------------------------------------------------------------------------
#  Smyčka na pozadí
# ----------------------------------------------------------------------------

def smycka() -> None:
    posledni_zpravy = 0.0
    posledni_upd = 0.0
    posledni_kal = 0.0
    stream_spusten = False
    while True:
        if UPDATE_REPO and not SERVER_MODE and time.time() - posledni_upd >= UPDATE_KONTROLA_MIN * 60:
            zkontroluj_aktualizaci()
            posledni_upd = time.time()
        try:
            obnov_ceny()
        except Exception as e:
            print(f"[chyba cen] {e}")
        if not stream_spusten:     # až po 1. načtení – známe správné tickery (SNDK/WDC)
            threading.Thread(target=live_stream, daemon=True).start()
            stream_spusten = True
        if KALENDAR_ZAPNUTO and time.time() - posledni_kal >= KALENDAR_KAZDYCH_MIN * 60:
            obnov_kalendar()
            posledni_kal = time.time()
        if time.time() - posledni_zpravy >= ZPRAVY_KAZDYCH_MIN * 60:
            try:
                obnov_zpravy()
                posledni_zpravy = time.time()
                print(f"[{datetime.now():%H:%M:%S}] zprávy aktualizovány")
            except Exception as e:
                print(f"[chyba zpráv] {e}")
        time.sleep(CENY_KAZDYCH_S)


# ----------------------------------------------------------------------------
#  Automatické aktualizace (GitHub Releases)
# ----------------------------------------------------------------------------

JE_EXE = getattr(sys, "frozen", False)
SERVER = None      # běží jako .exe (PyInstaller)?
UPD = {"nejnovejsi": None, "poznamky": "", "url": None, "soubor": None, "velikost": 0,
       "zkontrolovano": None, "chyba": None, "stav": "idle", "procent": 0}


def cislo_verze(v) -> int:
    m = re.search(r"(\d+)", str(v or ""))
    return int(m.group(1)) if m else 0


def je_novejsi() -> bool:
    return bool(UPD["url"]) and cislo_verze(UPD["nejnovejsi"]) > cislo_verze(VERZE)


def zkontroluj_aktualizaci() -> None:
    if not UPDATE_REPO:
        return
    try:
        r = requests.get(f"https://api.github.com/repos/{UPDATE_REPO}/releases/latest",
                         timeout=HTTP_TIMEOUT,
                         headers={"Accept": "application/vnd.github+json", "User-Agent": "MarketMonitor"})
        if r.status_code == 404:
            raise IOError("v repozitáři zatím není žádné vydání (Release)")
        r.raise_for_status()
        d = r.json()
        asset = None
        for a in d.get("assets", []):
            n = a.get("name", "")
            if JE_EXE and n.lower().endswith(".exe"):
                asset = a
                break
            if not JE_EXE and re.fullmatch(r"market_app_V\d+\.py", n):
                asset = a
                break
        UPD.update(nejnovejsi=d.get("tag_name") or d.get("name"),
                   poznamky=(d.get("body") or "").strip()[:3000],
                   url=asset["browser_download_url"] if asset else None,
                   soubor=asset["name"] if asset else None,
                   velikost=asset.get("size", 0) if asset else 0,
                   zkontrolovano=int(time.time()), chyba=None)
        if je_novejsi():
            print(f"[aktualizace] k dispozici je nová verze {UPD['nejnovejsi']}")
    except Exception as e:
        UPD.update(chyba=str(e)[:200], zkontrolovano=int(time.time()))


def nainstaluj_aktualizaci() -> None:
    try:
        if JE_EXE and os.name != "nt":
            raise OSError("na macOS spouštěj aplikaci jako .py (spustit_mac.command)")
        UPD.update(stav="stahuji", procent=0, chyba=None)
        if JE_EXE:
            cil = sys.executable
            docasny = cil + ".new"
        else:
            slozka = os.path.dirname(os.path.abspath(__file__))
            cil = os.path.join(slozka, UPD["soubor"])
            docasny = cil + ".part"

        hotovo = 0
        with requests.get(UPD["url"], stream=True, timeout=60,
                          headers={"User-Agent": "MarketMonitor"}) as r:
            r.raise_for_status()
            celkem = int(r.headers.get("content-length") or UPD["velikost"] or 0)
            with open(docasny, "wb") as f:
                for kus in r.iter_content(256 * 1024):
                    f.write(kus)
                    hotovo += len(kus)
                    if celkem:
                        UPD["procent"] = min(99, int(hotovo * 100 / celkem))
        if celkem and hotovo < celkem:
            raise IOError("stahování se nedokončilo")
        UPD["procent"] = 100

        if os.name != "nt":
            # macOS / Linux: nahradit soubor a restartovat se ve stejném okně Terminálu
            os.replace(docasny, cil)
            UPD["stav"] = "restart"
            print(f"\n[aktualizace] {UPD['nejnovejsi']} nainstalována – restartuji…\n")

            def _restart():
                try:
                    if SERVER is not None:
                        SERVER.socket.close()
                except Exception:
                    pass
                os.execv(sys.executable, [sys.executable, cil, "--no-browser"])
            threading.Timer(1.5, _restart).start()
            return

        pid = os.getpid()
        cekat_na = [pid]
        if JE_EXE:
            with open(docasny, "rb") as f:
                if f.read(2) != b"MZ":
                    raise IOError("stažený soubor není platný .exe")
            cekat_na.append(os.getppid())      # zavaděč PyInstalleru
            spust = (f':presun\r\nset /a POKUS+=1\r\n'
                     f'move /y "{docasny}" "{cil}" >nul 2>&1\r\n'
                     f'if errorlevel 1 if %POKUS% LSS 30 (timeout /t 1 /nobreak >nul & goto presun)\r\n'
                     f'start "" "{cil}" --no-browser\r\n')
        else:
            os.replace(docasny, cil)
            spust = f'start "Market Monitor" "{sys.executable}" "{cil}" --no-browser\r\n'

        cekani = "".join(
            f':cekej{p}\r\ntasklist /FI "PID eq {p}" 2>nul | find " {p} " >nul\r\n'
            f'if not errorlevel 1 (timeout /t 1 /nobreak >nul & goto cekej{p})\r\n' for p in cekat_na)
        bat = os.path.join(tempfile.gettempdir(), f"mm_update_{pid}.bat")
        with open(bat, "w", encoding="utf-8", newline="") as f:
            f.write("@echo off\r\nchcp 65001 >nul\r\nset POKUS=0\r\n" + cekani + spust + 'del "%~f0"\r\n')

        subprocess.Popen(["cmd", "/c", bat], close_fds=True,
                         creationflags=0x08000000 | 0x00000200)  # bez okna, samostatný proces
        UPD["stav"] = "restart"
        print(f"\n[aktualizace] {UPD['nejnovejsi']} nainstalována – aplikace se restartuje."
              "\nToto okno se zavře / můžeš ho zavřít.")
        threading.Timer(1.5, lambda: os._exit(0)).start()
    except Exception as e:
        UPD.update(stav="chyba", chyba=str(e)[:300])


def info_aktualizace() -> dict:
    if SERVER_MODE:
        return {"aktualni": VERZE, "nastaveno": False, "server": True, "novejsi": False}
    return {"aktualni": VERZE, "nastaveno": bool(UPDATE_REPO), "nejnovejsi": UPD["nejnovejsi"],
            "novejsi": je_novejsi(), "poznamky": UPD["poznamky"], "velikost": UPD["velikost"],
            "chyba": UPD["chyba"], "zkontrolovano": UPD["zkontrolovano"],
            "bez_souboru": bool(UPD["nejnovejsi"]) and not UPD["url"]
                           and cislo_verze(UPD["nejnovejsi"]) > cislo_verze(VERZE)}


# ----------------------------------------------------------------------------
#  HTTP server
# ----------------------------------------------------------------------------

AUTH_TOKEN = hmac.new(HESLO.encode("utf-8"), b"market-monitor-auth", hashlib.sha256).hexdigest() if HESLO else ""

LOGIN_HTML = """<!DOCTYPE html><html lang="cs"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>Market Monitor – přihlášení</title>
<style>
 body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;background:#0b0e14;color:#d1d4dc;
   font-family:-apple-system,"Segoe UI",Roboto,Arial,sans-serif}
 form{background:#181c27;border:1px solid #232838;border-radius:14px;padding:28px 26px;width:300px;max-width:88vw;
   box-shadow:0 20px 60px rgba(0,0,0,.5)}
 h1{font-size:19px;margin:0 0 4px;display:flex;align-items:center;gap:9px}
 h1 i{width:12px;height:12px;border-radius:3px;background:linear-gradient(135deg,#2962ff,#26a69a);display:inline-block}
 p{color:#7a7f8e;font-size:13px;margin:0 0 18px}
 input{width:100%;box-sizing:border-box;padding:11px 12px;border-radius:8px;border:1px solid #2e3446;background:#0b0e14;
   color:#d1d4dc;font-size:15px;outline:none}
 input:focus{border-color:#2962ff}
 button{width:100%;margin-top:12px;padding:11px;border:none;border-radius:8px;background:#2962ff;color:#fff;font-weight:700;
   font-size:15px;cursor:pointer}
 .err{color:#ef5350;font-size:13px;margin-top:10px}
</style></head><body>
<form method="post" action="/login">
 <h1><i></i>Market Monitor</h1><p>Zadej heslo pro vstup.</p>
 <input type="password" name="heslo" placeholder="Heslo" autofocus autocomplete="current-password">
 <button type="submit">Přihlásit</button>{{CHYBA}}
</form></body></html>"""


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def _prihlasen(self) -> bool:
        if not HESLO:
            return True
        for cast in self.headers.get("Cookie", "").split(";"):
            k, _, v = cast.strip().partition("=")
            if k == "mm_auth" and hmac.compare_digest(v, AUTH_TOKEN):
                return True
        return False

    def _presmeruj(self, kam: str, cookie: str | None = None) -> None:
        self.send_response(302)
        self.send_header("Location", kam)
        if cookie:
            self.send_header("Set-Cookie", cookie)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def _login_stranka(self, chyba: str = "") -> None:
        telo = LOGIN_HTML.replace("{{CHYBA}}", f'<div class="err">{chyba}</div>' if chyba else "")
        self._posli(200, telo.encode("utf-8"), "text/html; charset=utf-8")

    def _posli(self, kod: int, telo: bytes, typ: str) -> None:
        self.send_response(kod)
        self.send_header("Content-Type", typ)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(telo)))
        self.end_headers()
        self.wfile.write(telo)

    def _json(self, obj) -> None:
        self._posli(200, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                    "application/json; charset=utf-8")

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        q = urllib.parse.parse_qs(u.query)
        try:
            if u.path == "/healthz":
                self._posli(200, b"ok", "text/plain")
                return
            if u.path == "/login":
                if self._prihlasen():
                    self._presmeruj("/")
                else:
                    self._login_stranka()
                return
            if not self._prihlasen():
                if u.path.startswith("/api/"):
                    self._posli(401, b'{"chyba": "neprihlasen"}', "application/json")
                else:
                    self._presmeruj("/login")
                return
            if u.path in ("/", "/index.html"):
                self._posli(200, HTML.replace("{{VERZE}}", VERZE).encode("utf-8"), "text/html; charset=utf-8")
            elif u.path == "/api/state":
                with STAV_LOCK:
                    aktiva = []
                    for a in AKTIVA:
                        aktiva.append({
                            "id": a["id"], "kat": a.get("kat", "ostatni"),
                            "nazev": a["nazev"], "popis": a["popis"], "barva": a.get("barva"),
                            "desetinna": a["desetinna"], "mena": a["mena"],
                            "hodiny": a.get("hodiny") or VYCHOZI_HODINY.get(a.get("kat"), "krypto"),
                            "kotace": s_live_cenou(STAV["kotace"].get(a["id"])),
                            "zpravy": STAV["zpravy"].get(a["id"], []),
                        })
                    self._json({"verze": VERZE, "aktualizovano": STAV["aktualizovano"],
                                "zpravy_aktualizovano": STAV["zpravy_aktualizovano"],
                                "interval_s": CENY_KAZDYCH_S, "aktiva": aktiva})
            elif u.path == "/api/update":
                if q.get("force"):
                    zkontroluj_aktualizaci()
                self._json(info_aktualizace())
            elif u.path == "/api/update/status":
                self._json({"stav": UPD["stav"], "procent": UPD["procent"], "chyba": UPD["chyba"]})
            elif u.path == "/api/live":
                l = live_cena(q.get("id", [""])[0])
                self._json({**(l or {}), "rezim": LIVE_STAV["rezim"]})
            elif u.path == "/api/smc":
                aid, rozsah = q.get("id", [""])[0], q.get("range", ["1D"])[0]
                sm = smc_analyza(historie(aid, rozsah, q.get("iv", [None])[0])) if aid and rozsah in ROZSAHY else None
                self._json(sm or {"chyba": "Málo dat pro SMC"})
            elif u.path == "/api/zdroje":
                nazvy = {a["id"]: a["nazev"] for a in AKTIVA}
                vypis = []
                for z in ZDROJE_ZPRAV:
                    if any(v["nazev"] == z["nazev"] for v in vypis):
                        continue
                    akt = "všechna aktiva" if z.get("aktiva") == "vse" else ", ".join(nazvy.get(x, x) for x in z.get("aktiva", []))
                    vypis.append({"nazev": z["nazev"], "typ": "RSS" if z["typ"] == "rss" else "přes Google News",
                                  "aktiva": akt, "stav": ZDROJE_STAV.get(z["nazev"])})
                self._json({"zdroje": vypis, "kalendar": {"ok": not KALENDAR.get("chyba") and bool(KALENDAR.get("udalosti")),
                                                          "chyba": KALENDAR.get("chyba")}})
            elif u.path == "/api/debata":
                self._json(stav_debaty(q.get("id", [""])[0]))
            elif u.path == "/api/kalendar":
                self._json(KALENDAR)
            elif u.path == "/api/tech":
                self._json(technicka_analyza(q.get("id", [""])[0], q.get("tf", ["1D"])[0]))
            elif u.path == "/api/history":
                self._json(historie(q.get("id", [""])[0], q.get("range", ["1D"])[0], q.get("iv", [None])[0]))
            else:
                self._posli(404, b"Not found", "text/plain")
        except (BrokenPipeError, ConnectionResetError):
            pass


    def do_POST(self):
        try:
            if self.path == "/login":
                delka = min(int(self.headers.get("Content-Length") or 0), 2000)
                data = urllib.parse.parse_qs(self.rfile.read(delka).decode("utf-8", "replace"))
                zadane = (data.get("heslo") or [""])[0]
                if HESLO and hmac.compare_digest(zadane.encode("utf-8"), HESLO.encode("utf-8")):
                    https = self.headers.get("X-Forwarded-Proto", "") == "https"
                    cookie = (f"mm_auth={AUTH_TOKEN}; Path=/; Max-Age={60 * 60 * 24 * 30}; HttpOnly; SameSite=Lax"
                              + ("; Secure" if https else ""))
                    self._presmeruj("/", cookie)
                else:
                    time.sleep(1.5)            # zpomalí hádání hesla
                    self._login_stranka("Špatné heslo.")
                return
            if not self._prihlasen():
                self._posli(401, b'{"chyba": "neprihlasen"}', "application/json")
                return
            pu = urllib.parse.urlparse(self.path)
            if pu.path == "/api/debata/start":
                aid = (urllib.parse.parse_qs(pu.query).get("id") or [""])[0]
                if not groq_klic():
                    self._json({"ok": False, "chyba": "Chybí GROQ_API_KEY."})
                elif (DEBATY.get(aid) or {}).get("stav") == "bezi":
                    self._json({"ok": True})
                elif any(x["id"] == aid for x in AKTIVA):
                    threading.Thread(target=spust_debatu, args=(aid,), daemon=True).start()
                    self._json({"ok": True})
                else:
                    self._json({"ok": False, "chyba": "Neznámé aktivum."})
                return
            if self.path == "/api/update/install" and SERVER_MODE:
                self._json({"ok": False, "chyba": "Webová verze se aktualizuje sama z GitHubu."})
            elif self.path == "/api/update/install":
                if je_novejsi() and UPD["stav"] not in ("stahuji", "restart"):
                    threading.Thread(target=nainstaluj_aktualizaci, daemon=True).start()
                    self._json({"ok": True})
                else:
                    self._json({"ok": False, "chyba": "Není co instalovat."})
            else:
                self._posli(404, b"Not found", "text/plain")
        except (BrokenPipeError, ConnectionResetError):
            pass


def main() -> None:
    global SERVER
    server = None
    if SERVER_MODE:
        port = int(os.environ.get("PORT", PORT))
        server = ThreadingHTTPServer(("0.0.0.0", port), Handler)      # přístupné z internetu
        if not HESLO:
            print("POZOR: není nastavené heslo (MM_HESLO) – web uvidí kdokoli, kdo zná adresu!")
    else:
        for port in range(PORT, PORT + 10):
            try:
                server = ThreadingHTTPServer(("127.0.0.1", port), Handler)
                break
            except OSError:
                continue
    SERVER = server
    if server is None:
        print("Nepodařilo se najít volný port.")
        sys.exit(1)

    url = f"http://localhost:{server.server_address[1]}"
    print("=" * 56)
    print(f"  Market Monitor {VERZE} běží na:  " + url)
    print("  Okno prohlížeče můžeš zavřít a znovu otevřít kdykoli.")
    print("  Ukončení aplikace:  Ctrl + C  v tomto okně")
    print("=" * 56)
    print("Načítám první data (může trvat ~20 s)…")

    threading.Thread(target=smycka, daemon=True).start()
    if OTEVRIT_PROHLIZEC and not SERVER_MODE and "--no-browser" not in sys.argv:
        threading.Timer(1.2, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nUkončeno. Na shledanou!")
        server.server_close()


# ============================================================================
#  FRONTEND (HTML + CSS + JS v jednom)
# ============================================================================

HTML = r"""<!DOCTYPE html>
<html lang="cs">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Market Monitor {{VERZE}}</title>
<script src="https://unpkg.com/lightweight-charts@4.2.0/dist/lightweight-charts.standalone.production.js"></script>
<script>window.LightweightCharts || document.write('<script src="https://cdn.jsdelivr.net/npm/lightweight-charts@4.2.0/dist/lightweight-charts.standalone.production.js"><\/script>')</script>
<style>
  :root{
    --bg:#0b0e14; --panel:#131722; --panel2:#181c27; --border:#232838; --hover:#1c2130;
    --text:#d1d4dc; --muted:#7a7f8e; --up:#26a69a; --down:#ef5350; --accent:#2962ff; --warn:#f5a623;
  }
  *{box-sizing:border-box}
  html,body{margin:0;height:100%;background:var(--bg);color:var(--text);
    font-family:-apple-system,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif;font-size:14px}
  a{color:inherit;text-decoration:none}
  .num{font-variant-numeric:tabular-nums}
  .up{color:var(--up)} .down{color:var(--down)} .muted{color:var(--muted)}

  /* layout */
  .app{display:grid;grid-template-rows:52px 1fr;height:100vh}
  .topbar{display:flex;align-items:center;gap:18px;padding:0 18px;border-bottom:1px solid var(--border);background:var(--panel)}
  .logo{font-weight:700;font-size:16px;letter-spacing:.3px;display:flex;align-items:center;gap:8px}
  .logo .dot{width:10px;height:10px;border-radius:3px;background:linear-gradient(135deg,#2962ff,#26a69a)}
  .ver{font-size:11px;font-weight:700;padding:2px 7px;border-radius:4px;background:var(--hover);color:var(--muted);cursor:pointer;border:none;font-family:inherit}
  .ver:hover{color:var(--text)}
  .updbtn{background:var(--up);color:#fff;border:none;border-radius:6px;padding:6px 12px;font-weight:700;font-size:12px;cursor:pointer;
    animation:glow 2s infinite;font-family:inherit}
  .updbtn:hover{filter:brightness(1.1)}
  @keyframes glow{0%{box-shadow:0 0 0 0 rgba(38,166,154,.6)}70%{box-shadow:0 0 0 8px rgba(38,166,154,0)}100%{box-shadow:0 0 0 0 rgba(38,166,154,0)}}
  .hide{display:none !important}
  .modal{position:fixed;inset:0;background:rgba(0,0,0,.6);display:flex;align-items:center;justify-content:center;z-index:100}
  .mbox{background:var(--panel2);border:1px solid var(--border);border-radius:12px;width:460px;max-width:92vw;padding:20px 22px;
    box-shadow:0 20px 60px rgba(0,0,0,.5)}
  .mh{display:flex;align-items:center;justify-content:space-between;font-size:16px;font-weight:700;margin-bottom:10px}
  .mh .x{background:none;border:none;color:var(--muted);font-size:16px;cursor:pointer}
  .mbox p{margin:8px 0;line-height:1.5}
  .notes{white-space:pre-wrap;background:var(--bg);border:1px solid var(--border);border-radius:8px;padding:10px 12px;
    font-size:13px;max-height:200px;overflow:auto;margin:10px 0;color:var(--text)}
  .mbtns{display:flex;gap:8px;margin-top:14px}
  .primary{background:var(--accent);color:#fff;border:none;border-radius:6px;padding:9px 16px;font-weight:700;cursor:pointer;font-family:inherit}
  .primary:hover{filter:brightness(1.1)}
  .pbar{height:8px;background:var(--bg);border-radius:4px;overflow:hidden;margin:12px 0 6px}
  .pbar div{height:100%;width:0;background:linear-gradient(90deg,#2962ff,#26a69a);transition:width .3s}
  .status{margin-left:auto;display:flex;align-items:center;gap:8px;color:var(--muted);font-size:12px}
  .live{width:8px;height:8px;border-radius:50%;background:var(--up);box-shadow:0 0 0 0 rgba(38,166,154,.6);animation:pulse 2s infinite}
  .live.off{background:var(--down);animation:none}
  @keyframes pulse{0%{box-shadow:0 0 0 0 rgba(38,166,154,.6)}70%{box-shadow:0 0 0 8px rgba(38,166,154,0)}100%{box-shadow:0 0 0 0 rgba(38,166,154,0)}}
  .clock{font-variant-numeric:tabular-nums;color:var(--text);font-size:13px}

  .main{display:grid;grid-template-columns:290px 1fr 380px;min-height:0}
  .col{min-height:0;display:flex;flex-direction:column;border-right:1px solid var(--border)}
  .col:last-child{border-right:none}
  .col-h{padding:12px 16px;font-size:12px;text-transform:uppercase;letter-spacing:.8px;color:var(--muted);
    border-bottom:1px solid var(--border);display:flex;align-items:center;justify-content:space-between}

  /* watchlist */
  .wl{overflow:auto;flex:1}
  .wl{padding:4px 0}
  .wl-box{margin:10px 10px 12px;border:1px solid #2e3446;border-radius:10px;overflow:hidden;background:var(--panel)}
  .wl-box-h{display:flex;align-items:center;gap:8px;padding:9px 12px;background:var(--panel2);cursor:pointer;
    border-bottom:1px solid #2e3446;user-select:none;font-size:12px;font-weight:700;text-transform:uppercase;letter-spacing:.8px}
  .wl-box-h:hover{background:var(--hover)}
  .wl-box-h .chev{color:var(--muted);transition:transform .2s;font-size:10px}
  .wl-box.closed .chev{transform:rotate(-90deg)}
  .wl-box.closed .wl-box-h{border-bottom:none}
  .wl-box.closed .wl-box-b{display:none}
  .wl-box-h .cnt{color:var(--muted);font-weight:500}
  .wl-box-h .avg{margin-left:auto;text-transform:none;letter-spacing:0}
  .wl-tools{display:flex;gap:6px}
  .wl-edit{background:var(--panel2);border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:3px 9px;
    font-size:11px;font-weight:600;cursor:pointer;font-family:inherit;text-transform:none;letter-spacing:0}
  .wl-edit:hover{color:var(--text)} .wl-edit.on{background:var(--accent);border-color:var(--accent);color:#fff}
  .ord{display:none;gap:3px}
  .ord button{width:24px;height:22px;border-radius:5px;border:1px solid var(--border);background:var(--bg);color:var(--text);
    cursor:pointer;font-size:10px;line-height:1;padding:0}
  .ord button:hover{background:var(--accent);border-color:var(--accent)}
  .wl.editing .ord{display:flex}
  .wl.editing .ord-g{margin-left:auto}
  .wl.editing .wl-box-h .avg,.wl.editing .wl-box-h .chev{display:none}
  .wl.editing .ord-i{position:absolute;right:10px;top:50%;transform:translateY(-50%);flex-direction:column;z-index:2}
  .wl.editing .wl-price,.wl.editing .pill,.wl.editing .wl-alert{visibility:hidden}
  .wl.editing .wl-item,.wl.editing .wl-box-h{cursor:grab}
  .wl.editing .wl-box{border-style:dashed}
  .wl-item.dragover{box-shadow:inset 0 3px 0 var(--accent)}
  .wl-box.dragover{outline:2px solid var(--accent)}
  .wl-box-b .wl-item:last-child{border-bottom:none}
  .wl-ico{grid-row:1 / span 2;width:34px;height:34px;align-self:center}
  .wl-ico svg,.hdr-ico svg{width:100%;height:100%;display:block}
  .hdr-ico{width:30px;height:30px;align-self:center}
  .wl-item{display:grid;grid-template-columns:34px 1fr auto;grid-template-rows:auto auto;gap:2px 10px;
    padding:12px 16px;border-bottom:1px solid var(--border);cursor:pointer;position:relative;transition:background .15s}
  .wl-item:hover{background:var(--hover)}
  .wl-item.active{background:var(--panel2)}
  .wl-item.active::before{content:"";position:absolute;left:0;top:0;bottom:0;width:3px;background:var(--accent)}
  .wl-name{font-weight:600}
  .wl-tick{font-size:11px;color:var(--muted)}
  .wl-price{text-align:right;font-weight:600;border-radius:4px;padding:0 4px;transition:background .6s}
  .wl-price.flash-up{background:rgba(38,166,154,.25)} .wl-price.flash-down{background:rgba(239,83,80,.25)}
  .pill{justify-self:end;font-size:12px;font-weight:600;padding:2px 7px;border-radius:4px}
  .pill.up{background:rgba(38,166,154,.15)} .pill.down{background:rgba(239,83,80,.15)}
  .wl-spark{grid-column:1 / -1;height:30px;margin-top:6px}
  .wl-alert{position:absolute;top:10px;right:8px;width:7px;height:7px;border-radius:50%;background:var(--warn)}

  /* center */
  .center{background:var(--panel)}
  .hdr{padding:16px 20px 10px;border-bottom:1px solid var(--border)}
  .hdr-top{display:flex;align-items:center;gap:12px;flex-wrap:wrap}
  .hdr-name{font-size:20px;font-weight:700}
  .hdr-sub{color:var(--muted);font-size:13px}
  .hdr-price{display:flex;align-items:baseline;gap:12px;margin-top:6px}
  .big{font-size:32px;font-weight:700;border-radius:6px;padding:0 6px;margin-left:-6px;transition:background .6s}
  .big.flash-up{background:rgba(38,166,154,.22)} .big.flash-down{background:rgba(239,83,80,.22)}
  .livebadge{margin-left:auto;display:flex;align-items:center;gap:6px;font-size:12px;font-weight:600;color:var(--muted)}
  .livebadge .ld{width:8px;height:8px;border-radius:50%;background:var(--muted)}
  .livebadge.on{color:var(--up)} .livebadge.on .ld{background:var(--up);animation:pulse 1.6s infinite}
  .livebadge .sub{font-weight:500;color:var(--muted)}
  .chg{font-size:16px;font-weight:600}
  .stats{display:flex;gap:22px;margin-top:12px;flex-wrap:wrap}
  .stat .l{font-size:11px;color:var(--muted);text-transform:uppercase;letter-spacing:.5px}
  .stat .v{font-weight:600;margin-top:2px}
  .alerts{display:flex;gap:8px;flex-wrap:wrap;margin-top:10px}
  .alert-chip{font-size:12px;padding:4px 10px;border-radius:20px;background:rgba(245,166,35,.12);color:var(--warn);border:1px solid rgba(245,166,35,.3)}

  .toolbar{display:flex;align-items:center;gap:2px;padding:8px 10px;border-bottom:1px solid var(--border);flex-wrap:nowrap;
    overflow-x:auto;scrollbar-width:thin}
  .toolbar .btn{white-space:nowrap;flex:0 0 auto;padding:6px 8px}
  .toolbar .livebadge{white-space:nowrap;flex:0 0 auto;padding-left:8px}
  .toolbar::-webkit-scrollbar{height:4px}
  .btn{background:none;border:none;color:var(--muted);padding:6px 10px;border-radius:4px;cursor:pointer;font-size:13px;font-weight:600}
  .btn:hover{background:var(--hover);color:var(--text)}
  .btn.on{color:var(--text);background:var(--hover)}
  .sep{width:1px;height:18px;background:var(--border);margin:0 6px}
  .chart-wrap{flex:1;position:relative;min-height:0}
  #chart{position:absolute;inset:0}
  .sessov{position:absolute;inset:0;width:100%;height:100%;pointer-events:none;z-index:2;overflow:hidden}
  .sesswrap{position:relative}
  .sesspop{position:fixed;top:0;left:0;z-index:60;background:var(--panel2);border:1px solid var(--border);border-radius:8px;
    padding:8px 4px;min-width:210px;box-shadow:0 10px 30px rgba(0,0,0,.45)}
  .sesspop label{display:flex;align-items:center;gap:9px;padding:6px 10px;cursor:pointer;font-size:13px;border-radius:4px}
  .sesspop label:hover{background:var(--hover)}
  .sesspop .sw{width:12px;height:12px;border-radius:3px}
  .sesspop hr{border:none;border-top:1px solid var(--border);margin:4px 0}
  .sesspop .hint{font-size:11px;color:var(--muted);padding:4px 10px 2px}
  .btn.sess-on{color:#ff9800}
  .btn.smc-on{color:#b388ff}
  .btn.calls-on{color:#5b9dff}
  .ai-lv{display:flex;gap:12px;flex-wrap:wrap;font-size:12.5px;margin-top:9px;color:var(--muted)}
  .ai-lv b{color:var(--text)} .ai-lv .up b{color:#26a69a} .ai-lv .down b{color:#ef5350}
  .calls-sum{font-size:12px;margin-top:10px;padding-top:8px;border-top:1px solid var(--border);color:var(--muted)}
  .calls-sum b{color:var(--text)} .calls-sum b.up{color:#26a69a} .calls-sum b.down{color:#ef5350}
  .calls-list{margin-top:6px;max-height:200px;overflow:auto}
  .call-row{display:flex;gap:7px;align-items:center;font-size:11.5px;padding:4px 0;border-bottom:1px solid var(--border);flex-wrap:wrap}
  .call-v{font-weight:700} .call-v.sb,.call-v.b{color:#2962ff} .call-v.ss,.call-v.s{color:#f23645} .call-v.n{color:#9598a1}
  .ivwrap{position:relative}
  .ivpop{position:fixed;top:0;left:0;z-index:60;background:var(--panel2);border:1px solid var(--border);border-radius:10px;
    padding:6px;min-width:230px;box-shadow:0 10px 30px rgba(0,0,0,.45)}
  .ivpop-h{font-size:12px;font-weight:700;color:var(--muted);padding:6px 10px 8px;text-align:center}
  .ivopt{display:flex;justify-content:space-between;align-items:center;width:100%;background:none;border:none;color:var(--text);
    padding:8px 10px;border-radius:6px;font-size:13.5px;cursor:pointer;font-family:inherit;text-align:left}
  .ivopt:hover{background:var(--hover)}
  .ivopt.sel{color:#29a3ff;font-weight:600}
  .legend{position:absolute;left:14px;top:10px;z-index:3;font-size:12px;color:var(--muted);pointer-events:none}
  .legend b{color:var(--text);font-weight:600;margin-right:10px}
  .overlay{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;color:var(--muted);z-index:4;background:var(--panel)}
  .overlay.hide{display:none}

  /* news */
  .tabs{display:flex;gap:4px}
  .news{overflow:auto;flex:1}
  .tech{border-bottom:1px solid var(--border);flex:0 0 auto}
  .col.newscol{overflow-y:auto}
  .col.newscol .news{flex:none;overflow:visible}
  .tech-body{padding:6px 16px 12px;text-align:center}
  .gauge{width:270px;max-width:100%;margin:0 auto;display:block}
  .gauge .needle{transition:transform .9s cubic-bezier(.3,1.4,.5,1);transform-origin:120px 112px;transform-box:view-box}
  .tech-label{font-size:22px;font-weight:700;margin-top:-6px}
  .tech-label.sb,.tech-label.b{color:#2962ff} .tech-label.ss,.tech-label.s{color:#f23645} .tech-label.n{color:var(--muted)}
  .tech-sum{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:10px;text-align:left}
  .tech-box{background:var(--panel2);border:1px solid var(--border);border-radius:8px;padding:8px 10px}
  .tech-box .t{font-size:11px;color:var(--muted);text-transform:uppercase;letter-spacing:.5px}
  .tech-box .v{font-weight:700;margin:2px 0 4px}
  .tech-box .cnt{font-size:11px;color:var(--muted);display:flex;gap:8px}
  .tech-box .cnt b{font-weight:600}
  .tech-det{margin-top:10px;max-height:230px;overflow:auto;text-align:left;border:1px solid var(--border);border-radius:8px}
  .tech-det table{width:100%;border-collapse:collapse;font-size:12px}
  .tech-det th{position:sticky;top:0;background:var(--panel2);color:var(--muted);font-weight:600;text-align:left;padding:6px 8px}
  .tech-det td{padding:5px 8px;border-top:1px solid var(--border)}
  .tech-det .grp td{background:var(--bg);color:var(--muted);font-size:11px;text-transform:uppercase;letter-spacing:.5px}
  .tech-note{font-size:10.5px;color:var(--muted);margin-top:8px}
  .ai{margin-top:12px;border:1px solid #2e3446;border-radius:10px;background:var(--panel2);text-align:left;overflow:hidden}
  .ai-h{display:flex;align-items:center;gap:8px;padding:9px 12px;border-bottom:1px solid var(--border);font-weight:700;font-size:13px}
  .ai-h .bots{margin-left:2px;letter-spacing:1px;font-size:13px}
  .ai-h button{margin-left:auto}
  .primary.sm{padding:6px 12px;font-size:12px;border-radius:6px}
  .primary:disabled{opacity:.5;cursor:default;filter:none}
  .ai-b{padding:10px 12px}
  .ai-verd{display:flex;align-items:center;gap:10px}
  .ai-pill{font-weight:800;font-size:15px;padding:5px 12px;border-radius:6px;color:#fff}
  .ai-pill.sb,.ai-pill.b{background:#2962ff} .ai-pill.ss,.ai-pill.s{background:#f23645} .ai-pill.n{background:#5d6270}
  .ai-conf{flex:1;font-size:11px;color:var(--muted)}
  .ai-conf .bar{height:6px;border-radius:3px;background:var(--bg);margin-top:4px;overflow:hidden}
  .ai-conf .bar div{height:100%;background:linear-gradient(90deg,#2962ff,#26a69a)}
  .ai-sum{font-size:13px;line-height:1.5;margin-top:9px}
  .ai-meta{font-size:11px;color:var(--muted);margin-top:8px;display:flex;justify-content:space-between;gap:8px;flex-wrap:wrap}
  .ai-stances{display:flex;gap:6px;flex-wrap:wrap;margin-top:9px}
  .ai-st{font-size:11px;padding:3px 7px;border-radius:12px;background:var(--bg);border:1px solid var(--border)}
  .ai-st b.up{color:#2962ff} .ai-st b.down{color:#f23645}
  .ai-thread{margin-top:10px;border-top:1px solid var(--border);padding-top:6px;max-height:420px;overflow:auto}
  .ai-msg{display:flex;gap:9px;padding:8px 0}
  .ai-av{flex:0 0 30px;height:30px;border-radius:50%;background:var(--bg);display:flex;align-items:center;justify-content:center;font-size:15px}
  .ai-msg .who{font-size:12px;font-weight:700;margin-bottom:2px}
  .ai-msg .who span{font-weight:500;color:var(--muted);font-size:11px;margin-left:4px}
  .ai-msg .txt{font-size:12.5px;line-height:1.5;white-space:pre-wrap;color:var(--text)}
  .ai-msg.sef .txt{background:rgba(41,98,255,.08);border:1px solid rgba(41,98,255,.25);border-radius:8px;padding:7px 9px}
  .ai-run{display:flex;align-items:center;gap:9px;font-size:13px;color:var(--text)}
  .spin{width:14px;height:14px;border-radius:50%;border:2px solid var(--border);border-top-color:var(--accent);animation:sp .8s linear infinite}
  @keyframes sp{to{transform:rotate(360deg)}}
  .ai-err{color:#ef5350;font-size:12.5px;line-height:1.5}
  .mkt{display:inline-flex;align-items:center;gap:6px;border:1px solid var(--border);background:var(--panel2);color:var(--text);
    border-radius:14px;padding:3px 10px;font-size:12px;font-weight:600;cursor:pointer;font-family:inherit}
  .mkt:hover{background:var(--hover)}
  .mkt-dot{width:8px;height:8px;border-radius:50%;background:#787b86;display:inline-block}
  .mkt.open .mkt-dot,.hrs-status.open .mkt-dot{background:#26a69a;box-shadow:0 0 0 3px rgba(38,166,154,.18)}
  .mkt.ext .mkt-dot,.hrs-status.ext .mkt-dot{background:#f5a623}
  .mkt.closed .mkt-dot,.hrs-status.closed .mkt-dot{background:#ef5350}
  .mkt.open{color:#26a69a} .mkt.ext{color:#f5a623} .mkt.closed{color:#ef5350}
  .hrs-head{display:flex;align-items:center;gap:10px;margin-bottom:10px}
  .hrs-status{display:flex;align-items:center;gap:8px;padding:9px 12px;border:1px solid var(--border);border-radius:8px;
    background:var(--bg);font-size:13px;margin-bottom:12px;flex-wrap:wrap}
  .hrs-status.open b{color:#26a69a} .hrs-status.ext b{color:#f5a623} .hrs-status.closed b{color:#ef5350}
  .hrs-grid{position:relative}
  .hrs-row{display:grid;grid-template-columns:48px 1fr;align-items:center;padding:7px 0;border-radius:8px}
  .hrs-row.today{background:rgba(41,98,255,.12)}
  .hrs-day{font-size:13px;font-weight:700;color:var(--muted);padding-left:8px}
  .hrs-row.today .hrs-day{color:#5b9dff}
  .hrs-now-t{font-size:10.5px;font-weight:600;color:var(--text)}
  .hrs-cell{position:relative;padding-right:10px}
  .hrs-track{position:relative;height:7px;border-radius:4px;background:#1c2130;overflow:hidden}
  .hrs-seg{position:absolute;top:0;bottom:0;border-radius:4px}
  .hrs-seg.reg{background:#4cd964} .hrs-seg.ext{background:rgba(76,217,100,.35)}
  .hrs-txt{font-size:10.5px;color:var(--muted);margin-top:3px}
  .hrs-mark{position:absolute;top:-9px;width:0;height:0;border-left:6px solid transparent;border-right:6px solid transparent;
    border-top:7px solid #fff;transform:translateX(-6px)}
  .hrs-nowline{position:absolute;top:0;bottom:24px;width:2px;background:#29a3ff;z-index:1;pointer-events:none;margin-left:-1px}
  .hrs-axis{padding-top:2px}
  .hrs-ticks{display:flex;justify-content:space-between;font-size:10px;color:var(--muted);padding-right:10px}
  .srctab{width:100%;border-collapse:collapse;margin-bottom:8px}
  .srctab td{padding:7px 6px;border-bottom:1px solid var(--border);vertical-align:top;font-size:13px}
  .srctab td:first-child{width:16px}
  .ai-scen{margin-top:10px;border:1px solid var(--border);border-radius:8px;padding:8px 10px;background:var(--bg)}
  .ai-scen-h{font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.5px;color:var(--muted);margin-bottom:4px}
  .ai-sc{padding:5px 0}
  .ai-sc + .ai-sc{border-top:1px solid var(--border)}
  .ai-sc-t{display:flex;justify-content:space-between;font-size:12.5px;font-weight:600}
  .ai-sc-bar{height:4px;border-radius:2px;background:var(--panel2);margin:4px 0 3px;overflow:hidden}
  .ai-sc-bar div{height:100%}
  .ai-sc-p{font-size:12px;color:var(--muted);line-height:1.4}
  .linkbtn{background:none;border:none;color:var(--accent);cursor:pointer;font-size:12px;font-weight:600;margin-top:8px;font-family:inherit}
  .cal-day{padding:8px 16px 6px;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.6px;color:var(--muted);
    background:var(--bg);border-bottom:1px solid var(--border);position:sticky;top:0;z-index:1}
  .cal-row{display:grid;grid-template-columns:46px 38px 1fr;gap:8px;padding:9px 16px;border-bottom:1px solid var(--border);align-items:start}
  .cal-row.past{opacity:.45}
  .cal-row.next{background:linear-gradient(90deg,rgba(245,166,35,.12),transparent 70%)}
  .cal-time{font-weight:600;font-variant-numeric:tabular-nums}
  .cal-cur{font-size:11px;font-weight:700;padding:2px 5px;border-radius:3px;background:var(--hover);text-align:center}
  .cal-t{font-size:13px;font-weight:500;line-height:1.35}
  .cal-t .imp{display:inline-block;width:8px;height:8px;border-radius:2px;margin-right:6px;vertical-align:1px}
  .cal-t .imp.High{background:#f23645} .cal-t .imp.Medium{background:#ff9800} .cal-t .imp.Low{background:#f5d142}
  .cal-v{font-size:11px;color:var(--muted);margin-top:3px}
  .cal-v b{color:var(--text);font-weight:600}
  .cal-soon{color:var(--warn);font-weight:700}
  .n-item{display:block;padding:12px 16px;border-bottom:1px solid var(--border);transition:background .15s}
  .n-item:hover{background:var(--hover)}
  .n-meta{display:flex;align-items:center;gap:8px;font-size:11px;color:var(--muted);margin-bottom:5px}
  .n-title{font-size:13.5px;line-height:1.4;font-weight:500}
  .badge{font-size:10px;font-weight:700;padding:1px 6px;border-radius:3px;background:var(--accent);color:#fff;letter-spacing:.4px}
  .tag{font-size:10px;font-weight:600;padding:1px 6px;border-radius:3px;background:var(--hover);color:var(--text)}
  .n-item.fresh{background:linear-gradient(90deg,rgba(41,98,255,.10),transparent 60%)}
  .empty{padding:24px 16px;color:var(--muted);text-align:center}

  /* toasts */
  .toasts{position:fixed;right:18px;bottom:18px;display:flex;flex-direction:column;gap:10px;z-index:50;max-width:360px}
  .toast{background:var(--panel2);border:1px solid var(--border);border-left:3px solid var(--accent);border-radius:6px;
    padding:10px 14px;box-shadow:0 8px 24px rgba(0,0,0,.4);font-size:13px;animation:slide .25s ease-out;cursor:pointer}
  .toast.warn{border-left-color:var(--warn)}
  .toast .t-h{font-weight:700;margin-bottom:3px}
  @keyframes slide{from{transform:translateX(30px);opacity:0}to{transform:none;opacity:1}}

  .foot{padding:8px 16px;font-size:11px;color:var(--muted);border-top:1px solid var(--border)}
  ::-webkit-scrollbar{width:8px} ::-webkit-scrollbar-thumb{background:#2a2f40;border-radius:4px}

  @media (max-width:1150px){
    .main{grid-template-columns:240px 1fr}
    .col.newscol{display:none}
  }

  /* ---------- TELEFON ---------- */
  @media (max-width:820px){
    html,body{height:auto}
    .app{display:block;height:auto}
    .topbar{position:sticky;top:0;z-index:30;padding:0 12px;gap:10px}
    .topbar .clock,.topbar .status .sep{display:none}
    #upd{max-width:130px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:11px}
    .logo{font-size:15px}
    .main{display:flex;flex-direction:column}
    .col{border-right:none;border-bottom:1px solid var(--border)}
    .main > .col:first-child > .foot{display:none}
    .main > .col:first-child > .col-h{padding:6px 12px}
    .wl{display:flex;overflow-x:auto;overflow-y:hidden;padding:8px 4px;-webkit-overflow-scrolling:touch;scroll-snap-type:x proximity}
    .wl-box{flex:0 0 auto;margin:0 4px;display:flex;flex-direction:column;scroll-snap-align:start}
    .wl-box-h{padding:6px 10px;font-size:10.5px}
    .wl-box-h .avg{display:none}
    .wl-box-b{display:flex}
    .wl-item{width:168px;padding:8px 10px;border-bottom:none;border-right:1px solid var(--border);
      grid-template-columns:26px 1fr auto;gap:1px 8px}
    .wl-item:last-child{border-right:none}
    .wl-item.active::before{top:auto;bottom:0;left:0;right:0;width:auto;height:3px}
    .wl-ico{width:26px;height:26px}
    .wl-name{font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .wl-price{font-size:13px}
    .pill,.wl-price{font-size:11px;white-space:nowrap}
    .wl-price{font-size:13px}
    .wl-spark{height:22px;margin-top:4px}
    .wl-alert{top:6px;right:4px}
    .hdr{padding:12px 14px 8px}
    .hdr-name{font-size:18px}
    .big{font-size:26px}
    .chg{font-size:14px}
    .stats{gap:14px}
    .toolbar{overflow-x:auto;flex-wrap:nowrap;padding:6px 8px;-webkit-overflow-scrolling:touch}
    .toolbar .btn{flex:0 0 auto}
    .livebadge{flex:0 0 auto;padding-left:8px}
    .chart-wrap{flex:none;height:56vh;min-height:300px}
    .col.newscol{display:flex !important}
    .news{overflow:visible;flex:none}
    .tech-det{max-height:none}
    .toasts{left:10px;right:10px;bottom:10px;max-width:none}
    .sesspop{position:fixed;top:auto;left:10px;right:10px;bottom:10px}
    .ivpop{position:fixed;top:auto;left:0;right:0;bottom:0;border-radius:16px 16px 0 0;padding:10px 10px 18px;max-height:75vh;overflow:auto}
    .ivpop-h{font-size:16px;color:var(--text);padding:8px 10px 12px}
    .ivopt{font-size:16px;padding:13px 12px}
    .mbox{padding:16px}
  }
</style>
</head>
<body>
<div class="app">
  <div class="topbar">
    <div class="logo"><span class="dot"></span>Market Monitor <button class="ver" id="verbtn" title="Aktualizace">{{VERZE}}</button></div>
    <button class="updbtn hide" id="updbtn">⬆ Aktualizovat</button>
    <div class="status"><span class="live off" id="live"></span><span id="upd">Načítám data…</span>
      <span class="sep"></span><span class="clock" id="clock"></span></div>
  </div>

  <div class="main">
    <div class="col">
      <div class="col-h"><span>Watchlist</span><span class="wl-tools"><button class="wl-edit hide" id="wlreset" title="Vrátit výchozí pořadí">↺ Výchozí</button>
        <button class="wl-edit" id="wleditbtn" title="Seřadit skupiny a aktiva">⇅ Upravit</button></span></div>
      <div class="wl" id="wl"></div>
      <div class="foot">Data: Yahoo Finance · futures mohou být zpožděné ~10 min</div>
    </div>

    <div class="col center">
      <div class="hdr" id="hdr"></div>
      <div class="toolbar" id="toolbar">
        <button class="btn" data-r="1D">1D</button><button class="btn" data-r="5D">5D</button>
        <button class="btn" data-r="1M">1M</button><button class="btn" data-r="6M">6M</button>
        <button class="btn" data-r="1R">1R</button><button class="btn" data-r="5R">5R</button>
        <span class="ivwrap"><button class="btn" id="ivbtn" title="Interval svíček (1 min – 1 měsíc)">⏱ <span id="ivlbl">Auto</span> ▾</button>
          <div class="ivpop hide" id="ivpop"></div></span>
        <span class="sep"></span>
        <button class="btn" data-t="candle">Svíčky</button><button class="btn" data-t="area">Čára</button>
        <span class="sep"></span>
        <button class="btn" id="callsbtn" title="Šéfovy tipy na grafu (šipka, cíl, stop, ✓/✗)">👔 Tipy</button>
        <button class="btn" id="smcbtn" title="Smart Money Concepts: swingy, BOS/CHoCH, likvidita, sweepy">🧠 SMC</button>
        <span class="sesswrap"><button class="btn" id="sessbtn" title="Obchodní seance (Tokyo / Londýn / New York)">◫ Seance ▾</button>
          <div class="sesspop hide" id="sesspop"></div></span>
        <button class="btn" id="resetbtn" title="Obnovit zobrazení grafu (také dvojklik do grafu)">⟲ Reset</button>
        <span class="livebadge" id="livebadge"><span class="ld"></span><span>…</span></span>
      </div>
      <div class="chart-wrap">
        <div class="legend" id="legend"></div>
        <div id="chart"></div>
        <svg class="sessov" id="sessov"></svg>
        <svg class="sessov" id="smcov"></svg>
        <svg class="sessov" id="callov"></svg>
        <div class="overlay" id="overlay">Načítám graf…</div>
      </div>
    </div>

    <div class="col newscol">
      <div class="tech">
        <div class="col-h"><span>Technická analýza</span>
          <div class="tabs"><button class="btn" data-tf="1H">1H</button><button class="btn on" data-tf="1D">1D</button><button class="btn" data-tf="1T">1T</button></div>
        </div>
        <div class="tech-body">
          <svg class="gauge" id="gauge" viewBox="-34 -18 308 150"></svg>
          <div class="tech-label n" id="techlabel">Počítám…</div>
          <div class="tech-sum" id="techsum"></div>
          <button class="linkbtn" id="techmore">Zobrazit podrobnosti ▾</button>
          <div class="tech-det hide" id="techdet"></div>
          <div class="tech-note">Automatický výpočet z indikátorů – nejde o investiční doporučení.</div>
          <div class="ai">
            <div class="ai-h">AI tým <span class="bots">📊🧠🔭📰🛡️👔</span>
              <button class="primary sm" id="aibtn">Spustit debatu</button></div>
            <div class="ai-b" id="aibody"><div class="muted" style="font-size:12.5px">Šest AI botů (analytik, SMC bot, scenárista,
              zpravodaj, risk manažer a šéf) probere grafy, scénáře a zprávy a šéf vynese verdikt.</div></div>
          </div>
        </div>
      </div>
      <div class="col-h"><span>Zprávy</span>
        <div class="tabs"><button class="btn on" data-n="sel" id="tab-sel">Vybrané</button><button class="btn" data-n="all" id="tab-all">Vše</button></div>
      </div>
      <div class="news" id="news"><div class="empty">Hledám zprávy…</div></div>
      <div class="foot" id="newsfoot">Zdroje: Google News, Yahoo Finance, Reuters, EIA, Fed, ECB, BLS, CNBC, SEC, Kitco, OilPrice,
        CoinDesk a další · <button class="linkbtn" id="srcbtn" style="margin:0;font-size:11px">Stav zdrojů ▸</button></div>
    </div>
  </div>
</div>
<div class="toasts" id="toasts"></div>
<div class="modal hide" id="hoursmodal"><div class="mbox" style="width:560px">
  <div class="mh"><span>Obchodní hodiny</span><button class="x" id="hoursclose">✕</button></div>
  <div id="hoursbody"></div>
</div></div>
<div class="modal hide" id="srcmodal"><div class="mbox" style="width:520px">
  <div class="mh"><span>Stav zdrojů zpráv</span><button class="x" id="srcclose">✕</button></div>
  <div id="srcbody" style="max-height:65vh;overflow:auto"></div>
</div></div>
<div class="modal hide" id="modal"><div class="mbox">
  <div class="mh"><span>Aktualizace aplikace</span><button class="x" id="mclose">✕</button></div>
  <div id="mbody"></div>
</div></div>

<script>
const S = { assets: [], sel: null, range: '1D', type: 'candle', newsTab: 'sel',
            lastPrice: {}, knownNews: null, shownAlerts: new Set() };
let seen = new Set();
try { seen = new Set(JSON.parse(localStorage.getItem('mm_seen') || '[]')); } catch (e) {}
function saveSeen(){ try { localStorage.setItem('mm_seen', JSON.stringify([...seen].slice(-3000))); } catch(e){} }

const $ = id => document.getElementById(id);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmt = (v, d) => v == null ? '—' : Number(v).toLocaleString('cs-CZ', {minimumFractionDigits:d, maximumFractionDigits:d});
const fmtVol = v => !v ? '—' : v >= 1e9 ? (v/1e9).toFixed(2)+' mld' : v >= 1e6 ? (v/1e6).toFixed(2)+' mil' : v >= 1e3 ? (v/1e3).toFixed(1)+' tis' : v;
const cls = v => v > 0 ? 'up' : v < 0 ? 'down' : '';
const arrow = v => v > 0 ? '▲' : v < 0 ? '▼' : '•';
function ago(ts){
  if (!ts) return '';
  const m = Math.floor((Date.now()/1000 - ts)/60);
  if (m < 1) return 'právě teď';
  if (m < 60) return `před ${m} min`;
  if (m < 1440) return `před ${Math.floor(m/60)} h`;
  return `před ${Math.floor(m/1440)} d`;
}
const asset = id => S.assets.find(a => a.id === id);

/* ---------- hodiny ---------- */
setInterval(() => { $('clock').textContent = new Date().toLocaleTimeString('cs-CZ'); }, 1000);

/* ---------- sparkline ---------- */
function spark(points, up){
  if (!points || points.length < 2) return '';
  const w = 250, h = 30, min = Math.min(...points), max = Math.max(...points), r = (max - min) || 1;
  const xy = points.map((p, i) => `${(i/(points.length-1)*w).toFixed(1)},${(h - 2 - (p-min)/r*(h-4)).toFixed(1)}`);
  const col = up ? '#26a69a' : '#ef5350', gid = 'g' + Math.random().toString(36).slice(2);
  return `<svg viewBox="0 0 ${w} ${h}" preserveAspectRatio="none" width="100%" height="30">
    <defs><linearGradient id="${gid}" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="${col}" stop-opacity=".25"/><stop offset="1" stop-color="${col}" stop-opacity="0"/></linearGradient></defs>
    <polygon points="0,${h} ${xy.join(' ')} ${w},${h}" fill="url(#${gid})"/>
    <polyline points="${xy.join(' ')}" fill="none" stroke="${col}" stroke-width="1.5"/></svg>`;
}

/* ---------- watchlist ---------- */
const KATEGORIE = { akcie: 'Akcie', krypto: 'Krypto', forex: 'Forex', komodity: 'Komodity', ostatni: 'Ostatní' };
const katNazev = k => KATEGORIE[k] || k;
let closedGroups = new Set();
try { closedGroups = new Set(JSON.parse(localStorage.getItem('mm_closed') || '[]')); } catch (e) {}
const visibleAssets = () => orderedAssets().filter(a => !closedGroups.has(a.kat));   // pro šipky ↑↓

/* ---------- IKONY (vlastní kresba, žádná cizí loga) ---------- */
const ICONS = {
  btc: `<svg viewBox="0 0 36 36"><circle cx="18" cy="18" r="18" fill="#f7931a"/>
    <g transform="rotate(14 18 18)" fill="none" stroke="#fff" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round">
      <path d="M13.5 10.5h6a3.6 3.6 0 0 1 0 7.2h-6zM13.5 17.7h7a3.9 3.9 0 0 1 0 7.8h-7zM13.5 10.5v15"/>
      <path d="M16 8v2.5M19.5 8v2.5M16 25.5V28M19.5 25.5V28"/></g></svg>`,
  gold: `<svg viewBox="0 0 36 36"><defs><linearGradient id="igd" x1="0" y1="0" x2="0" y2="1">
      <stop offset="0" stop-color="#ffe27a"/><stop offset="1" stop-color="#c8921c"/></linearGradient></defs>
    <circle cx="18" cy="18" r="18" fill="#3b2f10"/>
    <g transform="translate(18 18.6) scale(1.3) translate(-18 -18.3)">
    <path d="M13 12.5h10l2 5H11z" fill="url(#igd)"/><path d="M8 19h10l2 5H6zM18 19h10l2 5H16z" fill="url(#igd)"/>
    <path d="M13 12.5h10l.6 1.5H12.4z" fill="#fff6c8" opacity=".7"/></g></svg>`,
  silver: `<svg viewBox="0 0 36 36"><defs><linearGradient id="isd" x1="0" y1="0" x2="0" y2="1">
      <stop offset="0" stop-color="#f4f6f8"/><stop offset="1" stop-color="#8e99a6"/></linearGradient></defs>
    <circle cx="18" cy="18" r="18" fill="#2a3038"/>
    <g transform="translate(18 18.6) scale(1.3) translate(-18 -18.3)">
    <path d="M13 12.5h10l2 5H11z" fill="url(#isd)"/><path d="M8 19h10l2 5H6zM18 19h10l2 5H16z" fill="url(#isd)"/>
    <path d="M13 12.5h10l.6 1.5H12.4z" fill="#fff" opacity=".7"/></g></svg>`,
  oil: `<svg viewBox="0 0 36 36"><circle cx="18" cy="18" r="18" fill="#23272f"/>
    <path d="M18 7.5c3.8 5.2 7 9 7 13a7 7 0 0 1-14 0c0-4 3.2-7.8 7-13z" fill="#e8eaed"/>
    <path d="M15 21.5a3.2 3.2 0 0 0 3 3" fill="none" stroke="#23272f" stroke-width="1.8" stroke-linecap="round"/></svg>`,
  eurusd: `<svg viewBox="0 0 36 36"><defs>
      <clipPath id="ieu"><circle cx="12.5" cy="23.5" r="12.5"/></clipPath><clipPath id="ius"><circle cx="23.5" cy="12.5" r="12.5"/></clipPath></defs>
    <g clip-path="url(#ius)"><rect x="11" y="0" width="25" height="25" fill="#fff"/>
      <g fill="#c8102e">${[0,1,2,3,4,5,6].map(i => `<rect x="11" y="${(i*3.85).toFixed(2)}" width="25" height="1.93"/>`).join('')}</g>
      <rect x="11" y="0" width="12" height="13.4" fill="#1f3d7a"/></g>
    <g clip-path="url(#ieu)"><rect x="0" y="11" width="25" height="25" fill="#1f4fb4"/></g>
    <g fill="#ffcc00">${Array.from({length:12},(_,i)=>{const t=i*Math.PI/6;return `<circle cx="${(12.5+7*Math.sin(t)).toFixed(2)}" cy="${(23.5-7*Math.cos(t)).toFixed(2)}" r="1.25"/>`}).join('')}</g>
    <circle cx="12.5" cy="23.5" r="12.5" fill="none" stroke="#131722" stroke-width="1.5"/></svg>`,
};
function letterIcon(a){
  const txt = (a.kotace?.ticker || a.nazev || '?').replace(/[^A-Za-z0-9]/g, '').slice(0, 1).toUpperCase();
  let col = a.barva;
  if (!col) { let h = 0; for (const c of a.id) h = (h * 31 + c.charCodeAt(0)) % 360; col = `hsl(${h},55%,45%)`; }
  return `<svg viewBox="0 0 36 36"><circle cx="18" cy="18" r="18" fill="${esc(col)}"/>
    <text x="18" y="18" dy=".36em" text-anchor="middle" font-family="Segoe UI,Arial,sans-serif" font-weight="700" font-size="17" fill="#fff">${esc(txt)}</text></svg>`;
}
let icoUid = 0;
const iconFor = a => {     // unikátní id gradientů – jinak by ikona ve sbaleném rámečku zmizela i z hlavičky
  if (!ICONS[a.id]) return letterIcon(a);
  const u = ++icoUid;
  return ICONS[a.id].replace(/\b(igd|isd|ieu|ius)\b/g, m => m + '_' + u);
};

/* ---------- VLASTNÍ POŘADÍ WATCHLISTU (uložené v prohlížeči) ---------- */
S.order = { groups: [], items: {} };
try { S.order = Object.assign({ groups: [], items: {} }, JSON.parse(localStorage.getItem('mm_order') || '{}')); } catch (e) {}
S.wlEdit = false;
const saveOrder = () => { try { localStorage.setItem('mm_order', JSON.stringify(S.order)); } catch (e) {} };
function orderedAssets(){
  const gIdx = k => { const i = S.order.groups.indexOf(k); return i < 0 ? 1000 : i; };
  const iIdx = a => { const i = (S.order.items[a.kat] || []).indexOf(a.id); return i < 0 ? 1000 : i; };
  const firstPos = {};
  S.assets.forEach((a, i) => { if (!(a.kat in firstPos)) firstPos[a.kat] = i; });
  return S.assets.map((a, i) => ({ a, i })).sort((x, y) =>
    (gIdx(x.a.kat) - gIdx(y.a.kat)) || (firstPos[x.a.kat] - firstPos[y.a.kat]) ||
    (iIdx(x.a) - iIdx(y.a)) || (x.i - y.i)).map(x => x.a);
}
function currentGroups(){ const g = []; orderedAssets().forEach(a => { if (!g.includes(a.kat)) g.push(a.kat); }); return g; }
function groupItems(kat){ return orderedAssets().filter(a => a.kat === kat).map(a => a.id); }
function moveGroup(kat, dir){
  const g = currentGroups(), i = g.indexOf(kat), j = i + dir;
  if (i < 0 || j < 0 || j >= g.length) return;
  [g[i], g[j]] = [g[j], g[i]]; S.order.groups = g; saveOrder(); renderWatchlist();
}
function moveItem(id, dir){
  const a = asset(id); if (!a) return;
  const it = groupItems(a.kat), i = it.indexOf(id), j = i + dir;
  if (j < 0 || j >= it.length) return;
  [it[i], it[j]] = [it[j], it[i]]; S.order.items[a.kat] = it; saveOrder(); renderWatchlist();
}
function dropBefore(list, moving, target){
  const l = list.filter(x => x !== moving), i = l.indexOf(target);
  l.splice(i < 0 ? l.length : i, 0, moving); return l;
}
function wireOrdering(wl){
  wl.querySelectorAll('[data-mvg]').forEach(b => b.onclick = e => { e.stopPropagation(); moveGroup(b.closest('.wl-box').dataset.box, +b.dataset.mvg); });
  wl.querySelectorAll('[data-mvi]').forEach(b => b.onclick = e => { e.stopPropagation(); moveItem(b.closest('.wl-item').dataset.id, +b.dataset.mvi); });
  if (!S.wlEdit) return;
  let drag = null;                                // přetahování myší (PC)
  wl.querySelectorAll('.wl-box-h').forEach(h => {
    h.draggable = true;
    h.ondragstart = e => { drag = { typ: 'g', id: h.parentElement.dataset.box }; e.dataTransfer.effectAllowed = 'move'; };
  });
  wl.querySelectorAll('.wl-item').forEach(it => {
    it.draggable = true;
    it.ondragstart = e => { e.stopPropagation(); drag = { typ: 'i', id: it.dataset.id }; e.dataTransfer.effectAllowed = 'move'; };
    it.ondragover = e => { if (drag && drag.typ === 'i' && asset(drag.id)?.kat === asset(it.dataset.id)?.kat) { e.preventDefault(); it.classList.add('dragover'); } };
    it.ondragleave = () => it.classList.remove('dragover');
    it.ondrop = e => {
      e.preventDefault(); e.stopPropagation(); it.classList.remove('dragover');
      if (!drag || drag.typ !== 'i' || drag.id === it.dataset.id) return;
      const kat = asset(it.dataset.id).kat;
      S.order.items[kat] = dropBefore(groupItems(kat), drag.id, it.dataset.id); saveOrder(); drag = null; renderWatchlist();
    };
  });
  wl.querySelectorAll('.wl-box').forEach(bx => {
    bx.ondragover = e => { if (drag && drag.typ === 'g') { e.preventDefault(); bx.classList.add('dragover'); } };
    bx.ondragleave = () => bx.classList.remove('dragover');
    bx.ondrop = e => {
      bx.classList.remove('dragover');
      if (!drag || drag.typ !== 'g' || drag.id === bx.dataset.box) return;
      e.preventDefault();
      S.order.groups = dropBefore(currentGroups(), drag.id, bx.dataset.box); saveOrder(); drag = null; renderWatchlist();
    };
  });
}
function syncWlEdit(){
  $('wleditbtn').textContent = S.wlEdit ? '✓ Hotovo' : '⇅ Upravit';
  $('wleditbtn').classList.toggle('on', S.wlEdit);
  $('wlreset').classList.toggle('hide', !S.wlEdit);
  $('wl').classList.toggle('editing', S.wlEdit);
}
$('wleditbtn').onclick = () => { S.wlEdit = !S.wlEdit; syncWlEdit(); renderWatchlist(); };
$('wlreset').onclick = () => { S.order = { groups: [], items: {} }; saveOrder(); renderWatchlist(); };

function itemHtml(a){
  return `<div class="wl-item" data-id="${a.id}">
      <div class="wl-ico">${iconFor(a)}</div>
      <div><div class="wl-name">${esc(a.nazev)}</div><div class="wl-tick" data-f="tick"></div></div>
      <div class="wl-price num" data-f="price">—</div>
      <div></div><div class="pill num" data-f="pill">—</div>
      <div class="wl-spark" data-f="spark"></div>
      <span class="ord ord-i"><button data-mvi="-1" title="Posunout výš">▲</button><button data-mvi="1" title="Posunout níž">▼</button></span>
    </div>`;
}

function renderWatchlist(){
  const wl = $('wl');
  const key = orderedAssets().map(a => a.kat + ':' + a.id).join(',') + (S.wlEdit ? '|edit' : '');
  if (wl.dataset.key !== key) {          // přestavět jen při změně seznamu / pořadí
    wl.dataset.key = key;
    const groups = [];
    for (const a of orderedAssets()) {
      let g = groups.find(x => x.kat === a.kat);
      if (!g) groups.push(g = { kat: a.kat, items: [] });
      g.items.push(a);
    }
    wl.innerHTML = groups.map(g => `
      <div class="wl-box${closedGroups.has(g.kat) ? ' closed' : ''}" data-box="${g.kat}">
        <div class="wl-box-h"><span class="chev">▼</span><span>${katNazev(g.kat)}</span>
          <span class="cnt">${g.items.length}</span><span class="avg" data-g="${g.kat}"></span>
          <span class="ord ord-g"><button data-mvg="-1" title="Skupinu výš">▲</button><button data-mvg="1" title="Skupinu níž">▼</button></span></div>
        <div class="wl-box-b">${g.items.map(itemHtml).join('')}</div>
      </div>`).join('');
    wl.querySelectorAll('.wl-item').forEach(el => el.onclick = () => select(el.dataset.id));
    wireOrdering(wl);
    wl.querySelectorAll('.wl-box-h').forEach(h => h.onclick = () => {
      if (S.wlEdit) return;                // při úpravě pořadí se skupiny nesbalují
      const box = h.parentElement, k = box.dataset.box;
      box.classList.toggle('closed');
      if (box.classList.contains('closed')) closedGroups.add(k); else closedGroups.delete(k);
      try { localStorage.setItem('mm_closed', JSON.stringify([...closedGroups])); } catch (e) {}
    });
    for (const id in S.lastPrice) delete S.lastPrice[id];
  }
  // průměrná denní změna skupiny v hlavičce rámečku
  wl.querySelectorAll('[data-g]').forEach(el => {
    const ch = S.assets.filter(a => a.kat === el.dataset.g && a.kotace).map(a => a.kotace.zmena_pct);
    if (!ch.length) { el.textContent = ''; return; }
    const avg = ch.reduce((x, v) => x + v, 0) / ch.length;
    el.className = 'avg ' + cls(avg);
    el.textContent = `ø ${avg >= 0 ? '+' : ''}${avg.toFixed(2)} %`;
  });
  for (const a of S.assets) {
    const el = wl.querySelector(`[data-id="${a.id}"]`), k = a.kotace;
    if (!el) continue;
    el.classList.toggle('active', a.id === S.sel);
    if (!k) continue;
    el.querySelector('[data-f=tick]').textContent = k.ticker;
    const pe = el.querySelector('[data-f=price]');
    const prev = S.lastPrice[a.id];
    pe.textContent = fmt(k.cena, a.desetinna);
    if (prev != null && prev !== k.cena) {
      pe.classList.add(k.cena > prev ? 'flash-up' : 'flash-down');
      setTimeout(() => pe.classList.remove('flash-up', 'flash-down'), 900);
    }
    S.lastPrice[a.id] = k.cena;
    const pill = el.querySelector('[data-f=pill]');
    pill.className = 'pill num ' + cls(k.zmena_pct);
    pill.textContent = `${k.zmena_pct >= 0 ? '+' : ''}${k.zmena_pct.toFixed(2)} %`;
    el.querySelector('[data-f=spark]').innerHTML = spark(k.spark, k.zmena_pct >= 0);
    let dot = el.querySelector('.wl-alert');
    if (k.upozorneni && k.upozorneni.length) { if (!dot) { dot = document.createElement('span'); dot.className = 'wl-alert'; el.appendChild(dot); } }
    else if (dot) dot.remove();
  }
}

/* ---------- hlavička ---------- */
function renderHeader(){
  const a = asset(S.sel); if (!a) return;
  const k = a.kotace, d = a.desetinna;
  if (!k) { $('hdr').innerHTML = `<div class="hdr-top"><span class="hdr-ico">${iconFor(a)}</span><span class="hdr-name">${esc(a.nazev)}</span><span class="hdr-sub">Data nedostupná</span></div>`; return; }
  const c = cls(k.zmena);
  $('hdr').innerHTML = `
    <div class="hdr-top"><span class="hdr-ico">${iconFor(a)}</span><span class="hdr-name">${esc(a.nazev)}</span>
      <span class="hdr-sub">${esc(k.ticker)} · ${esc(a.popis)}${a.mena ? ' · ' + a.mena : ''}</span>${mktChip(a)}</div>
    <div class="hdr-price"><span class="big num" id="bigprice">${fmt(k.cena, d)}</span>
      <span class="chg num ${c}">${arrow(k.zmena)} ${k.zmena >= 0 ? '+' : ''}${fmt(k.zmena, d)} (${k.zmena_pct >= 0 ? '+' : ''}${k.zmena_pct.toFixed(2)} %)</span>
      <span class="hdr-sub">dnes</span></div>
    <div class="stats">
      <div class="stat"><div class="l">Otevření</div><div class="v num">${fmt(k.open, d)}</div></div>
      <div class="stat"><div class="l">Max</div><div class="v num">${fmt(k.high, d)}</div></div>
      <div class="stat"><div class="l">Min</div><div class="v num">${fmt(k.low, d)}</div></div>
      <div class="stat"><div class="l">Předch. zavření</div><div class="v num">${fmt(k.predchozi, d)}</div></div>
      <div class="stat"><div class="l">Objem</div><div class="v num">${fmtVol(k.objem)}</div></div>
      <div class="stat"><div class="l">Změna 15 min</div><div class="v num ${cls(k.skok_pct)}">${k.skok_pct == null ? '—' : (k.skok_pct >= 0 ? '+' : '') + k.skok_pct.toFixed(2) + ' %'}</div></div>
    </div>
    ${k.upozorneni && k.upozorneni.length ? `<div class="alerts">${k.upozorneni.map(u => `<span class="alert-chip">⚠ ${esc(u.text)}</span>`).join('')}</div>` : ''}`;
}

/* ---------- zprávy ---------- */
/* ---------- EKONOMICKÝ KALENDÁŘ (ForexFactory) ---------- */
S.kal = { udalosti: [] };
const calNotified = new Set();
async function loadKalendar(){
  try { S.kal = await (await fetch('/api/kalendar')).json(); } catch (e) { return; }
  if (S.newsTab === 'cal') renderNews();
}
function renderCalendar(){
  const ev = S.kal.udalosti || [];
  if (!ev.length) {
    $('news').innerHTML = `<div class="empty">${S.kal.chyba ? 'Kalendář se nepodařilo načíst: ' + esc(S.kal.chyba) : 'Načítám kalendář…'}</div>`;
    return;
  }
  const now = Date.now() / 1000;
  const nextId = (ev.find(e => e.ts >= now) || {}).id;
  let lastDay = '', h = '';
  for (const e of ev) {
    const d = new Date(e.ts * 1000);
    const day = d.toLocaleDateString('cs-CZ', { weekday: 'long', day: 'numeric', month: 'numeric' });
    if (day !== lastDay) { h += `<div class="cal-day">${day}</div>`; lastDay = day; }
    const mins = Math.round((e.ts - now) / 60);
    const soon = mins >= 0 && mins < 180 ? `<span class="cal-soon"> · za ${mins < 60 ? mins + ' min' : Math.floor(mins / 60) + ' h ' + (mins % 60) + ' min'}</span>` : '';
    const vals = [e.skutecnost && `Skutečnost <b>${esc(e.skutecnost)}</b>`, e.prognoza && `Prognóza <b>${esc(e.prognoza)}</b>`,
                  e.predchozi && `Předchozí <b>${esc(e.predchozi)}</b>`].filter(Boolean).join(' · ');
    h += `<div class="cal-row${e.ts < now ? ' past' : ''}${e.id === nextId ? ' next' : ''}">
      <div class="cal-time">${d.toLocaleTimeString('cs-CZ', { hour: '2-digit', minute: '2-digit' })}</div>
      <div class="cal-cur">${esc(e.mena)}</div>
      <div><div class="cal-t"><span class="imp ${esc(e.dopad)}" title="${esc(e.dopad)}"></span>${esc(e.nazev)}${soon}</div>
        ${vals ? `<div class="cal-v">${vals}</div>` : ''}</div></div>`;
  }
  $('news').innerHTML = h + `<div class="empty" style="font-size:11px">Zdroj: ForexFactory · ${KAL_INFO}</div>`;
  const nx = $('news').querySelector('.cal-row.next');
  if (nx && !S._calScrolled) { nx.scrollIntoView({ block: 'center' }); S._calScrolled = true; }
}
const KAL_INFO = 'červená = vysoký dopad, oranžová = střední';
function checkCalendarAlerts(){
  const now = Date.now() / 1000;
  for (const e of (S.kal.udalosti || [])) {
    if (e.dopad !== 'High' || calNotified.has(e.id)) continue;
    const mins = (e.ts - now) / 60;
    if (mins > 0 && mins <= 15) {
      calNotified.add(e.id);
      toast(`⏰ Za ${Math.ceil(mins)} min: ${e.mena}`, e.nazev + (e.prognoza ? ` (prognóza ${e.prognoza})` : ''), true,
            () => { S.newsTab = 'cal'; syncNewsTabs(); renderNews(); });
    }
  }
}
// V13: kalendář je vypnutý (ForexFactory odmítal požadavky)

function renderNews(){
  if (S.newsTab === 'cal') { renderCalendar(); return; }
  let items;
  if (S.newsTab === 'sel') {
    const a = asset(S.sel); items = a ? a.zpravy.map(z => ({...z, _a: a})) : [];
  } else {
    items = S.assets.flatMap(a => a.zpravy.map(z => ({...z, _a: a})))
      .sort((x, y) => (y.ts || 0) - (x.ts || 0)).slice(0, 60);
  }
  if (!items.length) { $('news').innerHTML = `<div class="empty">Zatím žádné zprávy…</div>`; return; }
  $('news').innerHTML = items.map(z => {
    const fresh = !seen.has(z.id);
    const inner = `<div class="n-meta">${fresh ? '<span class="badge">NOVÉ</span>' : ''}
        ${S.newsTab === 'all' ? `<span class="tag">${esc(z._a.nazev)}</span>` : ''}
        <span>${esc(z.zdroj)}</span>${z.ts ? `<span>· ${ago(z.ts)}</span>` : ''}</div>
      <div class="n-title">${esc(z.titulek)}</div>`;
    return z.odkaz
      ? `<a class="n-item${fresh ? ' fresh' : ''}" href="${esc(z.odkaz)}" target="_blank" rel="noopener">${inner}</a>`
      : `<div class="n-item${fresh ? ' fresh' : ''}">${inner}</div>`;
  }).join('');
  // označit jako přečtené po chvíli zobrazení (zvýraznění zůstane do dalšího překreslení)
  const ids = items.map(z => z.id);
  setTimeout(() => { ids.forEach(i => seen.add(i)); saveSeen(); }, 4000);
}
function syncNewsTabs(){ document.querySelectorAll('[data-n]').forEach(b => b.classList.toggle('on', b.dataset.n === S.newsTab)); }
document.querySelectorAll('[data-n]').forEach(b => b.onclick = () => {
  S.newsTab = b.dataset.n; S._calScrolled = false;
  syncNewsTabs();
  renderNews();
});

/* ---------- notifikace ---------- */
function toast(title, body, warn, onClick){
  const t = document.createElement('div');
  t.className = 'toast' + (warn ? ' warn' : '');
  t.innerHTML = `<div class="t-h">${esc(title)}</div><div>${esc(body)}</div>`;
  t.onclick = () => { if (onClick) onClick(); t.remove(); };
  $('toasts').appendChild(t);
  setTimeout(() => t.remove(), 12000);
  while ($('toasts').children.length > 4) $('toasts').firstChild.remove();
}
function checkEvents(){
  const first = S.knownNews === null;   // při prvním načtení nic nevyskakuje
  for (const a of S.assets) {
    for (const u of (a.kotace?.upozorneni || [])) {
      const key = `${a.id}|${u.typ}|${Math.round(u.hodnota * 2)}`;
      if (!S.shownAlerts.has(key)) {
        S.shownAlerts.add(key);
        if (!first) toast(`⚠ ${a.nazev}`, u.text, true, () => select(a.id));
      }
    }
  }
  const all = S.assets.flatMap(a => a.zpravy.map(z => [z.id, a, z]));
  if (first) { if (all.length) S.knownNews = new Set(all.map(x => x[0])); return; }
  for (const [id, a, z] of all) {
    if (!S.knownNews.has(id)) { S.knownNews.add(id); toast(`📰 ${a.nazev}`, z.titulek, false, () => select(a.id)); }
  }
}

/* ---------- graf ---------- */
let chart, candle, area, vol;
function resetView(){
  if (!chart) return;
  chart.priceScale('right').applyOptions({ autoScale: true });   // zrušit ruční zoom ceny (trackpad)
  chart.timeScale().fitContent();
}
function initChart(){
  if (!window.LightweightCharts) { $('overlay').textContent = 'Knihovnu grafů se nepodařilo načíst (chybí internet?).'; return false; }
  chart = LightweightCharts.createChart($('chart'), {
    autoSize: true,
    layout: { background: { type: 'solid', color: '#131722' }, textColor: '#9598a1', fontSize: 12 },
    grid: { vertLines: { color: '#1b2030' }, horzLines: { color: '#1b2030' } },
    rightPriceScale: { borderColor: '#232838' },
    timeScale: { borderColor: '#232838', timeVisible: true, secondsVisible: false },
    crosshair: { mode: 0 },
  });
  candle = chart.addCandlestickSeries({ upColor:'#26a69a', downColor:'#ef5350', borderVisible:false, wickUpColor:'#26a69a', wickDownColor:'#ef5350' });
  area = chart.addAreaSeries({ lineColor:'#2962ff', topColor:'rgba(41,98,255,.35)', bottomColor:'rgba(41,98,255,0)', lineWidth:2, visible:false });
  vol = chart.addHistogramSeries({ priceFormat: { type: 'volume' }, priceScaleId: '' });
  vol.priceScale().applyOptions({ scaleMargins: { top: 0.82, bottom: 0 } });
  chart.timeScale().subscribeVisibleLogicalRangeChange(() => scheduleSessions());
  chart.subscribeCrosshairMove(() => scheduleSessions());
  try { new ResizeObserver(() => scheduleSessions()).observe($('chart')); } catch (e) {}
  ['wheel', 'mouseup', 'touchend', 'dblclick'].forEach(ev => $('chart').addEventListener(ev, () => scheduleSessions(), { passive: true }));
  chart.subscribeCrosshairMove(p => {
    const a = asset(S.sel); if (!a) return;
    const d = p.seriesData && (p.seriesData.get(candle) || p.seriesData.get(area));
    if (!d) { $('legend').innerHTML = ''; return; }
    const dd = a.desetinna;
    $('legend').innerHTML = d.open != null
      ? `<b>O</b>${fmt(d.open,dd)} &nbsp;<b>H</b>${fmt(d.high,dd)} &nbsp;<b>L</b>${fmt(d.low,dd)} &nbsp;<b>C</b><span class="${d.close>=d.open?'up':'down'}">${fmt(d.close,dd)}</span>`
      : `<b>Cena</b>${fmt(d.value,dd)}`;
  });
  return true;
}
const tzShift = () => -new Date().getTimezoneOffset() * 60;   // zobrazit místní čas
let chartReq = 0;
async function loadChart(fit = true){
  if (!chart && !initChart()) return;
  const a = asset(S.sel); if (!a) return;
  const my = ++chartReq;
  if (fit) { lastBar = null; $('overlay').classList.remove('hide'); $('overlay').textContent = 'Načítám graf…'; }
  try {
    const r = await fetch(`/api/history?id=${a.id}&range=${S.range}&iv=${effIv()}`);
    const data = await r.json();
    if (my !== chartReq) return;
    if (!data.length) { $('overlay').classList.remove('hide'); $('overlay').textContent = 'Pro tento rozsah nejsou data.'; return; }
    const sh = ivSec() ? tzShift() : 0;
    const pf = { type: 'price', precision: a.desetinna, minMove: Math.pow(10, -a.desetinna) };
    candle.applyOptions({ priceFormat: pf }); area.applyOptions({ priceFormat: pf });
    candle.setData(data.map(x => ({ time: x.time + sh, open: x.open, high: x.high, low: x.low, close: x.close })));
    area.setData(data.map(x => ({ time: x.time + sh, value: x.close })));
    const hasVol = data.some(x => x.volume > 0);
    vol.setData(hasVol ? data.map(x => ({ time: x.time + sh, value: x.volume,
      color: x.close >= x.open ? 'rgba(38,166,154,.35)' : 'rgba(239,83,80,.35)' })) : []);
    candle.applyOptions({ visible: S.type === 'candle' });
    area.applyOptions({ visible: S.type === 'area' });
    lastBar = { ...data[data.length - 1] };   // surové časy (UTC), posun až při vykreslení
    S.bars = data.map(x => ({ ...x }));
    scheduleSessions();
    if (S.smcOn) loadSMC();
    if (fit) resetView();
    $('overlay').classList.add('hide');
  } catch (e) {
    $('overlay').classList.remove('hide'); $('overlay').textContent = 'Chyba při načítání grafu.';
  }
}
function syncToolbar(){
  document.querySelectorAll('[data-r]').forEach(b => b.classList.toggle('on', b.dataset.r === S.range));
  document.querySelectorAll('[data-t]').forEach(b => b.classList.toggle('on', b.dataset.t === S.type));
}
document.querySelectorAll('[data-r]').forEach(b => b.onclick = () => {
  S.range = b.dataset.r; syncToolbar(); syncIv(); loadChart();
  const n = ivNote(); if (n) toast('⏱ Interval svíček', n, false);
});
document.querySelectorAll('[data-t]').forEach(b => b.onclick = () => {
  S.type = b.dataset.t; syncToolbar();
  if (candle) { candle.applyOptions({ visible: S.type === 'candle' }); area.applyOptions({ visible: S.type === 'area' }); scheduleSessions(); }
});

$('resetbtn').onclick = resetView;

/* ---------- OBCHODNÍ SEANCE (Tokyo / Londýn / New York) ---------- */
// Časy jsou v místním čase dané burzy (letní/zimní čas se počítá automaticky). Můžeš upravit.
const SESSIONS = [
  { id: 'tokyo',  nazev: 'Tokyo',    tz: 'Asia/Tokyo',       od: '09:00', do: '15:00', rgb: '41,98,255' },
  { id: 'london', nazev: 'Londýn',   tz: 'Europe/London',    od: '08:00', do: '16:30', rgb: '255,152,0' },
  { id: 'ny',     nazev: 'New York', tz: 'America/New_York', od: '09:30', do: '16:00', rgb: '38,166,154' },
];
S.sess = { on: false, tokyo: true, london: true, ny: true };
try { Object.assign(S.sess, JSON.parse(localStorage.getItem('mm_sess') || '{}')); } catch (e) {}
const saveSess = () => { try { localStorage.setItem('mm_sess', JSON.stringify(S.sess)); } catch (e) {} };

const _fmtCache = {};
function tzOffsetMs(ms, tz){
  const f = _fmtCache[tz] || (_fmtCache[tz] = new Intl.DateTimeFormat('en-US', { timeZone: tz, hourCycle: 'h23',
    year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', second: '2-digit' }));
  const p = {}; f.formatToParts(new Date(ms)).forEach(x => p[x.type] = x.value);
  return Date.UTC(+p.year, +p.month - 1, +p.day, +p.hour % 24, +p.minute, +p.second) - ms;
}
function zonedToUtc(y, m, d, hhmm, tz){            // místní čas burzy -> unix sekundy
  const [hh, mm] = hhmm.split(':').map(Number);
  const guess = Date.UTC(y, m, d, hh, mm);
  let t = guess - tzOffsetMs(guess, tz);
  t = guess - tzOffsetMs(t, tz);
  return Math.floor(t / 1000);
}
function sessionBlocks(bars){
  if (!bars || !bars.length) return [];
  const first = bars[0].time, last = bars[bars.length - 1].time, out = [];
  for (const se of SESSIONS) {
    if (!S.sess[se.id]) continue;
    for (let day = first - 2 * 86400; day <= last + 86400; day += 86400) {
      const dt = new Date(day * 1000), y = dt.getUTCFullYear(), m = dt.getUTCMonth(), d = dt.getUTCDate();
      const wd = new Date(Date.UTC(y, m, d)).getUTCDay();
      if (wd === 0 || wd === 6) continue;          // víkend
      const a = zonedToUtc(y, m, d, se.od, se.tz), b = zonedToUtc(y, m, d, se.do, se.tz);
      if (b < first || a > last) continue;
      const inb = bars.filter(x => x.time >= a && x.time < b);
      if (!inb.length) continue;
      const hi = Math.max(...inb.map(x => x.high)), lo = Math.min(...inb.map(x => x.low));
      const avg = inb.reduce((s2, x) => s2 + x.close, 0) / inb.length;
      out.push({ se, t1: inb[0].time, t2: inb[inb.length - 1].time, hi, lo, avg,
                 open: inb[0].open, close: inb[inb.length - 1].close });
    }
  }
  return out;
}
let _sessRaf = 0;
function scheduleSessions(){ if (!_sessRaf) _sessRaf = requestAnimationFrame(() => { _sessRaf = 0; drawSessions(); drawSMC(); drawCalls(); }); }

/* ---------- SMC NA GRAFU (swingy, BOS/CHoCH, likvidita, sweepy) ---------- */
S.smcOn = false;
try { S.smcOn = localStorage.getItem('mm_smc') === '1'; } catch (e) {}
S.smc = null; S.smcKey = '';
async function loadSMC(){
  const a = asset(S.sel); if (!a) return;
  const key = a.id + '|' + S.range + '|' + effIv();
  try {
    const d = await (await fetch(`/api/smc?id=${a.id}&range=${S.range}&iv=${effIv()}`)).json();
    if (key !== S.sel + '|' + S.range + '|' + effIv()) return;
    S.smc = d; S.smcKey = key;
  } catch (e) { S.smc = null; }
  scheduleSessions();
}
function drawSMC(){
  const svg = $('smcov');
  const sm = S.smc;
  if (!S.smcOn || !chart || !sm || sm.chyba || S.smcKey !== S.sel + '|' + S.range + '|' + effIv()) { svg.innerHTML = ''; return; }
  const a = asset(S.sel); if (!a) return;
  const ser = S.type === 'candle' ? candle : area, ts = chart.timeScale();
  const sh = ivSec() ? tzShift() : 0;
  const W = ts.width(), H = $('chart').clientHeight - ts.height();
  const X = t => ts.timeToCoordinate(t + sh), Y = p => ser.priceToCoordinate(p);
  const UP = '#26a69a', DN = '#ef5350', LQ = '#f5a623';
  let h = `<defs><clipPath id="smcclip"><rect x="0" y="0" width="${W}" height="${H}"/></clipPath></defs><g clip-path="url(#smcclip)" font-family="Segoe UI,Arial,sans-serif">`;
  for (const l of sm.likvidita || []) {                       // likvidita – tečkovaná čára doprava
    const y = Y(l.cena); if (y == null) continue;
    const x1 = X(l.t1) ?? 0;
    h += `<line x1="${x1}" x2="${W}" y1="${y}" y2="${y}" stroke="${LQ}" stroke-width="1" stroke-dasharray="2 3" opacity=".9"/>`
       + `<text x="${W - 6}" y="${y - 4}" text-anchor="end" font-size="10" font-weight="700" fill="${LQ}">${l.typ} $$$</text>`;
  }
  for (const z of sm.zlomy || []) {                           // BOS / CHoCH
    const x1 = X(z.t1), x2 = X(z.t2), y = Y(z.cena);
    if (x1 == null || x2 == null || y == null) continue;
    const c = z.smer === 'up' ? UP : DN;
    h += `<line x1="${x1}" x2="${x2}" y1="${y}" y2="${y}" stroke="${c}" stroke-width="1.3" stroke-dasharray="${z.typ === 'CHoCH' ? '6 3' : '3 3'}"/>`
       + `<text x="${(x1 + x2) / 2}" y="${z.smer === 'up' ? y - 4 : y + 12}" text-anchor="middle" font-size="10" font-weight="700" fill="${c}">${z.typ}</text>`;
  }
  for (const s of sm.swingy || []) {                          // HH / HL / LH / LL
    const x = X(s.t), y = Y(s.cena); if (x == null || y == null) continue;
    const c = (s.stitek === 'HH' || s.stitek === 'HL') ? UP : (s.stitek === 'LH' || s.stitek === 'LL') ? DN : '#9598a1';
    const top = s.typ === 'H';
    h += `<circle cx="${x}" cy="${y}" r="2.5" fill="${c}"/>`
       + `<text x="${x}" y="${top ? y - 7 : y + 15}" text-anchor="middle" font-size="10" font-weight="700" fill="${c}">${s.stitek}</text>`;
  }
  for (const w of sm.sweepy || []) {                          // sweep likvidity
    const x = X(w.t), y = Y(w.cena); if (x == null || y == null) continue;
    h += `<text x="${x}" y="${y + 4}" text-anchor="middle" font-size="13" font-weight="700" fill="${LQ}">✕</text>`
       + `<text x="${x + 8}" y="${w.strana === 'BSL' ? y - 6 : y + 16}" font-size="9.5" fill="${LQ}">sweep</text>`;
  }
  const col = sm.skore >= 20 ? UP : sm.skore <= -20 ? DN : '#9598a1';
  h += `<text x="${W - 8}" y="18" text-anchor="end" font-size="11.5" font-weight="700" fill="${col}">SMC: ${esc(sm.sila)} (${sm.skore > 0 ? '+' : ''}${sm.skore})</text>`;
  svg.innerHTML = h + '</g>';
}
function syncSmcBtn(){ $('smcbtn').classList.toggle('smc-on', !!S.smcOn); }
$('smcbtn').onclick = () => {
  S.smcOn = !S.smcOn;
  try { localStorage.setItem('mm_smc', S.smcOn ? '1' : '0'); } catch (e) {}
  syncSmcBtn();
  if (S.smcOn) loadSMC(); else scheduleSessions();
};
syncSmcBtn();
function drawSessions(){
  const svg = $('sessov');
  const iv = ivSec();
  if (!S.sess.on || !chart || !S.bars || !iv) { svg.innerHTML = ''; return; }
  const a = asset(S.sel); if (!a) return;
  const ser = S.type === 'candle' ? candle : area;
  const ts = chart.timeScale(), sh = tzShift();
  const W = ts.width(), H = $('chart').clientHeight - ts.height();
  const half = Math.max(1, (ts.options().barSpacing || 6) / 2);
  const d = a.desetinna;
  let h = `<defs><clipPath id="sessclip"><rect x="0" y="0" width="${W}" height="${H}"/></clipPath></defs><g clip-path="url(#sessclip)">`;
  for (const b of sessionBlocks(S.bars)) {
    const x1 = ts.timeToCoordinate(b.t1 + sh), x2 = ts.timeToCoordinate(b.t2 + sh);
    const yh = ser.priceToCoordinate(b.hi), yl = ser.priceToCoordinate(b.lo);
    if (x1 == null || x2 == null || yh == null || yl == null) continue;
    const L = x1 - half, R = x2 + half, c = b.se.rgb;
    if (R < 0 || L > W) continue;
    const yo = ser.priceToCoordinate(b.open), yc = ser.priceToCoordinate(b.close), ya = ser.priceToCoordinate(b.avg);
    h += `<rect x="${L}" y="${yh}" width="${Math.max(1, R - L)}" height="${Math.max(1, yl - yh)}" fill="rgba(${c},.13)" stroke="rgba(${c},.45)" stroke-width="1"/>`;
    if (yo != null) h += `<line x1="${L}" x2="${R}" y1="${yo}" y2="${yo}" stroke="rgba(${c},.9)" stroke-width="1" stroke-dasharray="5 4"/>`;
    if (yc != null) h += `<line x1="${L}" x2="${R}" y1="${yc}" y2="${yc}" stroke="rgba(${c},.9)" stroke-width="1" stroke-dasharray="5 4"/>`;
    if (ya != null) h += `<line x1="${L}" x2="${R}" y1="${ya}" y2="${ya}" stroke="rgba(${c},1)" stroke-width="1.2" stroke-dasharray="1.5 3"/>`;
    if (R - L > 40) {
      const tx = Math.max(L + 4, 4);
      const above = b.se.id === 'ny';          // NY popisek nad rámečkem, ať se nepřekrývá s Londýnem
      const ty = above ? yh - 34 : yl + 14;
      h += `<text x="${tx}" y="${ty}" font-size="11" fill="rgb(${c})" font-family="Segoe UI,Arial,sans-serif">`
         + `<tspan x="${tx}">Rozsah: ${fmt(b.hi - b.lo, d)}</tspan><tspan x="${tx}" dy="13">Průměr: ${fmt(b.avg, d)}</tspan>`
         + `<tspan x="${tx}" dy="13" font-weight="700">${esc(b.se.nazev)}</tspan></text>`;
    }
  }
  svg.innerHTML = h + '</g>';
}
function renderSessPop(){
  const lab = (id, txt, sw, chk) => `<label><input type="checkbox" data-s="${id}" ${chk ? 'checked' : ''}>${sw ? `<span class="sw" style="background:rgb(${sw})"></span>` : ''}${txt}</label>`;
  $('sesspop').innerHTML = lab('on', '<b>Zobrazit seance</b>', null, S.sess.on) + '<hr>'
    + SESSIONS.map(se => lab(se.id, `${se.nazev} <span class="muted" style="font-size:11px">${se.od}–${se.do}</span>`, se.rgb, S.sess[se.id])).join('')
    + '<div class="hint">Jen na 1D, 5D a 1M (svíčky v rámci dne).</div>';
  $('sesspop').querySelectorAll('input').forEach(i => i.onchange = () => {
    S.sess[i.dataset.s] = i.checked; saveSess(); syncSessBtn(); scheduleSessions();
  });
}
function syncSessBtn(){ $('sessbtn').classList.toggle('sess-on', !!S.sess.on); }
/* menu se otevírá nad grafem (mimo lištu, aby ho lišta neořízla) */
function openPop(pop, btn){
  const others = ['ivpop', 'sesspop'].map($).filter(x => x !== pop);
  others.forEach(x => x.classList.add('hide'));
  if (!pop.classList.contains('hide')) { pop.classList.add('hide'); return; }
  pop.classList.remove('hide');
  if (window.matchMedia('(max-width:820px)').matches) { pop.style.top = pop.style.left = ''; return; }   // telefon: zespodu
  const r = btn.getBoundingClientRect(), w = pop.offsetWidth;
  pop.style.top = (r.bottom + 6) + 'px';
  pop.style.left = Math.max(8, Math.min(r.left, window.innerWidth - w - 8)) + 'px';
}
document.body.appendChild($('sesspop'));
document.body.appendChild($('ivpop'));
$('sessbtn').onclick = e => { e.stopPropagation(); renderSessPop(); openPop($('sesspop'), $('sessbtn')); };
document.addEventListener('click', e => { if (!e.target.closest('.sesswrap') && !e.target.closest('#sesspop')) $('sesspop').classList.add('hide'); });
window.addEventListener('resize', () => { $('sesspop').classList.add('hide'); $('ivpop').classList.add('hide'); });
$('toolbar').addEventListener('scroll', () => { $('sesspop').classList.add('hide'); $('ivpop').classList.add('hide'); });
syncSessBtn();
$('chart').addEventListener('dblclick', resetView);

/* ---------- výběr aktiva ---------- */
function select(id){
  if (S.sel === id) return;
  S.sel = id;
  renderWatchlist(); renderHeader(); renderNews(); loadChart(); loadTech(); loadAI();
}
document.addEventListener('keydown', e => {
  if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return;
  e.preventDefault();
  const vis = visibleAssets(); if (!vis.length) return;
  const i = vis.findIndex(a => a.id === S.sel);
  const n = vis[(i + (e.key === 'ArrowDown' ? 1 : -1) + vis.length) % vis.length];
  const el = n && document.querySelector(`.wl-item[data-id="${n.id}"]`);
  if (el) el.scrollIntoView({ block: 'nearest' });
  if (n) select(n.id);
});

/* ---------- polling ---------- */
let lastUpdated = null;
async function poll(){
  try {
    const r = await fetch('/api/state');
    if (r.status === 401) { location.href = '/login'; return; }
    const st = await r.json();
    S.assets = st.aktiva;
    $('live').classList.toggle('off', !st.aktualizovano);
    $('upd').textContent = st.aktualizovano
      ? `Live · ceny ${new Date(st.aktualizovano*1000).toLocaleTimeString('cs-CZ')}` +
        (st.zpravy_aktualizovano ? ` · zprávy ${new Date(st.zpravy_aktualizovano*1000).toLocaleTimeString('cs-CZ')}` : '')
      : 'Načítám první data…';
    if (!S.sel && S.assets.length) { S.sel = (visibleAssets()[0] || S.assets[0]).id; syncToolbar(); loadChart(); }
    renderWatchlist(); renderHeader();
    const stamp = `${st.aktualizovano}|${st.zpravy_aktualizovano}`;
    if (stamp !== lastUpdated) {
      const first = lastUpdated === null;
      lastUpdated = stamp;
      renderNews(); checkEvents();
      if (!first) loadChart(false);   // jednou za minutu srovnat graf s historií
    }
  } catch (e) {
    $('live').classList.add('off');
    $('upd').textContent = 'Spojení s aplikací přerušeno – běží ještě okno konzole?';
  }
}
poll();
setInterval(poll, 3000);

/* ---------- LIVE: poslední svíčka v reálném čase ---------- */
/* ---------- INTERVAL SVÍČEK ---------- */
const IVSEC = { '1m': 60, '5m': 300, '10m': 600, '15m': 900, '30m': 1800, '1h': 3600, '4h': 14400, '1d': 0, '1wk': 0, '1mo': 0 };
const RANGE_IV = { '1D': '5m', '5D': '15m', '1M': '1h', '6M': '1d', '1R': '1d', '5R': '1wk' };
const IV_NAMES = [['auto', 'Auto (podle rozsahu)'], ['1m', '1 minuta'], ['5m', '5 minut'], ['10m', '10 minut'], ['15m', '15 minut'],
  ['30m', '30 minut'], ['1h', '1 hodina'], ['4h', '4 hodiny'], ['1d', '1 den'], ['1wk', '1 týden'], ['1mo', '1 měsíc']];
const IV_SHORT = { '1m': '1m', '5m': '5m', '10m': '10m', '15m': '15m', '30m': '30m', '1h': '1h', '4h': '4h', '1d': '1D', '1wk': '1T', '1mo': '1M' };
S.iv = 'auto';
try { S.iv = localStorage.getItem('mm_iv') || 'auto'; } catch (e) {}
function effIv(){ return S.iv === 'auto' ? RANGE_IV[S.range] : S.iv; }
function ivSec(){ return IVSEC[effIv()] || 0; }
function ivNote(){
  const iv = effIv();
  if (iv === '1m' && !['1D', '5D'].includes(S.range)) return '1min svíčky má Yahoo jen za posledních 7 dní.';
  if (['5m', '10m', '15m', '30m'].includes(iv) && ['6M', '1R', '5R'].includes(S.range)) return 'Svíčky 5–30 min má Yahoo jen za posledních 60 dní.';
  if (['1h', '4h'].includes(iv) && S.range === '5R') return 'Hodinové svíčky má Yahoo jen za poslední 2 roky.';
  return '';
}
function syncIv(){
  $('ivlbl').textContent = S.iv === 'auto' ? `Auto · ${IV_SHORT[effIv()]}` : IV_SHORT[S.iv];
  $('ivbtn').classList.toggle('on', S.iv !== 'auto');
}
function renderIvPop(){
  $('ivpop').innerHTML = `<div class="ivpop-h">Interval svíček</div>` + IV_NAMES.map(([k, n]) =>
    `<button class="ivopt${S.iv === k ? ' sel' : ''}" data-iv="${k}"><span>${n}${k === 'auto' ? ` <span class="muted">· teď ${IV_SHORT[RANGE_IV[S.range]]}</span>` : ''}</span>${S.iv === k ? '<span>✓</span>' : ''}</button>`).join('');
  $('ivpop').querySelectorAll('.ivopt').forEach(b => b.onclick = () => {
    S.iv = b.dataset.iv;
    try { localStorage.setItem('mm_iv', S.iv); } catch (e) {}
    $('ivpop').classList.add('hide'); syncIv(); loadChart();
    const n = ivNote(); if (n) toast('⏱ Interval svíček', n, false);
  });
}
$('ivbtn').onclick = e => { e.stopPropagation(); renderIvPop(); openPop($('ivpop'), $('ivbtn')); };
document.addEventListener('click', e => { if (!e.target.closest('.ivwrap') && !e.target.closest('#ivpop')) $('ivpop').classList.add('hide'); });
syncIv();
let lastBar = null;

function applyTick(price, ts){
  if (!lastBar || !candle || ts < lastBar.time) return;
  const iv = ivSec();
  if (iv && ts >= lastBar.time + iv) {          // začala nová svíčka
    const t = lastBar.time + Math.floor((ts - lastBar.time) / iv) * iv;
    const o = lastBar.close;
    lastBar = { time: t, open: o, high: Math.max(o, price), low: Math.min(o, price), close: price, volume: 0 };
  } else {
    lastBar.high = Math.max(lastBar.high, price);
    lastBar.low = Math.min(lastBar.low, price);
    lastBar.close = price;
  }
  const t = lastBar.time + (iv ? tzShift() : 0);
  try {
    candle.update({ time: t, open: lastBar.open, high: lastBar.high, low: lastBar.low, close: lastBar.close });
    area.update({ time: t, value: price });
    if (S.bars && S.bars.length) {
      const lb = S.bars[S.bars.length - 1];
      if (lb.time === lastBar.time) S.bars[S.bars.length - 1] = { ...lastBar };
      else if (lastBar.time > lb.time) S.bars.push({ ...lastBar });
      scheduleSessions();
    }
  } catch (e) {}
}

function setLiveBadge(L){
  const b = $('livebadge');
  const age = Date.now() / 1000 - (L.ts || 0);
  const live = L.ts && age < 20 * 60;           // futures mají na Yahoo ~10 min zpoždění
  b.classList.toggle('on', !!live);
  const src = L.zdroj === 'stream' ? 'stream' : `obnova ${10} s`;
  b.innerHTML = live
    ? `<span class="ld"></span><span>LIVE</span><span class="sub">· ${src}</span>`
    : `<span class="ld"></span><span>Trh zavřený</span><span class="sub">· poslední obchod ${L.ts ? ago(L.ts) : '—'}</span>`;
}

let liveBusy = false;
async function liveLoop(){
  if (liveBusy || !S.sel) return;
  liveBusy = true;
  const id = S.sel;
  try {
    const L = await (await fetch(`/api/live?id=${id}`)).json();
    if (id !== S.sel || L.cena == null) return;
    applyTick(L.cena, L.ts);
    setLiveBadge(L);
    const a = asset(id), k = a && a.kotace;
    if (k && L.ts >= k.cas && L.cena !== k.cena) {
      const up = L.cena > k.cena;
      k.cena = L.cena; k.zmena = L.cena - k.predchozi;
      k.zmena_pct = k.predchozi ? k.zmena / k.predchozi * 100 : 0;
      k.high = Math.max(k.high, L.cena); k.low = Math.min(k.low, L.cena); k.cas = L.ts;
      renderHeader(); renderWatchlist();
      const bp = $('bigprice');
      if (bp) { bp.classList.add(up ? 'flash-up' : 'flash-down'); setTimeout(() => bp.classList.remove('flash-up', 'flash-down'), 700); }
    }
  } catch (e) {
  } finally { liveBusy = false; }
}
setInterval(liveLoop, 2000);

/* ---------- TECHNICKÁ ANALÝZA (ukazatel) ---------- */
S.tf = '1D';
try { S.tf = localStorage.getItem('mm_tf') || '1D'; } catch (e) {}
const TECH_CLS = { 'Silný nákup': 'sb', 'Nákup': 'b', 'Neutrální': 'n', 'Prodej': 's', 'Silný prodej': 'ss' };

function buildGauge(){
  const cx = 120, cy = 112, R = 90;
  const pt = (deg, r) => [cx + r * Math.cos(deg * Math.PI / 180), cy - r * Math.sin(deg * Math.PI / 180)];
  const cols = ['#f23645', '#a8283a', '#787b86', '#2a5bd7', '#2962ff'];
  const names = ['Silný\nprodej', 'Prodej', 'Neutrální', 'Nákup', 'Silný\nnákup'];
  let h = '';
  for (let i = 0; i < 5; i++) {
    const a1 = 180 - i * 36 - 3, a2 = 180 - (i + 1) * 36 + 3;
    const [x1, y1] = pt(a1, R), [x2, y2] = pt(a2, R);
    h += `<path d="M${x1.toFixed(1)} ${y1.toFixed(1)} A${R} ${R} 0 0 1 ${x2.toFixed(1)} ${y2.toFixed(1)}" stroke="${cols[i]}" stroke-width="9" fill="none" stroke-linecap="round"/>`;
    const [lx, ly] = pt(180 - i * 36 - 18, R + 25);
    const lines = names[i].split('\n');
    h += `<text x="${lx.toFixed(1)}" y="${(ly - (lines.length - 1) * 5).toFixed(1)}" text-anchor="middle" font-size="9" fill="#7a7f8e">`
       + lines.map((t, j) => `<tspan x="${lx.toFixed(1)}" dy="${j ? 10 : 0}">${t}</tspan>`).join('') + `</text>`;
  }
  h += `<g class="needle" id="needle"><path d="M${cx - 70} ${cy} L${cx} ${cy - 4.5} L${cx} ${cy + 4.5} Z" fill="#d1d4dc"/></g>`
     + `<circle cx="${cx}" cy="${cy}" r="7" fill="#d1d4dc"/><circle cx="${cx}" cy="${cy}" r="3" fill="#131722"/>`;
  $('gauge').innerHTML = h;
}
buildGauge();

function setNeedle(r){
  const deg = Math.max(0, Math.min(180, (r + 1) / 2 * 180));
  $('needle').style.transform = `rotate(${deg}deg)`;
}
setNeedle(0);

function sigText(v){ return v > 0 ? '<span style="color:#2962ff">Nákup</span>' : v < 0 ? '<span style="color:#f23645">Prodej</span>' : '<span class="muted">Neutrální</span>'; }

let techReq = 0;
async function loadTech(){
  const a = asset(S.sel); if (!a) return;
  const my = ++techReq;
  document.querySelectorAll('[data-tf]').forEach(b => b.classList.toggle('on', b.dataset.tf === S.tf));
  let t;
  try { t = await (await fetch(`/api/tech?id=${a.id}&tf=${S.tf}`)).json(); } catch (e) { return; }
  if (my !== techReq) return;
  if (t.chyba) {
    setNeedle(0); $('techlabel').className = 'tech-label n'; $('techlabel').textContent = '—';
    $('techsum').innerHTML = `<div class="muted" style="grid-column:1/-1;text-align:center">${esc(t.chyba)}</div>`;
    $('techdet').innerHTML = ''; return;
  }
  setNeedle(t.rating);
  $('techlabel').className = 'tech-label ' + (TECH_CLS[t.stitek] || 'n');
  $('techlabel').textContent = t.stitek;
  const box = (nm, g) => `<div class="tech-box"><div class="t">${nm}</div>
      <div class="v" style="color:${g.rating >= 0.1 ? '#2962ff' : g.rating <= -0.1 ? '#f23645' : 'var(--muted)'}">${g.stitek}</div>
      <div class="cnt"><span>Prodej <b>${g.prodej}</b></span><span>Neutr. <b>${g.neutral}</b></span><span>Nákup <b>${g.nakup}</b></span></div></div>`;
  $('techsum').innerHTML = box('Oscilátory', t.oscilatory) + box('Klouzavé průměry', t.prumery);
  const d = a.desetinna;
  const rows = (arr, dec) => arr.map(x => `<tr><td>${esc(x.nazev)}</td><td class="num">${x.hodnota == null ? '—' : fmt(x.hodnota, dec)}</td><td>${sigText(x.signal)}</td></tr>`).join('');
  $('techdet').innerHTML = `<table><tr><th>Indikátor</th><th>Hodnota</th><th>Signál</th></tr>
    <tr class="grp"><td colspan="3">Oscilátory</td></tr>${rows(t.detail_oscilatory, 2)}
    <tr class="grp"><td colspan="3">Klouzavé průměry</td></tr>${rows(t.detail_prumery, d)}</table>`;
}
document.querySelectorAll('[data-tf]').forEach(b => b.onclick = () => {
  S.tf = b.dataset.tf;
  try { localStorage.setItem('mm_tf', S.tf); } catch (e) {}
  loadTech();
});
$('techmore').onclick = () => {
  const open = $('techdet').classList.toggle('hide') === false;
  $('techmore').textContent = open ? 'Skrýt podrobnosti ▴' : 'Zobrazit podrobnosti ▾';
};
setInterval(loadTech, 60000);
setTimeout(loadTech, 1500);

/* ---------- OBCHODNÍ HODINY ---------- */
const HOURS_INFO = {
  futures:  'CME Globex: neděle 18:00 – pátek 17:00 (newyorský čas), každý den pauza 17:00–18:00.',
  us_akcie: 'Burza v USA: po–pá 9:30–16:00 (newyorský čas). Světlejší = pre-market 4:00–9:30 a after-hours 16:00–20:00.',
  forex:    'Forex: nepřetržitě od neděle 17:00 do pátku 17:00 (newyorský čas).',
  krypto:   'Kryptoměny se obchodují nepřetržitě 24/7.',
};
const ET = 'America/New_York';
function etParts(sec){
  const dt = new Date(sec * 1000 + tzOffsetMs(sec * 1000, ET));
  return { y: dt.getUTCFullYear(), m: dt.getUTCMonth(), d: dt.getUTCDate(), wd: dt.getUTCDay() };
}
const etUtc = (p, hhmm) => zonedToUtc(p.y, p.m, p.d, hhmm, ET);
function hoursIntervals(typ, from, to){                 // [{a, b, kind}] v unix sekundách
  if (typ === 'krypto') return [{ a: from, b: to, kind: 'reg' }];
  const out = [], seen = new Set();
  for (let t = from - 4 * 86400; t <= to + 2 * 86400; t += 43200) {
    const p = etParts(t), key = `${p.y}-${p.m}-${p.d}`;
    if (seen.has(key)) continue;
    seen.add(key);
    if (typ === 'us_akcie' && p.wd >= 1 && p.wd <= 5) {
      out.push({ a: etUtc(p, '04:00'), b: etUtc(p, '09:30'), kind: 'ext' });
      out.push({ a: etUtc(p, '09:30'), b: etUtc(p, '16:00'), kind: 'reg' });
      out.push({ a: etUtc(p, '16:00'), b: etUtc(p, '20:00'), kind: 'ext' });
    } else if (typ === 'futures' && p.wd <= 4) {
      const a = etUtc(p, '18:00');
      out.push({ a, b: etUtc(etParts(a + 86400), '17:00'), kind: 'reg' });
    } else if (typ === 'forex' && p.wd === 0) {
      const a = etUtc(p, '17:00');
      out.push({ a, b: etUtc(etParts(a + 5 * 86400), '17:00'), kind: 'reg' });
    }
  }
  return out.filter(x => x.b > from && x.a < to).sort((x, y) => x.a - y.a);
}
const fmtHM = sec => new Date(sec * 1000).toLocaleTimeString('cs-CZ', { hour: '2-digit', minute: '2-digit' });
const fmtDur = s => { const m = Math.max(1, Math.round(s / 60)); return m < 60 ? `${m} min` : m < 1440 ? `${Math.floor(m / 60)} h ${m % 60} min` : `${Math.floor(m / 1440)} d ${Math.floor(m % 1440 / 60)} h`; };
function marketStatus(typ){
  const now = Date.now() / 1000;
  if (typ === 'krypto') return { cls: 'open', label: 'Otevřeno', detail: 'Obchoduje se nepřetržitě 24/7' };
  const iv = hoursIntervals(typ, now - 8 * 86400, now + 9 * 86400);
  const cur = iv.find(x => x.a <= now && now < x.b);
  const nextReg = iv.find(x => x.kind === 'reg' && x.a > now);
  if (cur && cur.kind === 'reg') {
    let end = cur.b;                                    // spojit navazující úseky
    for (const x of iv) if (x.kind === 'reg' && x.a <= end && x.b > end) end = x.b;
    return { cls: 'open', label: 'Otevřeno', detail: `Běžné hodiny · zavře za ${fmtDur(end - now)} (${end - now > 86400 ? new Date(end * 1000).toLocaleDateString('cs-CZ', { weekday: 'long' }) + ' ' : ''}${fmtHM(end)})` };
  }
  if (cur && cur.kind === 'ext') {
    const pre = nextReg && nextReg.a <= cur.b + 60;
    return { cls: 'ext', label: pre ? 'Pre-market' : 'After-hours',
             detail: pre ? `Hlavní obchodování začne za ${fmtDur(nextReg.a - now)} (${fmtHM(nextReg.a)})` : `Mimo hlavní hodiny · končí ${fmtHM(cur.b)}` };
  }
  if (!nextReg) return { cls: 'closed', label: 'Zavřeno', detail: '' };
  const den = new Date(nextReg.a * 1000).toLocaleDateString('cs-CZ', { weekday: 'long' });
  return { cls: 'closed', label: 'Zavřeno', detail: `Otevře za ${fmtDur(nextReg.a - now)} (${den} ${fmtHM(nextReg.a)})` };
}
function renderHours(){
  const a = asset(S.sel); if (!a) return;
  const typ = a.hodiny || 'krypto', st = marketStatus(typ);
  const now = new Date(), nowSec = now.getTime() / 1000;
  const mon = new Date(now.getFullYear(), now.getMonth(), now.getDate() - ((now.getDay() + 6) % 7));
  const names = ['Po', 'Út', 'St', 'Čt', 'Pá', 'So', 'Ne'];
  const frac = (now.getHours() * 3600 + now.getMinutes() * 60 + now.getSeconds()) / 86400 * 100;
  let rows = '';
  for (let i = 0; i < 7; i++) {
    const d0 = new Date(mon.getFullYear(), mon.getMonth(), mon.getDate() + i).getTime() / 1000;
    const d1 = new Date(mon.getFullYear(), mon.getMonth(), mon.getDate() + i + 1).getTime() / 1000;
    const len = d1 - d0, today = nowSec >= d0 && nowSec < d1;
    const iv = hoursIntervals(typ, d0, d1);
    const segs = iv.map(x => {
      const a1 = Math.max(x.a, d0), b1 = Math.min(x.b, d1);
      return `<div class="hrs-seg ${x.kind}" style="left:${(a1 - d0) / len * 100}%;width:${(b1 - a1) / len * 100}%"></div>`;
    }).join('');
    const reg = iv.filter(x => x.kind === 'reg').map(x => `${fmtHM(Math.max(x.a, d0))}–${Math.min(x.b, d1) >= d1 ? '24:00' : fmtHM(Math.min(x.b, d1))}`);
    rows += `<div class="hrs-row${today ? ' today' : ''}">
      <div class="hrs-day">${names[i]}${today ? `<div class="hrs-now-t">${fmtHM(nowSec)}</div>` : ''}</div>
      <div class="hrs-cell">${today ? `<div class="hrs-mark" style="left:${frac}%"></div>` : ''}
        <div class="hrs-track">${segs}</div>
        <div class="hrs-txt">${reg.length ? reg.join(', ') : 'zavřeno'}</div></div></div>`;
  }
  $('hoursbody').innerHTML = `
    <div class="hrs-head"><span class="hdr-ico" style="width:28px;height:28px">${iconFor(a)}</span>
      <div><b>${esc(a.nazev)}</b><div class="muted" style="font-size:12px">${esc(a.popis)}</div></div></div>
    <div class="hrs-status ${st.cls}"><span class="mkt-dot"></span><b>${st.label}</b><span class="muted">${st.detail ? ' · ' + esc(st.detail) : ''}</span></div>
    <div class="hrs-grid"><div class="hrs-nowline" style="left:calc(48px + (100% - 48px) * ${frac / 100})"></div>${rows}
      <div class="hrs-row hrs-axis"><div></div><div class="hrs-ticks"><span>0</span><span>6</span><span>12</span><span>18</span><span>24</span></div></div></div>
    <p class="muted" style="font-size:11.5px;margin-top:12px">${HOURS_INFO[typ] || ''}<br>Časy jsou ve tvém místním čase. Státní svátky a zkrácené dny nejsou zahrnuté.</p>`;
}
let hoursTimer = null;
function openHours(){
  $('hoursmodal').classList.remove('hide'); renderHours();
  clearInterval(hoursTimer); hoursTimer = setInterval(renderHours, 30000);
}
function closeHours(){ $('hoursmodal').classList.add('hide'); clearInterval(hoursTimer); }
$('hoursclose').onclick = closeHours;
$('hoursmodal').onclick = e => { if (e.target === $('hoursmodal')) closeHours(); };
$('hdr').addEventListener('click', e => { if (e.target.closest('#mktbtn')) openHours(); });
function mktChip(a){
  const st = marketStatus(a.hodiny || 'krypto');
  return `<button class="mkt ${st.cls}" id="mktbtn" title="${esc(st.detail)} – klikni pro obchodní hodiny"><span class="mkt-dot"></span>${st.label}</button>`;
}

/* ---------- STAV ZDROJŮ ---------- */
async function openSources(){
  $('srcmodal').classList.remove('hide');
  $('srcbody').innerHTML = '<p class="muted">Načítám…</p>';
  let d; try { d = await (await fetch('/api/zdroje')).json(); } catch (e) { return; }
  const row = z => {
    const st = z.stav;
    const icon = !st ? '<span class="muted">⏳</span>' : st.ok ? '<span class="up">●</span>' : '<span class="down">●</span>';
    const info = !st ? 'zatím nenačteno' : st.ok ? `${st.pocet} zpráv` : esc(st.chyba || 'nefunguje');
    return `<tr><td>${icon}</td><td><b>${esc(z.nazev)}</b><div class="muted" style="font-size:11px">${esc(z.typ)} · ${esc(z.aktiva)}</div></td>
      <td class="muted" style="font-size:12px;text-align:right">${info}</td></tr>`;
  };
  $('srcbody').innerHTML = `<table class="srctab">
    <tr><td><span class="up">●</span></td><td><b>Google News + Yahoo Finance</b><div class="muted" style="font-size:11px">hlavní zdroje · všechna aktiva</div></td><td></td></tr>
    ${d.zdroje.map(row).join('')}</table>
    <p class="muted" style="font-size:11.5px">Zdroje se obnovují každých 5 minut. Když nějaký web blokuje přístup, aplikace ho jen přeskočí.</p>`;
}
$('srcbtn').onclick = openSources;
$('srcclose').onclick = () => $('srcmodal').classList.add('hide');
$('srcmodal').onclick = e => { if (e.target === $('srcmodal')) $('srcmodal').classList.add('hide'); };

/* ---------- ŠÉFOVY TIPY (uložené v prohlížeči, vyhodnocené ✓/✗) ---------- */
S.calls = [];
try { S.calls = JSON.parse(localStorage.getItem('mm_calls') || '[]'); } catch (e) {}
S.callsOn = true;
try { S.callsOn = localStorage.getItem('mm_calls_on') !== '0'; } catch (e) {}
const saveCalls = () => { try { localStorage.setItem('mm_calls', JSON.stringify(S.calls.slice(-300))); } catch (e) {} };
const callDir = v => /nákup/i.test(v) ? 'up' : /prodej/i.test(v) ? 'down' : 'flat';
const CALL_LIFE = 5 * 86400;                     // tip se vyhodnocuje max 5 dní

function rememberCall(aid, d){
  if (d.stav !== 'hotovo' || !d.cas || !d.cena) return;
  const id = aid + '|' + d.cas;
  if (S.calls.some(c => c.id === id)) return;
  S.calls.push({ id, aid, cas: d.cas, verdikt: d.verdikt, jistota: d.jistota, cena: d.cena,
                 cil: d.cil ?? null, stop: d.stop ?? null, smer: callDir(d.verdikt),
                 stav: callDir(d.verdikt) === 'flat' ? 'neutral' : 'open' });
  saveCalls(); scheduleSessions(); setTimeout(evaluateCalls, 1500);
}

let evalBusy = false;
async function evaluateCalls(){
  if (evalBusy) return;
  const open = S.calls.filter(c => c.stav === 'open');
  if (!open.length) return;
  evalBusy = true;
  const cache = {}, now = Date.now() / 1000;
  let changed = false;
  try {
    for (const c of open) {
      if (!cache[c.aid]) {
        try { cache[c.aid] = await (await fetch(`/api/history?id=${c.aid}&range=5D&iv=15m`)).json(); } catch (e) { cache[c.aid] = []; }
      }
      const bars = (cache[c.aid] || []).filter(b => b.time >= c.cas - 900);
      let res = null;
      if (c.cil != null && c.stop != null) {
        for (const b of bars) {
          const hitStop = c.smer === 'up' ? b.low <= c.stop : b.high >= c.stop;
          const hitTgt = c.smer === 'up' ? b.high >= c.cil : b.low <= c.cil;
          if (hitStop) { res = { stav: 'loss', konec: b.time, cenaKonec: c.stop }; break; }   // v jedné svíčce obojí → raději ✗
          if (hitTgt) { res = { stav: 'win', konec: b.time, cenaKonec: c.cil }; break; }
        }
      } else if (now - c.cas >= 86400 && bars.length) {   // bez cíle/stopu: po 24 h podle směru
        const b = bars.find(x => x.time >= c.cas + 86400) || bars[bars.length - 1];
        const ok = c.smer === 'up' ? b.close > c.cena : b.close < c.cena;
        res = { stav: ok ? 'win' : 'loss', konec: b.time, cenaKonec: b.close };
      }
      if (!res && now - c.cas > CALL_LIFE) res = { stav: 'expired', konec: c.cas + CALL_LIFE, cenaKonec: null };
      if (res) {
        Object.assign(c, res); changed = true;
        const a = asset(c.aid);
        if (res.stav !== 'expired') toast(`👔 Šéfův tip – ${a ? a.nazev : c.aid}`,
          res.stav === 'win' ? `✓ ${c.verdikt}: cíl zasažen` : `✗ ${c.verdikt}: zasažen stop`, res.stav === 'loss', () => select(c.aid));
      }
    }
  } finally { evalBusy = false; }
  if (changed) { saveCalls(); scheduleSessions(); if (S.lastAI) renderAI(S.lastAI); }
}
setInterval(evaluateCalls, 60000);
setTimeout(evaluateCalls, 4000);

function callsSummaryHtml(aid){
  const list = S.calls.filter(c => c.aid === aid);
  if (!list.length) return '';
  const w = list.filter(c => c.stav === 'win').length, l = list.filter(c => c.stav === 'loss').length;
  const o = list.filter(c => c.stav === 'open').length;
  const pct = w + l ? Math.round(w / (w + l) * 100) : null;
  const icon = { win: '<b class="up">✓</b>', loss: '<b class="down">✗</b>', open: '<span class="muted">⏳</span>',
                 expired: '<span class="muted">⏱</span>', neutral: '<span class="muted">•</span>' };
  const d = asset(aid)?.desetinna ?? 2;
  const rows = list.slice(-10).reverse().map(c => `<div class="call-row">${icon[c.stav] || ''}
      <span class="muted">${new Date(c.cas * 1000).toLocaleString('cs-CZ', { day: 'numeric', month: 'numeric', hour: '2-digit', minute: '2-digit' })}</span>
      <span class="call-v ${TECH_CLS[c.verdikt] || 'n'}">${esc(c.verdikt)}</span>
      <span class="muted">${fmt(c.cena, d)}${c.cil != null ? ` → ${fmt(c.cil, d)} / stop ${fmt(c.stop, d)}` : ''}</span></div>`).join('');
  return `<div class="calls-sum">📈 Šéfovy tipy: <b class="up">${w} ✓</b> · <b class="down">${l} ✗</b>${pct != null ? ` · úspěšnost <b>${pct} %</b>` : ''}${o ? ` · ${o} běží` : ''}
    <button class="linkbtn" id="callstoggle" style="margin:0 0 0 6px;font-size:11px">${S.callsListOpen ? 'skrýt ▴' : 'historie ▾'}</button></div>
    ${S.callsListOpen ? `<div class="calls-list">${rows}</div>` : ''}`;
}
document.addEventListener('click', e => {
  if (e.target.id === 'callstoggle') { S.callsListOpen = !S.callsListOpen; if (S.lastAI) renderAI(S.lastAI); }
});

function barIndexAt(t){                           // první svíčka s časem >= t
  const b = S.bars; if (!b || !b.length) return -1;
  let lo = 0, hi = b.length - 1;
  if (t > b[hi].time) return hi;
  while (lo < hi) { const m = (lo + hi) >> 1; if (b[m].time < t) lo = m + 1; else hi = m; }
  return lo;
}
function drawCalls(){
  const svg = $('callov');
  if (!S.callsOn || !chart || !S.bars || !S.bars.length) { svg.innerHTML = ''; return; }
  const a = asset(S.sel); if (!a) return;
  const ser = S.type === 'candle' ? candle : area, ts = chart.timeScale();
  const sh = ivSec() ? tzShift() : 0, d = a.desetinna;
  const W = ts.width(), H = $('chart').clientHeight - ts.height();
  const step = ivSec() || 86400;
  const X = t => { if (t < S.bars[0].time - step) return null; const i = barIndexAt(t - step + 1); return i < 0 ? null : ts.timeToCoordinate(S.bars[i].time + sh); };
  const Y = p => ser.priceToCoordinate(p);
  const UP = '#26a69a', DN = '#ef5350';
  let h = `<defs><clipPath id="callclip"><rect x="0" y="0" width="${W}" height="${H}"/></clipPath></defs><g clip-path="url(#callclip)" font-family="Segoe UI,Arial,sans-serif">`;
  for (const c of S.calls.filter(c => c.aid === a.id)) {
    const x0 = X(c.cas), y0 = Y(c.cena);
    if (x0 == null || y0 == null) continue;
    const xe = c.konec ? (X(c.konec) ?? W) : W;
    if (c.cil != null && c.stop != null) {
      const yt = Y(c.cil), ys = Y(c.stop);
      if (yt != null) h += `<line x1="${x0}" x2="${xe}" y1="${yt}" y2="${yt}" stroke="${UP}" stroke-width="1.2" stroke-dasharray="5 3"/>`
        + `<text x="${x0 + 4}" y="${yt - 4}" font-size="10" font-weight="700" fill="${UP}">Cíl ${fmt(c.cil, d)}</text>`;
      if (ys != null) h += `<line x1="${x0}" x2="${xe}" y1="${ys}" y2="${ys}" stroke="${DN}" stroke-width="1.2" stroke-dasharray="5 3"/>`
        + `<text x="${x0 + 4}" y="${ys + 12}" font-size="10" font-weight="700" fill="${DN}">Stop ${fmt(c.stop, d)}</text>`;
      if (yt != null && ys != null && c.stav === 'open')
        h += `<rect x="${x0}" y="${Math.min(yt, y0)}" width="${Math.max(0, xe - x0)}" height="${Math.abs(yt - y0)}" fill="rgba(38,166,154,.07)"/>`
           + `<rect x="${x0}" y="${Math.min(ys, y0)}" width="${Math.max(0, xe - x0)}" height="${Math.abs(ys - y0)}" fill="rgba(239,83,80,.07)"/>`;
    }
    const col = c.smer === 'up' ? UP : c.smer === 'down' ? DN : '#9598a1';
    if (c.smer === 'up') h += `<path d="M${x0} ${y0 + 4} l-7 12 h14 z" fill="${col}"/>`;
    else if (c.smer === 'down') h += `<path d="M${x0} ${y0 - 4} l-7 -12 h14 z" fill="${col}"/>`;
    else h += `<circle cx="${x0}" cy="${y0}" r="5" fill="${col}"/>`;
    h += `<text x="${x0}" y="${c.smer === 'down' ? y0 - 20 : y0 + 30}" text-anchor="middle" font-size="10.5" font-weight="700" fill="${col}">👔 ${esc(c.verdikt)}${c.jistota != null ? ' ' + c.jistota + ' %' : ''}</text>`;
    if (c.stav === 'win' || c.stav === 'loss') {
      const ye = Y(c.cenaKonec);
      if (ye != null) h += `<line x1="${x0}" y1="${y0}" x2="${xe}" y2="${ye}" stroke="${col}" stroke-width="1" stroke-dasharray="2 3" opacity=".7"/>`
        + `<circle cx="${xe}" cy="${ye}" r="9" fill="${c.stav === 'win' ? UP : DN}"/>`
        + `<text x="${xe}" y="${ye + 4.5}" text-anchor="middle" font-size="12" font-weight="800" fill="#fff">${c.stav === 'win' ? '✓' : '✗'}</text>`;
    } else if (c.stav === 'expired') {
      h += `<text x="${xe}" y="${y0 + 4}" text-anchor="middle" font-size="12" fill="#9598a1">⏱</text>`;
    }
  }
  svg.innerHTML = h + '</g>';
}
function syncCallsBtn(){ $('callsbtn').classList.toggle('calls-on', !!S.callsOn); }
$('callsbtn').onclick = () => {
  S.callsOn = !S.callsOn;
  try { localStorage.setItem('mm_calls_on', S.callsOn ? '1' : '0'); } catch (e) {}
  syncCallsBtn(); scheduleSessions();
};
syncCallsBtn();

/* ---------- AI TÝM (debata 4 botů) ---------- */
let aiTimer = null, aiOpen = false, aiAsset = null;
const STANCE_CLS = s => /NÁKUP|NAKUP/.test(s) ? 'up' : /PRODEJ/.test(s) ? 'down' : '';
function aiMsgHtml(m){
  return `<div class="ai-msg ${m.bot === 'sef' ? 'sef' : ''}"><div class="ai-av">${m.ikona}</div>
    <div><div class="who">${esc(m.jmeno)}${m.kolo === 2 ? '<span>· reakce</span>' : ''}</div>
    <div class="txt">${esc(m.text)}</div></div></div>`;
}
function renderAI(d){
  S.lastAI = d;
  const btn = $('aibtn');
  if (!d.klic) {
    btn.disabled = true;
    $('aibody').innerHTML = `<div class="ai-err">Chybí klíč pro Groq (GROQ_API_KEY).</div>
      <div class="muted" style="font-size:12px;margin-top:5px">Web: Render → Environment → přidej GROQ_API_KEY.
      PC: soubor groq_klic.txt vedle aplikace.</div>`;
    return;
  }
  btn.disabled = d.stav === 'bezi';
  btn.textContent = d.stav === 'hotovo' ? 'Znovu' : 'Spustit debatu';
  if (d.stav === 'bezi') {
    $('aibody').innerHTML = `<div class="ai-run"><div class="spin"></div>${esc(d.krok || 'Debatují…')}</div>
      <div class="ai-thread">${d.zpravy.map(aiMsgHtml).join('')}</div>`;
    const th = $('aibody').querySelector('.ai-thread'); th.scrollTop = th.scrollHeight;
    return;
  }
  if (d.stav === 'chyba') {
    $('aibody').innerHTML = `<div class="ai-err">⚠ ${esc(d.chyba)}</div>` +
      (d.zpravy.length ? `<div class="ai-thread">${d.zpravy.map(aiMsgHtml).join('')}</div>` : '');
    return;
  }
  if (d.stav !== 'hotovo') {
    $('aibody').innerHTML = `<div class="muted" style="font-size:12.5px">Šest AI botů (analytik, SMC bot, scenárista, zpravodaj,
      risk manažer a šéf) probere grafy, scénáře a zprávy a šéf vynese verdikt s cílem a stopem. Debata trvá asi 1–2 min.</div>`
      + callsSummaryHtml(S.sel);
    return;
  }
  const names = { analytik: '📊 Analytik', smc: '🧠 SMC', scen: '🔭 Scenárista', zpravar: '📰 Zpravodaj', risk: '🛡️ Risk' };
  const SC = { up: ['🟢', '#26a69a'], side: ['⚪', '#9598a1'], down: ['🔴', '#ef5350'] };
  const scen = (d.scenare || []).length ? `<div class="ai-scen"><div class="ai-scen-h">🔭 Scénáře</div>` + d.scenare.map(x =>
      `<div class="ai-sc"><div class="ai-sc-t"><span>${SC[x.typ][0]} ${esc(x.nazev)}</span>
        ${x.pst != null ? `<b style="color:${SC[x.typ][1]}">${x.pst} %</b>` : ''}</div>
        ${x.pst != null ? `<div class="ai-sc-bar"><div style="width:${Math.min(100, x.pst)}%;background:${SC[x.typ][1]}"></div></div>` : ''}
        <div class="ai-sc-p">${esc(x.popis)}</div></div>`).join('') + `</div>` : '';
  const stances = Object.entries(d.postoje || {}).filter(([, v]) => v)
    .map(([k, v]) => `<span class="ai-st">${names[k]}: <b class="${STANCE_CLS(v)}">${esc(v.split('(')[0].trim())}</b></span>`).join('');
  const old = (Date.now() / 1000 - d.cas) / 60 > d.platnost_min;
  $('aibody').innerHTML = `
    <div class="ai-verd"><span class="ai-pill ${TECH_CLS[d.verdikt] || 'n'}">${esc(d.verdikt)}</span>
      ${d.jistota != null ? `<div class="ai-conf">Jistota šéfa ${d.jistota} %<div class="bar"><div style="width:${d.jistota}%"></div></div></div>` : ''}</div>
    ${d.cil != null && d.stop != null ? `<div class="ai-lv"><span>Vstup <b>${fmt(d.cena, asset(S.sel)?.desetinna ?? 2)}</b></span>
      <span class="up">Cíl <b>${fmt(d.cil, asset(S.sel)?.desetinna ?? 2)}</b></span>
      <span class="down">Stop <b>${fmt(d.stop, asset(S.sel)?.desetinna ?? 2)}</b></span></div>` : ''}
    <div class="ai-sum">${esc(d.shrnuti)}</div>
    ${stances ? `<div class="ai-stances">${stances}</div>` : ''}
    ${scen}
    <div class="ai-meta"><span>${old ? '⚠ ' : ''}Debata ${ago(d.cas)} · ${esc(d.model)}</span>
      <button class="linkbtn" id="aitoggle" style="margin:0">${aiOpen ? 'Skrýt debatu ▴' : 'Zobrazit debatu ▾'}</button></div>
    ${aiOpen ? `<div class="ai-thread">${d.zpravy.map(aiMsgHtml).join('')}</div>` : ''}
    ${callsSummaryHtml(S.sel)}
    <div class="tech-note" style="text-align:left">AI se může mýlit – nejde o investiční doporučení.</div>`;
  $('aitoggle').onclick = () => { aiOpen = !aiOpen; renderAI(d); };
}
async function loadAI(){
  const id = S.sel; if (!id) return;
  if (aiAsset !== id) { aiAsset = id; aiOpen = false; }
  let d;
  try { d = await (await fetch(`/api/debata?id=${id}`)).json(); } catch (e) { return; }
  if (id !== S.sel) return;
  rememberCall(id, d);
  renderAI(d);
  clearTimeout(aiTimer);
  if (d.stav === 'bezi') aiTimer = setTimeout(loadAI, 1500);
}
$('aibtn').onclick = async () => {
  $('aibtn').disabled = true;
  try {
    const r = await (await fetch(`/api/debata/start?id=${S.sel}`, { method: 'POST' })).json();
    if (!r.ok) { toast('AI tým', r.chyba || 'Nepodařilo se spustit.', true); }
  } catch (e) {}
  setTimeout(loadAI, 400);
};
setTimeout(loadAI, 1200);

/* ---------- AKTUALIZACE ---------- */
const CURRENT = '{{VERZE}}';
let UPDINFO = null, installing = false;
async function checkUpdate(force){
  try { UPDINFO = await (await fetch('/api/update' + (force ? '?force=1' : ''))).json(); } catch (e) { return; }
  const b = $('updbtn');
  b.classList.toggle('hide', !UPDINFO.novejsi);
  if (UPDINFO.novejsi) b.textContent = `⬆ Aktualizovat na ${UPDINFO.nejnovejsi}`;
  if (!$('modal').classList.contains('hide') && !installing) renderModal();
}
function openModal(){ $('modal').classList.remove('hide'); renderModal(); }
function closeModal(){ if (!installing) $('modal').classList.add('hide'); }
$('verbtn').onclick = openModal;
$('updbtn').onclick = openModal;
$('mclose').onclick = closeModal;
$('modal').onclick = e => { if (e.target === $('modal')) closeModal(); };

function renderModal(){
  const u = UPDINFO || {};
  let h = `<p>Nainstalovaná verze: <b>${esc(CURRENT)}</b></p>`;
  if (!UPDINFO) h += `<p class="muted">Zjišťuji…</p>`;
  else if (u.server) h += `<p class="muted">Toto je webová verze – aktualizuje se sama, když nahraješ novou verzi na GitHub.</p>`;
  else if (!u.nastaveno) h += `<p class="muted">Automatické aktualizace nejsou nastavené (v souboru chybí UPDATE_REPO).</p>`;
  else if (u.chyba) h += `<p class="down">Nepodařilo se zkontrolovat: ${esc(u.chyba)}</p>`;
  else if (u.novejsi) h += `<p>K dispozici je nová verze <b class="up">${esc(u.nejnovejsi)}</b>${u.velikost ? ` · ${(u.velikost/1048576).toFixed(0)} MB` : ''}</p>`
      + (u.poznamky ? `<div class="notes">${esc(u.poznamky)}</div>` : '')
      + `<p class="muted" style="font-size:12px">Aplikace stáhne novou verzi, nainstaluje ji a sama se restartuje.</p>`;
  else if (u.bez_souboru) h += `<p class="muted">Verze ${esc(u.nejnovejsi)} je vydaná, ale chybí u ní soubor ke stažení.</p>`;
  else h += `<p class="up">✓ Máš nejnovější verzi.</p>`;
  h += `<div class="mbtns">${u.novejsi ? '<button class="primary" id="doupd">Stáhnout a nainstalovat</button>' : ''}`
     + `${u.nastaveno ? '<button class="btn" id="recheck">Zkontrolovat znovu</button>' : ''}</div>`;
  $('mbody').innerHTML = h;
  if ($('doupd')) $('doupd').onclick = doInstall;
  if ($('recheck')) $('recheck').onclick = () => { $('mbody').innerHTML = '<p class="muted">Kontroluji…</p>'; checkUpdate(true); };
}

async function doInstall(){
  installing = true;
  $('mclose').classList.add('hide');
  $('mbody').innerHTML = `<p>Stahuji <b>${esc(UPDINFO.nejnovejsi)}</b>…</p>
    <div class="pbar"><div id="pfill"></div></div><p class="muted" id="pst">0 %</p>`;
  try { await fetch('/api/update/install', { method: 'POST' }); } catch (e) {}
  const start = Date.now();
  const iv = setInterval(async () => {
    let st = null;
    try { st = await (await fetch('/api/update/status')).json(); } catch (e) {}
    if (st && st.stav === 'stahuji') {
      $('pfill').style.width = st.procent + '%'; $('pst').textContent = st.procent + ' %';
    } else if (st && st.stav === 'chyba') {
      clearInterval(iv); installing = false; $('mclose').classList.remove('hide');
      $('mbody').innerHTML = `<p class="down">Aktualizace se nepovedla: ${esc(st.chyba)}</p>`;
    } else {
      $('pfill').style.width = '100%';
      $('pst').textContent = 'Instaluji a restartuji aplikaci… (stránka se sama obnoví)';
      try {
        const s2 = await (await fetch('/api/state')).json();
        if (s2.verze && s2.verze !== CURRENT) { clearInterval(iv); location.reload(); }
      } catch (e) {}
      if (Date.now() - start > 120000) {
        clearInterval(iv);
        $('pst').innerHTML = 'Restart trvá dlouho – spusť aplikaci ručně znovu a obnov stránku (F5).';
      }
    }
  }, 1000);
}
checkUpdate(false);
setInterval(() => checkUpdate(false), 5 * 60 * 1000);
</script>
</body>
</html>
"""

if __name__ == "__main__":
    main()
