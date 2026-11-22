# -*- coding: utf-8 -*-
"""
market_app_V9.py – Market Monitor jako webová aplikace (styl TradingView / Trading 212)

Python na pozadí stahuje ceny (Yahoo Finance) a zprávy (Google News + Yahoo),
prohlížeč zobrazuje tmavý dashboard s grafy. Vše běží jen u tebe na počítači.

Spuštění:   dvojklik na spustit_app.bat  (nebo: py market_app_V9.py)
            macOS: dvojklik na spustit_mac.command  (nebo: python3 market_app_V9.py)      (otevře se prohlížeč na http://localhost:8050)
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

VERZE = "V9"                   # V9: webová verze (Render), přihlášení heslem, mobilní rozložení
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
]

# --- EKONOMICKÝ KALENDÁŘ (ForexFactory, veřejný týdenní feed) ---
KALENDAR_URL = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"
KALENDAR_MENY = ["USD", "EUR"]            # které měny zobrazit (např. přidej "GBP", "JPY", "CNY")
KALENDAR_DOPAD = ["High", "Medium"]       # High / Medium / Low / Holiday
KALENDAR_KAZDYCH_MIN = 60
OTEVRIT_PROHLIZEC = True

# --- WEBOVÁ VERZE (běh na serveru, např. Render.com) ---
# Na serveru se spouští s parametrem --server (nebo automaticky na Renderu).
# Heslo se NEpíše sem – nastavuje se na serveru jako proměnná prostředí MM_HESLO.
SERVER_MODE = "--server" in sys.argv or bool(os.environ.get("RENDER"))
HESLO = os.environ.get("MM_HESLO", "")
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

ROZSAHY = {  # tlačítko -> (period, interval) pro yfinance
    "1D": ("5d", "5m"), "5D": ("5d", "15m"), "1M": ("1mo", "60m"),
    "6M": ("6mo", "1d"), "1R": ("1y", "1d"), "5R": ("5y", "1wk"),
}

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


def zpravy_rss(url: str, nazev: str) -> list[dict]:
    try:
        r = requests.get(url, timeout=HTTP_TIMEOUT, headers={"User-Agent": "Mozilla/5.0 (MarketMonitor)"})
        feed = feedparser.parse(r.content)
    except Exception:
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
    return out


def zpravy_z_webu(z: dict, dotaz: str) -> list[dict]:
    q = f'{z.get("dotaz") or dotaz} site:{z["domena"]}'
    vysledek = zpravy_google(q)
    for v in vysledek:
        v["zdroj"] = v["zdroj"] if v["zdroj"] and v["zdroj"] != "Google News" else z["nazev"]
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
                    rss_cache[z["url"]] = zpravy_rss(z["url"], z["nazev"])
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


def historie(aid: str, rozsah: str) -> list[dict]:
    klic = (aid, rozsah)
    if klic in CACHE_GRAFU and time.time() - CACHE_GRAFU[klic][0] < 55:
        return CACHE_GRAFU[klic][1]
    a = next((x for x in AKTIVA if x["id"] == aid), None)
    if a is None or rozsah not in ROZSAHY:
        return []
    period, interval = ROZSAHY[rozsah]
    ticker = ZVOLENY_TICKER.get(aid, a["tickers"][0])
    try:
        with YF_LOCK:
            df = yf.Ticker(ticker).history(period=period, interval=interval, auto_adjust=False)
        sekund = {"1m": 60, "5m": 300, "15m": 900, "60m": 3600}.get(interval)
        if sekund:
            df = ocisti_intraday(df.dropna(subset=["Close"]), sekund)
        if rozsah == "1D":
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
    data = [body[k] for k in sorted(body)]
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
        if time.time() - posledni_kal >= KALENDAR_KAZDYCH_MIN * 60:
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
            elif u.path == "/api/kalendar":
                self._json(KALENDAR)
            elif u.path == "/api/tech":
                self._json(technicka_analyza(q.get("id", [""])[0], q.get("tf", ["1D"])[0]))
            elif u.path == "/api/history":
                self._json(historie(q.get("id", [""])[0], q.get("range", ["1D"])[0]))
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

  .toolbar{display:flex;align-items:center;gap:4px;padding:8px 14px;border-bottom:1px solid var(--border)}
  .btn{background:none;border:none;color:var(--muted);padding:6px 10px;border-radius:4px;cursor:pointer;font-size:13px;font-weight:600}
  .btn:hover{background:var(--hover);color:var(--text)}
  .btn.on{color:var(--text);background:var(--hover)}
  .sep{width:1px;height:18px;background:var(--border);margin:0 6px}
  .chart-wrap{flex:1;position:relative;min-height:0}
  #chart{position:absolute;inset:0}
  .sessov{position:absolute;inset:0;width:100%;height:100%;pointer-events:none;z-index:2;overflow:hidden}
  .sesswrap{position:relative}
  .sesspop{position:absolute;top:34px;left:0;z-index:20;background:var(--panel2);border:1px solid var(--border);border-radius:8px;
    padding:8px 4px;min-width:210px;box-shadow:0 10px 30px rgba(0,0,0,.45)}
  .sesspop label{display:flex;align-items:center;gap:9px;padding:6px 10px;cursor:pointer;font-size:13px;border-radius:4px}
  .sesspop label:hover{background:var(--hover)}
  .sesspop .sw{width:12px;height:12px;border-radius:3px}
  .sesspop hr{border:none;border-top:1px solid var(--border);margin:4px 0}
  .sesspop .hint{font-size:11px;color:var(--muted);padding:4px 10px 2px}
  .btn.sess-on{color:#ff9800}
  .legend{position:absolute;left:14px;top:10px;z-index:3;font-size:12px;color:var(--muted);pointer-events:none}
  .legend b{color:var(--text);font-weight:600;margin-right:10px}
  .overlay{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;color:var(--muted);z-index:4;background:var(--panel)}
  .overlay.hide{display:none}

  /* news */
  .tabs{display:flex;gap:4px}
  .news{overflow:auto;flex:1}
  .tech{border-bottom:1px solid var(--border);flex:0 0 auto}
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
    .main > .col:first-child > .col-h, .main > .col:first-child > .foot{display:none}
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
      <div class="col-h"><span>Watchlist</span><span class="muted" style="text-transform:none;letter-spacing:0">↑↓ přepínání</span></div>
      <div class="wl" id="wl"></div>
      <div class="foot">Data: Yahoo Finance · futures mohou být zpožděné ~10 min</div>
    </div>

    <div class="col center">
      <div class="hdr" id="hdr"></div>
      <div class="toolbar" id="toolbar">
        <button class="btn" data-r="1D">1D</button><button class="btn" data-r="5D">5D</button>
        <button class="btn" data-r="1M">1M</button><button class="btn" data-r="6M">6M</button>
        <button class="btn" data-r="1R">1R</button><button class="btn" data-r="5R">5R</button>
        <span class="sep"></span>
        <button class="btn" data-t="candle">Svíčky</button><button class="btn" data-t="area">Čára</button>
        <span class="sep"></span>
        <span class="sesswrap"><button class="btn" id="sessbtn" title="Obchodní seance (Tokyo / Londýn / New York)">◫ Seance ▾</button>
          <div class="sesspop hide" id="sesspop"></div></span>
        <button class="btn" id="resetbtn" title="Obnovit zobrazení grafu (také dvojklik do grafu)">⟲ Reset</button>
        <span class="livebadge" id="livebadge"><span class="ld"></span><span>…</span></span>
      </div>
      <div class="chart-wrap">
        <div class="legend" id="legend"></div>
        <div id="chart"></div>
        <svg class="sessov" id="sessov"></svg>
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
        </div>
      </div>
      <div class="col-h"><span>Zprávy</span>
        <div class="tabs"><button class="btn on" data-n="sel" id="tab-sel">Vybrané</button><button class="btn" data-n="all" id="tab-all">Vše</button><button class="btn" data-n="cal" id="tab-cal">Kalendář</button></div>
      </div>
      <div class="news" id="news"><div class="empty">Hledám zprávy…</div></div>
      <div class="foot" id="newsfoot">Zdroje: Google News, Yahoo Finance, Reuters, EIA, Federal Reserve, ForexFactory</div>
    </div>
  </div>
</div>
<div class="toasts" id="toasts"></div>
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
const visibleAssets = () => S.assets.filter(a => !closedGroups.has(a.kat));   // pro šipky ↑↓

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

function itemHtml(a){
  return `<div class="wl-item" data-id="${a.id}">
      <div class="wl-ico">${iconFor(a)}</div>
      <div><div class="wl-name">${esc(a.nazev)}</div><div class="wl-tick" data-f="tick"></div></div>
      <div class="wl-price num" data-f="price">—</div>
      <div></div><div class="pill num" data-f="pill">—</div>
      <div class="wl-spark" data-f="spark"></div>
    </div>`;
}

function renderWatchlist(){
  const wl = $('wl');
  const key = S.assets.map(a => a.kat + ':' + a.id).join(',');
  if (wl.dataset.key !== key) {          // přestavět jen při změně seznamu
    wl.dataset.key = key;
    const groups = [];
    for (const a of S.assets) {
      let g = groups.find(x => x.kat === a.kat);
      if (!g) groups.push(g = { kat: a.kat, items: [] });
      g.items.push(a);
    }
    wl.innerHTML = groups.map(g => `
      <div class="wl-box${closedGroups.has(g.kat) ? ' closed' : ''}" data-box="${g.kat}">
        <div class="wl-box-h"><span class="chev">▼</span><span>${katNazev(g.kat)}</span>
          <span class="cnt">${g.items.length}</span><span class="avg" data-g="${g.kat}"></span></div>
        <div class="wl-box-b">${g.items.map(itemHtml).join('')}</div>
      </div>`).join('');
    wl.querySelectorAll('.wl-item').forEach(el => el.onclick = () => select(el.dataset.id));
    wl.querySelectorAll('.wl-box-h').forEach(h => h.onclick = () => {
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
      <span class="hdr-sub">${esc(k.ticker)} · ${esc(a.popis)}${a.mena ? ' · ' + a.mena : ''}</span></div>
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
loadKalendar();
setInterval(loadKalendar, 10 * 60 * 1000);
setInterval(() => { checkCalendarAlerts(); if (S.newsTab === 'cal') renderCalendar(); }, 30000);

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
    const r = await fetch(`/api/history?id=${a.id}&range=${S.range}`);
    const data = await r.json();
    if (my !== chartReq) return;
    if (!data.length) { $('overlay').classList.remove('hide'); $('overlay').textContent = 'Pro tento rozsah nejsou data.'; return; }
    const sh = S.range === '1D' || S.range === '5D' || S.range === '1M' ? tzShift() : 0;
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
document.querySelectorAll('[data-r]').forEach(b => b.onclick = () => { S.range = b.dataset.r; syncToolbar(); loadChart(); });
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
function scheduleSessions(){ if (!_sessRaf) _sessRaf = requestAnimationFrame(() => { _sessRaf = 0; drawSessions(); }); }
function drawSessions(){
  const svg = $('sessov');
  const iv = IV[S.range];
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
$('sessbtn').onclick = e => { e.stopPropagation(); renderSessPop(); $('sesspop').classList.toggle('hide'); };
document.addEventListener('click', e => { if (!e.target.closest('.sesswrap')) $('sesspop').classList.add('hide'); });
syncSessBtn();
$('chart').addEventListener('dblclick', resetView);

/* ---------- výběr aktiva ---------- */
function select(id){
  if (S.sel === id) return;
  S.sel = id;
  renderWatchlist(); renderHeader(); renderNews(); loadChart(); loadTech();
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
const IV = { '1D': 300, '5D': 900, '1M': 3600, '6M': 0, '1R': 0, '5R': 0 };   // délka svíčky (s); 0 = denní/týdenní
let lastBar = null;

function applyTick(price, ts){
  if (!lastBar || !candle || ts < lastBar.time) return;
  const iv = IV[S.range];
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
