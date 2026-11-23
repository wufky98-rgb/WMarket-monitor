# -*- coding: utf-8 -*-
"""
Spouštěč pro webový server (Render.com).
Najde nejvyšší verzi market_app_V*.py v této složce a spustí ji v serverovém režimu.
Rozumí i opravným verzím: V13-1 je novější než V13, V14 je novější než V13-1.
"""
import glob
import os
import re
import runpy
import sys

slozka = os.path.dirname(os.path.abspath(__file__))


def verze(cesta):
    m = re.search(r"_V(\d+)(?:-(\d+))?\.py$", cesta)
    return (int(m.group(1)), int(m.group(2) or 0)) if m else None


soubory = [p for p in glob.glob(os.path.join(slozka, "market_app_V*.py")) if verze(p)]
if not soubory:
    sys.exit("Nenašel jsem žádný soubor market_app_V*.py")

nejnovejsi = max(soubory, key=verze)
print(f"Spouštím {os.path.basename(nejnovejsi)} (serverový režim)", flush=True)
sys.argv = [nejnovejsi, "--server"]
runpy.run_path(nejnovejsi, run_name="__main__")
