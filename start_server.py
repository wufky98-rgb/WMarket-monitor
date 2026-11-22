# -*- coding: utf-8 -*-
"""
Spouštěč pro webový server (Render.com).
Najde nejvyšší verzi market_app_V*.py v této složce a spustí ji v serverovém režimu.
Díky tomu nemusíš na Renderu nic měnit, když nahraješ novou verzi (V10, V11…).
"""
import glob
import os
import re
import runpy
import sys

slozka = os.path.dirname(os.path.abspath(__file__))
soubory = glob.glob(os.path.join(slozka, "market_app_V*.py"))
if not soubory:
    sys.exit("Nenašel jsem žádný soubor market_app_V*.py")

nejnovejsi = max(soubory, key=lambda p: int(re.search(r"_V(\d+)\.py$", p).group(1)))
print(f"Spouštím {os.path.basename(nejnovejsi)} (serverový režim)", flush=True)
sys.argv = [nejnovejsi, "--server"]
runpy.run_path(nejnovejsi, run_name="__main__")
