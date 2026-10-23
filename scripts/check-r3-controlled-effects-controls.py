#!/usr/bin/env python3
"""Strict selected controls for actual controlled effects and replay admission."""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).with_name('check-r3-episode-controls.py')))['main']('controlled-effects')
