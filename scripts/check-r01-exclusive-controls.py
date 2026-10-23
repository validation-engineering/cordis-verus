#!/usr/bin/env python3
"""Strict selected R01 prewrite guards; not full regression or paper closure."""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).with_name('check-r3-episode-controls.py')))['main']('r01-exclusive')
