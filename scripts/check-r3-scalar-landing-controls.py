#!/usr/bin/env python3
"""Run the strict source-derived scalar input control; not full regression."""
import runpy
from pathlib import Path

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).with_name('check-r3-episode-controls.py')))['main']('scalar-landing')
