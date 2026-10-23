#!/usr/bin/env python3
"""Run the strict R3 real managed target-execution control profile."""
import runpy
from pathlib import Path

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).with_name('check-r3-episode-controls.py')))['main']('target-execution')
