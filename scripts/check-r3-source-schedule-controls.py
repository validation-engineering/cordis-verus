#!/usr/bin/env python3
"""Strict source-position and typed-landing controls; not full regression."""
import runpy
from pathlib import Path

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).with_name('check-r3-episode-controls.py')))['main']('source-schedule')
