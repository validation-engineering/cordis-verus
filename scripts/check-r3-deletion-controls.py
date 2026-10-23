#!/usr/bin/env python3
"""Run the fixed native episode deletion controls through the shared strict runner."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
path = Path(__file__).with_name('check-r3-episode-controls.py')
spec = importlib.util.spec_from_file_location('r3_controls', path)
runner = importlib.util.module_from_spec(spec)
exec(compile(path.read_bytes(), str(path), 'exec'), runner.__dict__)

if __name__ == '__main__':
    runner.main('deletion')
