#!/usr/bin/env python3
"""Five strict production fault controls; neither full regression nor R01 closure."""
from pathlib import Path
import runpy
if __name__ == "__main__":
    runpy.run_path(str(Path(__file__).with_name("check-r3-episode-controls.py")))["main"]("update-recovery")
