#!/usr/bin/env python3
"""Run slang on a file list via pyslang's Driver API and emit a JSON diagnostic file."""

import sys
import pyslang


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <flist> <output.json>", file=sys.stderr)
        sys.exit(1)

    flist, output_json = sys.argv[1], sys.argv[2]

    driver = pyslang.driver.Driver()
    driver.parseCommandLine(
        f"-f {flist}"
        f" --top axi_lint_top"
        f" --error-limit 0"
        f" --diag-json {output_json}"
    )
    driver.runFullCompilation()
    # Exit 0 regardless of compile errors so the CI step continues
    # and reviewdog can annotate the diagnostics.


if __name__ == "__main__":
    main()
