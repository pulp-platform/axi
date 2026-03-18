#!/usr/bin/env python3
"""Convert slang JSON diagnostic output to reviewdog rdjson format."""

import json
import re
import sys

SEVERITY_MAP = {
    "error":   "ERROR",
    "fatal":   "ERROR",
    "warning": "WARNING",
    "note":    "INFO",
    "info":    "INFO",
}

LOCATION_RE = re.compile(r'^(.+):(\d+):(\d+)$')


def parse_location(location_str):
    """Parse 'path:line:col' into a rdjson location object."""
    m = LOCATION_RE.match(location_str)
    if not m:
        return {"path": location_str}
    return {
        "path": m.group(1),
        "range": {
            "start": {
                "line":   int(m.group(2)),
                "column": int(m.group(3)),
            }
        },
    }


def convert(slang_diagnostics):
    diagnostics = []
    for d in slang_diagnostics:
        entry = {
            "message":  d.get("message", ""),
            "location": parse_location(d.get("location", "")),
            "severity": SEVERITY_MAP.get(d.get("severity", "").lower(), "WARNING"),
        }
        option_name = d.get("optionName")
        if option_name:
            entry["code"] = {"value": option_name}
            if entry["severity"] == "WARNING":
                entry["code"]["url"] = "https://sv-lang.com/warning-ref.html#" + option_name
        diagnostics.append(entry)

    return {
        "source": {
            "name": "slang",
            "url":  "https://sv-lang.com",
        },
        "diagnostics": diagnostics,
    }


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <slang-output.json>", file=sys.stderr)
        sys.exit(1)
    with open(sys.argv[1]) as f:
        slang_diagnostics = json.load(f)
    result = convert(slang_diagnostics)
    json.dump(result, sys.stdout, indent=2)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
