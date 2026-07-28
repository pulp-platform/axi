#!/usr/bin/env python3

import sys
import argparse
from pathlib import Path

# Automatically add parent dir of 'util/' to sys.path
sys.path.append(str(Path(__file__).resolve().parents[1]))

from axi_parser import AXIParser
from axi_elaborate import AXIElaborate
import axi_utils

def parse_arguments():
    parser = argparse.ArgumentParser(
        description="Filter and analyze AXI transactions from log files."
    )
    parser.add_argument(
        "--type", "-t", type=str, required=True,
        help="Transaction type to filter (e.g., AW, W, AR, etc.)"
    )
    parser.add_argument(
        "--addr", "-a", type=str, required=True,
        help="Address to filter for (e.g., 0x7000b080)"
    )
    parser.add_argument(
        "--logdir", "-l", type=str, default="axi_log/",
        help="Directory containing AXI log files (default: axi_log/)"
    )
    return parser.parse_args()


def main():
    args = parse_arguments()

    log_dir = args.logdir
    tran_type = args.type
    addr = args.addr


    parser = AXIParser()
    df = parser.collect_df(log_dir)

    elab  = AXIElaborate(df)


    axi_utils.save_to_csv(df,"elab.csv")
    df = elab.resolve_write_addresses()

    df_filtered = elab.filter_transactions(tran_type, addr=addr)
    df_formatted = axi_utils.format_for_display(df_filtered)
    axi_utils.save_to_csv(df_formatted, "write_trans.csv")


if __name__ == "__main__":
  main()
