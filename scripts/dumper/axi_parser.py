from   pathlib import Path
import pandas as pd
import json
import re
from  axi_utils import INT_FIELDS, raise_exception, cprint, gprint, rprint

class AXIParser:
    """
    Responsible for parsing raw AXI log files into structured pandas DataFrames.
    """
    def __init__(self):
        pass


    def clean_and_parse(self, line):
        """
        Cleans a single line from the AXI log and converts it to a JSON-parsable dict.
        """

        line = re.sub(r',\s*}', '}', line.strip())
        line = re.sub(r"(0x[\da-fA-FxX]+)", r'"\1"', line)
        line = line.replace("'", '"')
        return json.loads(line)


    def parse_axi_dump(self, file_path):
        """
        Parses a single AXI log file and returns a DataFrame of all transaction entries.
        Each transaction is parsed into a dict and converted into appropriate Python types.
        """

        parsed_entries = []
        cprint(f"Parsing {file_path.name}")
        with open(file_path, 'r') as file:
            for line in file:
                try:
                    parsed = self.clean_and_parse(line)
                    formatted = {}
                    for k, v in parsed.items():
                        if k in INT_FIELDS:
                            formatted[k] = int(v, 16) if isinstance(v, str) and v.startswith('0x') else int(v)
                        else:
                            formatted[k] = str(v)
                    parsed_entries.append(formatted)
                except Exception as e:
                    rprint(f"Error parsing line:\n{line.strip()}\n -> {e}")
        return pd.DataFrame(parsed_entries)

    def collect_df(self, directory, pattern="axi_trace_mem_tile_*.log"):
        """
        Collects all matching AXI log files from a directory and returns a combined, time-sorted DataFrame.
        Automatically tags each row with its source file for traceability.
        """

        directory = Path(directory)
        all_dfs = []

        for file_path in sorted(directory.glob(pattern)):
            df = self.parse_axi_dump(file_path)
            df['source_file'] = file_path.name
            all_dfs.append(df)

        if not all_dfs:
            raise_exception(FileNotFoundError, f"No AXI log files found in '{directory}' matching '{pattern}'")

        df_combined = pd.concat(all_dfs, ignore_index=True)

        if 'source_file' in df_combined.columns and 'time' in df_combined.columns:
            cols = ['source_file', 'time'] + [col for col in df_combined.columns if col not in ('source_file', 'time')]
            df_combined = df_combined[cols]

        df_combined.sort_values(by=['source_file', 'time'], inplace=True)
        return df_combined
