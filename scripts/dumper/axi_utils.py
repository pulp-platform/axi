import re
import pandas as pd

INT_FIELDS = {'addr', 'atop', 'burst', 'cache', 'id', 'len', 'size'}

def print_rgb(message: str):
    styles = {
        r"\\gb\{(.*?)\}": "\033[1;32m\\1\033[0m",
        r"\\rb\{(.*?)\}": "\033[1;31m\\1\033[0m",
        r"\\yb\{(.*?)\}": "\033[1;33m\\1\033[0m",
        r"\\cb\{(.*?)\}": "\033[1;36m\\1\033[0m",
    }
    styled = message
    for pattern, replacement in styles.items():
        styled = re.sub(pattern, replacement, styled)
    print(styled)

def gprint(msg): print_rgb(f"\\gb{{{msg}}}")
def rprint(msg): print_rgb(f"\\rb{{{msg}}}")
def yprint(msg): print_rgb(f"\\yb{{{msg}}}")
def cprint(msg): print_rgb(f"\\cb{{{msg}}}")

def raise_exception(extype: type[Exception], msg: str):
    rprint(msg)
    raise extype(msg)

def format_for_display(df):
        """
        Converts numeric fields into human-readable hex strings.
        """
        df_formatted = df.copy()
        for col in INT_FIELDS:
            if col in df_formatted.columns:
                df_formatted[col] = df_formatted[col].apply(
                    lambda x: f"0x{int(x):x}" if pd.notnull(x) else "None"
                )
        return df_formatted

def save_to_csv(df, file_name):
    """
    Saves the current DataFrame to a CSV file.
    """
    df.to_csv(file_name, index=False)
