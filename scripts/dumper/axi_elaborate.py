import pandas as pd
from  axi_utils import INT_FIELDS, raise_exception

class AXIElaborate:
    """
    A class responsible for processing and analyzing AXI transaction DataFrames.
    It includes methods to resolve write addresses and filter transactions.
    """

    def __init__(self, df):
        self.df = df

    def resolve_write_addresses(self):
        """
        Resolves write addresses for W transactions using preceding AW entries.
        Groups by source_file to avoid cross-contamination between interfaces.

        Returns:
            pd.DataFrame: DataFrame with resolved addresses in W entries.
        """
        resolved_dfs = []

        for source, group in self.df.groupby('source_file', sort=False):
            resolved = self.resolve_write_addresses_per_interface(group)
            resolved_dfs.append(resolved)

        self.df = pd.concat(resolved_dfs, ignore_index=True)
        return self.df


    def resolve_write_addresses_per_interface(self, df):
        """
        Resolves and fills in missing 'addr' fields for W transactions based
        on the most recent AW entry within the same file (interface).

        Parameters:
            df (pd.DataFrame): Subset of AXI transactions from a single source file.

        Returns:
            pd.DataFrame: Updated DataFrame with resolved addresses.
        """
        current_aw = None
        w_counter = 0
        df = df.copy()

        for idx, row in df.iterrows():
            if row.get('type') == 'AW':
                current_aw = {'addr': row.get('addr'), 'size': row.get('size')}
                w_counter = 0

            elif row.get('type') == 'W':
                if current_aw is not None:
                    bytes_per_transfer = 1 << int(current_aw['size'])
                    resolved_addr = current_aw['addr'] + w_counter * bytes_per_transfer
                    df.at[idx, 'addr'] = resolved_addr
                    w_counter += 1

                    if row.get('last') == 1:
                        current_aw = None
                        w_counter = 0
                else:
                    raise_exception(RuntimeError,
                        f"[{row.get('source_file')}] Found W entry without preceding AW at {row.get('time')} ps")

        return df


    def apply_field_filters(self, df_subset, **kwargs):
        """
        Helper method to apply key-value filters to a DataFrame subset.
        Hex strings are automatically converted to integers.

        Parameters:
            df_subset (pd.DataFrame): DataFrame to filter.
            kwargs: Field filters.

        Returns:
            pd.DataFrame: Filtered DataFrame.
        """
        for key, val in kwargs.items():
            if key not in df_subset.columns:
                raise_exception(ValueError, f"Column '{key}' not found in DataFrame.")

            if isinstance(val, str) and val.startswith('0x'):
                try:
                    val = int(val, 16)
                except ValueError:
                    raise_exception(ValueError, f"Invalid hex value for {key}: '{val}'")

            df_subset = df_subset[df_subset[key] == val]

        return df_subset.reset_index(drop=True)


    def select_aw(self, **kwargs):
        """
        Selects AW transactions which match field filters.

        Returns:
            pd.DataFrame: Filtered AW transactions.
        """
        df_aw = self.df[self.df['type'] == 'AW']
        return self.apply_field_filters(df_aw, **kwargs)


    def select_w(self, **kwargs):
        """
        Selects W transactions which match field filters.

        Returns:
            pd.DataFrame: Filtered W transactions.
        """
        df_w = self.df[self.df['type'] == 'W']
        return self.apply_field_filters(df_w, **kwargs)


    def filter_transactions(self, tx_type, **kwargs):
        """
        Filters transactions by type and additional field criteria.

        Parameters:
            tx_type (str): Transaction type ('AW', 'W', etc).
            kwargs: Additional field filters (e.g., addr='0x70000000').

        Returns:
            pd.DataFrame: Filtered subset of transactions.
        """
        tx_type = tx_type.upper()

        if tx_type == "AW":
            return self.select_aw(**kwargs)
        elif tx_type == "W":
            return self.select_w(**kwargs)
        else:
            raise_exception(ValueError, f"Unsupported transaction type '{tx_type}'")

