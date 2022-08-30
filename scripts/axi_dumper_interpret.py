# Copyright (c) 2020 ETH Zurich, University of Bologna
# All rights reserved.
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.

# Interpretation script for axi_dumper log files.
# This script can be used to help with finding issues in the AXI transactions along a BUS.

import ast
import argparse


# Expand strobe to bits from bytes
def expand_strb(strb, num_bytes):
    output = 0
    for i in range(num_bytes):
        if strb & 1 << i:
            output |= 0xFF << (8 * i)
    return output


# Split burst into individual transactions
def burst_splitter(stat_list):
    new_list = []
    data_sum = 0
    for stat in stat_list:
        data_sum += len(stat['data'])
        for i in range(stat['len'] + 1):
            newstat = { 'start' : stat['start'],
                        'end'   : stat['end'],
                        'addr'  : stat['addr'] + (2**stat['size'])*i,
                        'data'  : stat['data'][i],
                      }
            if 'strb' in stat.keys():
                newstat['strb'] = stat['strb'][i]
            new_list.append(newstat)
    return new_list


# Recombine subsequent identical requests with different strobes
def recombine_identical(stat_list, num_bytes):
    new_list = []
    for stat in stat_list:
        if len(new_list) > 0 and new_list[-1]['addr'] == stat['addr']:
            if 'strb' in stat.keys():
                if ~(new_list[-1]['strb'] & stat['strb']):
                    new_list[-1]['data'] = (new_list[-1]['data'] & expand_strb(new_list[-1]['strb'], num_bytes)) | (stat['data'] & expand_strb(stat['strb'], num_bytes))
                    new_list[-1]['strb'] = new_list[-1]['strb'] | stat['strb']
                else:
                    new_list.append(stat)
            else:
                continue
        else:
            new_list.append(stat)
    # TODO: shrink also based on size?
    return new_list


# Validate all reads based on AR, and R
def validate_read(ar_list, r_list):
    stat_list = []

    r_index_list = {}
    for ar_index in range(len(ar_list)):
        ar = ar_list[ar_index]
        stat = { 'start' : 0,
                 'end'   : 0,
                 'addr'  : 0,
                 'len'   : 0,
                 'size'  : 0,
                 'data'  : [],
                }
        stat['start'] = ar['time']
        stat['len'] = ar['len']
        stat['addr'] = ar['addr']
        stat['size'] = ar['size']
        stat['data'] = []

        ar_id = ar['id']
        if ar_id in r_index_list:
            r_index = r_index_list[ar_id]
        else:
            r_index = 0
        for i in range(stat['len'] + 1):
            while r_list[r_index]['id'] != ar_id:
                r_index += 1
                if (r_index >= len(r_list)):
                    print("No R remaining for {}".format(ar))
                    print("Current state: {}".format(stat))
                    print("{} AR remaining".format(len(ar_list)-ar_index-1))
                    return stat_list
            stat['data'].append(r_list[r_index]['data'])
            if (r_list[r_index]['last'] and (i != stat['len'])) or \
               ((i == stat['len']) and (not r_list[r_index]['last'])):
                print("R last and length mismatch for {}".format(ar))
                print("Current state: ".format(stat))
                print("ARs")
                for j in range(-2, 3):
                    print(ar_list[ar_index + j])
                    print("Rs")
                for j in range(-19, 20):
                    print(r_list[r_index + j])
                return stat_list
            if (r_list[r_index]['last'] and (i == stat['len'])):
                stat['end'] = r_list[r_index]['time']
            r_index += 1
            if (r_index >= len(r_list)):
                print("No R remaining for {}".format(ar))
                print("Current state: {}".format(stat))
                print("{} AR remaining".format(len(ar_list)-ar_index-1))
                return stat_list
        stat_list.append(stat)
        r_index_list[ar_id] = r_index
    return stat_list


# Validate all writes based on AW, W, and B
def validate_write(aw_list, w_list, b_list):
    stat_list = []

    w_index = 0        # W are always in order of AW as no ID available
    b_index_list = {}  # To sort for ID
    for aw_index in range(len(aw_list)):
        aw = aw_list[aw_index]
        stat = { 'start' : 0,
                'end'   : 0,
                'addr'  : 0,
                'len'   : 0,
                'size'  : 0,
                'data'  : [],
                'strb'  : [],
            }
        stat['start'] = aw['time']
        stat['len'] = aw['len']
        stat['addr'] = aw['addr']
        stat['size'] = aw['size']
        stat['data'] = []
        aw_id = aw['id']
        if aw_id in b_index_list:
            b_index = b_index_list[aw_id]
        else:
            b_index = 0
        for i in range(stat['len'] + 1):
            if (w_index >= len(w_list)):
                print("No W remaining for {}".format(aw))
                print("Current state: {}".format(stat))
                print("{} AW remaining".format(len(aw_list)-aw_index-1))
                return stat_list
            stat['data'].append(w_list[w_index]['data'])
            stat['strb'].append(w_list[w_index]['strb'])
            if (w_list[w_index]['last'] and (i != stat['len'])) or \
               ((i == stat['len']) and (not w_list[w_index]['last'])):
                print("W last and length mismatch for {}".format(aw))
                print("Current state: {}".format(stat))
                return stat_list
            if w_list[w_index]['last'] and (i == stat['len']):
                while b_list[b_index]['id'] != aw_id:
                    b_index += 1
                if (b_index >= len(b_list)):
                    print("No B remaining for {}".format(aw))
                    print("Current state: {}".format(stat))
                    print("{} AW remaining".format(len(aw_list)-aw_index-1))
                    return stat_list
                stat['end'] = b_list[b_index]['time']
                b_index += 1
            w_index += 1
        b_index_list[aw_id] = b_index
        stat_list.append(stat)
    return stat_list


# funtion to trace file
def trace_file(filename, num_bytes):
    axi_dict = { 'type'   : '',
                 'time'   : 0,
                 'id'     : 0,
                 'addr'   : 0,
                 'len'    : 0,
                 'size'   : 0,
                 'burst'  : 0,
                 'lock'   : 0,
                 'cache'  : 0,
                 'prot'   : 0,
                 'qos'    : 0,
                 'region' : 0,
                 'atop'   : 0,
                 'user'   : 0,
                 'data'   : 0,
                 'strb'   : 0,
                 'last'   : 0,
                 'resp'   : 0,
               }

    aw_list = []
    ar_list = []
    w_list = []
    r_list = []
    b_list = []

    aw_hex = 0x4157  # AW in ASCII
    ar_hex = 0x4152  # AR in ASCII
    w_hex = 0x57     # W  in ASCII
    r_hex = 0x52     # R  in ASCII
    b_hex = 0x42     # B  in ASCII

    with open(filename, 'r') as trace_file:
        i = 0
        for line in trace_file:
            i += 1
            try: 
                trace_dict = ast.literal_eval(line)
            except:
                print("dict parsing failed")
                break

            if trace_dict["type"] == aw_hex or trace_dict["type"] == "AW":
                aw_list.append(trace_dict)
            elif trace_dict["type"] == ar_hex or trace_dict["type"] == "AR":
                ar_list.append(trace_dict)
            elif trace_dict["type"] == w_hex or trace_dict["type"] == "W":
                w_list.append(trace_dict)
            elif trace_dict["type"] == r_hex or trace_dict["type"] == "R":
                r_list.append(trace_dict)
            elif trace_dict["type"] == b_hex or trace_dict["type"] == "B":
                b_list.append(trace_dict)
            else:
                print("type ERROR")
                break
            # if (i > 4000000): break
            # print(trace_dict)
        # TODO: split reads per ID
        read_stats = validate_read(ar_list, r_list)
        write_stats = validate_write(aw_list, w_list, b_list)
        split_reads = burst_splitter(read_stats)
        split_writes = burst_splitter(write_stats)
        recomb_reads = recombine_identical(split_reads, num_bytes)
        recomb_writes = recombine_identical(split_writes, num_bytes)
        print("Successfully processed:")
        print("\treads:  {} ARs, {} Rs, {} shrunk accesses".format(len(read_stats), len(split_reads), len(recomb_reads)))
        print("\twrites: {} AWs, {} Ws, {} shrunk accesses".format(len(write_stats), len(split_writes), len(recomb_writes)))
        print("Total in list:")
        print("\treads:  {} ARs, {} Rs".format(len(ar_list), len(r_list)))
        print("\twrites: {} AWs, {} Ws, {} Bs".format(len(aw_list), len(w_list), len(b_list)))
    return (recomb_reads, recomb_writes)


if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='Analyze an axi trace.')
    parser.add_argument('axi_trace_log', metavar='axi_trace_log', type=str,
                        help='the raw log file emitted by axi dumper.')
    parser.add_argument('num_bytes', metavar='num_bytes', type=int, default=8,
                        help='number of bytes in a data word')

    args = parser.parse_args()

    trace_file(args.axi_trace_log, args.num_bytes)
