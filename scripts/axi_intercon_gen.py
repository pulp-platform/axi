#!/usr/bin/env python3
import math
import sys
from collections import OrderedDict, defaultdict
import yaml

from verilogwriter import Signal, Wire, Instance, ModulePort, Port, VerilogWriter

if sys.version[0] == '2':

    math.log2 = lambda x : math.log(x, 2)

class Widths:
    addr = 0
    user = 0
    data = 0
    max_id = 0

def axi_signals(w, id_width):
    signals = [
        ("aw", "id"    , False, id_width),
        ("aw", "addr"  , False, w.addr  ),
        ("aw", "len"   , False, 8  ),
        ("aw", "size"  , False, 3  ),
        ("aw", "burst" , False, 2 ),
        ("aw", "lock"  , False, 0 ),
        ("aw", "cache" , False, 4 ),
        ("aw", "prot"  , False, 3 ),
        ("aw", "region", False, 4),
        ("aw", "user"  , False, w.user),
        ("aw", "qos"   , False, 4),
        ("aw", "atop"  , False, 6),
        ("aw", "valid" , False, 0),
        ("aw", "ready" , True , 0),

        ("ar", "id"    , False, id_width),
        ("ar", "addr"  , False, w.addr),
        ("ar", "len"   , False, 8),
        ("ar", "size"  , False, 3),
        ("ar", "burst" , False, 2),
        ("ar", "lock"  , False, 0),
        ("ar", "cache" , False, 4),
        ("ar", "prot"  , False, 3),
        ("ar", "region", False, 4),
        ("ar", "user"  , False, w.user),
        ("ar", "qos"   , False, 4),
        ("ar", "valid" , False, 0),
        ("ar", "ready" , True , 0),

        ("w", "data" , False, w.data),
        ("w", "strb" , False, w.data//8),
        ("w", "last" , False, 0),
        ("w", "user"  , False, w.user),
        ("w", "valid", False, 0),
        ("w", "ready", True , 0),

        ("b", "id"   , True , id_width),
        ("b", "resp" , True , 2),
        ("b", "valid", True , 0),
        ("b", "user"  , True, w.user),
        ("b", "ready", False, 0),

        ("r", "id"   , True , id_width),
        ("r", "data" , True , w.data),
        ("r", "resp" , True , 2),
        ("r", "last" , True , 0),
        ("r", "user"  , True, w.user),
        ("r", "valid", True , 0),
        ("r", "ready", False, 0),
    ]
    return signals

def module_ports(w, intf, id_width, is_input):
    ports = []
    for (ch, name, _dir, width) in axi_signals(w, id_width):
        if name == 'user' and not w.user:
            continue
        if name == 'atop' and not w.atop:
            continue
        if ch in ['aw', 'w', 'b'] and intf.read_only:
            continue
        prefix = 'o' if is_input == _dir else 'i'
        ports.append(ModulePort("{}_{}_{}{}".format(prefix, intf.name, ch, name),
                                'output' if is_input == _dir else 'input',
                                width))
    return ports

def assigns(w, max_idw, masters, slaves):
    raw = '\n'
    i = 0
    for m in masters:
        raw += "   //Master {}\n".format(m.name)
        for (ch, name, _dir, width) in axi_signals(w, m.idw):
            if name in ['valid','ready']:
                _name = ch+'_'+name
            else:
                _name = ch+'.'+name
            if name == 'user' and not w.user:
                continue
            if _dir:
                if m.read_only and ((ch == 'aw') or (ch == 'w') or (ch == 'b')):
                    continue

                src = "masters_resp[{}].{}".format(i, _name)
                if ch in ['b', 'r'] and name == 'id' and m.idw < max_idw:
                    src = src+'[{}:0]'.format(m.idw-1)
                raw += "   assign o_{}_{}{} = {};\n".format(m.name, ch, name, src)
            else:
                src = "i_{}_{}{}".format(m.name, ch, name)
                if name == 'atop' and not w.atop:
                    src = "6'd0"
                if ch in ['ar', 'aw'] and name == 'id' and m.idw < max_idw:
                    src = "{"+ str(max_idw-m.idw)+"'d0,"+src+"}"
                if m.read_only and (ch in ['aw' , 'w', 'b']):
                    if ch == 'aw' and name == 'id':
                        _w = max_idw
                    else:
                        _w = max(1,width)
                    src = "{}'d0".format(_w)
                raw += "   assign masters_req[{}].{} = {};\n".format(i, _name, src)
        raw += "\n"
        i += 1

    i = 0
    for m in slaves:
        raw += "   //Slave {}\n".format(m.name)
        for (ch, name, _dir, width) in axi_signals(w, max_idw):
            if name == 'user' and not w.user:
                continue
            if name == 'atop' and not w.atop:
                continue
            if _dir:
                if name in ['valid','ready']:
                    _name = ch+'_'+name
                else:
                    _name = ch+'.'+name
                raw += "   assign slaves_resp[{}].{} = i_{}_{}{};\n".format(i, _name, m.name, ch, name)
            else:
                if name in ['valid','ready']:
                    _name = ch+'_'+name
                else:
                    _name = ch+'.'+name
                raw += "   assign o_{}_{}{} = slaves_req[{}].{};\n".format(m.name, ch, name, i, _name)
        i += 1
        raw += "\n"

    raw += "\n"
    return raw

def instance_ports(w, id_width, masters, slaves):
    ports = [Port('clk_i'  , 'clk_i'),
             Port('rst_ni', 'rst_ni'),
             Port('test_i', "1'b0"),
             Port('slv_ports_req_i' , 'masters_req'),
             Port('slv_ports_resp_o', 'masters_resp'),
             Port('mst_ports_req_o' , 'slaves_req'),
             Port('mst_ports_resp_i', 'slaves_resp'),
             Port('addr_map_i'      , 'AddrMap'),
             Port('en_default_mst_port_i', "{}'d0".format(len(masters))),
             Port('default_mst_port_i', "'0"),
    ]
    return ports

def template_ports(w, intf, id_width, is_input):
    ports = []
    for (ch, name, _dir, width) in axi_signals(w, id_width):
        if name == 'user' and not w.user:
            continue
        if name == 'atop' and not w.atop:
            continue
        if intf.read_only and ch in ['aw', 'w', 'b']:
            continue
        port_name = "{}_{}{}".format(intf.name, ch, name)
        prefix = 'o' if is_input == _dir else 'i'
        ports.append(Port("{}_{}".format(prefix, port_name), port_name))
    return ports

def template_wires(w, intf, id_width):
    wires = []
    for (ch, name, _dir, width) in axi_signals(w, id_width):
        if name == 'user' and not w.user:
            continue
        if name == 'atop' and not w.atop:
            continue
        if intf.read_only and ch in ['aw', 'w', 'b']:
            continue
        wires.append(Wire("{}_{}{}".format(intf.name, ch, name), width))
    return wires

class Master:
    def __init__(self, name, d=None):
        self.name = name
        self.slaves = []
        self.idw = 1
        self.read_only = False
        if d:
            self.load_dict(d)

    def load_dict(self, d):
        for key, value in d.items():
            if key == 'slaves':
                # Handled in file loading, ignore here
                continue
            if key == 'id_width':
                self.idw = value
            elif key == 'read_only':
                self.read_only = value
            else:
                print(key)
                raise UnknownPropertyError(
                    "Unknown property '%s' in master section '%s'" % (
                    key, self.name))

class Slave:
    def __init__(self, name, d=None):
        self.name = name
        self.masters = []
        self.offset = 0
        self.size = 0
        self.mask = 0
        self.read_only = False
        if d:
            self.load_dict(d)

    def load_dict(self, d):
        for key, value in d.items():
            if key == 'offset':
                self.offset = value
            elif key == 'size':
                self.size = value
                self.mask = ~(self.size-1) & 0xffffffff
            elif key == 'read_only':
                self.read_only = value
            else:
                raise UnknownPropertyError(
                    "Unknown property '%s' in slave section '%s'" % (
                    key, self.name))

class Parameter:
    def __init__(self, name, value):
        self.name  = name
        self.value = value



class AxiIntercon:
    def __init__(self, name, config_file):
        self.verilog_writer = VerilogWriter(name)
        self.template_writer = VerilogWriter(name)
        self.name = name
        d = OrderedDict()
        self.slaves = []
        self.masters = []
        import yaml

        def ordered_load(stream, Loader=yaml.Loader, object_pairs_hook=OrderedDict):
            class OrderedLoader(Loader):
                pass
            def construct_mapping(loader, node):
                loader.flatten_mapping(node)
                return object_pairs_hook(loader.construct_pairs(node))
            OrderedLoader.add_constructor(
                yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
                construct_mapping)
            return yaml.load(stream, OrderedLoader)
        data = ordered_load(open(config_file))

        config     = data['parameters']

        self.vlnv       = data['vlnv']

        for k,v in config['masters'].items():
            print("Found master " + k)
            self.masters.append(Master(k,v))
        for k,v in config['slaves'].items():
            print("Found slave " + k)
            self.slaves.append(Slave(k,v))

        self.output_file = config.get('output_file', 'axi_intercon.v')
        self.atop = config.get('atop', False)

    def _dump(self):
        print("*Masters*")
        for master in self.masters.values():
            print(master.name)
            for slave in master.slaves:
                print(' ' + slave.name)

        print("*Slaves*")
        for slave in self.slaves.values():
            print(slave.name)
            for master in slave.masters:
                print(' ' + master.name)

    def write(self):
        w = Widths()
        w.addr = 32
        w.data = 64
        w.user = 0
        w.atop = self.atop

        max_idw = max([m.idw for m in self.masters])
        max_sidw = max_idw + int(math.ceil(math.log2(len(self.masters))))
        file = self.output_file

        _template_ports = [Port('clk_i'  , 'clk'),
                           Port('rst_ni', 'rst_n')]
        template_parameters = []

        #Module header
        self.verilog_writer.add(ModulePort('clk_i'  , 'input'))
        self.verilog_writer.add(ModulePort('rst_ni', 'input'))
        for master in self.masters:
            for port in module_ports(w, master, master.idw, True):
                self.verilog_writer.add(port)
            for wire in template_wires(w, master, master.idw):
                self.template_writer.add(wire)
            _template_ports += template_ports(w, master, master.idw, True)

        for slave in self.slaves:
            for port in module_ports(w, slave, max_sidw, False):
                self.verilog_writer.add(port)
            for wire in template_wires(w, slave, max_sidw):
                self.template_writer.add(wire)
            _template_ports += template_ports(w, slave, max_sidw, False)

        raw = ""
        nm = len(self.masters)
        ns = len(self.slaves)

        raw += """
  localparam int unsigned NoMasters   = 32'd{};    // How many Axi Masters there are
  localparam int unsigned NoSlaves    = 32'd{};    // How many Axi Slaves  there are

  // axi configuration
  localparam int unsigned AxiIdWidthMasters =  32'd{};
  localparam int unsigned AxiIdUsed         =  32'd{}; // Has to be <= AxiIdWidthMasters
  localparam int unsigned AxiIdWidthSlaves  =  AxiIdWidthMasters + $clog2(NoMasters);
  localparam int unsigned AxiAddrWidth      =  32'd32;    // Axi Address Width
  localparam int unsigned AxiDataWidth      =  32'd64;    // Axi Data Width
  localparam int unsigned AxiStrbWidth      =  AxiDataWidth / 8;
  localparam int unsigned AxiUserWidth      =  1;
""".format(nm, ns, max_idw, max_idw)
        raw += "  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{\n"
        raw += """
    NoSlvPorts:         NoMasters,
    NoMstPorts:         NoSlaves,
    MaxMstTrans:        10,
    MaxSlvTrans:        6,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    AxiIdWidthSlvPorts: AxiIdWidthMasters,
    AxiIdUsedSlvPorts:  AxiIdUsed,
    UniqueIds:          1'b0,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        NoSlaves
"""
        raw += "  };\n"
        raw += """
  typedef logic [AxiIdWidthMasters-1:0] id_mst_t;
  typedef logic [AxiIdWidthSlaves-1:0]  id_slv_t;
  typedef logic [AxiAddrWidth-1:0]      addr_t;
  typedef axi_pkg::xbar_rule_32_t       rule_t; // Has to be the same width as axi addr
  typedef logic [AxiDataWidth-1:0]      data_t;
  typedef logic [AxiStrbWidth-1:0]      strb_t;
  typedef logic [AxiUserWidth-1:0]      user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_mst_t, id_mst_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_slv_t, id_slv_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_mst_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_mst_t, data_t, id_mst_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_slv_t, data_t, id_slv_t, user_t)

  `AXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_mst_t, w_chan_t, ar_chan_mst_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, b_chan_mst_t, r_chan_mst_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, b_chan_slv_t, r_chan_slv_t)

"""

        raw += "  localparam rule_t [{}:0] AddrMap = '".format(ns-1)
        raw += "{\n"
        i = 0
        rules = []
        for slave in self.slaves:
            rule = "    '{"
            rule += "idx: 32'd{}, start_addr: 32'h{:08x}, end_addr: 32'h{:08x}".format(i, slave.offset, slave.offset+slave.size)
            rule += "}"
            i += 1
            rules.append(rule)
        raw += ',\n'.join(rules)
        raw +=   "};\n"

        raw += "   slv_req_t  [{}:0] masters_req;\n".format(nm-1)
        raw += "   slv_resp_t [{}:0] masters_resp;\n".format(nm-1)

        raw += "   mst_req_t  [{}:0] slaves_req;\n".format(ns-1)
        raw += "   mst_resp_t [{}:0] slaves_resp;\n".format(ns-1)

        ns = len(self.slaves)

        raw += assigns(w, max_idw, self.masters, self.slaves)

        self.verilog_writer.raw = raw
        parameters = [
            Parameter('Cfg'          , 'xbar_cfg' ),
            Parameter('ATOPs'        , "1'b"+str(int(self.atop))),
            Parameter('slv_aw_chan_t', 'aw_chan_mst_t'),
            Parameter('mst_aw_chan_t', 'aw_chan_slv_t'),
            Parameter('w_chan_t'     , 'w_chan_t'     ),
            Parameter('slv_b_chan_t' , 'b_chan_mst_t' ),
            Parameter('mst_b_chan_t' , 'b_chan_slv_t' ),
            Parameter('slv_ar_chan_t', 'ar_chan_mst_t'),
            Parameter('mst_ar_chan_t', 'ar_chan_slv_t'),
            Parameter('slv_r_chan_t' , 'r_chan_mst_t' ),
            Parameter('mst_r_chan_t' , 'r_chan_slv_t' ),
            Parameter('slv_req_t'    , 'slv_req_t'    ),
            Parameter('slv_resp_t'   , 'slv_resp_t'   ),
            Parameter('mst_req_t'    , 'mst_req_t'    ),
            Parameter('mst_resp_t'   , 'mst_resp_t'   ),
            Parameter('rule_t'       , 'rule_t'       ),
        ]
        ports = instance_ports(w, max_idw, self.masters, self.slaves)

        self.verilog_writer.add(Instance('axi_xbar',
                                         'axi_xbar',
                                         parameters,
                                         ports))

        self.template_writer.add(Instance(self.name,
                                          self.name,
                                          template_parameters,
                                          _template_ports))

        self.verilog_writer.write(file)
        self.template_writer.write(file+'h')

        core_file = self.vlnv.split(':')[2]+'.core'
        vlnv = self.vlnv
        with open(core_file, 'w') as f:
            f.write('CAPI=2:\n')
            files = [{file     : {'file_type' : 'systemVerilogSource'}},
                     {file+'h' : {'is_include_file' : True,
                                  'file_type' : 'verilogSource'}}
            ]
            coredata = {'name' : vlnv,
                        'targets' : {'default' : {}},
            }

            coredata['filesets'] = {'rtl' : {'files' : files}}
            coredata['targets']['default']['filesets'] = ['rtl']

            f.write(yaml.dump(coredata))

if __name__ == "__main__":
    name = "axi_intercon"
    g = AxiIntercon(name, sys.argv[1])
    print("="*80)
    g.write()
