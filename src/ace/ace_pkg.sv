// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
// Copyright (c) 2022 PlanV GmbH
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


//! ACE Package
/// Contains all necessary type definitions, constants, and generally useful functions.
package ace_pkg;

  //////////////
  // Typedefs //
  //////////////

  // Additional types for already existing AXI channels
  typedef logic [3:0] arsnoop_t;
  typedef logic [2:0] awsnoop_t;
  typedef logic [1:0] axbar_t;
  typedef logic [1:0] axdomain_t;
  typedef logic [3:0] rresp_t;
  typedef logic [0:0] awunique_t;

  // Snoop related types
  typedef logic [3:0] acsnoop_t;
  typedef logic [2:0] acprot_t;

  typedef struct packed {
    logic WasUnique;
    logic IsShared;
    logic PassDirty;
    logic Error;
    logic DataTransfer;
  } crresp_t;

  typedef struct packed {
    acsnoop_t snoop_trs;
    logic accepts_dirty;
    logic accepts_dirty_shared;
    logic accepts_shared;
  } snoop_info_t;

  ///////////////
  // Encodings //
  ///////////////

  // AxDOMAIN
  localparam axdomain_t NonShareable   = 2'b00;
  localparam axdomain_t InnerShareable = 2'b01;
  localparam axdomain_t OuterShareable = 2'b10;
  localparam axdomain_t System         = 2'b11;


  // AxBAR
  localparam axbar_t NormalAccessRespectingBarriers = 2'b00;
  localparam axbar_t MemoryBarrier                  = 2'b01;
  localparam axbar_t NormalAccessIgnoringBarriers   = 2'b10;
  localparam axbar_t SynchronizationBarrier         = 2'b11;

  // Uniquely defined here both for ARSNOOP and AWSNOOP
  localparam int unsigned Barrier = 0;

  // ARSNOOP
  localparam arsnoop_t ReadNoSnoop        = 4'b0000;
  localparam arsnoop_t ReadOnce           = 4'b0000;
  localparam arsnoop_t ReadShared         = 4'b0001;
  localparam arsnoop_t ReadClean          = 4'b0010;
  localparam arsnoop_t ReadNotSharedDirty = 4'b0011;
  localparam arsnoop_t ReadUnique         = 4'b0111;
  localparam arsnoop_t CleanUnique        = 4'b1011;
  localparam arsnoop_t MakeUnique         = 4'b1100;
  localparam arsnoop_t CleanShared        = 4'b1000;
  localparam arsnoop_t CleanInvalid       = 4'b1001;
  localparam arsnoop_t MakeInvalid        = 4'b1101;
  localparam arsnoop_t DVMComplete        = 4'b1110;
  localparam arsnoop_t DVMMessage         = 4'b1111;
  /* Barrier is already defined */

  // AWSNOOP
  localparam awsnoop_t WriteNoSnoop    = 3'b000;
  localparam awsnoop_t WriteUnique     = 3'b000;
  localparam awsnoop_t WriteLineUnique = 3'b001;
  localparam awsnoop_t WriteClean      = 3'b010;
  localparam awsnoop_t WriteBack       = 3'b011;
  localparam awsnoop_t Evict           = 3'b100;
  localparam awsnoop_t WriteEvict      = 3'b101;
  /* Barrier is already defined */

  // ACSNOOP
  //
  //  The encoding is shared with ARSNOOP transactions for the following cases:
  //    - ReadOnce
  //    - ReadShared
  //    - ReadClean
  //    - ReadNotSharedDirty
  //    - ReadUnique
  //    - CleanShared
  //    - CleanInvalid
  //    - MakeInvalid
  //    - DVMComplete
  //    - DVMMessage
  //  Cast the parameters to acsnoop_t for consistency (but works anyway)

  //////////////////
  // Domain rules //
  //////////////////

  localparam int unsigned MaxMasterNum  = 16;
  localparam int unsigned MasterIdxBits = $clog2(MaxMasterNum);

  typedef struct packed {
        logic [MasterIdxBits-1:0] InnerShareableNum;
        logic [MaxMasterNum-1:0][MasterIdxBits-1:0] InnerShareableList;
        logic [MasterIdxBits-1:0] OuterShareableNum;
        logic [MaxMasterNum-1:0][MasterIdxBits-1:0] OuterShareableList;
  } domain_rule_t;

endpackage
