
@[inline]
def ofIType («imm[11:0]» : BitVec 12) (rs1 : BitVec 5) (funct3 : BitVec 3) (rd : BitVec 5) :=
  UInt32.ofBitVec <| «imm[11:0]» ++ rs1 ++ funct3 ++ rd ++ 0b001_0011#7

@[inline]
def ofUType («imm[31:12]» : BitVec 20) (rd : BitVec 5) (opcode : BitVec 7) :=
  UInt32.ofBitVec <| «imm[31:12]» ++ rd ++ opcode

@[inline]
def ofRType (funct7 : BitVec 7) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3) (rd : BitVec 5) :=
  UInt32.ofBitVec <| funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ 0b011_0011#7

inductive IsInstruction : UInt32 → Prop
  -- I-Type
  | addi  rd rs imm                : IsInstruction <| ofIType imm               rs 0b000 rd
  | slli  rd rs (shamt : BitVec 5) : IsInstruction <| ofIType (   0#7 ++ shamt) rs 0b001 rd
  | slti  rd rs imm                : IsInstruction <| ofIType imm               rs 0b010 rd
  | sltiu rd rs imm                : IsInstruction <| ofIType imm               rs 0b011 rd
  | xori  rd rs imm                : IsInstruction <| ofIType imm               rs 0b100 rd
  | srli  rd rs (shamt : BitVec 5) : IsInstruction <| ofIType (   0#7 ++ shamt) rs 0b101 rd
  | srai  rd rs (shamt : BitVec 5) : IsInstruction <| ofIType (0x20#7 ++ shamt) rs 0b101 rd
  | ori   rd rs imm                : IsInstruction <| ofIType imm               rs 0b110 rd
  | andi  rd rs imm                : IsInstruction <| ofIType imm               rs 0b111 rd
  -- U-Type
  | lui   rd imm : IsInstruction <| ofUType imm rd 0b011_0111#7
  | auipc rd imm : IsInstruction <| ofUType imm rd 0b001_0111#7
  -- R-Type
  | add  rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b000 rd
  | sub  rd rs1 rs2 : IsInstruction <| ofRType 0x20 rs2 rs1 0b000 rd
  | sll  rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b001 rd
  | slt  rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b010 rd
  | sltu rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b011 rd
  | xor  rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b100 rd
  | srl  rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b101 rd
  | sra  rd rs1 rs2 : IsInstruction <| ofRType 0x20 rs2 rs1 0b101 rd
  | or   rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b110 rd
  | and  rd rs1 rs2 : IsInstruction <| ofRType    0 rs2 rs1 0b111 rd

def Instruction := Subtype IsInstruction

namespace Instruction

section
variable (i : UInt32)

@[inline] def opcode       : BitVec  7 := i.toBitVec.extractLsb'  0  7
@[inline] def rd           : BitVec  5 := i.toBitVec.extractLsb'  7  5
@[inline] def «imm[31:12]» : BitVec 20 := i.toBitVec.extractLsb' 12 20
@[inline] def funct3       : BitVec  3 := i.toBitVec.extractLsb' 12  3
@[inline] def rs1          : BitVec  5 := i.toBitVec.extractLsb' 15  5
@[inline] def «imm[11:0]»  : BitVec 12 := i.toBitVec.extractLsb' 20 12
@[inline] def rs2          : BitVec  5 := i.toBitVec.extractLsb' 20  5
@[inline] def funct7       : BitVec  7 := i.toBitVec.extractLsb' 25  7

variable {i : UInt32}

theorem ofIType_self (h : opcode i = 0b001_0011) :
    ofIType («imm[11:0]» i) (rs1 i) (funct3 i) (rd i) = i :=
  sorry

end

structure Visitor.{u} (motive : Instruction → Sort u) where
  addi  : ∀ rd rs imm  , motive ⟨_, .addi  rd rs imm  ⟩
  slli  : ∀ rd rs shamt, motive ⟨_, .slli  rd rs shamt⟩
  slti  : ∀ rd rs imm  , motive ⟨_, .slti  rd rs imm  ⟩
  sltiu : ∀ rd rs imm  , motive ⟨_, .sltiu rd rs imm  ⟩
  xori  : ∀ rd rs imm  , motive ⟨_, .xori  rd rs imm  ⟩
  srli  : ∀ rd rs shamt, motive ⟨_, .srli  rd rs shamt⟩
  srai  : ∀ rd rs shamt, motive ⟨_, .srai  rd rs shamt⟩
  ori   : ∀ rd rs imm  , motive ⟨_, .ori   rd rs imm  ⟩
  andi  : ∀ rd rs imm  , motive ⟨_, .andi  rd rs imm  ⟩

protected def rec {motive} (visitor : Visitor motive) (i : Instruction) : motive i :=
  let ⟨i, hi⟩ := i
  let opcode := opcode i
  if hI : opcode = 0b001_0011 then
    let funct3 := funct3 i
    have {h} : motive ⟨ofIType _ _ funct3 _, h⟩ = motive ⟨i, hi⟩ :=
      congrArg motive (Subtype.ext (ofIType_self hI))
    match f3 : funct3 with
    | 0b000 => this.rec <| visitor.addi  ..
    | 0b010 => this.rec <| visitor.slti  ..
    | 0b011 => this.rec <| visitor.sltiu ..
    | 0b100 => this.rec <| visitor.xori  ..
    | 0b110 => this.rec <| visitor.ori   ..
    | 0b111 => this.rec <| visitor.andi  ..
    | 0b001 =>
      let funct7 := funct7 i
      if f7 : funct7 = 0 then
        sorry
      else
        sorry
    | 0b101 =>
      let funct7 := funct7 i
      sorry
  else if hU : opcode = 0b011_0111 ∨ opcode = 0b001_0111 then
    sorry
  else if hR : opcode = 0b011_0011 then
    let funct7 := funct7 i
    if f7 : funct7 = 0 then
      let funct3 := funct3 i
      match funct3 with
      | 0b000 => sorry
      | 0b001 => sorry
      | 0b010 => sorry
      | 0b011 => sorry
      | 0b100 => sorry
      | 0b101 => sorry
      | 0b110 => sorry
      | 0b111 => sorry
    else if funct7 = 0x20 then
      let funct3 := funct3 i
      if funct3 = 0 ∨ funct3 = 0b101 then
        sorry
      else
        sorry
    else
      sorry
  else
    sorry
  /-
  match i.property with
  -- I-Type
  | .addi  rd rs imm   => suffices ofIType imm rs 0 rd = i.val from sorry
    sorry
  | .slli  rd rs shamt => sorry
  | .slti  rd rs imm   => sorry
  | .sltiu rd rs imm   => sorry
  | .xori  rd rs imm   => sorry
  | .srli  rd rs shamt => sorry
  | .srai  rd rs shamt => sorry
  | .ori   rd rs imm   => sorry
  | .andi  rd rs imm   => sorry
  -- U-Type
  | .lui   rd imm => sorry
  | .auipc rd imm => sorry
  -- R-Type
  | .add  rd rs1 rs2 => sorry
  | .sub  rd rs1 rs2 => sorry
  | .sll  rd rs1 rs2 => sorry
  | .slt  rd rs1 rs2 => sorry
  | .sltu rd rs1 rs2 => sorry
  | .xor  rd rs1 rs2 => sorry
  | .srl  rd rs1 rs2 => sorry
  | .sra  rd rs1 rs2 => sorry
  | .or   rd rs1 rs2 => sorry
  | .and  rd rs1 rs2 => sorry
  -/

def disassembly : Visitor fun _ => String where
  addi  rd rs imm   := s!"addi    {rd}, {rs}, {imm}"
  slti  rd rs imm   := s!"slti    {rd}, {rs}, {imm}"
  sltiu rd rs imm   := s!"sltiu   {rd}, {rs}, {imm}"
  xori  rd rs imm   := s!"xori    {rd}, {rs}, {imm}"
  ori   rd rs imm   := s!"ori     {rd}, {rs}, {imm}"
  andi  rd rs imm   := s!"andi    {rd}, {rs}, {imm}"
  slli  rd rs shamt := s!"slli    {rd}, {rs}, {shamt}"
  srli  rd rs shamt := s!"srli    {rd}, {rs}, {shamt}"
  srai  rd rs shamt := s!"srai    {rd}, {rs}, {shamt}"

instance : ToString Instruction where
  toString := Instruction.rec disassembly
