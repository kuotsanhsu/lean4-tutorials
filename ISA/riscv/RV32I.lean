namespace riscv.RV32I

@[inline]
def ofIType («imm[11:0]» : BitVec 12) (rs1 : BitVec 5) (funct3 : BitVec 3) (rd : BitVec 5) :=
  UInt32.ofBitVec <| «imm[11:0]» ++ rs1 ++ funct3 ++ rd ++ 0b001_0011#7

inductive IType : UInt32 → Prop
  | addi  imm src dest : IType <| ofIType imm src 0b000 dest
  | slti  imm src dest : IType <| ofIType imm src 0b010 dest
  | sltiu imm src dest : IType <| ofIType imm src 0b011 dest
  | xori  imm src dest : IType <| ofIType imm src 0b100 dest
  | ori   imm src dest : IType <| ofIType imm src 0b110 dest
  | andi  imm src dest : IType <| ofIType imm src 0b111 dest
  | slli  (shamt : BitVec 5) src dest : IType <| ofIType (0#7 ++ shamt) src 0b001 dest
  | srli  (shamt : BitVec 5) src dest : IType <| ofIType (0#7 ++ shamt) src 0b101 dest
  | srai  (shamt : BitVec 5) src dest : IType <| ofIType (0x20#7 ++ shamt) src 0b101 dest

@[inline]
def ofUType («imm[31:12]» : BitVec 20) (rd : BitVec 5) (opcode : BitVec 7) :=
  UInt32.ofBitVec <| «imm[31:12]» ++ rd ++ opcode

inductive UType : UInt32 → Prop
  | lui   imm dest : UType <| ofUType imm dest 0b011_0111#7
  | auipc imm dest : UType <| ofUType imm dest 0b001_0111#7

@[inline]
def ofRType (funct7 : BitVec 7) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3) (rd : BitVec 5) :=
  UInt32.ofBitVec <| funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ 0b011_0011#7

inductive RType : UInt32 → Prop
  | add  src2 src1 dest : RType <| ofRType    0 src2 src1 0b000 dest
  | sub  src2 src1 dest : RType <| ofRType 0x20 src2 src1 0b000 dest
  | sll  src2 src1 dest : RType <| ofRType    0 src2 src1 0b001 dest
  | slt  src2 src1 dest : RType <| ofRType    0 src2 src1 0b010 dest
  | sltu src2 src1 dest : RType <| ofRType    0 src2 src1 0b011 dest
  | xor  src2 src1 dest : RType <| ofRType    0 src2 src1 0b100 dest
  | srl  src2 src1 dest : RType <| ofRType    0 src2 src1 0b101 dest
  | sra  src2 src1 dest : RType <| ofRType 0x20 src2 src1 0b101 dest
  | or   src2 src1 dest : RType <| ofRType    0 src2 src1 0b110 dest
  | and  src2 src1 dest : RType <| ofRType    0 src2 src1 0b111 dest

def nop := IType.addi 0 0 0

inductive SType : UInt32 → Prop

inductive IsInstruction (i : UInt32) : Prop
  | ofIType (_ : IType i)
  | ofUType (_ : UType i)
  | ofRType (_ : RType i)

namespace IsInstruction

instance : Coe (IType i) (IsInstruction i) where coe := ofIType
instance : Coe (UType i) (IsInstruction i) where coe := ofUType
instance : Coe (RType i) (IsInstruction i) where coe := ofRType

-- export IType (addi slti sltiu xori ori andi slli srli srai)
-- export UType (lui auipc)
export RType (add sub sll slt sltu xor srl sra or and)

end IsInstruction

def Instruction := Subtype IsInstruction

@[inline] def opcode (i : UInt32) : BitVec 7 := i.toBitVec.extractLsb'  0 7
@[inline] def rd     (i : UInt32) : BitVec 5 := i.toBitVec.extractLsb'  7 5
@[inline] def «imm[31:12]» (i : UInt32) : BitVec 20 := i.toBitVec.extractLsb' 12 20
@[inline] def funct3 (i : UInt32) : BitVec 3 := i.toBitVec.extractLsb' 12 3
@[inline] def rs1    (i : UInt32) : BitVec 5 := i.toBitVec.extractLsb' 15 5
@[inline] def «imm[11:0]» (i : UInt32) : BitVec 12 := i.toBitVec.extractLsb' 20 12
@[inline] def rs2    (i : UInt32) : BitVec 5 := i.toBitVec.extractLsb' 20 5
@[inline] def funct7 (i : UInt32) : BitVec 7 := i.toBitVec.extractLsb' 25 7

theorem aux {v w} (x : BitVec v) (y : BitVec w) : (x ++ y).extractLsb' 0 w  = y.extractLsb' 0 w :=
  -- BitVec.extractLsb'_append_eq_of_add_le <| show 0 + w ≤ w by simp
  by grind

theorem aux_eq (i : UInt32) :
    UInt32.ofBitVec (funct7 i ++ rs2 i ++ rs1 i ++ funct3 i ++ rd i ++ opcode i) = i :=
  let x := i.toBitVec
  UInt32.eq_of_toBitVec_eq <|
  calc funct7 i ++ rs2 i ++ rs1 i ++ funct3 i ++ rd i ++ opcode i
   _ = «imm[11:0]» i ++ rs1 i ++ funct3 i ++ rd i ++ opcode i
    := congrArg (· ++ _ ++ _ ++ _ ++ _) <| x.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
   _ = x.extractLsb' 15 17 ++ funct3 i ++ rd i ++ opcode i
    := congrArg (· ++ _ ++ _ ++ _) <| x.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
   _ = «imm[31:12]» i ++ rd i ++ opcode i
    := congrArg (· ++ _ ++ _) <| x.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
   _ = x.extractLsb' 7 25 ++ opcode i
    := congrArg (· ++ _) <| x.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
   _ = x.extractLsb' 0 32 := x.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
   _ = x := x.extractLsb'_eq_self

section
variable {i : UInt32}

theorem IType.opcode_eq : IType i → opcode i = 0b001_0011
  | h => by cases h <;> exact aux _ 0b001_0011#7

theorem UType.opcode_eq : UType i → opcode i = 0b011_0111 ∨ opcode i = 0b001_0111
  | lui .. => .inl (aux _ 0b011_0111#7)
  | auipc .. => .inr (aux _ 0b001_0111#7)

theorem RType.opcode_eq : RType i → opcode i = 0b011_0011
  | h => by cases h <;> exact aux _ 0b011_0011#7

theorem ofIType_self (h : opcode i = 0b001_0011) :
    ofIType («imm[11:0]» i) (rs1 i) (funct3 i) (rd i) = i :=
  sorry

theorem ofUType_self : ofUType («imm[31:12]» i) (rd i) (opcode i) = i :=
  let x := i.toBitVec
  UInt32.eq_of_toBitVec_eq <|
  calc x.extractLsb' 12 20 ++ rd i ++ opcode i
    _ = x.extractLsb' 7 25 ++ opcode i
    := congrArg (· ++ opcode i) <| BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
    _ = x.extractLsb' 0 32 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
    _ = x := BitVec.extractLsb'_eq_self

theorem ofRType_self (h : opcode i = 0b011_0011) :
    ofRType (funct7 i) (rs2 i) (rs1 i) (funct3 i) (rd i) = i :=
  calc UInt32.ofBitVec (_ ++ 0b011_0011#7)
   _ = UInt32.ofBitVec (_ ++ opcode i) := h ▸ rfl
   _ = i := aux_eq i

end

instance decIsInstruction : DecidablePred IsInstruction := fun i =>
  -- let opcode := i &&& 0b111_1111
  -- have e : opcode.toBitVec = (i.toBitVec.extractLsb' 0 7).setWidth' (by decide) := sorry
  let opcode := opcode i
  if hI : opcode = 0b001_0011 then
    let funct3 := funct3 i
    have : UInt32.ofBitVec (_ ++ _ ++ funct3 ++ _ ++ _) = i := ofIType_self hI
    match f3 : funct3 with
    | 0b000 => isTrue <| show IType i from this ▸ .addi  ..
    | 0b010 => isTrue <| show IType i from this ▸ .slti  ..
    | 0b011 => isTrue <| show IType i from this ▸ .sltiu ..
    | 0b100 => isTrue <| show IType i from this ▸ .xori  ..
    | 0b110 => isTrue <| show IType i from this ▸ .ori   ..
    | 0b111 => isTrue <| show IType i from this ▸ .andi  ..
    | 0b001 =>
      let funct7 := funct7 i
      if f7 : funct7 = 0 then
        suffices _ from isTrue <| show IType i from this ▸ f7 ▸ f3 ▸ hI ▸ .slli ..
        show UInt32.ofBitVec (funct7 ++ _ ++ _ ++ funct3 ++ _ ++ opcode) = i from aux_eq i
      else
        isFalse sorry
    | 0b101 =>
      let funct7 := funct7 i
      match f7 : funct7 with
      | 0    => suffices _ from isTrue <| show IType i from this ▸ f7 ▸ f3 ▸ hI ▸ .srli ..
        show UInt32.ofBitVec (funct7 ++ _ ++ _ ++ funct3 ++ _ ++ opcode) = i from aux_eq i
      | 0x20 => suffices _ from isTrue <| show IType i from this ▸ f7 ▸ f3 ▸ hI ▸ .srai ..
        show UInt32.ofBitVec (funct7 ++ _ ++ _ ++ funct3 ++ _ ++ opcode) = i from aux_eq i
      | _ => isFalse sorry
  else if hU : opcode = 0b011_0111 ∨ opcode = 0b001_0111 then
    suffices UType i from isTrue this
    let imm := «imm[31:12]» i
    let dest := rd i
    have e : ofUType imm dest opcode = i := ofUType_self
    suffices UType (ofUType imm dest opcode) from e.rec this
    hU.rec (· ▸ .lui imm dest) (· ▸ .auipc imm dest)
  else if hR : opcode = 0b011_0011 then
    let funct7 := funct7 i
    if f7 : funct7 = 0 then
      let funct3 := funct3 i
      have :=
        calc UInt32.ofBitVec (0#7 ++ rs2 i ++ rs1 i ++ funct3 ++ rd i ++ 0b011_0011#7)
         _ = UInt32.ofBitVec (funct7 ++ _ ++ _ ++ _ ++ _ ++ opcode) := f7 ▸ hR ▸ rfl
         _ = i := aux_eq i
      match funct3 with
      | 0b000 => isTrue <| show RType i from this ▸ .add  ..
      | 0b001 => isTrue <| show RType i from this ▸ .sll  ..
      | 0b010 => isTrue <| show RType i from this ▸ .slt  ..
      | 0b011 => isTrue <| show RType i from this ▸ .sltu ..
      | 0b100 => isTrue <| show RType i from this ▸ .xor  ..
      | 0b101 => isTrue <| show RType i from this ▸ .srl  ..
      | 0b110 => isTrue <| show RType i from this ▸ .or   ..
      | 0b111 => isTrue <| show RType i from this ▸ .and  ..
    else if funct7 = 0x20 then
      let funct3 := funct3 i
      if funct3 = 0 ∨ funct3 = 0b101 then
        isTrue sorry
      else
        isFalse sorry
    else
      isFalse sorry
  else
    isFalse fun
    | .ofIType h => hI h.opcode_eq
    | .ofUType h => hU h.opcode_eq
    | .ofRType h => hR h.opcode_eq

structure Instruction.Visitor (m) [Monad m] (α) where
  -- IType
  addi  (imm   : BitVec 12) (src dest : BitVec 5) : m α
  slti  (imm   : BitVec 12) (src dest : BitVec 5) : m α
  sltiu (imm   : BitVec 12) (src dest : BitVec 5) : m α
  xori  (imm   : BitVec 12) (src dest : BitVec 5) : m α
  ori   (imm   : BitVec 12) (src dest : BitVec 5) : m α
  andi  (imm   : BitVec 12) (src dest : BitVec 5) : m α
  slli  (shamt : BitVec  5) (src dest : BitVec 5) : m α
  srli  (shamt : BitVec  5) (src dest : BitVec 5) : m α
  srai  (shamt : BitVec  5) (src dest : BitVec 5) : m α
  -- UType
  lui   (imm : BitVec 20) (dest : BitVec 5) : m α
  auipc (imm : BitVec 20) (dest : BitVec 5) : m α
  -- RType
  add   (src2 src1 dest : BitVec 5) : m α
  sub   (src2 src1 dest : BitVec 5) : m α
  sll   (src2 src1 dest : BitVec 5) : m α
  slt   (src2 src1 dest : BitVec 5) : m α
  sltu  (src2 src1 dest : BitVec 5) : m α
  xor   (src2 src1 dest : BitVec 5) : m α
  srl   (src2 src1 dest : BitVec 5) : m α
  sra   (src2 src1 dest : BitVec 5) : m α
  or    (src2 src1 dest : BitVec 5) : m α
  and   (src2 src1 dest : BitVec 5) : m α
  -- Error
  unknown (i : UInt32) : m α

#check List.map
#check List.mapM
#check IO.println

#check_failure Instruction.rec

def Instruction.rec.{u} {motive : Instruction → Sort u}
    (add : (src2 src1 dest : BitVec 5) → motive ⟨ofRType    0 src2 src1 0b000 dest, .add src2 src1 dest⟩)
  : (i : Instruction) → motive i := sorry

def Instruction.disassemblyVisitor {m} [Monad m] : Visitor m String where
  -- IType
  addi  imm   rs  rd := pure s!"addi    {rd}, {rs}, {imm}"
  slti  imm   rs  rd := pure s!"slti    {rd}, {rs}, {imm}"
  sltiu imm   rs  rd := pure s!"sltiu   {rd}, {rs}, {imm}"
  xori  imm   rs  rd := pure s!"xori    {rd}, {rs}, {imm}"
  ori   imm   rs  rd := pure s!"ori     {rd}, {rs}, {imm}"
  andi  imm   rs  rd := pure s!"andi    {rd}, {rs}, {imm}"
  slli  shamt rs  rd := pure s!"slli    {rd}, {rs}, {shamt}"
  srli  shamt rs  rd := pure s!"srli    {rd}, {rs}, {shamt}"
  srai  shamt rs  rd := pure s!"srai    {rd}, {rs}, {shamt}"
  -- UType
  lui   imm       rd := pure s!"lui     {rd}, {imm}"
  auipc imm       rd := pure s!"auipc   {rd}, {imm}"
  -- RType
  add   rs2   rs1 rd := pure s!"add     {rd}, {rs1}, {rs2}"
  sub   rs2   rs1 rd := pure s!"sub     {rd}, {rs1}, {rs2}"
  sll   rs2   rs1 rd := pure s!"sll     {rd}, {rs1}, {rs2}"
  slt   rs2   rs1 rd := pure s!"slt     {rd}, {rs1}, {rs2}"
  sltu  rs2   rs1 rd := pure s!"sltu    {rd}, {rs1}, {rs2}"
  xor   rs2   rs1 rd := pure s!"xor     {rd}, {rs1}, {rs2}"
  srl   rs2   rs1 rd := pure s!"srl     {rd}, {rs1}, {rs2}"
  sra   rs2   rs1 rd := pure s!"sra     {rd}, {rs1}, {rs2}"
  or    rs2   rs1 rd := pure s!"or      {rd}, {rs1}, {rs2}"
  and   rs2   rs1 rd := pure s!"and     {rd}, {rs1}, {rs2}"
  -- Error
  unknown i := pure "bad"

section
#check Nat.rec

def Instruction.recAux.{u} {motive : UInt32 → Sort u}
    (known : (i : Instruction) → motive i.val)
    (unknown : (i : UInt32) → motive i)
    (i : UInt32) : motive i := unknown i

end

def Instruction.decode? (i : UInt32) : Option Instruction :=
  if h : IsInstruction i then some ⟨i, h⟩ else none

def Instruction.Visitor.visit {m} [Monad m] {α} (visitor : Visitor m α) (i : UInt32) : m α := do
  sorry

def Instruction.disassemble (i : UInt32) : IO Unit := do
  IO.println (← disassemblyVisitor.visit i)

def main : IO Unit :=
  let code : List UInt32 := [0, 1, 2]
  code.forM Instruction.disassemble
