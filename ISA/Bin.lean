import Lean.LocalContext
/-!

- [opaque](https://lean-lang.org/doc/reference/latest/Definitions/Definitions/#Lean___Parser___Command___declaration-next-next-next-next-next-next-next-next-next-next-next)
- [implemented_by](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#Lean___Parser___Attr___simple)
- [StateT](https://leanprover.github.io/functional_programming_in_lean/monad-transformers/transformers.html#state)
- https://llvm.org/docs/LangRef.html#instruction-reference
- https://en.wikipedia.org/wiki/X86#Structure
- https://en.wikipedia.org/wiki/FLAGS_register
- https://www.felixcloutier.com/x86/

-/
namespace X64

opaque Byte : Type -- := UInt8
structure Word where (highByte lowByte : Byte)
structure Dword where (highWord lowWord : Word)
structure Qword where (highDword lowDword : Dword)

#check UInt16.toUInt8
#check Lean.LocalDecl.isLet

structure RegisterFile where
  (rax rbx rcx rdx r8 r9 r10 r11 r12 r13 r14 r15 : Qword)
  (cs ds ss es fs gs : Word)
  (rsp rbp : Qword)
  (rsi rdi : Qword)
  (rip : Qword)
  (cf pf af zf sf tf «if» df of iopl nt md rf vm ac vif vip id ai : Bool)

namespace RegisterFile
variable (self : RegisterFile)

def eax : Dword := self.rax.lowDword
def  ax :  Word := self.eax.lowWord
def  ah :  Byte :=  self.ax.highByte
def  al :  Byte :=  self.ax.lowByte

def ebx : Dword := self.rbx.lowDword
def  bx :  Word := self.ebx.lowWord
def  bh :  Byte :=  self.bx.highByte
def  bl :  Byte :=  self.bx.lowByte

def ecx : Dword := self.rcx.lowDword
def  cx :  Word := self.ecx.lowWord
def  ch :  Byte :=  self.cx.highByte
def  cl :  Byte :=  self.cx.lowByte

def edx : Dword := self.rdx.lowDword
def  dx :  Word := self.edx.lowWord
def  dh :  Byte :=  self.dx.highByte
def  dl :  Byte :=  self.dx.lowByte

def r8d : Dword := self.r8.lowDword
def r8w :  Word := self.r8d.lowWord
def r8b :  Byte := self.r8w.lowByte

def r9d : Dword := self.r9.lowDword
def r9w :  Word := self.r9d.lowWord
def r9b :  Byte := self.r9w.lowByte

def r10d : Dword := self.r10.lowDword
def r10w :  Word := self.r10d.lowWord
def r10b :  Byte := self.r10w.lowByte

def r11d : Dword := self.r11.lowDword
def r11w :  Word := self.r11d.lowWord
def r11b :  Byte := self.r11w.lowByte

def r12d : Dword := self.r12.lowDword
def r12w :  Word := self.r12d.lowWord
def r12b :  Byte := self.r12w.lowByte

def r13d : Dword := self.r13.lowDword
def r13w :  Word := self.r13d.lowWord
def r13b :  Byte := self.r13w.lowByte

def r14d : Dword := self.r14.lowDword
def r14w :  Word := self.r14d.lowWord
def r14b :  Byte := self.r14w.lowByte

def r15d : Dword := self.r15.lowDword
def r15w :  Word := self.r15d.lowWord
def r15b :  Byte := self.r15w.lowByte

def esp : Dword := self.rsp.lowDword
def  sp :  Word := self.esp.lowWord
def  spl : Byte :=  self.sp.lowByte

def ebp : Dword := self.rbp.lowDword
def  bp :  Word := self.ebp.lowWord
def  bpl : Byte :=  self.bp.lowByte

def esi : Dword := self.rsi.lowDword
def  si :  Word := self.esi.lowWord
def  sil : Byte :=  self.si.lowByte

def edi : Dword := self.rdi.lowDword
def  di :  Word := self.edi.lowWord
def  dil : Byte :=  self.di.lowByte

def eip : Dword := self.rip.lowDword
def  ip :  Word := self.eip.lowWord

end RegisterFile

def Byte.add : Byte → Byte → Byte × Bool := sorry
def Word.add : Word → Word → Word × Bool := sorry
def Dword.add : Dword → Dword → Dword × Bool := sorry
def Qword.add : Qword → Qword → Qword × Bool := sorry

def Byte.zeroExtendToWord : Byte → Word := sorry
def Byte.signExtendToWord : Byte → Word × Bool := sorry
def Byte.zeroExtendToDword : Byte → Dword := sorry
def Byte.signExtendToDword : Byte → Dword × Bool := sorry
def Byte.zeroExtendToQword : Byte → Qword := sorry
def Byte.signExtendToQword : Byte → Qword × Bool := sorry

def Word.zeroExtendToDword : Word → Dword := sorry
def Word.signExtendToDword : Word → Dword × Bool := sorry
def Word.zeroExtendToQword : Word → Qword := sorry
def Word.signExtendToQword : Word → Qword × Bool := sorry

def Dword.zeroExtendToQword : Dword → Qword := sorry
def Dword.signExtendToQword : Dword → Qword × Bool := sorry

inductive Qreg
  | rax | rbx | rcx | rdx
  -- | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  -- | rsp | rbp
  -- | rsi | rdi
  -- | rip

def addq {m} [Monad m] (rd rs1 rs2 : Qreg) : StateT RegisterFile m Unit := do
  let regs ← get
  let (sum, cf) := Qword.add (getReg regs rs1) (getReg regs rs2)
  match rd with
  | .rax => modify fun regs => {regs with rax := sum, cf}
  | .rbx => modify fun regs => {regs with rbx := sum, cf}
  | .rcx => modify fun regs => {regs with rcx := sum, cf}
  | .rdx => modify fun regs => {regs with rdx := sum, cf}
  where
    getReg (regs : RegisterFile) : Qreg → Qword
      | .rax => regs.rax
      | .rbx => regs.rbx
      | .rcx => regs.rcx
      | .rdx => regs.rdx

section

inductive Bin'
  | nil
  | zed (b : Bin')
  | one (b : Bin')

inductive Bin
  | nil
  | pos (b : Bin')

def Bin'.toNat : Bin' → Nat
  | nil => 1
  | zed b => 2 * b.toNat
  | one b => 2 * b.toNat + 1

def Bin.toNat : Bin → Nat
  | nil => 0
  | pos b => b.toNat

def Bin'.succ : Bin' → Bin'
  | nil => nil.zed
  | zed b => b.one
  | one b => b.succ.zed

def Bin.succ : Bin → Bin
  | nil => pos .nil
  | pos b => pos b.succ

def Bin.ofNat : Nat → Bin
  | 0 => nil
  | n + 1 => (ofNat n).succ


theorem Bin.ofNat_of_toNat_eq_self : {b : Bin} → ofNat b.toNat = b
  | nil => rfl
  | pos b =>
    calc ofNat b.toNat
     _ = pos b := sorry

theorem Bin'.toNat_of_succ_eq_succ_of_toNat : {b : Bin'} → b.succ.toNat = b.toNat + 1
  | nil
  | zed _ => rfl
  | one b =>
    show 2 * b.succ.toNat = 2 * (b.toNat + 1) from congrArg _ toNat_of_succ_eq_succ_of_toNat

theorem Bin.toNat_of_succ_eq_succ_of_toNat : {b : Bin} → b.succ.toNat = b.toNat + 1
  | nil => rfl
  | pos b => show b.succ.toNat = b.toNat + 1 from b.toNat_of_succ_eq_succ_of_toNat

theorem Bin.toNat_of_ofNat_eq_self : {n : Nat} → (ofNat n).toNat = n
  | 0 => rfl
  | n + 1 =>
    calc (ofNat n).succ.toNat
     _ = (ofNat n).toNat + 1 := toNat_of_succ_eq_succ_of_toNat
     _ = n + 1 := congrArg _ toNat_of_ofNat_eq_self

theorem Bin.ofNat_of_succ_eq_succ_of_ofNat : {n : Nat} → ofNat (n + 1) = (ofNat n).succ := rfl

end
