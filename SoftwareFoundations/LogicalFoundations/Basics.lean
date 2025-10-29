/-! # Functional Programming in Coq
-/

/-! ## Binary Numerals
-/

example {n : Nat} : n * 2 = 0 + n + n := rfl

def Nat.double (n : Nat) : Nat := n + n

/-- `Inductive bin : Type` -/
inductive Bin
  | nil
  | zed (b : Bin)
  | one (b : Bin)

namespace Bin

--               LSB                         MSB
example : Bin :=                             nil -- 0
example : Bin :=                      one <| nil -- 1
example : Bin :=               zed <| one <| nil -- 2
example : Bin :=               one <| one <| nil -- 3
example : Bin :=        zed <| zed <| one <| nil -- 4
example : Bin :=        one <| zed <| one <| nil -- 5
example : Bin :=        zed <| one <| one <| nil -- 6
example : Bin :=        one <| one <| one <| nil -- 7
example : Bin := zed <| zed <| zed <| one <| nil -- 8

--               MSB             LSB
example : Bin :=                 nil -- 0
example : Bin :=             nil.one -- 1
example : Bin :=         nil.one.zed -- 2
example : Bin :=         nil.one.one -- 3
example : Bin :=     nil.one.zed.zed -- 4
example : Bin :=     nil.one.zed.one -- 5
example : Bin :=     nil.one.one.zed -- 6
example : Bin :=     nil.one.one.one -- 7
example : Bin := nil.one.zed.zed.zed -- 8

/-- `Fixpoint incr (m:bin) : bin` -/
def succ : Bin → Bin
  | nil => nil.one
  | zed b => b.one
  | one b => b.succ.zed

/-- `Fixpoint bin_to_nat (m:bin) : nat` -/
def toNat : Bin → Nat
  | nil => 0
  | zed b => b.toNat.double
  | one b => b.toNat.double + 1

/-- test_bin_incr1 -/
example : nil.one.succ = nil.one.zed := rfl
/-- test_bin_incr2 -/
example : nil.one.zed.succ = nil.one.one := rfl
/-- test_bin_incr3 -/
example : nil.one.one.succ = nil.one.zed.zed := rfl
/-- test_bin_incr4 -/
example : nil.one.zed.toNat = 2 := rfl
/-- test_bin_incr5 -/
example : nil.one.succ.toNat = nil.one.toNat + 1 := rfl
/-- test_bin_incr6 -/
example : nil.one.succ.succ.toNat = nil.one.toNat + 2 := rfl

end Bin
