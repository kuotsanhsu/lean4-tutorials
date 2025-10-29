import SoftwareFoundations.LogicalFoundations.Basics

namespace Bin

/-- `Theorem bin_to_nat_pres_incr : ∀ b : bin, bin_to_nat (incr b) = 1 + bin_to_nat b.` -/
theorem toNat_of_succ_eq_succ_of_toNat : {b : Bin} → b.succ.toNat = b.toNat + 1
  | nil | zed _ => rfl
  | one b =>
    calc b.succ.toNat.double
     _ = (b.toNat + 1).double := congrArg _ b.toNat_of_succ_eq_succ_of_toNat
     _ = b.toNat.double + 2 := Nat.add_add_add_comm ..

/-- `Fixpoint nat_to_bin (n:nat) : bin` -/
def ofNat : Nat → Bin
  | 0 => nil
  | n + 1 => (ofNat n).succ

/-- `Theorem nat_bin_nat : ∀ n, bin_to_nat (nat_to_bin n) = n.` -/
theorem toNat_of_ofNat : {n : Nat} → (ofNat n).toNat = n
  | 0 => rfl
  | n + 1 =>
    calc (ofNat n).succ.toNat
     _ = (ofNat n).toNat + 1 := toNat_of_succ_eq_succ_of_toNat
     _ = n + 1 := congrArg _ toNat_of_ofNat

end Bin

example {n : Nat} : n + 2 = n + 1 + 1 := rfl

/-- `Lemma double_incr : ∀ n : nat, double (S n) = S (S (double n)).` -/
theorem Nat.double_of_succ : {n : Nat} → (n + 1).double = n.double + 2
  | 0 => rfl
  | n + 1 => Nat.add_add_add_comm (n + 1) 1 (n + 1) 1

namespace Bin

/-- `Definition double_bin (b:bin) : bin` -/
def double : Bin → Bin
  | nil => nil
  | b => b.zed

/-- `Example double_bin_zero : double_bin Z = Z.` -/
example : nil.double = nil := rfl

/-- `Lemma double_incr_bin : ∀ b, double_bin (incr b) = incr (incr (double_bin b)).` -/
theorem double_of_succ : {b : Bin} → b.succ.double = b.double.succ.succ
  | nil | zed _ | one _ => rfl

/-- `Theorem bin_nat_bin_fails : ∀ b, nat_to_bin (bin_to_nat b) = b.` -/
example : ¬∀ b : Bin, ofNat b.toNat = b
  | h => nomatch show nil = nil.zed from h nil.zed

/-- `Fixpoint normalize (b:bin) : bin` -/
def normalize : Bin → Bin
  | nil => nil
  | zed b => b.normalize.double
  | one b => b.normalize.one

example : nil.normalize = nil := rfl
example : nil.zed.normalize = nil := rfl
example : nil.zed.zed.normalize = nil := rfl
example : nil.zed.zed.zed.normalize = nil := rfl
example : nil.zed.zed.one.normalize = nil.one := rfl
example : nil.zed.zed.zed.one.zed.one.normalize = nil.one.zed.one := rfl
example : nil.one.normalize = nil.one := rfl
example : nil.one.zed.zed.one.normalize = nil.one.zed.zed.one := rfl

theorem ofNat_of_double : {n : Nat} → ofNat n.double = (ofNat n).double
  | 0 => rfl
  | n + 1 =>
    calc ofNat (n + 1).double
     _ = ofNat (n.double + 2) := congrArg ofNat Nat.double_of_succ
     _ = (ofNat n.double).succ.succ := rfl
     _ = (ofNat n).double.succ.succ := congrArg (·.succ.succ) ofNat_of_double
     _ = (ofNat n).succ.double := double_of_succ.symm
     _ = (ofNat (n + 1)).double := rfl

theorem succ_of_double : {b : Bin} → b.double.succ = b.one
  | nil | zed _ | one _ => rfl

/-- `Theorem bin_nat_bin : ∀ b, nat_to_bin (bin_to_nat b) = normalize b.` -/
theorem ofNat_of_toNat : {b : Bin} → ofNat b.toNat = b.normalize
  | nil => rfl
  | zed b => aux
  | one b =>
    calc (ofNat b.toNat.double).succ
     _ = b.normalize.double.succ := congrArg succ aux
     _ = b.normalize.one := succ_of_double
where
  aux {b : Bin} :=
    calc ofNat b.toNat.double
    _ = (ofNat b.toNat).double := ofNat_of_double
    _ = b.normalize.double := congrArg double ofNat_of_toNat

end Bin
