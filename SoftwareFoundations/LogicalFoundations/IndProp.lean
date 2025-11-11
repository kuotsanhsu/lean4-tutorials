import SoftwareFoundations.LogicalFoundations.Induction
import SoftwareFoundations.LogicalFoundations.Lists

/-! # Inductively Defined Propositions

## Inductively Defined Propositions

In the `Logic` chapter, we looked at several ways of writing propositions, including conjunction, disjunction, and existential quantification.

In this chapter, we bring yet another new tool into the mix: *inductively defined propositions*.

To begin, some examples...

### Example: The Collatz Conjecture

The *Collatz Conjecture* is a famous open problem in number theory.

Its statement is quite simple. First, we define a function `csf` on numbers, as follows (where `csf` stands for "Collatz step function"):
-/

namespace Nat

mutual
  inductive Even : Nat → Prop
    | zero : Even 0
    | succ {n} : Odd n → Even (n + 1)

  inductive Odd : Nat → Prop
    | succ {n} : Even n → Odd (n + 1)
end

theorem even_or_odd : {n : Nat} → Even n ∨ Odd n
  | 0 => .inl .zero
  | n + 1 => n.even_or_odd.imp .succ .succ |>.symm

theorem not_even_and_odd : {n : Nat} → ¬(Even n ∧ Odd n)
  | _ + 1, ⟨.succ odd, .succ even⟩ => not_even_and_odd ⟨even, odd⟩

example n : ¬Even n ↔ Odd n where
  mp hn := even_or_odd.elim hn.elim id
  mpr odd even := not_even_and_odd ⟨even, odd⟩

example n : ¬Odd n ↔ Even n where
  mp hn := even_or_odd.elim id hn.elim
  mpr even odd := not_even_and_odd ⟨even, odd⟩

example : ¬Odd 0 := nofun

mutual
  theorem not_even_iff_odd {n} : ¬Even n ↔ Odd n := ⟨mp, mpr⟩ where
    mp : {n : Nat} → ¬Even n → Odd n
      | 0, hn => absurd .zero hn
      | n + 1, (hn : ¬Even (n + 1)) => .succ <| not_odd_iff_even.mp <| show ¬Odd n from hn ∘ .succ
    mpr : {n : Nat} → Odd n → ¬Even n
      | n + 1, .succ (h : Even n), .succ (h' : Odd n) => mpr h' h

  theorem not_odd_iff_even {n} : ¬Odd n ↔ Even n := ⟨mp, mpr⟩ where
    mp : {n : Nat} → ¬Odd n → Even n
      | 0, _ => .zero
      | n + 1, (hn : ¬Odd (n + 1)) => .succ <| not_even_iff_odd.mp <| show ¬Even n from hn ∘ .succ
    mpr : {n : Nat} → Even n → ¬Odd n
      | n + 1, .succ (h : Odd n), .succ (h' : Even n) => mpr h' h
end

theorem even_of_succ_iff_odd {n : Nat} : Even (n + 1) ↔ Odd n := ⟨fun (.succ h) => h, .succ⟩
theorem odd_of_succ_iff_even {n : Nat} : Odd (n + 1) ↔ Even n where
  mp | .succ h => h
  mpr := .succ

mutual
  instance decEven : DecidablePred Even
    | 0 => isTrue Even.zero
    | n + 1 =>
      match n.decOdd with
      | isTrue h => isTrue <| Even.succ h
      | isFalse hn => isFalse <| hn ∘ even_of_succ_iff_odd.mp

  instance decOdd : DecidablePred Odd
    | 0 => isFalse nofun
    | n + 1 =>
      match n.decEven with
      | isTrue h => isTrue <| Odd.succ h
      | isFalse hn => isFalse <| hn ∘ odd_of_succ_iff_even.mp
end

theorem even_imp_double : {n : Nat} → Even n → ∃ m : Nat, m.double = n
  | 0, _ => ⟨0, rfl⟩
  | _ + 2, .succ (.succ hn) =>
    let ⟨m, hm⟩ := even_imp_double hn
    ⟨m + 1, hm ▸ double_of_succ⟩

theorem plus_two_even {n : Nat} : Even (n + 2) ↔ Even n where
  mp h := match n, h with
    | 0, _ => .zero
    | _ + 2, .succ (.succ h) => h
  mpr := .succ ∘ .succ

theorem plus_two_odd {n : Nat} : Odd (n + 2) ↔ Odd n :=
  (iff_congr even_of_succ_iff_odd even_of_succ_iff_odd).mp plus_two_even

example : {n : Nat} → Odd (n + 2) ↔ Odd n := ⟨mp, .succ ∘ .succ⟩ where
  mp : {n : Nat} → Odd (n + 2) → Odd n
    | 1, _ => .succ .zero
    | _ + 2, .succ (.succ h) => h

theorem double_is_even : (n : Nat) → Even n.double
  | 0 => .zero
  | n + 1 =>
    have : Even (n.double + 2) := plus_two_even.mpr n.double_is_even
    double_of_succ ▸ this

def halve : (n : Nat) → Even n → Nat
  | 0, _ => 0
  | n + 2, h => n.halve (plus_two_even.mp h) + 1

theorem double_of_halve : {n : Nat} → (h : Even n) → (n.halve h).double = n
  | 0, _ => rfl
  | n + 2, h =>
    calc (n.halve _ + 1).double
     _ = (n.halve _).double + 2 := double_of_succ
     _ = n + 2 := congrArg (· + 2) <| double_of_halve (plus_two_even.mp h)

def div2 : Nat → Nat
  | n + 2 => n.div2 + 1
  | _ => 0

-- QUESTION: can one define a custom recursive principle from `Even` and `Odd`?

end Nat

example (n : Nat) : Nat := if n.Even then n.div2 else n * 3 + 1
def csf (n : Nat) : Nat := if h : n.Even then n.halve h else n * 3 + 1

partial def Collatz_sequence : Nat → List Nat
  | 0 => []
  | 1 => [1]
  | n => n::Collatz_sequence (csf n)

example : Collatz_sequence 0 = [] := by native_decide
example : Collatz_sequence 1 = [1] := by native_decide
example : Collatz_sequence 12 = [12, 6, 3, 10, 5, 16, 8, 4, 2, 1] := by native_decide
example : Collatz_sequence 19 =
  [19, 58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1] := by native_decide

inductive Collatz_holds_for : Nat → Prop
  | one : Collatz_holds_for 1
  | even {n} (h : n.Even) : Collatz_holds_for (n.halve h) → Collatz_holds_for n
  | odd {n} (h : n.Odd) : Collatz_holds_for (n * 3 + 1) → Collatz_holds_for n

example : Collatz_holds_for 12 :=
  suffices Collatz_holds_for  6 from .even parity12 this
  suffices Collatz_holds_for  3 from .even parity6  this
  suffices Collatz_holds_for 10 from .odd  parity3  this
  suffices Collatz_holds_for  5 from .even parity10 this
  suffices Collatz_holds_for 16 from .odd  parity5  this
  suffices Collatz_holds_for  8 from .even parity16 this
  suffices Collatz_holds_for  4 from .even parity8  this
  suffices Collatz_holds_for  2 from .even parity4  this
  suffices Collatz_holds_for  1 from .even parity2  this
  .one
where
  parity2  : Nat.Even  2 := .zero    |> .succ |> .succ
  parity3  : Nat.Odd   3 := parity2  |> .succ
  parity4  : Nat.Even  4 := parity3  |> .succ
  parity5  : Nat.Odd   5 := parity4  |> .succ
  parity6  : Nat.Even  6 := parity5  |> .succ
  parity8  : Nat.Even  8 := parity6  |> .succ |> .succ
  parity10 : Nat.Even 10 := parity8  |> .succ |> .succ
  parity12 : Nat.Even 12 := parity10 |> .succ |> .succ
  parity16 : Nat.Even 16 := parity12 |> .succ |> .succ |> .succ |> .succ

example : Collatz_holds_for 12 :=
  suffices Collatz_holds_for  6 from .even (by decide+kernel) this
  suffices Collatz_holds_for  3 from .even (by decide+kernel) this
  suffices Collatz_holds_for 10 from .odd  (by decide+kernel) this
  suffices Collatz_holds_for  5 from .even (by decide+kernel) this
  suffices Collatz_holds_for 16 from .odd  (by decide+kernel) this
  suffices Collatz_holds_for  8 from .even (by decide+kernel) this
  suffices Collatz_holds_for  4 from .even (by decide+kernel) this
  suffices Collatz_holds_for  2 from .even (by decide+kernel) this
  suffices Collatz_holds_for  1 from .even (by decide+kernel) this
  .one

theorem Collatz {n : Nat} : n ≠ 0 → Collatz_holds_for n := sorry

#print Nat.le
example : 3 ≤ 5 := .step (.step (.refl : 3 ≤ 3) : 3 ≤ 4)

/-! ### Example: Transitive Closure -/

#check Relation.TransGen
inductive clos_trans (r : α → α → Prop) : α → α → Prop
  | step : r x y → clos_trans r x y
  | trans : clos_trans r x y → clos_trans r y z → clos_trans r x z

inductive Person | Sage | Cleo | Ridley | Moss
namespace Person

inductive parent_of : Person → Person → Prop
  | Cleo   : Sage.parent_of Cleo
  | Ridley : Sage.parent_of Ridley
  | Moss   : Cleo.parent_of Moss

def ancestor_of : Person → Person → Prop := clos_trans parent_of

example : Sage.ancestor_of Moss := .trans (.step parent_of.Cleo) (.step parent_of.Moss)

local instance : Trans ancestor_of ancestor_of ancestor_of where trans := .trans
local instance {parent child : Person} : Coe (parent.parent_of child) (parent.ancestor_of child)
  where coe := .step

example : Sage.ancestor_of Moss :=
  calc
    Sage.ancestor_of Cleo := parent_of.Cleo
    Cleo.ancestor_of Moss := parent_of.Moss

example : Sage.ancestor_of Moss :=
  calc            Sage
    ancestor_of _ Cleo := parent_of.Cleo
    ancestor_of _ Moss := parent_of.Moss

end Person

/-! ### Example: Reflexive and Transitive Closure -/

inductive clos_refl_trans (r : α → α → Prop) : α → α → Prop
  | step : r x y → clos_refl_trans r x y
  | refl : clos_refl_trans r x x
  | trans : clos_refl_trans r x y → clos_refl_trans r y z → clos_refl_trans r x z

def cs (m n : Nat) : Prop := csf m = n

def cms := clos_refl_trans cs

theorem Collatz' {n : Nat} : n ≠ 0 → cms n 1 := sorry

example : cms 16 1 := .trans
  (  show cms 16 4 from .trans
    (show cms 16 8 from .step <| show csf 16 = 8 from rfl)
    (show cms  8 4 from .step <| show csf  8 = 4 from rfl)
  ) (show cms  4 1 from .trans
    (show cms  4 2 from .step <| show csf  4 = 2 from rfl)
    (show cms  2 1 from .step <| show csf  2 = 1 from rfl)
  )

inductive clos_refl_symm_trans (r : α → α → Prop) : α → α → Prop
  | step : r x y → clos_refl_symm_trans r x y
  | refl : clos_refl_symm_trans r x x
  | symm : clos_refl_symm_trans r x y → clos_refl_symm_trans r y x
  | trans : clos_refl_symm_trans r x y → clos_refl_symm_trans r y z → clos_refl_symm_trans r x z

/-! ### Example: Permutations -/

namespace List

inductive Perm3 {α} : List α → List α → Prop
  | swap12 {a b c : α} : Perm3 [a, b, c] [b, a, c]
  | swap23 {a b c : α} : Perm3 [a, b, c] [a, c, b]
  | trans {as bs cs : List α} : Perm3 as bs → Perm3 bs cs → Perm3 as cs

example : Perm3 [1, 2, 3] [3, 2, 1] := .trans (.trans .swap12 .swap23) .swap12

example : Perm3 [1, 2, 3] [1, 2, 3] := .trans .swap12 .swap12

end List

/-! ### Example: Evenness (yet again) -/

namespace Nat

inductive ev : Nat → Prop
  | zero : ev 0
  | succ_succ {n} : ev n → ev n.succ.succ

#check (.zero : ev 0)
#check (.succ_succ : ∀ {n}, ev n → ev n.succ.succ)

example : ev 4 := ev.zero.succ_succ.succ_succ

example {n : Nat} : ev n → ev (n + 4) := .succ_succ ∘ .succ_succ

theorem ev_double : {n : Nat} → ev n.double
  | 0 => .zero
  | n + 1 => double_of_succ ▸ show (n.double + 2).ev from ev.succ_succ n.ev_double

end Nat

/-! ### Constructing Evidence for Permutations -/

namespace List

local instance {α} : Trans (@Perm3 α) Perm3 Perm3 where trans := .trans

example : Perm3 [1, 2, 3] [2, 3, 1] :=
  calc      [1, 2, 3]
    Perm3 _ [2, 1, 3] := .swap12
    Perm3 _ [2, 3, 1] := .swap23

example {a b c : α} : Perm3 [a, b, c] [a, b, c] := .trans .swap12 .swap12

end List

/-!
## Using Evidence in Proofs

### Destructing and Inverting Evidence
-/

namespace Nat

theorem ev_inversion {n : Nat} : n.ev → n = 0 ∨ ∃ m, n = m + 2 ∧ m.ev
  | .zero => .inl rfl
  | .succ_succ h => .inr ⟨_, rfl, h⟩

theorem le_inversion {m n : Nat} : m ≤ n → m = n ∨ ∃ k, n = k + 1 ∧ m ≤ k
  | .refl => .inl rfl
  | .step h => .inr ⟨_, rfl, h⟩

example {n : Nat} : (n + 2).ev → n.ev := fun (.succ_succ h) => h

example : ¬ev 1 := nofun

example {n : Nat} : (n + 4).ev → n.ev := fun (.succ_succ (.succ_succ h)) => h

example : ev 5 → 2 + 2 = 9 := nofun

example : {a b c : Nat} → [a, b] = [c, c] → [a] = [b] | _, _, _, rfl => rfl

example : {n : Nat} → n + 1 = 0 → 2 + 2 = 5 := nofun

/-! ### Induction on Evidence -/

theorem ev_Even {n : Nat} : n.ev → ∃ m : Nat, n = m.double
  | .zero => ⟨0, rfl⟩
  | .succ_succ h => have ⟨_, k⟩ := ev_Even h ; ⟨_, double_of_succ ▸ congrArg (· + 2) k⟩

theorem ev_Even_iff {n : Nat} : n.ev ↔ ∃ m : Nat, n = m.double := ⟨ev_Even, Even_ev⟩ where
  Even_ev : {n : Nat} → (∃ m : Nat, n = m.double) → n.ev
    | _, ⟨0, rfl⟩ => .zero
    | _, ⟨m + 1, h⟩ => have k := trans h double_of_succ ; k ▸ (Even_ev ⟨m, rfl⟩).succ_succ

theorem ev_sum {m n : Nat} : m.ev → n.ev → (m + n).ev
  | hm, .zero => hm
  | hm, .succ_succ hn => .succ_succ (ev_sum hm hn)

theorem ev_ev__ev {m n : Nat} : (m + n).ev → m.ev → n.ev
  | h => aux <| show (n + m).ev from m.add_comm n ▸ h
where aux {m : Nat} : {n : Nat} → (m + n).ev → n.ev → m.ev
  | _, h, .zero => h
  | n + 2, .succ_succ h, .succ_succ hn => aux h hn

theorem ev_plus_plus {a b c : Nat} : (a + b).ev → (a + c).ev → (b + c).ev
  | hab, hac =>
    suffices (a + a + (b + c)).ev from ev_ev__ev this (ev_Even_iff.mpr ⟨a, rfl⟩)
    suffices (a + b + (a + c)).ev from Nat.add_add_add_comm .. ▸ this
    ev_sum hab hac

inductive ev' : Nat → Prop
  | zero : ev' 0
  | two : ev' 2
  | sum : ev' m → ev' n → ev' (m + n)

theorem ev'_ev {n} : ev' n ↔ ev n := ⟨mp, mpr⟩ where
  mp {n} : ev' n → ev n | .zero => .zero | .two => .succ_succ .zero | .sum h h' => ev_sum (mp h) (mp h')
  mpr {n} : ev n → ev' n | .zero => .zero | .succ_succ h => .sum (mpr h) .two

end Nat

namespace List
variable {α}

theorem Perm3.symm {l₁ l₂ : List α} : Perm3 l₁ l₂ → Perm3 l₂ l₁
  | .swap12 => .swap12 | .swap23 => .swap23 | .trans h₁ h₂ => .trans h₂.symm h₁.symm

theorem Perm3.mem {x : α} {l₁ l₂ : List α} : Perm3 l₁ l₂ → x ∈ l₁ → x ∈ l₂
  | .trans h₁ h₂, h => h₂.mem (h₁.mem h)
  | .swap12, .tail _ (.head _)
  | .swap23, .head _ => .head _
  | .swap12, .head _
  | .swap23, .tail _ (.tail _ (.head _)) => .tail _ (.head _)
  | .swap12, .tail _ (.tail _ (.head _))
  | .swap23, .tail _ (.head _) => .tail _ (.tail _ (.head _))

theorem Perm3.not_mem {x : α} {l₁ l₂ : List α} : Perm3 l₁ l₂ → x ∉ l₁ → x ∉ l₂
  | h, h₁, h₂ => h₁ (h.symm.mem h₂)

example : ¬Perm3 [1, 2, 3] [1, 2, 4]
  | h =>
    suffices 3 ∈ [1, 2, 4] from nomatch this
    suffices 3 ∈ [1, 2, 3] from h.mem this
    .tail 1 (.tail 2 (.head []))

example : 3 ∈ [1, 2, 3] := by decide
example : 3 ∉ [1, 2, 4] := by decide
example : 3 ∉ [1, 2, 4] := nofun
example : ¬@Perm3 α [] [] := sorry

end List

/-! ## Exercising with Inductive Relations -/

#print Nat.le

example : 3 ≤ 3 := .refl
example : 3 ≤ 6 := Nat.le.refl.step.step.step
example : 2 ≤ 1 → 2 + 2 = 5 := nofun

#print Nat.lt
#check GE.ge

#check Nat.le_trans
theorem le_trans {a b c : Nat} (h : a ≤ b) : b ≤ c → a ≤ c
  | .refl => h
  | .step h' => (le_trans h h').step

theorem O_le_n : {n : Nat} → 0 ≤ n
  | 0 => .refl
  | _ + 1 => O_le_n.step

section
set_option autoImplicit false
variable {a b c : Nat}

example : a ≤ b → b ≤ c → a ≤ c := (Nat.le.rec · fun _ => .step)
example : 0 ≤ a := a.rec .refl fun _ => .step
theorem n_le_m__Sn_le_Sm : a ≤ b → a + 1 ≤ b + 1 := Nat.le.rec .refl fun _ => .step
example : a + 1 ≤ b + 1 → a ≤ b := Nat.le.rec sorry fun _ => id

theorem Sn_le_Sm__n_le_m : {b : Nat} → a + 1 ≤ b + 1 → a ≤ b
  | _, .refl => .refl
  | _, .step h => le_trans Nat.le.refl.step h

theorem le_plus_l : a ≤ a + b := b.rec .refl fun _ => .step
theorem le_plus_r : a ≤ b + a := Nat.add_comm .. ▸ le_plus_l
theorem plus_le : a + b ≤ c → a ≤ c ∧ b ≤ c :=
  Nat.le.rec ⟨le_plus_l, le_plus_r⟩ fun _ h => ⟨h.1.step, h.2.step⟩
theorem plus_le_cases : {b d : Nat} → a + b ≤ c + d → a ≤ c ∨ b ≤ d
  | _, 0, h => .inl (plus_le h).1
  | 0, _, _ => .inr O_le_n
  | _ + 1, _ + 1, h => plus_le_cases (Sn_le_Sm__n_le_m h) |>.imp id n_le_m__Sn_le_Sm

theorem plus_le_compat_l : a ≤ b → c + a ≤ c + b := Nat.le.rec .refl fun _ => .step
theorem plus_le_compat_r : a ≤ b → a + c ≤ b + c := c.rec id fun _ hi h => n_le_m__Sn_le_Sm (hi h)
example (h : a ≤ b) : a + c ≤ b + c :=
  calc a + c
   _ = c + a := Nat.add_comm ..
   _ ≤ c + b := plus_le_compat_l h
   _ = b + c := Nat.add_comm ..

theorem le_plus_trans : a ≤ b → a ≤ b + c := c.rec id fun _ hi h => .step (hi h)

end
