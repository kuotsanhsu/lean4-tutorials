import Lake.Config.Meta
import Std.Tactic.Do.Syntax

/-! # Working with Structured Data
-/

/-! ## Pairs of Numbers
-/

inductive NatProd
  | pair (n₁ n₂ : Nat)

namespace NatProd

#check (pair 3 5 : NatProd)
def fst : NatProd → Nat | pair x _ => x
def snd : NatProd → Nat | pair _ y => y
#eval fst (pair 3 5) -- 3

-- `Notation "( x , y )" := (pair x y).`

#eval fst ⟨3, 5⟩ -- 3
def fst' : NatProd → Nat | ⟨x, _⟩ => x
def snd' : NatProd → Nat | ⟨_, y⟩ => y
def swap : NatProd → NatProd | ⟨x, y⟩ => ⟨y, x⟩

theorem surjective_pairing' : ∀ {n m : Nat}, pair n m = ⟨fst ⟨n, m⟩, snd ⟨n, m⟩⟩ := rfl
theorem surjective_pairing : ∀ {p : NatProd}, p = ⟨fst p, snd p⟩ := rfl

theorem snd_fst_is_swap {p : NatProd} : ⟨snd p, fst p⟩ = swap p := rfl
theorem fst_swap_is_snd {p : NatProd} : fst (swap p) = snd p := rfl

end NatProd

/-
private abbrev nat := Nat

class NatList where
  natprod : Type
  pair (n₁ n₂ : nat) : natprod
  fst (p : natprod) : nat
  snd (p : natprod) : nat

namespace NatList

-- attribute [match_pattern] pair

private local instance : NatList where
  natprod := NatProd
  pair := NatProd.pair
  -- fst p := match p with | pair x y => x
  fst | ⟨x, _⟩ => x
  snd | ⟨_, y⟩ => y

#check (pair 3 5 : natprod)
#eval fst (pair 3 5) -- 3

end NatList
-/

/-! ## Lists of Numbers
-/

inductive NatList
  | nil
  | cons (n : Nat) (l : NatList)

namespace NatList

example : NatList := cons 1 (cons 2 (cons 3 nil))

-- #check 1::[2]
-- #check #[1,2]
#check «term[_]»
#check «term#[_,]»
#check Vector.«term#v[_,]»
#check List.toArray
#check Lean.Syntax.TSepArray.getElems
#check Lean.Parser.Tactic.MCasesPat.parse.goAlts
#check Lake.expandConfigDecl

-- @[inherit_doc]
local infixr:67 " :: " => cons
local syntax (priority := high) "[" withoutPosition(sepBy(term, ";", "; ", allowTrailingSep)) "]" : term
local macro_rules
  | `([ $terms;* ]) =>
    terms.getElems.foldrM (β := Lean.Term) (init := Lean.mkIdent ``nil) fun term acc => `($term :: $acc)

example := 1 :: (2 :: 3 :: nil)
example := 1 :: 2 :: 3 :: nil
example := [1;2;3]

example : [] = nil := rfl
example : [1] = 1 :: nil := rfl
example : [1;2;3] = 1 :: 2 :: 3 :: nil := rfl

end NatList
