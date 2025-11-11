import Std.Tactic.Do.Syntax
import Lake.Config.Meta
/-! # Working with Structured Data
-/

/-! ## Pairs of Numbers
-/

inductive NatProd
  | pair (n₁ n₂ : Nat)

namespace NatProd

/-- info: pair 3 5 : NatProd -/ #guard_msgs in #check pair 3 5
def fst : NatProd → Nat | pair x _ => x
def snd : NatProd → Nat | pair _ y => y
/-- info: 3 -/ #guard_msgs in #eval fst (pair 3 5)

-- `Notation "( x , y )" := (pair x y).`

/-- info: 3 -/ #guard_msgs in #eval fst ⟨3, 5⟩
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

/--
info: equations:
@[defeq] theorem List.replicate.eq_1.{u} : ∀ {α : Type u} (x : α), List.replicate 0 x = []
@[defeq] theorem List.replicate.eq_2.{u} : ∀ {α : Type u} (x : α) (n : Nat),
  List.replicate n.succ x = x :: List.replicate n x
-/
#guard_msgs in
#print eqns List.replicate
def replicate (n : Nat) : (count : Nat) → NatList
  | 0 => []
  | count + 1 => n :: replicate n count

def length : NatList → Nat
  | [] => 0
  | _ :: t => t.length + 1

def append : NatList → NatList → NatList
  | [], l₂ => l₂
  | h :: t, l₂ => h :: append t l₂

local instance : Append NatList where append

example : [1;2;3] ++ [4;5] = [1;2;3;4;5] := rfl
example : [] ++ [4;5] = [4;5] := rfl
example : [1;2;3] ++ [] = [1;2;3] := rfl

def headD (default : Nat) : NatList → Nat
  | [] | default :: _ => default

def tail : NatList → NatList
  | [] => []
  | _ :: t => t

example : headD 0 [1;2;3] = 1 := rfl
example : headD 0 [] = 0 := rfl
example : tail [1;2;3] = [2;3] := rfl

def nonzeros : NatList → NatList
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t

example : nonzeros [0;1;0;2;3;0;0] = [1;2;3] := rfl

def oddmembers : NatList → NatList
  | [] => []
  | h :: t => let t := oddmembers t ; if h % 2 = 1 then h :: t else t

example : oddmembers [0;1;0;2;3;0;0] = [1;3] := rfl

def countoddmembers (l : NatList) : Nat := l.oddmembers.length

example : countoddmembers [1;0;3;1;4;5] = 4 := rfl
example : countoddmembers [0;2;4] = 0 := rfl
example : countoddmembers nil = 0 := rfl

def alternate : NatList → NatList → NatList
  | [], l | l, [] => l
  | h₁ :: t₁, h₂ :: t₂ => h₁ :: h₂ :: alternate t₁ t₂

example : alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6] := rfl
example : alternate [1] [4;5;6] = [1;4;5;6] := rfl
example : alternate [1;2;3] [4] = [1;4;2;3] := rfl
example : alternate [] [20;30] = [20;30] := rfl

end NatList
