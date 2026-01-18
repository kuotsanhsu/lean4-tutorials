set_option autoImplicit false

namespace Try1

structure Semigroup.{u} where
  M : Sort u
  p : M → M → M
  assoc {a b c} : p (p a b) c = p a (p b c)

structure Monoid extends Semigroup where
  unit : M
  unitl {a} : p unit a = a
  unitr {a} : p a unit = a

section
variable {S}

def p (a b : S) := b

def sg : Semigroup where
  M := S
  p
  assoc {a b c} := show c = c from rfl

example (unit : S) (single : ∀ {a : S}, unit = a) : Monoid where
  toSemigroup := sg
  unit
  unitl {a} := show a = a from rfl
  unitr {a} := show unit = a from single

end

end Try1

class Semigroup (M) where
  op : M → M → M
  assoc {a b c} : op (op a b) c = op a (op b c)

local instance {M} [inst : Semigroup M] : Mul M where
  mul := inst.op

class Monoid (M) extends Semigroup M where
  unit : M
  unitl {a} : unit * a = a
  unitr {a} : a * unit = a

local instance {M} [inst : Monoid M] : One M where
  one := inst.unit

instance SelfMaps (S) : Monoid (S → S) where
  op f g := f ∘ g
  assoc := rfl
  unit  := id
  unitl := rfl
  unitr := rfl

section
variable {S}

local instance : Semigroup S where
  op a b := b
  assoc {a b c} := show c = c from rfl

local instance (unit : S) (single : ∀ {a b : S}, a = b) : Monoid S where
  unit
  unitl {a} := show a = a from rfl
  unitr {a} := show unit = a from single

end

section

structure EightLetterWord (α) where
  (a b c d e f g h : α)

variable {α} -- The set of alphabets.

example : Semigroup (EightLetterWord α) where
  op | {a, b, c, d, e, ..}, {f, g, h, ..} => {a, b, c, d, e, f, g, h}
  assoc := rfl

example : Semigroup (EightLetterWord α) where
  op | {e, f, g, h, ..}, {a, b, c, d, ..} => {a, b, c, d, e, f, g, h}
  assoc := rfl

end

class Group (G) extends Monoid G where
  inv : G → G
  invl {u} : inv u * u = 1
  invr {u} : u * inv u = 1

local instance {G} [inst : Group G] : Inv G where
  inv := inst.inv

def Units (M) [Monoid M] := {u : M // ∃ v : M, u * v = 1 ∧ v * u = 1}

namespace Semigroup
variable {S} [Semigroup S] {a b c d : S}

instance : CoeSort (Semigroup S) (Type _) where
  coe _ := S

theorem mul_assoc : (a * b) * c = a * (b * c) := assoc
theorem mul_assoc4 : a * b * (c * d) = a * (b * c) * d := by rw [mul_assoc, mul_assoc, mul_assoc]

end Semigroup

namespace Monoid
variable {M} [inst : Monoid M]

instance : CoeSort (Monoid M) (Type _) where
  coe _ := M

theorem mul_one {a : M} : a * 1 = a := unitr

instance : Monoid (Units M) where
  op | ⟨u₁, h₁⟩, ⟨u₂, h₂⟩ => suffices ∃ v, u₁ * u₂ * v = 1 ∧ v * (u₁ * u₂) = 1 from ⟨u₁ * u₂, this⟩
    let ⟨v₁, (l₁ : u₁ * v₁ = 1), (r₁ : v₁ * u₁ = 1)⟩ := h₁
    let ⟨v₂, (l₂ : u₂ * v₂ = 1), (r₂ : v₂ * u₂ = 1)⟩ := h₂
    suffices u₁ * u₂ * (v₂ * v₁) = 1 ∧ v₂ * v₁ * (u₁ * u₂) = 1 from ⟨v₂ * v₁, this⟩
    ⟨by rw [inst.mul_assoc4, l₂, inst.mul_one, l₁], by rw [inst.mul_assoc4, r₁, inst.mul_one, r₂]⟩
  assoc := Subtype.ext inst.assoc
  unit  := ⟨1, 1, inst.unitl, inst.unitr⟩
  unitl := Subtype.ext inst.unitl
  unitr := Subtype.ext inst.unitr

noncomputable instance : Group (Units M) where
  inv | ⟨u, h⟩ => ⟨h.choose, u, h.choose_spec.symm⟩
  invl {u} := Subtype.ext u.property.choose_spec.right
  invr {u} := Subtype.ext u.property.choose_spec.left

end Monoid

noncomputable def Sym (S) : Group (Units (SelfMaps S)) := inferInstance

namespace Function

def Bijective {α} (f : α → α) := Injective f ∧ Surjective f

namespace Surjective
variable {α β} {f : α → β} (h : Surjective f)

noncomputable def rightInverse : β → α := fun b => (h b).choose

theorem RightInverse : RightInverse h.rightInverse f := fun b => (h b).choose_spec

end Surjective

end Function

example {S} : {f : SelfMaps S // Function.Bijective f} = Units (SelfMaps S) :=
  have (f : S → S) : Function.Bijective f = ∃ g, f ∘ g = id ∧ g ∘ f = id := propext {
    mp := fun ⟨inj, sur⟩ =>
      let g := sur.rightInverse
      have hfg : ∀ b, f (g b) = b := sur.RightInverse
      have hgf a : g (f a) = a := inj <| show f (g (f a)) = f a from hfg (f a)
      ⟨g, funext hfg, funext hgf⟩
    mpr := fun ⟨g, hfg, hgf⟩ =>
      have (a₁ a₂ : S) (e : f a₁ = f a₂) :=
        calc a₁
         _ = g (f a₁) := congrFun hgf.symm a₁
         _ = g (f a₂) := congrArg g e
         _ = a₂ := congrFun hgf a₂
      ⟨this, fun b => ⟨g b, congrFun hfg b⟩⟩
  }
  congrArg Subtype (funext this)

def Nat.fact : Nat → Nat
  | 0 => 1
  | n + 1 => n.fact * (n + 1)

example : Nat.fact 0 =   1 := rfl
example : Nat.fact 1 =   1 := rfl
example : Nat.fact 2 =   2 := rfl
example : Nat.fact 3 =   6 := rfl
example : Nat.fact 4 =  24 := rfl
example : Nat.fact 5 = 120 := rfl

def Nat.factLinear (n : Nat) : Nat := Id.run do
  let mut p := 1
  let mut m := 1
  while m <= n do
    p := p * m
    m := m + 1
  return p

example : Nat.factLinear 0 =   1 := by native_decide
example : Nat.factLinear 1 =   1 := by native_decide
example : Nat.factLinear 2 =   2 := by native_decide
example : Nat.factLinear 3 =   6 := by native_decide
example : Nat.factLinear 4 =  24 := by native_decide
example : Nat.factLinear 5 = 120 := by native_decide

def Nat.fact2 (n : Nat) : Nat := Id.run do
  let mut p := 1
  for m in [1:n + 1] do
    p := p * m
  return p

example : Nat.fact2 0 =   1 := by native_decide
example : Nat.fact2 1 =   1 := by native_decide
example : Nat.fact2 2 =   2 := by native_decide
example : Nat.fact2 3 =   6 := by native_decide
example : Nat.fact2 4 =  24 := by native_decide
example : Nat.fact2 5 = 120 := by native_decide

/-- Binary Tree -/
inductive Tree (α)
  | leaf
  | node (data : α) (left right : Tree α)

#check Std.PartialOrderPackage
#check Std.IsPartialOrder

#check List.all
#check_failure List.forall

inductive Tree.All {α} (p : α → Prop) : Tree α → Prop
  | leaf : leaf.All p
  | node {data left right} : p data → left.All p → right.All p → (node data left right).All p

inductive Tree.IsBST {α} [ord : LT α] : Tree α → Prop
  | leaf : leaf.IsBST
  | node {data left right}
    : left.All (· < data) → left.IsBST
    → right.All (· > data) → right.IsBST
    → (node data left right).IsBST

/-- Binary Search Tree-/
def Tree.BST (α) [ord : LT α] := Subtype (IsBST (ord := ord))

inductive Tree.IsHeap {α} [ord : LT α] : Tree α → Prop
  | leaf : leaf.IsHeap
  | node {data left right}
    : left.All (· < data) → left.IsHeap
    → right.All (· < data) → right.IsHeap
    → (node data left right).IsHeap

/-- Binary Heap -/
def Heap (α) [ord : LT α] := Subtype (Tree.IsHeap (ord := ord))

def ordFst (α β) [LT α] : LT (α × β) where
  lt x y := x.fst < y.fst

def ordSnd (α β) [LT β] : LT (α × β) where
  lt x y := x.snd < y.snd

/-- Cartesian Tree-/
structure Treap (α β) [LT α] [LT β] where
  tree : Tree (α × β)
  bst : tree.IsBST (ord := ordFst α β)
  heap : tree.IsHeap (ord := ordSnd α β)

theorem Nat.pow_max {a m n : Nat} (pos : a > 0) : max (a ^ m) (a ^ n) = a ^ max m n :=
  Nat.le_antisymm mp mpr
where
  mp : max (a ^ m) (a ^ n) ≤ a ^ max m n :=
    have h₁ := Nat.pow_le_pow_right pos (m.le_max_left n)
    have h₂ := Nat.pow_le_pow_right pos (m.le_max_right n)
    Nat.max_le_of_le_of_le h₁ h₂
  mpr : a ^ max m n ≤ max (a ^ m) (a ^ n) :=
    if h : m ≤ n then
      calc a ^ max m n
       _ = a ^ n := congrArg _ (if_pos h)
       _ ≤ max (a ^ m) (a ^ n) := Nat.le_max_right ..
    else
      calc a ^ max m n
       _ = a ^ m := congrArg _ (if_neg h)
       _ ≤ max (a ^ m) (a ^ n) := Nat.le_max_left ..

namespace Tree
variable {α}

/-- Leafs are not counted making an empty tree having size 0. -/
def size : Tree α → Nat
  | leaf => 0
  | node _ left right => left.size + right.size + 1

/-- Leafs have 0 height making an empty tree having height 0. -/
def height : Tree α → Nat
  | leaf => 0
  | node _ left right => max left.height right.height + 1

theorem size_height : ∀ t : Tree α, t.size + 1 ≤ 2 ^ t.height
  | leaf => show 1 ≤ 1 from Nat.le.refl
  | node _ left right =>
    let m := 2 ^ left.height
    let n := 2 ^ right.height
    calc left.size + right.size + (1 + 1)
     _ = (left.size + 1) + (right.size + 1) := Nat.add_add_add_comm ..
     _ ≤ m + n := Nat.add_le_add left.size_height right.size_height
     _ ≤ max m n + max m n := Nat.add_le_add (m.le_max_left n) (m.le_max_right n)
     _ = max m n * 2 := (max m n).mul_two.symm
     _ = 2 ^ max left.height right.height * 2
      := congrArg (· * 2) <| Nat.pow_max <| show 2 > 0 from Nat.le.refl.step
     _ = 2 ^ (max left.height right.height + 1) := rfl

def BST.contains [LT α] [DecidableLT α] (a : α) : BST α → Bool
  | ⟨leaf, _⟩ => false
  | ⟨node data left right, h⟩ =>
    if a < data then
      contains a ⟨left, match h with | .node _ hl _ _ => hl⟩
    else if a > data then
      contains a ⟨right, match h with | .node _ _ _ hr => hr⟩
    else
      true
  termination_by bst => bst.val

#check List.Mem
inductive Mem (a : α) : Tree α → Prop
  | curr {left right} : Mem a (node a left right)
  | left {data left right} : Mem a left → Mem a (node data left right)
  | right {data left right} : Mem a right → Mem a (node data left right)

instance : Membership α (Tree α) where
  mem := flip Mem

variable [LE α] [DecidableLE α] [Std.IsLinearOrder α]
instance : Std.LinearOrderPackage α := .ofLE _

instance BST.decMem (a : α) : (bst : BST α) → Decidable (a ∈ bst.val)
  | ⟨leaf, _⟩ => isFalse nofun
  | ⟨node data left right, h⟩ =>
    let tree := node data left right
    if hlt : a < data then
      have h : left.IsBST ∧ right.All (· > data) := match h with | .node _ hl hr _ => ⟨hl, hr⟩
      let r : Decidable (a ∈ left) := decMem a ⟨left, h.1⟩
      suffices (a ∈ left) = (a ∈ tree) from this.rec r
      suffices a ∈ tree → a ∈ left from propext ⟨Mem.left, this⟩
      fun h : a ∈ node data left right =>
      match h with
      | .curr => Std.Irrefl.irrefl a hlt |>.rec
      | .left h => h
      | .right h => sorry
    else if a > data then
      let r : Decidable (a ∈ right) := decMem a ⟨right, match h with | .node _ _ _ hr => hr⟩
      suffices (a ∈ right) = (a ∈ tree) from this.rec r
      suffices a ∈ tree → a ∈ right from propext ⟨Mem.right, this⟩
      sorry
    else
      isTrue sorry
  termination_by bst => bst.val

theorem mem_left {left right} [LT α] {a data : α} (m : a ∈ node data left right) (h : a < data) :
    IsBST (node data left right) → a ∈ left := sorry

end Tree

/-
def Tree.All' {α} (p : α → Prop) : Tree α → Prop
  | leaf => True
  | node data left right => p data ∧ left.All' p ∧ right.All' p

def Tree.IsBST' {α} [ord : LT α] : Tree α → Prop
  | leaf => True
  | node data left right =>
    left.All' (· < data) ∧ left.IsBST' ∧ right.All' (· > data) ∧ right.IsBST'

inductive Tree.Rec {α} (p q : α → α → Prop) (h : Tree α → Prop) : Tree α → Prop
  | leaf : Rec p q h leaf
  | node {data left right}
    : All (p data) left → h left
    → All (q data) right → h right
    → h right → Rec p q h (node data left right)

def Tree.IsBST₂ {α} [ord : LT α] := Rec (flip ord.lt) ord.lt IsBST₂
-/
