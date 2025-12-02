import Lean.Data.RBTree
set_option autoImplicit false

/-- Binary Tree -/
inductive BinTree (α)
  | leaf
  | node (data : α) (left right : BinTree α)

namespace BinTree
universe u
variable {α : Type u}

inductive Mem (a : α) : BinTree α → Prop
  | curr {left right} : Mem a (node a left right)
  | left {data left right} : Mem a left → Mem a (node data left right)
  | right {data left right} : Mem a right → Mem a (node data left right)

instance : Membership α (BinTree α) where
  mem tree := tree.Mem

/-- Binary Search Tree-/
class inductive IsBST [LT α] : BinTree α → Prop
  | leaf : leaf.IsBST
  | node {data left right}
    : (∀ a ∈ left, a < data) → left.IsBST
    → (∀ a ∈ right, data < a) → right.IsBST
    → (node data left right).IsBST

section
variable [LE α] [DecidableLE α] [Std.IsLinearOrder α]
local instance : Std.LinearOrderPackage α := .ofLE _

instance decMem (a : α) : (tree : BinTree α) → [IsBST tree] → Decidable (a ∈ tree)
  | leaf, _ => isFalse nofun
  | node data left right, h =>
    if hlt : a < data then
      let r : Decidable (a ∈ left) := suffices left.IsBST from decMem a left
        match h with | .node _ hl _ _ => hl
      suffices (a ∈ left) = (a ∈ node data left right) from this.rec r
      suffices a ∈ node data left right → a ∈ left from propext ⟨.left, this⟩
      fun | .curr => nomatch Std.Irrefl.irrefl a hlt
          | .left ha => ha
          | .right ha => suffices hgt : data < a from nomatch Std.Asymm.asymm a data hlt hgt
            match h with | .node _ _ hgt _ => hgt a ha
    else if hgt : data < a then
      let r : Decidable (a ∈ right) := suffices right.IsBST from decMem a right
        match h with | .node _ _ _ hr => hr
      suffices (a ∈ right) = (a ∈ node data left right) from this.rec r
      suffices a ∈ node data left right → a ∈ right from propext ⟨.right, this⟩
      fun | .curr => nomatch Std.Irrefl.irrefl a hgt
          | .right ha => ha
          | .left ha => suffices hlt : a < data from nomatch Std.Asymm.asymm a data hlt hgt
            match h with | .node hlt _ _ _ => hlt a ha
    else
      suffices a ∈ node data left right from isTrue this
      suffices a = data from this.rec .curr
      have hle : a ≤ data := Lean.Grind.LinearOrder.le_of_not_lt hgt
      have hge : data ≤ a := Lean.Grind.LinearOrder.le_of_not_lt hlt
      Std.Antisymm.antisymm a data hle hge

end

#check ForIn
#check ForIn'
#check List.forM
#check List.forIn'
#check Lean.RBTree.forIn
#check Lean.RBNode.forIn
#check HasSubset

inductive Subtree (tree : BinTree α) : BinTree α → Prop
  | rfl : Subtree tree tree
  | left {data left right} : Subtree tree left → Subtree tree (node data left right)
  | right {data left right} : Subtree tree right → Subtree tree (node data left right)

instance : HasSubset (BinTree α) where
  Subset := Subtree

example {data} {left right : BinTree α} : left ⊆ node data left right := .left .rfl
example {data} {left right : BinTree α} : right ⊆ node data left right := .right .rfl

theorem Subtree.trans {t₁ t₂ t₃ : BinTree α} (h : t₁ ⊆ t₂) : t₂ ⊆ t₃ → t₁ ⊆ t₃
  | rfl => h
  | left hl => (h.trans hl).left
  | right hr => (h.trans hr).right

-- instance : Trans (@Subtree α) Subtree Subtree where
--   trans h | .rfl => h
--           | .left hl => .left (subtree_trans h hl)
--           | .right hr => .right (subtree_trans h hr)

-- instance : Trans (@Subset (BinTree α) instHasSubset) Subset Subset where
--   trans h | .rfl => h
--           | .left hl => .left (subtree_trans h hl)
--           | .right hr => .right (subtree_trans h hr)

theorem Mem.trans {a} {t₁ t₂ : BinTree α} (h : a ∈ t₁) : t₁ ⊆ t₂ → a ∈ t₂
  | .rfl => h
  | .left hl => left (h.trans hl)
  | .right hr => right (h.trans hr)

section
variable {β m} [Monad m]

@[inline] def forIn' (tree : BinTree α) (init : β) (f : ∀ a ∈ tree, β → m (ForInStep β)) : m β := do
  match ← inorder tree init Subtree.rfl with
  | .done b
  | .yield b => return b
where
  @[specialize] inorder (subtree : BinTree α) (b : β) (h : subtree ⊆ tree) : m (ForInStep β) := do
    match subtree with
    | leaf => return .yield b
    | node data left right =>
      match ← inorder left b (Subtree.rfl.left.trans h) with
      | r@(.done _) => return r
      | .yield b =>
        match ← f data (Mem.curr.trans h) b with
        | r@(.done _) => return r
        | .yield b => inorder right b (Subtree.rfl.right.trans h)

instance : ForIn' m (BinTree α) α inferInstance where forIn'

end

example (tree : BinTree Nat) : IO Unit := do
  for h : data in tree do
    println! data

def toSortedList : BinTree α → List α
  | leaf => []
  | node data left right => left.toSortedList ++ data :: right.toSortedList
