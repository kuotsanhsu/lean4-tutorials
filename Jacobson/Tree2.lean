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

@[inline] def forIn' (tree : BinTree α) (init : β) (f : ∀ a ∈ tree, β → m (ForInStep β)) : m β :=
  inorder init tree Subtree.rfl <&> ForInStep.value
where
  @[specialize] inorder (b : β) : ∀ subtree ⊆ tree, m (ForInStep β)
    | leaf, _ => pure (.yield b)
    | node data left right, h => do
      let := inorder b left (Subtree.rfl.left.trans h)
      let .yield b ← this | this
      let := f data (Mem.curr.trans h) b
      let .yield b ← this | this
      inorder b right (Subtree.rfl.right.trans h)

instance : ForIn' m (BinTree α) α inferInstance where forIn'

end

/-- info: 123 -/
#guard_msgs in
#eval show IO Unit from
  let tree : BinTree Nat := node 2 (node 1 leaf leaf) (node 3 leaf leaf)
  for data in tree do
    IO.print data

def toSortedList : BinTree α → List α
  | leaf => []
  | node data left right => left.toSortedList ++ data :: right.toSortedList

/-!
- [Types of binary trees](https://en.wikipedia.org/wiki/Binary_tree#Types_of_binary_trees)
-/

inductive IsFull : BinTree α → Prop
  | leaf : leaf.IsFull
  | node {data left right} : left.IsFull → right.IsFull → (node data left right).IsFull

-- inductive Subtree.Level {subtree tree : BinTree α} : subtree ⊆ tree → Nat → Prop

def height : BinTree α → Nat
  | leaf => 0
  | node _ left right => max left.height right.height + 1

inductive IsPerfect : BinTree α → (height : Nat) → Prop
  | leaf : leaf.IsPerfect 0
  | node {data left right} height :
    left.IsPerfect height → right.IsPerfect height → (node data left right).IsPerfect (height + 1)

def Perfect (tree : BinTree α) := tree.IsPerfect tree.height

namespace IsPerfect

theorem height_eq {height} : {tree : BinTree α} → tree.IsPerfect height → tree.height = height
  | .leaf, leaf => rfl
  | .node _ left right, node height hl hr =>
    suffices max left.height right.height = height from congrArg Nat.succ this
    calc max left.height right.height
     _ = max left.height height := congrArg (max _ ·) hr.height_eq
     _ = max height height := congrArg (max · _) hl.height_eq
     _ = height := height.max_self

theorem toPerfect {height} {tree : BinTree α} : tree.IsPerfect height → tree.Perfect
  | hp => hp.height_eq.symm.subst hp

end IsPerfect

theorem Perfect.toIsFull {tree : BinTree α} : tree.Perfect → tree.IsFull
  | .leaf => .leaf
  | .node _ hl hr => .node hl.toPerfect.toIsFull hr.toPerfect.toIsFull

inductive IsComplete : BinTree α → Prop

inductive IsBalanced : BinTree α → Prop

end BinTree

structure Heap {α} (as : Array α) where
  index : Nat
  valid : index < as.size

namespace Heap
variable {α} {as : Array α}

@[inline] def left (heap : Heap as) (valid : heap.index * 2 + 1 < as.size) : Heap as where
  index := heap.index * 2 + 1
  valid

@[inline] def right (heap : Heap as) (valid : heap.index * 2 + 2 < as.size) : Heap as where
  index := heap.index * 2 + 2
  valid

@[inline] def mk? (index : Nat) : Option (Heap as) :=
  if valid : index < as.size then some {index, valid} else none

@[inline] def left? (heap : Heap as) : Option (Heap as) :=
  mk? (heap.index * 2 + 1)

@[inline] def right? (heap : Heap as) : Option (Heap as) :=
  mk? (heap.index * 2 + 2)

inductive Mem (a : α) : Heap as → Prop
  | curr {heap} : as[heap.index]'heap.valid = a → Mem a heap
  | left {heap} (hl : heap.index * 2 + 1 < as.size) : Mem a (heap.left hl) → Mem a heap
  | right {heap} (hr : heap.index * 2 + 2 < as.size) : Mem a (heap.right hr) → Mem a heap

instance : Membership α (Heap as) where mem heap := heap.Mem

end Heap

/-- MaxHeap -/
def Array.isHeap {α} [LT α] [DecidableLT α] (as : Array α) : Bool := Id.run do
  for (i, a) in ← as.mapIdxM (Function.curry id) do
    if let some l := as[i * 2 + 1]? then
      if a < l then return false
    if let some r := as[i * 2 + 2]? then
      if a < r then return false
  true

#eval #[1,2,3,4,5].isHeap
#eval #[1,2,3,4,5].reverse.isHeap
