set_option autoImplicit false

/-- Binary Tree -/
inductive BinTree α
  | leaf
  | node (data : α) (left right : BinTree α)

abbrev RBTree α := BinTree (Bool × α)

namespace BinTree
variable {α}

@[match_pattern]
abbrev red (data : α) (left right : RBTree α) : RBTree α := node (false, data) left right

@[match_pattern]
abbrev black (data : α) (left right : RBTree α) : RBTree α := node (true, data) left right

@[inline]
def balanceLeft : α → RBTree α → RBTree α → RBTree α
  | data₂, red data (red data₁ left₁ right₁) left₂, right₂
  | data₂, red data₁ left₁ (red data right₁ left₂), right₂ =>
    red data (black data₁ left₁ right₁) (black data₂ left₂ right₂)
  | data, left, right => black data left right

@[inline]
def balanceRight : α → RBTree α → RBTree α → RBTree α
  | data₁, left₁, red data₂ (red data right₁ left₂) right₂
  | data₁, left₁, red data right₁ (red data₂ left₂ right₂) =>
    red data (black data₁ left₁ right₁) (black data₂ left₂ right₂)
  | data, left, right => black data left right

end BinTree

#check Decidable

namespace BinTree
variable {α}



end BinTree

class inductive Tree α {τ} : τ → Prop
  | isLeaf {leaf} : Tree α leaf
  | isNode {node left right : τ} (data : α) : Tree α left → Tree α right → Tree α node

#check Subarray

structure Heap α where
  array : Array α
  index : Nat

instance Heap.tree {α} (heap : Heap α) : Tree α heap :=
  if h : heap.index < heap.array.size then
    .isNode heap.array[heap.index]
      {heap with index := heap.index * 2 + 1}.tree
      {heap with index := heap.index * 2 + 2}.tree
  else
    .isLeaf
