set_option autoImplicit false

/-- Binary Tree -/
inductive BinTree (α)
  | leaf
  | node (data : α) (left right : BinTree α)

namespace BinTree
variable {α}

inductive Mem (a : α) : BinTree α → Prop
  | curr {left right} : Mem a (node a left right)
  | left {data left right} : Mem a left → Mem a (node data left right)
  | right {data left right} : Mem a right → Mem a (node data left right)

instance : Membership α (BinTree α) where
  mem := flip Mem

section
variable [LT α]

/-- Binary Search Tree-/
class inductive IsBST : BinTree α → Prop
  | leaf : leaf.IsBST
  | node {data left right}
    : (∀ a ∈ left, a < data) → left.IsBST
    → (∀ a ∈ right, data < a) → right.IsBST
    → (node data left right).IsBST

-- instance (data : α) {left right : Tree α} [bst : IsBST (.node data left right)] : IsBST left :=
--   match bst with
--   | .node _ hl _ _ => hl

-- def IsBST.right {data : α} {left right : Tree α} : IsBST (.node data left right) → IsBST right
--   | node _ _ _ hr => hr

variable [DecidableLT α]

def contains (a : α) : (tree : BinTree α) → [IsBST tree] → Bool
  | leaf, _ => false
  | node data left right, h =>
    if a < data then
      have : left.IsBST := match h with | .node _ hl _ _ => hl
      contains a left
    else if data < a then
      have : right.IsBST := match h with | .node _ _ _ hr => hr
      contains a right
    else
      true

end

section
variable [LE α] [DecidableLE α] [Std.IsLinearOrder α]
local instance : Std.LinearOrderPackage α := .ofLE _

instance decMem (a : α) : (tree : BinTree α) → [IsBST tree] → Decidable (a ∈ tree)
  | leaf, _ => isFalse nofun
  | node data left right, h =>
    if hlt : a < data then
      have : left.IsBST := match h with | .node _ hl _ _ => hl
      have hgt : a ∈ right → a > data := match h with | .node _ _ hgt _ => hgt a
      let r : Decidable (a ∈ left) := decMem a left
      suffices (a ∈ left) = (a ∈ node data left right) from this.rec r
      suffices a ∈ node data left right → a ∈ left from propext ⟨Mem.left, this⟩
      fun | .curr => nomatch Std.Irrefl.irrefl a hlt
          | .left ha => ha
          | .right ha => nomatch Std.Asymm.asymm a data hlt (hgt ha)
    else if hgt : data < a then
      have : right.IsBST := match h with | .node _ _ _ hr => hr
      have hlt : a ∈ left → a < data := match h with | .node hlt _ _ _ => hlt a
      let r : Decidable (a ∈ right) := decMem a right
      suffices (a ∈ right) = (a ∈ node data left right) from this.rec r
      suffices a ∈ node data left right → a ∈ right from propext ⟨Mem.right, this⟩
      fun | .curr => nomatch Std.Irrefl.irrefl a hgt
          | .left ha => nomatch Std.Asymm.asymm a data (hlt ha) hgt
          | .right ha => ha
    else
      suffices a ∈ node data left right from isTrue this
      suffices a = data from this.rec Mem.curr
      have hle : a ≤ data := Lean.Grind.LinearOrder.le_of_not_lt hgt
      have hge : data ≤ a := Lean.Grind.LinearOrder.le_of_not_lt hlt
      Std.Antisymm.antisymm a data hle hge

theorem decMem_eq_contains {a}
  : {tree : BinTree α} → [IsBST tree] → decide (a ∈ tree) = tree.contains a
  | leaf, _ => rfl
  | node data left right, .node hlt hl hgt hr =>
    if hlt : a < data then
      sorry
    else if hgt : data < a then
      sorry
    else
      sorry

end

end BinTree

#check_failure Time
#check_failure time
#check_failure Std.Time
#check ite
#check dite
#check cond
#check Bool.dcond
#check dite_eq_ite
#check Bool.cond_eq_ite

namespace Try1

class Time {α β} (f : α → β) (a : α) where
  time : Nat

abbrev TimeClosed {β} (b : β) := Time (fun _ => b) ()

/-- Ignoring branch jumping time. -/
instance {α c} [h : Decidable c] {t e : α}
    [tc : TimeClosed (decide c)] [tt : TimeClosed t] [te : TimeClosed e]
  : TimeClosed (ite c t e) where
  time := tc.time + max tt.time te.time

section

local instance {a b} : Time (Function.uncurry Int32.add) (a, b) where
  time := 1

end

end Try1

#check Thunk
example : (fun _ : Unit => ()) = (fun _ : Unit => ()) := rfl
example : (fun _ : Bool => true) = (fun _ : Bool => !!true) := rfl
example : (fun x : Nat => x) = (fun x : Nat => x + 0) := rfl
example : (fun x : Nat => x) = (fun x : Nat => 0 + x) := funext fun x => x.zero_add.symm
