/-!
- https://opendatastructures.org/ods-python/9_2_RedBlackTree_Simulated_.html
- https://www.reddit.com/r/programming/comments/69tpu/robert_sedgwicks_left_leaning_redblack_trees/
- https://en.wikipedia.org/wiki/AA_tree
- https://www.mew.org/~kazu/proj/red-black-tree/
- https://read.seas.harvard.edu/~kohler/notes/llrb.html
  - https://news.ycombinator.com/item?id=8679109
- https://web.archive.org/web/20170207072643/https://web.student.chalmers.se/groups/datx02-dtp/
- https://www.cs.utexas.edu/~scottm/cs307/handouts/Slides/Topic19RedBlackTrees.pdf
- https://softwareengineering.stackexchange.com/questions/116614/where-does-the-term-red-black-tree-come-from
- [B-Trees Require Fewer Comparisons Than Balanced Binary Search Trees](https://news.ycombinator.com/item?id=40768418)
- https://www.nayuki.io/page/aa-tree-set
- https://www.cs.princeton.edu/~appel/papers/redblack.pdf
- https://ccs.neu.edu/~camoy/pub/red-black-tree.pdf
-/

set_option autoImplicit false

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

inductive RBTree.{u} (α : Sort u) : (isRed : Bool) → (blackHeight : Nat) → Sort (max 1 u)
  | leaf : RBTree α false 0
  | red (data : α) {n} (left right : RBTree α false n) : RBTree α true n
  | black (data : α) n x (left : RBTree α x n) y (right : RBTree α y n) (leftLeaning : x || !y)
    : RBTree α false n.succ

namespace RBTree
variable {α}

def size {isRed n} : RBTree α isRed n → Nat
  | leaf => 0
  | red _ left right
  | black _ _ _ left _ right _ => left.size + right.size + 1

def height {isRed n} : RBTree α isRed n → Nat
  | leaf => 0
  | red _ left right
  | black _ _ _ left _ right _ => max left.height right.height + 1

theorem size_height {isRed n} : ∀ t : RBTree α isRed n, t.size < 2 ^ t.height
  | leaf => show 1 ≤ 1 from Nat.le.refl
  | red _ left right
  | black _ _ _ left _ right _ =>
    let m := 2 ^ left.height
    let n := 2 ^ right.height
    calc left.size + right.size + (1 + 1)
     _ = left.size.succ + right.size.succ := Nat.add_add_add_comm ..
     _ ≤ m + n := Nat.add_le_add left.size_height right.size_height
     _ ≤ max m n + max m n := Nat.add_le_add (m.le_max_left n) (m.le_max_right n)
     _ = max m n * 2 := (max m n).mul_two.symm
     _ = 2 ^ max left.height right.height * 2
      := congrArg (· * 2) <| Nat.pow_max <| show 2 > 0 from Nat.le.refl.step
     _ = 2 ^ (max left.height right.height + 1) := rfl

mutual
theorem height_blackHeight {n} : ∀ {isRed} (tree : RBTree α isRed n), tree.height ≤ 2 * n + 1
  | false, tree =>
    calc tree.height
     _ ≤ 2 * n := tree.black_height_blackHeight
     _ ≤ 2 * n + 1 := Nat.le.refl.step
  | true, red _ left right =>
    suffices max left.height right.height ≤ 2 * n from Nat.succ_le_succ this
    Nat.max_le_of_le_of_le left.black_height_blackHeight right.black_height_blackHeight

theorem black_height_blackHeight {n} : ∀ tree : RBTree α false n, tree.height ≤ 2 * n
  | leaf => show 0 ≤ 0 from Nat.le.refl
  | black _ n _ left _ right _ =>
    suffices max left.height right.height ≤ 2 * n + 1 from Nat.succ_le_succ this
    Nat.max_le_of_le_of_le left.height_blackHeight right.height_blackHeight
end

mutual
theorem blackHeight_height {n} : ∀ {isRed} (tree : RBTree α isRed n), n ≤ tree.height
  | true, tree => Nat.le_of_lt tree.red_blackHeight_height
  | false, leaf => show 0 ≤ 0 from Nat.le.refl
  | false, black _ n _ left _ right _ =>
    suffices n ≤ max left.height right.height from Nat.succ_le_succ this
    calc n
     _ ≤ left.height := left.blackHeight_height
     _ ≤ max left.height _ := Nat.le_max_left ..

theorem red_blackHeight_height {n} : ∀ tree : RBTree α true n, n < tree.height
  | red _ left right => suffices n ≤ max left.height right.height from Nat.succ_le_succ this
    calc n
     _ ≤ left.height := left.blackHeight_height
     _ ≤ max left.height _ := Nat.le_max_left ..
end

end RBTree
