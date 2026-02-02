set_option autoImplicit false

example : [1, 3].isSublist [0, 1, 2, 3, 4] := rfl
example : ¬ [1, 3].isSublist [0, 1, 2, 4] := nofun
example : ! [1, 3].isSublist [0, 1, 2, 4] := by decide

#check List.isSublist_iff_sublist
example : [1, 3].Sublist [0, 1, 2, 3, 4] := by decide

section
open scoped List

example {α} {xs ys : List α} : List.Sublist xs ys = (xs <+ ys) := rfl

example : [1, 3] <+ [0, 1, 2, 3, 4] := by decide

example : [1, 3] <+ [0, 1, 2, 3, 4] :=
  have : [1, 3] <+ [1] ++ [3] := List.Sublist.refl [1, 3]
  calc    [1,    3]
  _ <+    [1, 2, 3] := List.Sublist.middle this 2
  _ <+ [0, 1, 2, 3] := List.sublist_cons_self 0 [1, 2, 3]
  _ <+ [0, 1, 2, 3, 4] := List.sublist_append_left [0, 1, 2, 3] [4]

example : [1, 3] <+ [0, 1, 2, 3, 4] :=
  calc    [1,    3]
  _ <+    [1, 2, 3] := suffices [1, 3] <+ [1] ++ [3] from this.middle 2 ; List.Sublist.refl [1, 3]
  _ <+ [0, 1, 2, 3] := [1, 2, 3].sublist_cons_self 0
  _ <+ [0, 1, 2, 3, 4] := [0, 1, 2, 3].sublist_append_left [4]

example : [1, 3] <+ [0, 1, 2, 3, 4] :=
  calc    [1,    3]
  _ <+    [1, 2, 3] := List.Sublist.refl _ |>.middle (l₁ := [1]) _
  _ <+ [0, 1, 2, 3] := List.sublist_cons_self ..
  _ <+ [0, 1, 2, 3, 4] := List.sublist_append_left ..

example : [1, 3] <+ [0, 1, 2, 3, 4] :=
  let xs := [1, 2, 3, 4]
  have hl : [1] <+ [1, 2] := [1].sublist_append_left [2]
  have hr : [3] <+ [3, 4] := [3].sublist_append_left [4]
  calc [1, 3]
  _ <+    xs := hl.append hr
  _ <+ 0::xs := xs.sublist_cons_self 0

example : [1, 3] <+ [0, 1, 2, 3, 4] :=
  calc
  _ <+    _ := [1].sublist_append_left [2] |>.append <| [3].sublist_append_left [4]
  _ <+ 0::_ := List.sublist_cons_self ..

end

/-!
# Longest Common Subsequence (Sublist)
-/

#check Subarray -- contiguous by definition

namespace List
variable {α}

def CommonSublist (cs xs ys : List α) : Prop := cs <+ xs ∧ cs <+ ys

def LCS (cs xs ys : List α) : Prop :=
  CommonSublist cs xs ys ∧ ∀ cs', CommonSublist cs' xs ys → cs'.length ≤ cs.length

variable [DecidableEq α]

/-- Brute recursive. -/
def lcsAux0 : List α → List α → List α × Nat
  | [], _
  | _, [] => ([], 0)
  | x::as, y::bs =>
    if x = y then
      let diag := lcsAux0 as bs
      (x::diag.1, diag.2 + 1)
    else
      let left := lcsAux0 as (y::bs)
      let up := lcsAux0 (x::as) bs
      if left.2 ≥ up.2 then left else up

@[inherit_doc lcsAux0]
def lcs0 (xs ys : List α) : List α := (lcsAux0 xs ys).1

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs0 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs0 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs0 "XMJYAUZ".toList "MZJAWXU".toList

theorem lcsAux0_nil₁ : (ys : List α) → lcsAux0 [] ys = ([], 0)
  | [] | _::_ => by unfold lcsAux0 ; rfl
theorem lcsAux0_nil₂ : (xs : List α) → lcsAux0 xs [] = ([], 0)
  | [] | _::_ => by unfold lcsAux0 ; rfl
theorem lcs0_nil₁ (ys : List α) : lcs0 [] ys = [] :=
  congrArg Prod.fst ys.lcsAux0_nil₁
theorem lcs0_nil₂ (xs : List α) : lcs0 xs [] = [] :=
  congrArg Prod.fst xs.lcsAux0_nil₂

theorem lcs0_sublist₁ (xs ys : List α) : lcs0 xs ys <+ xs :=
  match xs, ys with
  | [], ys =>
    calc lcs0 [] ys
    _  = [] := ys.lcs0_nil₁
    _ <+ [] := Sublist.slnil
  | xs, [] =>
    calc lcs0 xs []
    _  = [] := xs.lcs0_nil₂
    _ <+ [] ++ xs := sublist_append_left [] xs
  | x::as, y::bs =>
    if h₁ : x = y then
      let diag := lcsAux0 as bs
      have : lcsAux0 (x::as) (y::bs) = (x::diag.1, diag.2 + 1) := by unfold lcsAux0 ; exact if_pos h₁
      calc lcs0 (x::as) (y::bs)
      _  = x::diag.1 := congrArg Prod.fst this
      _ <+ x::as := Sublist.cons₂ x <| show diag.1 <+ as from lcs0_sublist₁ as bs
    else
      let left := lcsAux0 as (y::bs)
      let up := lcsAux0 (x::as) bs
      have : lcsAux0 (x::as) (y::bs) = if left.2 ≥ up.2 then left else up := by unfold lcsAux0 ; exact if_neg h₁
      if h₂ : left.2 ≥ up.2 then
        calc lcs0 (x::as) (y::bs)
        _  = left.1 := congrArg Prod.fst <| show lcsAux0 (x::as) (y::bs) = left from trans this (if_pos h₂)
        _ <+ x::as := Sublist.cons x <| show left.1 <+ as from lcs0_sublist₁ as (y::bs)
      else
        calc lcs0 (x::as) (y::bs)
        _  = up.1 := congrArg Prod.fst <| show lcsAux0 (x::as) (y::bs) = up from trans this (if_neg h₂)
        _ <+ x::as := lcs0_sublist₁ (x::as) bs

theorem lcs0_sublist₂ (xs ys : List α) : lcs0 xs ys <+ ys := sorry

theorem lcs0_length (xs ys : List α) : (lcs0 xs ys).length = (lcsAux0 xs ys).2 := sorry

theorem lcs0_LCS (xs ys : List α) : LCS (lcs0 xs ys) xs ys := sorry

abbrev DP α := List α × Nat
abbrev DPS α := List (α × DP α)

/-- Quadratic space dynamic programming. -/
def lcs1 (xs ys : List α) : List α :=
  match xs.foldl aux1 (ys.reverse.map (·, [], 0)) with
  | [] => []
  | (_, cs, _)::_ => cs.reverse
where
  aux1 (dps : DPS α) (x : α) : DPS α := dps.foldr (aux2 x) ([], ([], 0), ([], 0)) |>.1
  aux2 (x : α) : α × DP α → DPS α × DP α × DP α → DPS α × DP α × DP α
    | (y, up), (dps, left, diag) =>
      let left := if x = y then (x::diag.1, diag.2 + 1) else if left.2 ≥ up.2 then left else up
      ((y, left)::dps, left, up)

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs1 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs1 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs1 "XMJYAUZ".toList "MZJAWXU".toList

theorem lcs1_LCS (xs ys : List α) : LCS (lcs1 xs ys) xs ys := sorry

/-- Linear space dynamic programming. -/
def lcs2 (xs ys : List α) : List α := Id.run do
  let mut dp : Vector (List α × Nat) ys.length := default
  for x in xs do
    let mut i := 0
    let mut left : List α × Nat := ([], 0)
    let mut diag : List α × Nat := ([], 0)
    for y in ys do
      -- have : i < dp.size := sorry
      let up := dp[i]!
      left := if x = y then (x::diag.1, diag.2 + 1) else if left.2 ≥ up.2 then left else up
      dp := dp.set! i left
      diag := up
      i := i + 1
  return dp.back?.getD ([], 0) |>.1.reverse

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs2 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs2 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs2 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs2 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs2 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs2 "XMJYAUZ".toList "MZJAWXU".toList

end List
