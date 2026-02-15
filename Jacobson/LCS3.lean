import Std.Tactic.Do

set_option autoImplicit false

/-!
# Longest Common Subsequence (Sublist)

I first define what it means for a list to be a common sublist of two other lists. Then, I define
what it means for a common sublist of two lists to be the longest.

I provide 3 implementations of the LCS algorithm. Their unit tests take the form of
`#guard_msgs in #eval`. Currently, I prove the correctness of the slow recursive implementation,
i.e. the theorem `lcs0_LCS`. To prove the correctness of `lcs1_LCS` and `lcs2_LCS`, it suffices to
prove the functional equality between `lcs0`, `lcs1`, `lcs2` which are captured by the theorems:
`lcs1_eq_lcs0` and `lcs2_eq_lcs1`. Only `lcs2_eq_lcs1` remains to be proved.

-/

namespace List
variable {α} [DecidableEq α]

structure CommonSublist (xs ys cs : List α) : Prop where
  sublist₁ : cs <+ xs
  sublist₂ : cs <+ ys

structure LCS (xs ys lcs : List α) : Prop extends CommonSublist xs ys lcs where
  longest : ∀ cs, CommonSublist xs ys cs → cs.length ≤ lcs.length

abbrev test_string (lcs : List Char → List Char → List Char) : String → String → String
  | ⟨xs⟩, ⟨ys⟩ => ⟨lcs xs ys⟩

/-!
## Straightforward recursion but slow
-/

/-- Slow recursive. -/
@[reducible] def lcs0 : List α → List α → List α
  | [], _
  | _, [] => []
  | x :: xs, y :: ys =>
    if x = y then
      x :: lcs0 xs ys
    else
      let xx := lcs0 xs (y :: ys)
      let yy := lcs0 (x :: xs) ys
      if xx.length ≥ yy.length then xx else yy

section unittest
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs0 ""        ""
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs0 "ABCD"    ""
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs0 ""        "ACBAD"
/-- info: "ACD"  -/ #guard_msgs(info) in #eval test_string lcs0 "ABCD"    "ACBAD"
/-- info: "AC"   -/ #guard_msgs(info) in #eval test_string lcs0 "GAC"     "AGCAT"
/-- info: "MJAU" -/ #guard_msgs(info) in #eval test_string lcs0 "XMJYAUZ" "MZJAWXU"
end unittest

theorem nil_lcs0 : {ys : List α} → lcs0 [] ys = []
  | [] => rfl
  | _ :: _ => by unfold lcs0 ; rfl
theorem lcs0_nil : {xs : List α} → lcs0 xs [] = []
  | [] => rfl
  | _ :: _ => by unfold lcs0 ; rfl

theorem lcs0_LCS : {xs ys : List α} → LCS xs ys (lcs0 xs ys)
  | [], ys =>
    show LCS [] ys (lcs0 [] ys) from
    suffices LCS [] ys [] by rw [nil_lcs0] ; exact this
    {
      sublist₁ := show [] <+ [] from .slnil
      sublist₂ := show [] <+ ys from ys.nil_sublist
      longest
      | cs, ⟨(h : cs <+ []), _⟩ =>
        show cs.length ≤ [].length from
        suffices cs = [] from this.rec Nat.le.refl
        eq_nil_of_sublist_nil h
    }
  | xs, [] =>
    show LCS xs [] (lcs0 xs []) from
    suffices LCS xs [] [] by rw [lcs0_nil] ; exact this
    {
      sublist₁ := show [] <+ xs from xs.nil_sublist
      sublist₂ := show [] <+ [] from .slnil
      longest
      | cs, ⟨_, (h : cs <+ [])⟩ =>
        show cs.length ≤ [].length from
        suffices cs = [] from this.rec Nat.le.refl
        eq_nil_of_sublist_nil h
    }
  | x :: xs, y :: ys =>
    if h₁ : x = y then
      let xy := lcs0 xs ys ; have hxy : LCS xs ys xy := lcs0_LCS
      have h : lcs0 (x :: xs) (y :: ys) = x :: xy := by unfold lcs0 ; exact if_pos h₁
      show LCS (x :: xs) (y :: ys) (lcs0 (x :: xs) (y :: ys)) from
      suffices LCS (x :: xs) (y :: ys) (x :: xy) from h ▸ this
      {
        sublist₁ := show x :: xy <+ x :: xs from hxy.sublist₁.cons₂ x
        sublist₂ := show x :: xy <+ y :: ys from h₁ ▸ hxy.sublist₂.cons₂ y
        longest
        | [], _ => show [].length ≤ _ from Nat.zero_le _
        | c :: cs, ⟨(hx : c :: cs <+ x :: xs), (hy : c :: cs <+ y :: ys)⟩ =>
          show (c :: cs).length ≤ (x :: xy).length from
          suffices cs.length ≤ xy.length from Nat.succ_le_succ this
          hxy.longest cs ⟨hx.of_cons_cons, hy.of_cons_cons⟩
      }
    else
      let xx := lcs0 xs (y :: ys) ; have hxx : LCS xs (y :: ys) xx := lcs0_LCS
      let yy := lcs0 (x :: xs) ys ; have hyy : LCS (x :: xs) ys yy := lcs0_LCS
      if h₂ : xx.length ≥ yy.length then
        have h : lcs0 (x :: xs) (y :: ys) = xx := by unfold lcs0 ; rw [if_neg h₁, if_pos h₂]
        show LCS (x :: xs) (y :: ys) (lcs0 (x :: xs) (y :: ys)) from
        suffices LCS (x :: xs) (y :: ys) xx from h ▸ this
        {
          hxx with
          sublist₁ := show xx <+ x :: xs from hxx.sublist₁.cons x
          longest
          | cs, ⟨(hx : cs <+ x :: xs), (hy : cs <+ y :: ys)⟩ =>
            match sublist_cons_iff.mp hx with
            | .inl (h : cs <+ xs) => show cs.length ≤ xx.length from hxx.longest cs ⟨h, hy⟩
            | .inr ⟨_, (h : cs = x :: _), _⟩ =>
              have : cs <+ ys :=
                match sublist_cons_iff.mp hy with
                | .inl h => h
                | .inr ⟨_, (e : cs = y :: _), _⟩ =>
                  suffices x = y from absurd this h₁
                  cons.inj (h.symm.trans e) |>.1
              calc cs.length
              _  ≤ yy.length := hyy.longest cs ⟨hx, this⟩
              _  ≤ xx.length := h₂
        }
      else
        have h : lcs0 (x :: xs) (y :: ys) = yy := by unfold lcs0 ; rw [if_neg h₁, if_neg h₂]
        show LCS (x :: xs) (y :: ys) (lcs0 (x :: xs) (y :: ys)) from
        suffices LCS (x :: xs) (y :: ys) yy from h ▸ this
        {
          hyy with
          sublist₂ := show yy <+ y :: ys from hyy.sublist₂.cons y
          longest
          | cs, ⟨(hx : cs <+ x :: xs), (hy : cs <+ y :: ys)⟩ =>
            match sublist_cons_iff.mp hy with
            | .inl (h : cs <+ ys) => show cs.length ≤ yy.length from hyy.longest cs ⟨hx, h⟩
            | .inr ⟨_, (h : cs = y :: _), _⟩ =>
              have : cs <+ xs :=
                match sublist_cons_iff.mp hx with
                | .inl h => h
                | .inr ⟨_, (e : cs = x :: _), _⟩ =>
                  suffices x = y from absurd this h₁
                  cons.inj (e.symm.trans h) |>.1
              calc cs.length
              _  ≤ xx.length := hxx.longest cs ⟨this, hy⟩
              _  ≤ yy.length := Nat.le_of_not_ge h₂
        }

/-!
## Dynamic programming taking quadratic time and quadratic space (list of list)
-/

namespace lcs1

structure DP α where
  lcs : List α
  length : Nat
  length_eq : lcs.length = length

def dp0 : DP α := ⟨[], 0, rfl⟩
def DPS α := List (α × DP α)
abbrev DPS.dp : DPS α → DP α | [] => dp0 | (_, dp) :: _ => dp
def dps0 : List α → DPS α := map (·, dp0)

end lcs1

open lcs1 in
/-- Quadratic time and quadratic space dynamic programming. -/
def lcs1 (xs ys : List α) : List α := aux0.dp.lcs
where
  aux0 : DPS α := xs.foldr aux1 (dps0 ys)
  aux1 (x : α) (dps : DPS α) : DPS α := (aux2 x dps).1
  aux2 (x : α) (dps : DPS α) : DPS α × DP α × DP α := dps.foldr (aux3 x) ([], dp0, dp0)
  aux3 (x : α) : α × DP α → DPS α × DP α × DP α → DPS α × DP α × DP α
    | (y, xx), (dps, yy, xy) => let dp := aux4 x y xx yy xy ; ((y, dp) :: dps, dp, xx)
  aux4 (x y : α) (xx yy xy : DP α) : DP α :=
    if x = y then
      ⟨x :: xy.lcs, xy.length + 1, xy.length_eq.rec rfl⟩
    else
      if xx.length ≥ yy.length then xx else yy

section unittest
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs1 ""        ""
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs1 "ABCD"    ""
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs1 ""        "ACBAD"
/-- info: "ACD"  -/ #guard_msgs(info) in #eval test_string lcs1 "ABCD"    "ACBAD"
/-- info: "AC"   -/ #guard_msgs(info) in #eval test_string lcs1 "GAC"     "AGCAT"
/-- info: "MJAU" -/ #guard_msgs(info) in #eval test_string lcs1 "XMJYAUZ" "MZJAWXU"
end unittest

namespace lcs1
variable {x y : α} {xs ys : List α}

example :=
  calc aux0 (x :: xs) ys
  _  = (x :: xs).foldr aux1 (dps0 ys) := rfl
  _  = aux1 x (xs.foldr aux1 (dps0 ys)) := rfl
  _  = aux1 x (aux0 xs ys) := rfl

theorem aux0_nil : {xs : List α} → aux0 xs [] = []
  | [] => rfl
  | x :: xs =>
    calc aux0 (x :: xs) []
    _  = aux1 x (aux0 xs []) := rfl
    _  = aux1 x [] := congrArg (aux1 x) aux0_nil
    _  = [] := rfl

theorem aux0_cons : {xs : List α} → aux0 xs (y :: ys) = (y, (aux0 xs (y :: ys)).dp) :: aux0 xs ys
  | [] => rfl
  | x :: xs =>
    let xx := aux0 xs (y :: ys) |>.dp
    let dp := aux0 (x :: xs) (y :: ys) |>.dp
    let pp := aux2 x (aux0 xs ys) |>.2
    let eq := aux4 x y xx pp.1 pp.2
    have h :=
      calc aux0 (x :: xs) (y :: ys)
      _  = aux1 x (aux0 xs (y :: ys)) := rfl
      _  = aux1 x ((y, xx) :: aux0 xs ys) := congrArg (aux1 x) aux0_cons
      _  = (y, eq) :: aux0 (x :: xs) ys := rfl
    have : dp = eq := congrArg DPS.dp h
    calc aux0 (x :: xs) (y :: ys)
    _  = (y, eq) :: aux0 (x :: xs) ys := h
    _  = (y, dp) :: aux0 (x :: xs) ys := this.rec rfl

theorem aux0_def {y : α} {ys : List α} : aux0 (x :: xs) (y :: ys) =
    (y, aux4 x y (aux0 xs (y :: ys)).dp (aux0 (x :: xs) ys).dp (aux0 xs ys).dp) :: aux0 (x :: xs) ys :=
  let xx := aux0 xs (y :: ys) |>.dp
  let yy := aux0 (x :: xs) ys |>.dp
  let xy := aux0 xs ys |>.dp
  let dp := aux4 x y xx yy xy
  let pp := aux2 x (aux0 xs ys) |>.2
  let eq := aux4 x y xx pp.1 pp.2
  have : eq = dp :=
    have : pp = (yy, xy) := congrArg Prod.snd lem
    have h₁ : pp.1 = yy := congrArg Prod.fst this
    have h₂ : pp.2 = xy := congrArg Prod.snd this
    show aux4 x y xx pp.1 pp.2 = aux4 x y xx yy xy by rw [h₁, h₂]
  calc aux0 (x :: xs) (y :: ys)
  _  = aux1 x (aux0 xs (y :: ys)) := rfl
  _  = aux1 x ((y, xx) :: aux0 xs ys) := congrArg (aux1 x) aux0_cons
  _  = (y, eq) :: aux0 (x :: xs) ys := rfl
  _  = (y, dp) :: aux0 (x :: xs) ys := this.rec rfl
where lem : ∀ {ys}, aux2 x (aux0 xs ys) = (aux0 (x :: xs) ys, (aux0 (x :: xs) ys).dp, (aux0 xs ys).dp)
  | [] =>
    calc aux2 x (aux0 xs [])
    _  = aux2 x [] := congrArg _ aux0_nil
    _  = ([], dp0, dp0) := rfl
    _  = (aux0 (x :: xs) [], (aux0 (x :: xs) []).dp, (aux0 xs []).dp) := by rw [aux0_nil, aux0_nil]
  | y :: ys =>
    let zz := aux0 (x :: xs) (y :: ys) |>.dp
    let xx := aux0 xs (y :: ys) |>.dp
    let dps := aux0 (x :: xs) ys
    let yy := aux0 (x :: xs) ys |>.dp
    let xy := aux0 xs ys |>.dp
    let dp := aux4 x y xx yy xy

    have h₁ : aux0 (x :: xs) (y :: ys) = (y, dp) :: dps := aux0_def
    have h₂ : zz = dp := congrArg DPS.dp h₁

    calc aux2 x (aux0 xs (y :: ys))
    _  = aux2 x ((y, xx) :: aux0 xs ys) := congrArg _ aux0_cons
    _  = aux3 x (y, xx) (aux2 x (aux0 xs ys)) := rfl
    _  = aux3 x (y, xx) (dps, yy, xy) := congrArg _ lem
    _  = ((y, dp) :: dps, dp, xx) := rfl
    _  = (aux0 (x :: xs) (y :: ys), zz, xx) := by rw [h₁, h₂]

end lcs1

section
open lcs1

theorem nil_lcs1 {ys : List α} : lcs1 [] ys = [] := ys.casesOn rfl fun _ _ => rfl
theorem lcs1_nil {xs : List α} : lcs1 xs [] = [] := congrArg (DP.lcs ∘ DPS.dp) aux0_nil

theorem lcs1_eq_lcs0 : {xs ys : List α} → lcs1 xs ys = lcs0 xs ys
  | [], ys => nil_lcs1.trans nil_lcs0.symm
  | xs, [] => lcs1_nil.trans lcs0_nil.symm
  | x :: xs, y :: ys =>
    let xx1 := aux0 xs (y :: ys) |>.dp
    let yy1 := aux0 (x :: xs) ys |>.dp
    let xy1 := aux0 xs ys |>.dp

    let xx0 := lcs0 xs (y :: ys)
    let yy0 := lcs0 (x :: xs) ys
    let xy0 := lcs0 xs ys

    have hxx : xx1.lcs = xx0 := lcs1_eq_lcs0
    have hyy : yy1.lcs = yy0 := lcs1_eq_lcs0
    have hxy : xy1.lcs = xy0 := lcs1_eq_lcs0

    let e1 := if xx1.length ≥ yy1.length then xx1.lcs else yy1.lcs
    let e0 := if xx0.length ≥ yy0.length then xx0 else yy0
    have he : e1 = e0 := by unfold e1 ; rw [←xx1.length_eq, ←yy1.length_eq, hxx, hyy]

    calc lcs1 (x :: xs) (y :: ys)
    _  = (aux0 (x :: xs) (y :: ys)).dp.lcs := rfl
    _  = (aux4 x y xx1 yy1 xy1).lcs := congrArg (DP.lcs ∘ DPS.dp) aux0_def
    _  = if x = y then x :: xy1.lcs else DP.lcs _ := apply_ite DP.lcs ..
    _  = if x = y then x :: xy1.lcs else e1 := congrArg _ (apply_ite DP.lcs ..)
    _  = if x = y then x :: xy0 else e0 := by rw [hxy, he]
    _  = lcs0 (x :: xs) (y :: ys) := by unfold lcs0 ; rfl

end

theorem lcs1_LCS {xs ys : List α} : LCS xs ys (lcs1 xs ys) := lcs1_eq_lcs0.symm.rec lcs0_LCS

/-!
## Dynamic programming taking quadratic time and backtracking space (mutable vector)
-/

/-- Quadratic time and backtracking space dynamic programming. -/
def lcs2 (xs ys : List α) : List α := Id.run do
  if ys.isEmpty then
    return []
  let mut dps : Vector (List α × Nat) ys.length := default
  for x in xs.reverse do
    let mut i := 0
    let mut yy : List α × Nat := ([], 0)
    let mut xy : List α × Nat := ([], 0)
    for y in ys.reverse do
      let xx := dps[i]!
      yy := if x = y then (x :: xy.1, xy.2 + 1) else if xx.2 ≥ yy.2 then xx else yy
      dps := dps.set! i yy
      xy := xx
      i := i + 1
  return dps.back!.1

section unittest
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs2 ""        ""
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs2 "ABCD"    ""
/-- info: ""     -/ #guard_msgs(info) in #eval test_string lcs2 ""        "ACBAD"
/-- info: "ACD"  -/ #guard_msgs(info) in #eval test_string lcs2 "ABCD"    "ACBAD"
/-- info: "AC"   -/ #guard_msgs(info) in #eval test_string lcs2 "GAC"     "AGCAT"
/-- info: "MJAU" -/ #guard_msgs(info) in #eval test_string lcs2 "XMJYAUZ" "MZJAWXU"
end unittest

theorem lcs2_nil {xs : List α} : lcs2 xs [] = [] := rfl

open Std.Do in
theorem nil_lcs2 {ys : List α} : lcs2 [] ys = [] := by
  generalize h : lcs2 [] ys = zs
  apply Id.of_wp_run_eq h
  mvcgen invariants
  . ⇓ (_, dps) => ⌜dps = default⌝
  . ⇓ _ => ⌜True⌝
  case vc3.step.post.success pref _ _ h _ _ _ _ => match pref with | [] => nomatch h
  case vc5.a.isFalse.post.success hys dps h => exact
    match ys, hys with
    | y :: ys, _ =>
      show dps.back!.fst = [] from
      suffices dps.back! = default from congrArg Prod.fst this
      suffices dps.back? = some default from
        calc dps.back!
        _  = dps.back?.getD _ := Array.back!_eq_back?
        _  = (some default).getD _ := congrArg (Option.getD · default) this
      suffices _ from Array.back?_eq_some_iff.mpr ⟨_, this⟩
      calc dps.toArray
      _  = Array.replicate ys.length.succ default := congrArg _ h
      _  = (Array.replicate ys.length default).push default := Array.replicate_succ

theorem lcs2_eq_lcs1 : {xs ys : List α} → lcs2 xs ys = lcs1 xs ys
  | [], ys => nil_lcs2.trans nil_lcs1.symm
  | xs, [] => lcs2_nil.trans lcs1_nil.symm
  | x :: xs, y :: ys => sorry

theorem lcs2_eq_lcs0 {xs ys : List α} : lcs2 xs ys = lcs0 xs ys := trans lcs2_eq_lcs1 lcs1_eq_lcs0

theorem lcs2_LCS {xs ys : List α} : LCS xs ys (lcs2 xs ys) := lcs2_eq_lcs1.symm.rec lcs1_LCS
