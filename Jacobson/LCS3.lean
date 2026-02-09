set_option autoImplicit false

/-!
# Longest Common Subsequence (Sublist)

I first define what it means for a list to be a common sublist of two other lists. Then, I define
what it means for a common sublist of two lists to be the longest.

I provide 3 implementations of the LCS algorithm. Their unit tests take the form of
`#guard_msgs in #eval`. Currently, I prove the correctness of the slow recursive implementation,
i.e. the theorem `lcs0_LCS`. To prove the correctness of `lcs1_LCS` and `lcs2_LCS`, it suffices to
prove the functional equality between `lcs0`, `lcs1`, `lcs2` which are captured by the two unproven
theorems: `lcs1_eq_lcs0` and `lcs2_eq_lcs1`; nowhere else is `sorry` to be seen.

-/

namespace List
variable {α} [DecidableEq α]

structure CommonSublist (xs ys cs : List α) : Prop where
  sublist₁ : cs <+ xs
  sublist₂ : cs <+ ys

structure LCS (xs ys lcs : List α) : Prop extends CommonSublist xs ys lcs where
  longest : ∀ cs, CommonSublist xs ys cs → cs.length ≤ lcs.length

/-!
## Straightforward recursion but slow
-/

/-- Slow recursive. -/
def lcs0 (xs ys : List α) : List α := aux xs ys
where aux : (xs ys : List α) → Subtype (LCS xs ys)
  | [], ys =>
    {
      val := []
      property.sublist₁ := .slnil
      property.sublist₂ := ys.nil_sublist
      property.longest | _, ⟨h, _⟩ => eq_nil_of_sublist_nil h ▸ Nat.le.refl
    }
  | xs, [] =>
    {
      val := []
      property.sublist₁ := xs.nil_sublist
      property.sublist₂ := .slnil
      property.longest | _, ⟨_, h⟩ => eq_nil_of_sublist_nil h ▸ Nat.le.refl
    }
  | x::as, y::bs =>
    if h₁ : x = y then
      let xy := aux as bs
      {
        val := x::xy
        property.sublist₁ := show x::xy <+ x::as from xy.2.sublist₁.cons₂ x
        property.sublist₂ := show x::xy <+ y::bs from h₁ ▸ xy.2.sublist₂.cons₂ x
        property.longest
          | [], _ => show [].length ≤ _ from Nat.zero_le _
          | _::cs, ⟨ha, hb⟩ =>
            show (_::cs).length ≤ (_::xy.1).length from
            suffices cs.length ≤ xy.1.length from Nat.succ_le_succ this
            xy.2.longest cs ⟨ha.of_cons_cons, hb.of_cons_cons⟩
      }
    else
      let xx := aux as (y::bs)
      let yy := aux (x::as) bs
      if h₂ : xx.1.length ≥ yy.1.length then
        {
          xx with
          property.sublist₁ := show xx <+ x::as from xx.2.sublist₁.cons x
          property.longest
            | cs, ⟨(ha : cs <+ x::as), (hb : cs <+ y::bs)⟩ =>
              match sublist_cons_iff.mp ha with
              | .inl (h : cs <+ as) => show cs.length ≤ xx.1.length from xx.2.longest cs ⟨h, hb⟩
              | .inr ⟨_, (h : cs = x::_), _⟩ =>
                have : cs <+ bs :=
                  match sublist_cons_iff.mp hb with
                  | .inl h => h
                  | .inr ⟨_, (e : cs = y::_), _⟩ =>
                    suffices x = y from absurd this h₁
                    cons.inj (h.symm.trans e) |>.1
                calc cs.length
                _  ≤ yy.1.length := yy.2.longest cs ⟨ha, this⟩
                _  ≤ xx.1.length := h₂
        }
      else
        {
          yy with
          property.sublist₂ := show yy <+ y::bs from yy.2.sublist₂.cons y
          property.longest
            | cs, ⟨(ha : cs <+ x::as), (hb : cs <+ y::bs)⟩ =>
              match sublist_cons_iff.mp hb with
              | .inl (h : cs <+ bs) => show cs.length ≤ yy.1.length from yy.2.longest cs ⟨ha, h⟩
              | .inr ⟨_, (h : cs = y::_), _⟩ =>
                have : cs <+ as :=
                  match sublist_cons_iff.mp ha with
                  | .inl h => h
                  | .inr ⟨_, (e : cs = x::_), _⟩ =>
                    suffices x = y from absurd this h₁
                    cons.inj (e.symm.trans h) |>.1
                calc cs.length
                _  ≤ xx.1.length := xx.2.longest cs ⟨this, hb⟩
                _  ≤ yy.1.length := Nat.le_of_not_ge h₂
        }

theorem lcs0_LCS {xs ys : List α} : LCS xs ys (lcs0 xs ys) := (lcs0.aux xs ys).property

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs0 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs0 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs0 "XMJYAUZ".toList "MZJAWXU".toList

/-!
## Dynamic programming taking quadratic time and space (list of list)
-/

structure DP α where
  lcs : List α
  length : Nat
  length_eq : lcs.length = length

abbrev dp0 : DP α := ⟨[], 0, rfl⟩

abbrev DPS α := List (α × DP α)
def DPS.ys : DPS α → List α := map Prod.fst
def DPS.dp : DPS α → DP α
  | [] => dp0
  | (_, dp)::_ => dp

abbrev dps0 (ys : List α) : DPS α := ys.map (·, dp0)

/-- Quadratic space dynamic programming. -/
def lcs1 (xs ys : List α) : List α := aux0.dp.lcs
where
  aux0 : DPS α := xs.foldr aux1 ys.dps0
  aux1 (x : α) (dps : DPS α) : DPS α := (aux2 x dps).1
  aux2 (x : α) (dps : DPS α) : DPS α × DP α × DP α :=
    dps.foldr (aux3 x) ([], dp0, dp0)
  aux3 (x : α) : α × DP α → DPS α × DP α × DP α → DPS α × DP α × DP α
    | (y, xx), (dps, yy, xy) =>
      let dp := aux4 x y xx yy xy
      ((y, dp) :: dps, dp, xx)
  aux4 (x y : α) (xx yy xy : DP α) : DP α :=
    if x = y then
      ⟨x :: xy.1, xy.2 + 1, xy.length_eq.rec rfl⟩
    else if xx.2 ≥ yy.2 then xx else yy

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs1 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs1 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs1 "XMJYAUZ".toList "MZJAWXU".toList

theorem aux0_ex {y : α} {xs ys : List α} :
    lcs1.aux0 xs (y :: ys) = (y, (lcs1.aux0 xs (y :: ys)).dp) :: lcs1.aux0 xs ys :=
  match xs with
  | [] => rfl
  | x :: xs =>
    let xx := lcs1.aux0 xs (y :: ys) |>.dp
    let dp := lcs1.aux0 (x :: xs) (y :: ys) |>.dp
    let pp := lcs1.aux2 x (lcs1.aux0 xs ys) |>.2
    let eq := lcs1.aux4 x y xx pp.1 pp.2
    have h :=
      calc lcs1.aux0 (x :: xs) (y :: ys)
      _  = (x :: xs).foldr lcs1.aux1 (y :: ys).dps0 := rfl
      _  = lcs1.aux1 x (lcs1.aux0 xs (y :: ys)) := rfl
      _  = lcs1.aux1 x ((y, xx) :: lcs1.aux0 xs ys) := congrArg (lcs1.aux1 x) aux0_ex
      _  = (y, eq) :: lcs1.aux0 (x :: xs) ys := rfl
    have : dp = eq := congrArg DPS.dp h
    calc lcs1.aux0 (x :: xs) (y :: ys)
    _  = (y, eq) :: lcs1.aux0 (x :: xs) ys := h
    _  = (y, dp) :: lcs1.aux0 (x :: xs) ys := this.rec rfl

theorem aux0_nil {xs : List α} : lcs1.aux0 xs [] = [] :=
  match xs with
  | [] => rfl
  | x :: xs =>
    calc lcs1.aux0 (x :: xs) []
    _  = (x :: xs).foldr lcs1.aux1 [] := rfl
    _  = lcs1.aux1 x (xs.foldr lcs1.aux1 []) := rfl
    _  = lcs1.aux1 x (lcs1.aux0 xs []) := rfl
    _  = lcs1.aux1 x [] := congrArg (lcs1.aux1 x) aux0_nil
    _  = [] := rfl

mutual
theorem aux4_rec {x : α} {xs ys : List α} :
    lcs1.aux2 x (lcs1.aux0 xs ys) =
    (lcs1.aux0 (x :: xs) ys, (lcs1.aux0 (x :: xs) ys).dp, (lcs1.aux0 xs ys).dp) :=
  match ys with
  | [] =>
    calc lcs1.aux2 x (lcs1.aux0 xs [])
    _  = lcs1.aux2 x [] := congrArg _ aux0_nil
    _  = ([], dp0, dp0) := rfl
    _  = (lcs1.aux0 (x :: xs) [], (lcs1.aux0 (x :: xs) []).dp, (lcs1.aux0 xs []).dp) :=
      by rw [aux0_nil, aux0_nil] ; rfl
  | y :: ys =>
    let zz := lcs1.aux0 (x :: xs) (y :: ys) |>.dp
    let xx := lcs1.aux0 xs (y :: ys) |>.dp
    let dps := lcs1.aux0 (x :: xs) ys
    let yy := lcs1.aux0 (x :: xs) ys |>.dp
    let xy := lcs1.aux0 xs ys |>.dp
    let dp := lcs1.aux4 x y xx yy xy

    have h₁ : lcs1.aux0 (x :: xs) (y :: ys) = (y, dp) :: dps := aux0_rec
    have h₂ : zz = dp := congrArg DPS.dp h₁

    calc lcs1.aux2 x (lcs1.aux0 xs (y :: ys))
    _  = lcs1.aux2 x ((y, xx) :: lcs1.aux0 xs ys) := congrArg _ aux0_ex
    _  = lcs1.aux3 x (y, xx) (lcs1.aux2 x (lcs1.aux0 xs ys)) := rfl
    _  = lcs1.aux3 x (y, xx) (dps, yy, xy) := congrArg _ aux4_rec
    _  = ((y, dp) :: dps, dp, xx) := rfl
    _  = (lcs1.aux0 (x :: xs) (y :: ys), zz, xx) := by rw [h₁, h₂]

theorem aux0_rec {x y : α} {xs ys : List α} :
    lcs1.aux0 (x :: xs) (y :: ys) =
    (y, lcs1.aux4 x y (lcs1.aux0 xs (y :: ys)).dp (lcs1.aux0 (x :: xs) ys).dp (lcs1.aux0 xs ys).dp)
    :: lcs1.aux0 (x :: xs) ys :=
  let xx := lcs1.aux0 xs (y :: ys) |>.dp
  let yy := lcs1.aux0 (x :: xs) ys |>.dp
  let xy := lcs1.aux0 xs ys |>.dp
  let dp := lcs1.aux4 x y xx yy xy
  let pp := lcs1.aux2 x (lcs1.aux0 xs ys) |>.2
  let eq := lcs1.aux4 x y xx pp.1 pp.2
  have : eq = dp :=
    have : pp = (yy, xy) := congrArg Prod.snd aux4_rec
    have h₁ : pp.1 = yy := congrArg Prod.fst this
    have h₂ : pp.2 = xy := congrArg Prod.snd this
    show lcs1.aux4 x y xx pp.1 pp.2 = lcs1.aux4 x y xx yy xy by rw [h₁, h₂]
  calc lcs1.aux0 (x :: xs) (y :: ys)
  _  = (x :: xs).foldr lcs1.aux1 (y :: ys).dps0 := rfl
  _  = lcs1.aux1 x (lcs1.aux0 xs (y :: ys)) := rfl
  _  = lcs1.aux1 x ((y, xx) :: lcs1.aux0 xs ys) := congrArg (lcs1.aux1 x) aux0_ex
  _  = (y, eq) :: lcs1.aux0 (x :: xs) ys := rfl
  _  = (y, dp) :: lcs1.aux0 (x :: xs) ys := this.rec rfl
end

theorem nil_lcs1 {ys : List α} : lcs1 [] ys = [] := ys.casesOn rfl fun _ _ => rfl
theorem lcs1_nil {xs : List α} : lcs1 xs [] = [] := congrArg (DP.lcs ∘ DPS.dp) aux0_nil

def lcs0' : List α → List α → List α
  | [], _
  | _, [] => []
  | x :: xs, y :: ys =>
    if x = y then
      x :: lcs0' xs ys
    else
      let xx := lcs0' xs (y :: ys)
      let yy := lcs0' (x :: xs) ys
      if xx.length ≥ yy.length then xx else yy

theorem nil_lcs0' : {ys : List α} → lcs0' [] ys = [] | [] | _ :: _ => by unfold lcs0' ; rfl
theorem lcs0'_nil : {xs : List α} → lcs0' xs [] = [] | [] | _ :: _ => by unfold lcs0' ; rfl

theorem lcs0_eq_lcs0' {xs ys : List α} : lcs0 xs ys = lcs0' xs ys :=
  match xs, ys with
  | [], ys => by unfold lcs0 ; unfold lcs0.aux ; unfold lcs0' ; cases ys ; rfl ; rfl
  | xs, [] => by unfold lcs0 ; unfold lcs0.aux ; unfold lcs0' ; cases xs ; rfl ; rfl
  | x :: xs, y :: ys => by unfold lcs0 ; unfold lcs0.aux ; unfold lcs0' ; exact
    if h₁ : x = y then
      by { rw [if_pos h₁, apply_dite Subtype.val] ; simp [h₁] ; exact lcs0_eq_lcs0' }
    else
      let xx := lcs0.aux xs (y :: ys)
      let xx' := lcs0' xs (y :: ys)
      have hxx : xx.1 = xx' := lcs0_eq_lcs0'
      let yy := lcs0.aux (x :: xs) ys
      let yy' := lcs0' (x :: xs) ys
      have hyy : yy.1 = yy' := lcs0_eq_lcs0'
      by {
        rw [if_neg h₁] ; simp [h₁]
        calc
        _  = if h : xx.1.length ≥ yy.1.length then xx.1 else yy.1 := apply_dite Subtype.val ..
        _  = if h : xx'.length ≥ yy'.length then xx' else yy' := by rw [hxx, hyy]
        _  = if xx'.length ≥ yy'.length then xx' else yy' := dite_eq_ite
      }

theorem lcs1_eq_lcs0' {xs ys : List α} : lcs1 xs ys = lcs0' xs ys :=
  match xs, ys with
  | [], ys => nil_lcs1.trans nil_lcs0'.symm
  | xs, [] => lcs1_nil.trans lcs0'_nil.symm
  | x :: xs, y :: ys =>
    let xx1 := lcs1.aux0 xs (y :: ys) |>.dp
    let yy1 := lcs1.aux0 (x :: xs) ys |>.dp
    let xy1 := lcs1.aux0 xs ys |>.dp

    let xx0 := lcs0' xs (y :: ys)
    let yy0 := lcs0' (x :: xs) ys
    let xy0 := lcs0' xs ys

    have hxx : xx1.lcs = xx0 := lcs1_eq_lcs0'
    have hyy : yy1.lcs = yy0 := lcs1_eq_lcs0'
    have hxy : xy1.lcs = xy0 := lcs1_eq_lcs0'

    let e1 := if xx1.length ≥ yy1.length then xx1.lcs else yy1.lcs
    let e0 := if xx0.length ≥ yy0.length then xx0 else yy0
    have ee : e1 = e0 := by unfold e1 ; rw [←xx1.length_eq, ←yy1.length_eq, hxx, hyy]

    calc lcs1 (x :: xs) (y :: ys)
    _  = (lcs1.aux0 (x :: xs) (y :: ys)).dp.lcs := rfl
    _  = (lcs1.aux4 x y xx1 yy1 xy1).lcs := congrArg (DP.lcs ∘ DPS.dp) aux0_rec
    _  = if x = y then x :: xy1.lcs else DP.lcs _ := apply_ite DP.lcs ..
    _  = if x = y then x :: xy1.lcs else e1 := congrArg _ (apply_ite DP.lcs ..)
    _  = if x = y then x :: xy0 else e0 := by rw [hxy, ee]
    _  = lcs0' (x :: xs) (y :: ys) := by unfold lcs0' ; rfl

theorem lcs1_eq_lcs0 {xs ys : List α} : lcs1 xs ys = lcs0 xs ys := lcs1_eq_lcs0'.trans lcs0_eq_lcs0'.symm

theorem lcs1_LCS {xs ys : List α} : LCS xs ys (lcs1 xs ys) := lcs1_eq_lcs0.symm.rec lcs0_LCS

/-!
## Dynamic programming taking quadratic time and backtracking space (mutable vector)
-/

/-- Linear space dynamic programming. -/
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
      yy := if x = y then (x::xy.1, xy.2 + 1) else if xx.2 ≥ yy.2 then xx else yy
      dps := dps.set! i yy
      xy := xx
      i := i + 1
  return dps.back!.1

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs2 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs2 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs2 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs2 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs2 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs2 "XMJYAUZ".toList "MZJAWXU".toList

theorem lcs2_eq_lcs1 {xs ys : List α} : lcs2 xs ys = lcs1 xs ys := sorry

theorem lcs2_eq_lcs0 {xs ys : List α} : lcs2 xs ys = lcs0 xs ys := trans lcs2_eq_lcs1 lcs1_eq_lcs0

theorem lcs2_LCS {xs ys : List α} : LCS xs ys (lcs2 xs ys) := lcs2_eq_lcs1.symm.rec lcs1_LCS
