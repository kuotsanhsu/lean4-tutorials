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

abbrev DPS α := List (α × DP α)
def DPS.ys : DPS α → List α := map Prod.fst
def DPS.lcs : DPS α → List α
  | [] => []
  | (_, dp)::_ => dp.lcs

/-- Quadratic space dynamic programming. -/
def lcs1 (xs ys : List α) : List α := xs.foldr aux1 (ys.map (·, ⟨[], 0, rfl⟩)) |>.lcs
where
  aux1 (x : α) (dps : DPS α) : DPS α := dps.foldr (aux2 x) ([], ⟨[], 0, rfl⟩, ⟨[], 0, rfl⟩) |>.1
  aux2 (x : α) : α × DP α → DPS α × DP α × DP α → DPS α × DP α × DP α
    | (y, xx), (dps, yy, xy) =>
      let dp := aux3 x y xx yy xy
      ((y, dp)::dps, dp, xx)
  aux3 (x y : α) (xx yy xy : DP α) : DP α :=
    if x = y then ⟨x::xy.1, xy.2 + 1, xy.length_eq.rec rfl⟩ else if xx.2 ≥ yy.2 then xx else yy

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs1 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs1 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs1 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs1 "XMJYAUZ".toList "MZJAWXU".toList

theorem aux1_ys {x : α} {dps} : (lcs1.aux1 x dps).ys = dps.ys :=
  match dps with
  | [] => rfl
  | (y, xx)::(dps : DPS α) =>
    let dp0 : DP α := ⟨[], 0, rfl⟩
    have :=
      calc ((y, xx)::dps).foldr (lcs1.aux2 x) ([], dp0, dp0)
      _  = lcs1.aux2 x (y, xx) (dps.foldr (lcs1.aux2 x) _) := rfl
      _  = ((y, _)::lcs1.aux1 x dps, _, _) := rfl
    calc ((y, xx)::dps).foldr (lcs1.aux2 x) _ |>.1.ys
    _  = DPS.ys ((y, _)::lcs1.aux1 x dps) := congrArg (·.1.ys) this
    _  = y::(lcs1.aux1 x dps).ys := rfl
    _  = y::dps.ys := congrArg _ aux1_ys
    _  = DPS.ys ((y, xx)::dps) := rfl

theorem aux1_correct {x} {xs ys : List α} {dps : DPS α} (h : dps.lcs = lcs1 xs ys) :
    (lcs1.aux1 x dps).lcs = lcs1 (x::xs) ys := sorry

theorem correct : {xs ys : List α} → lcs1 xs ys = lcs0 xs ys
  | [], ys => sorry
  | xs, [] => sorry
  | x::as, ys =>
    let dp0 : DP α := ⟨[], 0, rfl⟩
    let dps0 := ys.map (·, dp0)
    let init : DPS α × DP α × DP α := ([], dp0, dp0)
    -- match e : dps.foldr (lcs1.aux2 x) init with
    -- | (dps', yy, xy) =>
    --   let dp := lcs1.aux3 x y xx yy xy
    --   have :=
    --     calc ((y, xx)::dps).foldr (lcs1.aux2 x) init
    --     _  = lcs1.aux2 x (y, xx) (dps.foldr (lcs1.aux2 x) init) := rfl
    --     _  = lcs1.aux2 x (y, xx) (dps', yy, xy) := congrArg _ e
    --     _  = ((y, dp)::dps', _) := rfl
    let dps := as.foldr lcs1.aux1 dps0
    match e : dps with
    | [] => sorry
    | (y, xx)::dps' =>
      match e' : dps'.foldr (lcs1.aux2 x) init with
      | (dps'', yy, xy) =>
        let dp := lcs1.aux3 x y xx yy xy
        calc lcs1 (x::as) ys
        _  = ((x::as).foldr lcs1.aux1 dps0).lcs := rfl
        _  = (lcs1.aux1 x dps).lcs := rfl
        _  = (dps.foldr (lcs1.aux2 x) init).1.lcs := rfl
        _  = (lcs1.aux2 x (y, xx) (dps'.foldr (lcs1.aux2 x) init)).1.lcs := e ▸ rfl
        _  = (lcs1.aux2 x (y, xx) (dps'', yy, xy)).1.lcs := e' ▸ rfl
        _  = dp.lcs := rfl
        _  = lcs0 (x::as) ys := sorry

theorem lcs1_eq_lcs0 {xs ys : List α} : lcs1 xs ys = lcs0 xs ys :=
  let dp0 : DP α := ⟨[], 0, rfl⟩
  let dps0 : DPS α := ys.map (·, dp0)
  have dps0_ys : dps0.ys = ys :=
    match e : ys with
    | [] => show DPS.ys (ys.map (·, dp0)) = DPS.ys ([].map (·, dp0)) from e ▸ rfl
    | y::bs =>
      calc DPS.ys (ys.map (·, dp0))
      _  = DPS.ys ((y::bs).map (·, dp0)) := e ▸ rfl
      _  = (y::bs).map id := map_map
      _  = y::bs := map_id _
  have dps0_lcs : dps0.lcs = [] :=
    match e : ys with
    | [] => show DPS.lcs (ys.map (·, dp0)) = DPS.lcs ([].map (·, dp0)) from e ▸ rfl
    | y::bs => show DPS.lcs (ys.map (·, dp0)) = DPS.lcs ((y::bs).map (·, dp0)) from e ▸ rfl
  have lcs0_nil : lcs0 [] ys = [] :=
    match ys with | [] | y::bs => by unfold lcs0 ; unfold lcs0.aux ; rfl
  match xs with
  | [] =>
    calc lcs1 [] ys
    _  = ([].foldr lcs1.aux1 dps0).lcs := rfl
    _  = dps0.lcs := congrArg _ foldr_nil
    _  = [] := dps0_lcs
    _  = lcs0 [] ys := lcs0_nil.symm
  | x::as =>
    let dps := as.foldr lcs1.aux1 dps0
    have e :=
      calc dps.ys
      _  = dps0.ys := tt3
      _  = ys := dps0_ys
    have :=
      calc dps.lcs
      _  = (as.foldr lcs1.aux1 dps0).lcs := rfl
      _  = lcs0 as ys := lcs1_eq_lcs0
      _  = lcs0 as dps.ys := congrArg _ e.symm
    calc ((x::as).foldr lcs1.aux1 dps0).lcs
    _  = (lcs1.aux1 x dps).lcs := congrArg _ rfl
    _  = lcs0 (x::as) dps.ys := tt4 this
    _  = lcs0 (x::as) ys := congrArg _ e
where
  tt2 {x : α} {dps} : (lcs1.aux1 x dps).ys = dps.ys :=
    match dps with
    | [] => rfl
    | (y, xx)::(dps : DPS α) =>
      let dp0 : DP α := ⟨[], 0, rfl⟩
      have :=
        calc ((y, xx)::dps).foldr (lcs1.aux2 x) ([], dp0, dp0)
        _  = lcs1.aux2 x (y, xx) (dps.foldr (lcs1.aux2 x) _) := rfl
        _  = ((y, _)::lcs1.aux1 x dps, _, _) := rfl
      calc ((y, xx)::dps).foldr (lcs1.aux2 x) _ |>.1.ys
      _  = DPS.ys ((y, _)::lcs1.aux1 x dps) := congrArg (·.1.ys) this
      _  = y::(lcs1.aux1 x dps).ys := rfl
      _  = y::dps.ys := congrArg _ tt2
      _  = DPS.ys ((y, xx)::dps) := rfl
  tt3 {xs dps} : (xs.foldr lcs1.aux1 dps).ys = dps.ys :=
    match xs with
    | [] => rfl
    | x::as =>
      let dps' := as.foldr lcs1.aux1 dps
      calc ((x::as).foldr lcs1.aux1 dps).ys
      _  = (lcs1.aux1 x dps').ys := rfl
      _  = dps'.ys := tt2
      _  = dps.ys := tt3
  tt4 {x : α} {as dps} (h : dps.lcs = lcs0 as dps.ys) : (lcs1.aux1 x dps).lcs = lcs0 (x::as) dps.ys :=
    match dps with
    | [] =>
      calc (lcs1.aux1 x []).lcs
      _  = [] := sorry
      _  = lcs0 (x::as) [] := sorry
    | (y, xx)::(dps : DPS α) =>
      let dp0 : DP α := ⟨[], 0, rfl⟩
      match e : dps.foldr (lcs1.aux2 x) ([], dp0, dp0) with
      | (dps', yy, xy) =>
        let dp := lcs1.aux3 x y xx yy xy
        have :=
          calc ((y, xx)::dps).foldr (lcs1.aux2 x) ([], dp0, dp0)
          _  = lcs1.aux2 x (y, xx) (dps.foldr (lcs1.aux2 x) ([], dp0, dp0)) := rfl
          _  = lcs1.aux2 x (y, xx) (dps', yy, xy) := congrArg _ e
          _  = ((y, dp)::dps', _) := rfl
          -- _  = ((y, dp)::lcs1.aux1 x dps, _, _) := sorry
        calc (lcs1.aux1 x ((y, xx)::dps)).lcs
        _  = (((y, xx)::dps).foldr (lcs1.aux2 x) _).1.lcs := rfl
        _  = dp.lcs := congrArg (·.1.lcs) this
        _  = DPS.lcs ((y, dp)::dps') := rfl
        _  = lcs0 (x::as) (DPS.ys ((y, xx)::dps)) := sorry

example {x y : α} {xx dps yy xy} : (lcs1.aux2 x (y, xx) (dps, yy, xy)).2 = (lcs1.aux3 x y xx yy xy, xx) := rfl
example {x y : α} {xx dps yy xy} : (lcs1.aux2 x (y, xx) (dps, yy, xy)).1 = (y, lcs1.aux3 x y xx yy xy)::dps := rfl

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
