set_option autoImplicit false

namespace List
variable {α} [DecidableEq α]

def CommonSublist (cs xs ys : List α) : Prop := cs <+ xs ∧ cs <+ ys

def LCS (cs xs ys : List α) : Prop :=
  CommonSublist cs xs ys ∧ ∀ cs', CommonSublist cs' xs ys → cs'.length ≤ cs.length

structure LCS0 (xs ys : List α) where
  lcs : List α
  length : Nat
  length_eq : lcs.length = length
  sublist₁ : lcs <+ xs
  sublist₂ : lcs <+ ys
  longest : ∀ cs, CommonSublist cs xs ys → cs.length ≤ length

/-- Slow recursive. -/
def lcsAux0 : (xs ys : List α) → LCS0 xs ys
  | [], ys =>
    {
      lcs := []
      length := 0
      length_eq := rfl
      sublist₁ := .slnil
      sublist₂ := ys.nil_sublist
      longest _ h := eq_nil_of_sublist_nil h.1 ▸ Nat.le.refl
    }
  | xs, [] =>
    {
      lcs := []
      length := 0
      length_eq := rfl
      sublist₁ := xs.nil_sublist
      sublist₂ := .slnil
      longest _ h := eq_nil_of_sublist_nil h.2 ▸ Nat.le.refl
    }
  | x::as, y::bs =>
    if h₁ : x = y then
      let diag := lcsAux0 as bs
      {
        lcs := x::diag.lcs
        length := diag.length + 1
        length_eq := show diag.lcs.length + 1 = diag.length + 1 from diag.length_eq ▸ rfl
        sublist₁ := show x::diag.lcs <+ x::as from diag.sublist₁.cons₂ x
        sublist₂ := show x::diag.lcs <+ y::bs from h₁ ▸ diag.sublist₂.cons₂ x
        longest
          | [], _ => show [].length ≤ _ from Nat.zero_le _
          | _::cs, ⟨ha, hb⟩ =>
            show (_::cs).length ≤ diag.length + 1 from
            suffices cs.length ≤ diag.length from Nat.succ_le_succ this
            diag.longest cs ⟨ha.of_cons_cons, hb.of_cons_cons⟩
      }
    else
      let left := lcsAux0 as (y::bs)
      let up := lcsAux0 (x::as) bs
      if h₂ : left.length ≥ up.length then
        {
          left with
          sublist₁ := show left.lcs <+ x::as from left.sublist₁.cons x
          longest
            | cs, ⟨(ha : cs <+ x::as), (hb : cs <+ y::bs)⟩ =>
              match sublist_cons_iff.mp ha with
              | .inl (h : cs <+ as) => show cs.length ≤ left.length from left.longest cs ⟨h, hb⟩
              | .inr ⟨_, (h : cs = x::_), _⟩ =>
                have : cs <+ bs :=
                  match sublist_cons_iff.mp hb with
                  | .inl h => h
                  | .inr ⟨_, (e : cs = y::_), _⟩ =>
                    suffices x = y from absurd this h₁
                    cons.inj (h.symm.trans e) |>.1
                calc cs.length
                _  ≤ up.length := up.longest cs ⟨ha, this⟩
                _  ≤ left.length := h₂
        }
      else
        {
          up with
          sublist₂ := show up.lcs <+ y::bs from up.sublist₂.cons y
          longest
            | cs, ⟨(ha : cs <+ x::as), (hb : cs <+ y::bs)⟩ =>
              match sublist_cons_iff.mp hb with
              | .inl (h : cs <+ bs) => show cs.length ≤ up.length from up.longest cs ⟨ha, h⟩
              | .inr ⟨_, (h : cs = y::_), _⟩ =>
                have : cs <+ as :=
                  match sublist_cons_iff.mp ha with
                  | .inl h => h
                  | .inr ⟨_, (e : cs = x::_), _⟩ =>
                    suffices x = y from absurd this h₁
                    cons.inj (e.symm.trans h) |>.1
                calc cs.length
                _  ≤ left.length := left.longest cs ⟨this, hb⟩
                _  ≤ up.length := Nat.le_of_not_ge h₂
        }

example {x y : α} (hn : x ≠ y) {as bs : List α} (h : x::as <+ y::bs) : x::as <+ bs :=
  match y, sublist_cons_iff.mp h with
  | _, .inl (h : x::as <+ bs) => h
  | _, .inr ⟨_, rfl, _⟩ => absurd rfl hn

@[inherit_doc lcsAux0]
def lcs0 (xs ys : List α) : List α := (lcsAux0 xs ys).lcs

/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 [] []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 "ABCD".toList []
/-- info: ""     -/ #guard_msgs(info) in #eval String.mk <| lcs0 [] "ACBAD".toList
/-- info: "ACD"  -/ #guard_msgs(info) in #eval String.mk <| lcs0 "ABCD".toList "ACBAD".toList
/-- info: "AC"   -/ #guard_msgs(info) in #eval String.mk <| lcs0 "GAC".toList "AGCAT".toList
/-- info: "MJAU" -/ #guard_msgs(info) in #eval String.mk <| lcs0 "XMJYAUZ".toList "MZJAWXU".toList

-- theorem lcsAux0_nil₁ : (ys : List α) → lcsAux0 [] ys = ([], 0)
--   | [] | _::_ => by unfold lcsAux0 ; rfl
-- theorem lcsAux0_nil₂ : (xs : List α) → lcsAux0 xs [] = ([], 0)
--   | [] | _::_ => by unfold lcsAux0 ; rfl
-- theorem lcs0_nil₁ (ys : List α) : lcs0 [] ys = [] :=
--   congrArg Prod.fst ys.lcsAux0_nil₁
-- theorem lcs0_nil₂ (xs : List α) : lcs0 xs [] = [] :=
--   congrArg Prod.fst xs.lcsAux0_nil₂

theorem lcs0_sublist₁ (xs ys : List α) : lcs0 xs ys <+ xs := sorry

theorem lcs0_sublist₂ (xs ys : List α) : lcs0 xs ys <+ ys := sorry

theorem lcs0_length (xs ys : List α) : (lcs0 xs ys).length = (lcsAux0 xs ys).2 := sorry

theorem lcs0_LCS (xs ys : List α) : LCS (lcs0 xs ys) xs ys := sorry
