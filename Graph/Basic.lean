structure Graph.{v,e} where
  V : Sort v
  E : Sort e
  src : E → V
  dst : E → V

-- inductive E
--   | «12» | «23» | «34» | «45» | «56» | «61»
--   | «17» | «18» | «27» | «29» | «38» | «39»
--   | «47» | «48» | «57» | «59» | «68» | «69»

example {α} (f : α → α) : Graph where
  V := α
  E := α
  src := id
  dst := f

example {α β} (f : α → β) : Graph where
  V := α ⊕ β
  E := α
  src := .inl
  dst := .inr ∘ f

example : Graph where
  V := Nat
  E := Nat
  src := id
  dst := .succ

example {V : Sort _} : Graph where
  V
  E := False
  src := False.rec
  dst := False.rec

def Fin.divisor {m n : Nat} (x : Fin n) (h : ∃ k, k * m = n) : Fin m :=
  if hm : m > 0 then
    ⟨x % m, x.modn_lt hm⟩
  else
    suffices n = 0 from (x.cast this).elim0
    have ⟨k, (hk : k * m = n)⟩ := h
    calc n
     _ = k * m := hk.symm
     _ = k * 0 := suffices m = 0 from congrArg _ this ; Nat.eq_zero_of_not_pos hm

#check Fin.zero_mul

example : Graph where
  V := Fin 6 ⊕ Fin 3 -- 7 => 1 | 8 => 0 | 9 => 2
  E := Fin 6 × (Unit ⊕ Fin 2)
  src | ⟨v, _⟩ => .inl v
  dst | ⟨v, .inl _⟩ => .inl (v + 1)
      | ⟨v, .inr b⟩ =>
        let u : Fin 3 := v.divisor ⟨2, rfl⟩
        .inr (u + Fin.ofNat 3 b)

#check Fin.add_def
