#check Classical.em
def excluded_middle : Prop := ∀ p : Prop, p ∨ ¬p

/-! ## Exercise: 5 stars, standard, optional (classical_axioms)

For those who like a challenge, here is an exercise adapted from the Coq'Art book by Bertot and Casteran (p. 123). Each of the following five statements, together with `excluded_middle`, can be considered as characterizing classical logic. We can't prove any of them in Coq, but we can consistently add any one of them as an axiom if we wish to work in classical logic.

Prove that all six propositions (these five plus `excluded_middle`) are equivalent.

Hint: Rather than considering all pairs of statements pairwise, prove a single circular chain of implications that connects them all.
-/

def peirce : Prop := ∀ p q : Prop, ((p → q) → p) → p

#check Classical.not_not
def double_negation_elim : Prop := ∀ p : Prop, ¬¬p → p

#check Classical.not_and_iff_not_or_not
def de_morgan_not_and_not : Prop := ∀ p q : Prop, ¬(¬p ∧ ¬q) → p ∨ q

def implies_to_or : Prop := ∀ p q : Prop, (p → q) → (¬p ∨ q)

def consequentia_mirabilis : Prop := ∀ p : Prop, (¬p → p) → p

example : excluded_middle → peirce
  | h, p, _, h' => (h p).elim id fun hnp => h' hnp.elim

example : peirce → double_negation_elim
  | h, hp, hnnp => h hp False hnnp.elim

example : double_negation_elim → de_morgan_not_and_not
  | h, p, q, hn => h (p ∨ q) fun h' => hn ⟨h' ∘ .inl, h' ∘ .inr⟩

example : de_morgan_not_and_not → implies_to_or
  | h, p, q, hpq => h (¬p) q fun ⟨hnnp, hnq⟩ => hnnp (hnq ∘ hpq)

example : implies_to_or → consequentia_mirabilis
  | h, p => (h p p id).symm.elim id

example : consequentia_mirabilis → excluded_middle
  | h, p => h (p ∨ ¬p) fun h' => h'.elim (.inr (h' ∘ .inl))

example : consequentia_mirabilis → excluded_middle
  | (h : ∀ p, (¬p → p) → p), p => show p ∨ ¬p by
    apply h (p ∨ ¬p) ; intro (h' : ¬(p ∨ ¬p))
    exfalso ; apply h' ; right
    intro (hp : p) ; apply h' ; left ; exact hp

example : consequentia_mirabilis → excluded_middle
  | (h : ∀ p, (¬p → p) → p), p => show p ∨ ¬p from
    h (p ∨ ¬p) fun h' : ¬(p ∨ ¬p) =>
    False.elim <| h' <| .inr
    fun hp : p => h' <| .inl hp

example p : p → ¬¬p | hp, hnp => hnp hp
example p : ¬¬(p ∨ ¬p) | h => h (.inr (h ∘ .inl))
example p : ¬¬(p ∨ ¬p) | h => (h ∘ .inr) (h ∘ .inl)
#check not_not_em
