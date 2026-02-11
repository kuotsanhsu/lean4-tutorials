import Std.Tactic.Do

set_option autoImplicit false

def sum1 (ns : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for n in ns do
    sum := sum + n
  return sum

def sum2 (ns : Array Nat) : Nat := prog.run
where prog : Id Nat := do
  let mut sum := 0
  for n in ns do
    sum := sum + n
  return sum

section
variable {ns : Array Nat}

open Std.Do

example : sum1 ns = ns.sum := by
  generalize h : sum1 ns = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  . ⇓g => ⌜g.1.prefix.sum = g.2⌝
  with grind

example : sum1 ns = ns.sum := by
  generalize h : sum1 ns = x
  apply Id.of_wp_run_eq h
  mvcgen
  . exact .noThrow fun (c, s) => .pure (c.prefix.sum = s)
  . case _ h => simp ; simp at h ; exact h -- simp_all
  . simp
  . case _ h => simp at h ; exact h.symm

example : sum1 ns = ns.sum := by
  generalize h : sum1 ns = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  . ⇓g => ⌜g.1.prefix.sum = g.2⌝
  case _ h => simp ; exact h -- simp_all
  case _ h => simp at h ; exact h.symm

example : sum1 ns = ns.sum := by
  generalize h : sum1 ns = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓g => ⌜g.1.prefix.sum = g.2⌝
  with
  | _ ns n _ _ s h =>
    calc (ns ++ [n]).sum
    _  = ns.sum + n := List.sum_append_nat
    _  = s + n := h ▸ rfl
  | _ s h =>
    calc s
    _  = ns.toList.sum := h.symm
    _  = ns.sum := Array.sum_eq_sum_toList


-- #eval ⌜True⌝.down
#reduce wp⟦sum2.prog ns⟧ (PostCond.noThrow fun a => ⟨a = ns.sum⟩)

example : sum2 ns = ns.sum :=
  let inv : PostCond (ns.toList.Cursor × Nat) PostShape.pure :=
    PostCond.noThrow fun (c, s) => SPred.pure (c.prefix.sum = s)
  let P : Nat → Prop := (· = ns.sum)
  let a : Assertion PostShape.pure := wp⟦sum2.prog ns⟧ (PostCond.noThrow fun s => ⟨P s⟩)
  suffices ⊢ₛ a from @Id.of_wp_run_eq Nat (sum2 ns) (sum2.prog ns) rfl P this
  -- Spec.forIn_array inv _
  show Triple (sum2.prog ns) ⌜True⌝ (PostCond.noThrow fun a => _) from
  -- show @SPred.entails [] ⌜True⌝ a from
  fun _ => show a.down from
  show (sum2.prog ns).run = ns.sum from
  -- Spec.forIn_array inv _
  sorry

#guard_msgs(drop error) in
example : sum2 ns = ns.sum :=
  let inv := fun g : ns.toList.Cursor × Nat => g.1.prefix.sum = g.2
  suffices _ from Id.of_wp_run_eq (prog := sum2.prog ns) _ inv this
  fun x => _

#check Id.of_wp_run_eq

end
