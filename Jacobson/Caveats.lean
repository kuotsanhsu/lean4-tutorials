set_option autoImplicit false

variable {α}

example {x : α} : ([x], 0) = ([x], 0) := rfl

def g : List Nat → List Nat → Nat × Nat
  | [], _
  | _, [] => (0, 1)
  | x::_, y::_ => (2, 3)
example : g [] [] = (0, 1) := rfl
example (y : Nat) (ys : List Nat) : g [] (y::ys) = (0, 1) := rfl
example (x : Nat) (xs : List Nat) : g (x::xs) [] = (0, 1) := rfl
example (ys : List Nat) : g [] ys = (0, 1) := by unfold g ; simp
example (xs : List Nat) : g xs [] = (0, 1) := by unfold g ; simp
example : (ys : List Nat) → g [] ys = (0, 1)
  | [] => rfl
  | _::_ => rfl
example : (xs : List Nat) → g xs [] = (0, 1)
  | [] => rfl
  | _::_ => rfl

@[reducible]
def f : List α → List α → List α × Nat
  | x::_, y::_ => ([x, y], 2)
  | [], _
  | _, [] => ([], 0)
example (ys : List α) : f [] ys = ([], 0) := rfl
example (xs : List α) : f xs [] = ([], 0) := rfl
