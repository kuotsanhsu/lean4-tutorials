set_option autoImplicit false

namespace InformalSyntactic

inductive Term Var
  /-- `x` -/
  | var (x : Var)
  /-- `λx.t` -/
  | lam (x : Var) (t : Term Var)
  /-- `t(t')` -/
  | app (t t' : Term Var)

namespace Term
variable {Var}

instance : Coe Var (Term Var) where coe := var

example : Term String := "x"
example (t : Term String) : Term String := lam "x" t
example (t t' : Term String) : Term String := app t t'

/-- We write `B[a/x]` for the **substitution** of a term `a` for free occurrences of the variable `x` in the term `B`, with possible capture-avoiding renaming of bound variables. -/
def subst (B a : Term Var) (x : Var) : Term Var := sorry

inductive Alpha : Term Var → Term Var → Prop
  | refl {t} : Alpha t t
  | conv {i j t} : Alpha (lam i t) (lam j (t.subst j i))

inductive Beta : Term Var → Term Var → Prop
  | alpha {t t'} : Alpha t t' → Beta t t'
  | conv {x t u} : Beta (app (lam x t) u) (t.subst u x)
  | congr_app {t t' s s'} : Beta t t' → Beta s s' → Beta (app t s) (app t' s')
  | congr_lam {t t' x} : Beta (lam x t) (lam x t')

end Term

/-- `a : A` -/
structure JTy Var where
  (element type : Term Var)

/-- The equality judgment `t ≡ u : A`. -/
structure JEq Var where
  (left right type : Term Var)
  beta : left.Beta right

/-
mutual
inductive Context Var
  | empty : Context Var
  | push (Γ : Context Var) (x : Var) (A : Term Var) (distinct : ¬Mem Var Γ x)
inductive Mem Var : Context Var → Var → Prop
end
-/

#check List.Pairwise
#check List.lookup
structure Context Var where
  assumptions : List (Var × Term Var)
  distinct : assumptions.Pairwise fun ⟨x, _⟩ ⟨y, _⟩ => x ≠ y

end InformalSyntactic

namespace FormalSyntactic

inductive Tm
  | app
  | lam
inductive Ty
  | Pi (A B : Ty)
  | U
  | El (A : Tm)
inductive Con
  | emp
  | ext (Γ : Con) (A : Ty)

mutual
  inductive JCon : Con → Prop
    | emp : JCon .emp
    | ext {Γ A} : JCon Γ → JTy Γ A → JCon (Γ.ext A)
  inductive JTy : Con → Ty → Prop
    | Pi {Γ A B} : JCon Γ → JTy Γ A → JTy (Γ.ext A) B → JTy Γ (.Pi A B)
    | U {Γ} : JCon Γ → JTy Γ .U
    | El {Γ A} : JTm Γ A .U → JTy Γ (.El A)
  inductive JTm : Con → Tm → Ty → Prop
    | app {Γ A B f} : JTm Γ f (.Pi A B) → JTm (Γ.ext A) .app B
    | lam {Γ A B b} : JTm (Γ.ext A) b B → JTm Γ .lam (.Pi A B)
end

example {Γ} : JCon Γ → JCon Γ := id
example {Γ A} : JTy Γ A → JCon Γ := sorry
example {Γ a A} : JTm Γ a A → JCon Γ := sorry

example : JCon (Con.emp.ext .U) :=
  have : JCon .emp := .emp
  have : JTy .emp .U := .U this
  have : JCon (.ext .emp .U) := .ext .emp this
  this

end FormalSyntactic

namespace Substitution

inductive ts
  | emp
  | ext
  | rfl
  | trans (ε δ : ts)
  | fst (δ : ts)
inductive tm
  | subst (a : tm) (δ : ts)
  | snd
  | app
  | lam (a : tm)
inductive ty
  | subst (A : ty) (δ : ts)
  | Pi (A B : ty)
  | U
  | El (A : tm)
inductive tx
  | emp
  | ext (Γ : tx) (A : ty)

mutual
  inductive Tx : tx → Prop
    | emp : Tx .emp
    | ext {Γ A} : Tx Γ → Ty Γ A → Tx (Γ.ext A)
  inductive Ty : tx → ty → Prop
    /-- Apply a substitution from `Γ` to `∆` to a type in context `∆` producing a type in context `Γ` -/
    | subst {Γ Δ A B δ} : Ty Δ A → Ts Γ Δ δ → Ty Γ B
    | Pi {Γ A B} : Tx Γ → Ty Γ A → Ty (Γ.ext A) B → Ty Γ (.Pi A B)
    | U {Γ} : Tx Γ → Ty Γ .U
    | El {Γ A} : Tm Γ A .U → Ty Γ (.El A)
  inductive Ts : tx → tx → ts → Prop
    | emp {Γ} : Tx Γ → Ts Γ .emp .emp
    | ext {Γ Δ a A δ} : Tx Γ → Tx Δ → Ts Γ Δ δ → Tm Γ a (A.subst δ) → Ts Γ (Δ.ext A) .ext
    | rfl {Γ} : Tx Γ → Ts Γ Γ .rfl
    | trans {Γ Δ E ε δ} : Tx Γ → Tx Δ → Tx E → Ts Δ E ε → Ts Γ Δ δ → Ts Γ E (.trans ε δ)
    | fst {Γ Δ A δ} : Tx Γ → Ts Γ (Δ.ext A) δ → Ts Γ Δ (.fst δ)
  inductive Tm : tx → tm → ty → Prop
    | subst {Γ Δ a A δ} : Tm Δ a A → Ts Γ Δ δ → Tm Γ (.subst a δ) (.subst A δ)
    | snd {Γ Δ A δ} : Ts Γ (.ext Δ A) δ → Tm Γ .snd (.subst A (.fst δ))
    | app {Γ A B f} : Tm Γ f (.Pi A B) → Tm (Γ.ext A) .app B
    | lam {Γ A B b} : Tm (Γ.ext A) b B → Tm Γ (.lam b) (.Pi A B)
end

example {Γ} : Tx Γ → Tx Γ := id
theorem Ty.toTx {Γ A} : Ty Γ A → Tx Γ := sorry
theorem Tm.toTx {Γ a A} : Tm Γ a A → Tx Γ := sorry
theorem Tm.toTy {Γ a A} : Tm Γ a A → Ty Γ A := sorry
example {Γ Δ δ} : Ts Γ Δ δ → Tx Γ := sorry
example {Γ Δ δ} : Ts Γ Δ δ → Tx Δ := sorry

def wk {Γ A} (j : Ty Γ A) : {δ : ts // Ts (Γ.ext A) Γ δ} :=
  have : Tx (Γ.ext A) := .ext j.toTx j
  ⟨_, .fst this (.rfl this)⟩

def vz {Γ A} (j : Ty Γ A) : {a : tm // Tm (Γ.ext A) a (.subst A (wk j))} :=
  have : Tx (Γ.ext A) := .ext j.toTx j
  ⟨_, .snd (.rfl this)⟩

def vs {Γ a A} (j : Tm Γ a A) : {b : tm // Tm (Γ.ext A) b (.subst A (wk j.toTy).1)} :=
  ⟨_, .subst j (wk _).2⟩

example :=
  have : Tx .emp := .emp
  have h : Ty .emp .U := .U this
  -- have : JCon (.ext .emp .U) := .ext .emp h
  -- have h : JTy (.ext .emp .U) .U := .U this
  have : Tm (.ext .emp .U) (vz h) .U := sorry -- (vz h).2
  have : Tm .emp (.lam (vz h)) (.Pi .U .U) := .lam this
  1

end Substitution

namespace Minimal

inductive ts
mutual
  inductive tx
    | emp
    | ext (Γ : tx) (A : ty)
  inductive ty
    | sub (Γ : tx) (A : ty) (σ : ts)
    | map (Γ : tx) (A B : ty)
end
inductive tm
  | lam (Γ : tx) (b : tm)
  | app (Γ : tx) (f a : tm)

mutual
  inductive Ts : tx → tx → ts → Prop
  inductive Tx : tx → Prop
    | emp : Tx .emp
    | ext {Γ A} : Ty Γ A → Tx (Γ.ext A)
  inductive Ty : tx → ty → Prop
    | sub {Γ Δ A σ} : Ty Γ A → Ts Γ Δ σ → Ty Δ (.sub Γ A σ)
    | map {Γ A B} : Ty Γ A → Ty (Γ.ext A) B → Ty Γ (.map Γ A B)
  inductive Tm : tx → ty → tm → Prop
    | lam {Γ A B b} : Tm (Γ.ext A) B b → Tm Γ (.map Γ A B) (.lam Γ b)
    | app {Γ A B f a σ} : Tm Γ (.map Γ A B) f → Tm Γ A a → Tm (Γ.ext A) (.sub Γ B σ) (.app Γ f a)
end

theorem Ty.toTx {Γ A} : Ty Γ A → Tx Γ
  | map h .. => h.toTx
theorem Tx.toTy {Γ A} : Tx (Γ.ext A) → Ty Γ A
  | ext h => h
theorem Tx.toTx {Γ A} : Tx (Γ.ext A) → Tx Γ
  | h => h.toTy.toTx
theorem Tm.toTy {Γ a} : {A : ty} → Tm Γ A a → Ty Γ A := sorry
  -- | .map _ A B, lam h => show Ty Γ (.map _ A B) from
  --   have : Ty (Γ.ext A) B := h.toTy
  --   .map this.toTx.toTy this
  -- | C, app hf ha => sorry
theorem Tm.toTx {Γ A a} : Tm Γ A a → Tx Γ
  | h => h.toTy.toTx

def wkTy {Γ A B} : Ty Γ A → Ty Γ B → Ty (Γ.ext A) B := sorry
-- def wkTm {Γ A B b} : Ty Γ A → Tm Γ b B → Tm (Γ.ext A) b B := sorry

end Minimal
