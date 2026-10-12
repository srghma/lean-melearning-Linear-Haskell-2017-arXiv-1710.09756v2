module

public import RequestProject.LinearHaskell.Mult

/-!
# Syntax of `λq→` (Section 3.1, Fig. 5)

* Types `A, B ::= A →_π B | ∀ p. A | D π₁ … πₙ`.
* Datatype declarations `data D p₁ … pₙ where (c_k : A₁ →_{π₁} … A_{n_k} →_{π_{n_k}} D)_{k=1}^m`
  are collected in a signature `Sig`.
* Terms: variables, abstraction `λ_π (x : A). t`, application, multiplicity abstraction
  `λ p. t`, multiplicity application `t π`, data construction `c t₁ … tₙ`,
  `case_π t of {c_k x₁ … x_{n_k} → u_k}` and `let_π x₁ : A₁ = t₁ … xₙ : Aₙ = tₙ in u`.

Both term variables and multiplicity variables are represented by de Bruijn indices.
-/

@[expose] public section

namespace LinearHaskell

/-- Types of `λq→` (Fig. 5). In `all A`, the multiplicity variable `0` of `A` is bound.
In `data D ps`, `D` names a datatype of the signature and `ps` are its multiplicity
arguments. -/
inductive Ty : Type
  | arr (π : Mult) (A B : Ty) : Ty
  | all (A : Ty) : Ty
  | data (D : ℕ) (ps : List Mult) : Ty

instance : Inhabited Ty := ⟨.data 0 []⟩

namespace Ty

/-- Substitution of multiplicity variables in a type. -/
def bind (σ : ℕ → Mult) : Ty → Ty
  | arr π A B => arr (Mult.bind σ π) (bind σ A) (bind σ B)
  | all A => all (bind (Mult.up σ) A)
  | data D ps => data D (ps.map (Mult.bind σ))

/-- Shift the free multiplicity variables of a type (used for "`p` fresh for `Γ`"). -/
def shift (A : Ty) : Ty := bind (fun n => Mult.var (n + 1)) A

/-- `A[π/p]` where `p` is the bound variable `0`. -/
def inst (π : Mult) (A : Ty) : Ty := bind (Mult.inst π) A

theorem up_var : Mult.up Mult.var = Mult.var := by
  funext n; cases n with
  | zero => rfl
  | succ n => simp [Mult.up, Mult.shift]

@[simp] theorem bind_var (A : Ty) : bind Mult.var A = A := by
  induction A with
  | arr π A B ihA ihB => simp [bind, ihA, ihB]
  | all A ih => simp [bind, up_var, ih]
  | data D ps =>
    have : Mult.bind Mult.var = id := funext Mult.bind_var_eq
    simp [bind, this]

theorem bind_bind (σ τ : ℕ → Mult) (A : Ty) :
    bind τ (bind σ A) = bind (fun n => Mult.bind τ (σ n)) A := by
  induction A generalizing σ τ with
  | arr π A B ihA ihB => simp [bind, ihA, ihB, Mult.bind_bind]
  | all A ih =>
    simp only [bind, ih]
    congr 2
    funext n
    exact Mult.up_bind σ τ n
  | data D ps => simp [bind, Mult.bind_bind]

theorem bind_up_shift (σ : ℕ → Mult) (A : Ty) : bind (Mult.up σ) (shift A) = shift (bind σ A) := by
  simp only [shift, bind_bind]
  rfl

theorem bind_inst_shift (π : Mult) (A : Ty) : bind (Mult.inst π) (shift A) = A := by
  simp only [shift, bind_bind]
  exact bind_var A

theorem bind_inst (σ : ℕ → Mult) (π : Mult) (A : Ty) :
    bind σ (inst π A) = inst (Mult.bind σ π) (bind (Mult.up σ) A) := by
  simp only [inst, bind_bind]
  congr 1
  funext n
  exact (Mult.inst_bind σ π n).symm

end Ty

/-- Substitution sending the `i`-th parameter of a datatype to `ps[i]`. -/
def psSubst (ps : List Mult) (i : ℕ) : Mult := ps.getD i 1

theorem bind_psSubst (σ : ℕ → Mult) (ps : List Mult) (i : ℕ) :
    Mult.bind σ (psSubst ps i) = psSubst (ps.map (Mult.bind σ)) i := by
  unfold psSubst
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ps[i]? <;> rfl

/-- A signature of datatype declarations. `nparams D` is the number of multiplicity
parameters of `D`, and `ctors D` is the list of its constructors; each constructor is
described by the list of its fields `(μᵢ, Aᵢ)`, i.e.
`c_k : A₁ →_{μ₁} … →_{μ_{n_k}} D p₁ … pₙ`. In the `μᵢ` and `Aᵢ` the free multiplicity
variables `0, …, n-1` stand for the parameters `p₁ … pₙ`. -/
structure Sig where
  nparams : ℕ → ℕ
  ctors : ℕ → List (List (Mult × Ty))

namespace Sig

variable (S : Sig)

/-- The fields of the `k`-th constructor of `D`. -/
def fields (D k : ℕ) : List (Mult × Ty) := (S.ctors D).getD k []

/-- The multiplicities `μᵢ[π₁ … πₙ]` of the fields of constructor `k` of `D π₁ … πₙ`. -/
def fieldMults (D k : ℕ) (ps : List Mult) : List Mult :=
  (S.fields D k).map (fun f => Mult.bind (psSubst ps) f.1)

/-- The types `Aᵢ[π₁ … πₙ]` of the fields of constructor `k` of `D π₁ … πₙ`. -/
def fieldTys (D k : ℕ) (ps : List Mult) : List Ty :=
  (S.fields D k).map (fun f => Ty.bind (psSubst ps) f.2)

/-- The multiplicity of the `i`-th field. -/
def fieldMult (D k : ℕ) (ps : List Mult) (i : ℕ) : Mult := (S.fieldMults D k ps).getD i 1

/-- The type of the `i`-th field. -/
def fieldTy (D k : ℕ) (ps : List Mult) (i : ℕ) : Ty := (S.fieldTys D k ps).getD i default

end Sig

/-- Terms of `λq→` (Fig. 5).

* `lam π A t` is `λ_π (x : A). t` (binds term variable `0` in `t`);
* `mlam t` is `λ p. t` (binds multiplicity variable `0` in `t`);
* `mapp t π` is `t π`;
* `con D k ts` is `c_k t₁ … tₙ`, the `k`-th constructor of datatype `D`;
* `case π t bs` is `case_π t of {c_k x₁ … x_{n_k} → u_k}`: the `k`-th branch is
  `(n_k, u_k)`, where `u_k` binds the term variables `0, …, n_k - 1` (variable `i` is the
  field `x_{i+1}`);
* `letin π bs u` is `let_π x₁ : A₁ = t₁ … xₙ : Aₙ = tₙ in u` with `bs = [(A₁,t₁), …]`;
  `u` binds the variables `0, …, n - 1` (variable `i` is `x_{i+1}`). -/
inductive Tm : Type
  | var (x : ℕ) : Tm
  | lam (π : Mult) (A : Ty) (t : Tm) : Tm
  | app (t u : Tm) : Tm
  | mlam (t : Tm) : Tm
  | mapp (t : Tm) (π : Mult) : Tm
  | con (D k : ℕ) (ts : List Tm) : Tm
  | case (π : Mult) (t : Tm) (bs : List (ℕ × Tm)) : Tm
  | letin (π : Mult) (bs : List (Ty × Tm)) (u : Tm) : Tm

instance : Inhabited Tm := ⟨.var 0⟩

/-- Extend an environment `f` (indexed by de Bruijn indices) by the list `l`:
index `i < l.length` is sent to `l[i]` and index `l.length + j` to `f j`. -/
def prep {α : Type*} (l : List α) (f : ℕ → α) (i : ℕ) : α :=
  if h : i < l.length then l[i] else f (i - l.length)

namespace Tm

theorem sizeOf_snd_lt {α : Type} [SizeOf α] {b : α × Tm} {bs : List (α × Tm)} (h : b ∈ bs) :
    sizeOf b.2 < sizeOf bs := by
  have := List.sizeOf_lt_of_mem h
  rcases b with ⟨a, t⟩
  simp only [Prod.mk.sizeOf_spec] at this ⊢
  omega

/-- Termination tactic for recursion through branch lists. -/
macro "tm_decreasing" : tactic =>
  `(tactic| all_goals first
    | decreasing_tactic
    | (have := sizeOf_snd_lt ‹_›; simp_wf; omega))

/-- Substitution of multiplicity variables in a term. -/
def mbind (σ : ℕ → Mult) : Tm → Tm
  | var x => var x
  | lam π A t => lam (Mult.bind σ π) (Ty.bind σ A) (mbind σ t)
  | app t u => app (mbind σ t) (mbind σ u)
  | mlam t => mlam (mbind (Mult.up σ) t)
  | mapp t π => mapp (mbind σ t) (Mult.bind σ π)
  | con D k ts => con D k (ts.map (fun t => mbind σ t))
  | case π t bs => case (Mult.bind σ π) (mbind σ t) (bs.map (fun b => (b.1, mbind σ b.2)))
  | letin π bs u =>
      letin (Mult.bind σ π) (bs.map (fun b => (Ty.bind σ b.1, mbind σ b.2))) (mbind σ u)
termination_by t => t
decreasing_by tm_decreasing

/-- Shift the free multiplicity variables of a term. -/
def mshift (t : Tm) : Tm := mbind (fun n => Mult.var (n + 1)) t

/-- Lift a renaming under `n` binders. -/
def upR (n : ℕ) (ξ : ℕ → ℕ) (i : ℕ) : ℕ := if i < n then i else ξ (i - n) + n

/-- Renaming of term variables. -/
def rename (ξ : ℕ → ℕ) : Tm → Tm
  | var x => var (ξ x)
  | lam π A t => lam π A (rename (upR 1 ξ) t)
  | app t u => app (rename ξ t) (rename ξ u)
  | mlam t => mlam (rename ξ t)
  | mapp t π => mapp (rename ξ t) π
  | con D k ts => con D k (ts.map (fun t => rename ξ t))
  | case π t bs => case π (rename ξ t) (bs.map (fun b => (b.1, rename (upR b.1 ξ) b.2)))
  | letin π bs u =>
      letin π (bs.map (fun b => (b.1, rename ξ b.2))) (rename (upR bs.length ξ) u)
termination_by t => t
decreasing_by tm_decreasing

/-- Shift all free term variables by `n`. -/
def shiftN (n : ℕ) (t : Tm) : Tm := rename (· + n) t

/-- Lift a substitution under `n` term binders. -/
def upS (n : ℕ) (s : ℕ → Tm) (i : ℕ) : Tm := if i < n then var i else shiftN n (s (i - n))

/-- Simultaneous substitution of term variables. -/
def subst (s : ℕ → Tm) : Tm → Tm
  | var x => s x
  | lam π A t => lam π A (subst (upS 1 s) t)
  | app t u => app (subst s t) (subst s u)
  | mlam t => mlam (subst (fun i => mshift (s i)) t)
  | mapp t π => mapp (subst s t) π
  | con D k ts => con D k (ts.map (fun t => subst s t))
  | case π t bs => case π (subst s t) (bs.map (fun b => (b.1, subst (upS b.1 s) b.2)))
  | letin π bs u =>
      letin π (bs.map (fun b => (b.1, subst s b.2))) (subst (upS bs.length s) u)
termination_by t => t
decreasing_by tm_decreasing

/-- The substitution `[u / k]`: replaces variable `k` by `u` and lowers the variables above
`k` (since `k` disappears from the context). -/
def substAtFun (k : ℕ) (u : Tm) (i : ℕ) : Tm :=
  if i < k then var i else if i = k then u else var (i - 1)

/-- `t[u/k]`. -/
def substAt (k : ℕ) (u : Tm) (t : Tm) : Tm := subst (substAtFun k u) t

/-- Simultaneous substitution of the variables `0, …, n-1` of `b` by `ts = [t₀, …, t_{n-1}]`
(terms living in the outer context), used for `case` and `let`. -/
def substList : List Tm → Tm → Tm
  | [], b => b
  | t :: ts, b => substList ts (substAt 0 (shiftN ts.length t) b)

end Tm

end LinearHaskell
