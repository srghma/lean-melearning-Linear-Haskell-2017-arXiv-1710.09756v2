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

All syntax is *well scoped by construction*:

* `Ty Δ m` is the type of types with at most `m` free multiplicity variables;
* `Tm S m n` is the type of terms with at most `m` free multiplicity variables and at most
  `n` free term variables, `var : Fin n → Tm S m n`. Hence `Tm S m 0` is the type of
  closed terms (no free term variable) and `Tm S 0 0` the type of fully closed terms.

The same holds for datatypes: a type `D π₁ … πₙ` must supply exactly as many multiplicity
arguments as `D` has parameters, a constructor `c_k` must be applied to exactly as many
arguments as it has fields, and a `case` has exactly one branch per constructor of its
datatype, binding exactly as many variables as the constructor has fields.

Variables (of both kinds) are de Bruijn *levels*: a binder in a scope of size `n` binds the
variable `Fin.last n` (more generally, `k` binders bind `Fin.natAdd n i` for `i : Fin k`), and
the variables of the outer scope keep their numbers (`Fin.castAdd`). This matches the
paper's convention of extending contexts on the right, `Γ, x :_π A`.
-/

@[expose] public section

namespace LinearHaskell

/-- The names of the datatypes of a signature and their numbers of multiplicity
parameters. -/
structure DataSig where
  /-- Names of datatypes. -/
  Name : Type
  /-- The number of multiplicity parameters of each datatype. -/
  arity : Name → ℕ

/-- Types of `λq→` (Fig. 5) with at most `m` free multiplicity variables. In `all A`, the
variable `Fin.last m` of `A` is bound. In `data D ps`, `D` names a datatype and `ps` are its
multiplicity arguments, exactly one for each parameter of `D`. -/
inductive Ty (Δ : DataSig) : ℕ → Type
  | arr {m : ℕ} (π : Mult m) (A B : Ty Δ m) : Ty Δ m
  | all {m : ℕ} (A : Ty Δ (m + 1)) : Ty Δ m
  | data {m : ℕ} (D : Δ.Name) (ps : Fin (Δ.arity D) → Mult m) : Ty Δ m

namespace Ty

variable {Δ : DataSig} {m m' m'' : ℕ}

/-- Substitution of multiplicity variables in a type. -/
def bind : {m m' : ℕ} → (Fin m → Mult m') → Ty Δ m → Ty Δ m'
  | _, _, σ, arr π A B => arr (Mult.bind σ π) (bind σ A) (bind σ B)
  | _, _, σ, all A => all (bind (Mult.up σ) A)
  | _, _, σ, data D ps => data D (fun i => Mult.bind σ (ps i))

/-- Weakening of a type by one multiplicity variable (used for "`p` fresh for `Γ`"). -/
def shift (A : Ty Δ m) : Ty Δ (m + 1) := bind (fun i => Mult.var i.castSucc) A

/-- `A[π/p]` where `p` is the bound variable `Fin.last m`. -/
def inst (π : Mult m) (A : Ty Δ (m + 1)) : Ty Δ m := bind (Mult.inst π) A

theorem up_var : Mult.up (Mult.var : Fin m → Mult m) = Mult.var := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [Mult.shift]

@[simp] theorem bind_var (A : Ty Δ m) : bind Mult.var A = A := by
  induction A with
  | arr π A B ihA ihB => simp [bind, ihA, ihB]
  | all A ih => simp [bind, up_var, ih]
  | data D ps => simp [bind]

theorem bind_bind (σ : Fin m → Mult m') (τ : Fin m' → Mult m'') (A : Ty Δ m) :
    bind τ (bind σ A) = bind (fun i => Mult.bind τ (σ i)) A := by
  induction A generalizing m' m'' with
  | arr π A B ihA ihB => simp [bind, ihA, ihB, Mult.bind_bind]
  | all A ih =>
    simp only [bind, ih]
    congr 2
    funext i
    exact Mult.up_bind σ τ i
  | data D ps => simp [bind, Mult.bind_bind]

theorem bind_up_shift (σ : Fin m → Mult m') (A : Ty Δ m) :
    bind (Mult.up σ) (shift A) = shift (bind σ A) := by
  simp only [shift, bind_bind]
  simp [Mult.shift]

theorem bind_inst_shift (π : Mult m) (A : Ty Δ m) : bind (Mult.inst π) (shift A) = A := by
  simp only [shift, bind_bind]
  simp

theorem bind_inst (σ : Fin m → Mult m') (π : Mult m) (A : Ty Δ (m + 1)) :
    bind σ (inst π A) = inst (Mult.bind σ π) (bind (Mult.up σ) A) := by
  simp only [inst, bind_bind]
  congr 1
  funext i
  exact (Mult.inst_bind σ π i).symm

end Ty

/-- A signature of datatype declarations
`data D p₁ … pₙ where (c_k : A₁ →_{μ₁} … →_{μ_{n_k}} D p₁ … pₙ)_k`.
Each datatype `D` has `nctors D` constructors; constructor `k` has `nfields D k` fields, the
`i`-th of which has multiplicity `fieldMult D k i` and type `fieldTy D k i`. These may
mention exactly the parameters `p₁ … pₙ` of `D` (as multiplicity variables `0, …, n-1`). -/
structure Sig extends DataSig where
  /-- The number of constructors of each datatype. -/
  nctors : Name → ℕ
  /-- The number of fields of each constructor. -/
  nfields : (D : Name) → Fin (nctors D) → ℕ
  /-- The multiplicity `μᵢ` of each field. -/
  fieldMult : (D : Name) → (k : Fin (nctors D)) → Fin (nfields D k) → Mult (arity D)
  /-- The type `Aᵢ` of each field. -/
  fieldTy : (D : Name) → (k : Fin (nctors D)) → Fin (nfields D k) → Ty toDataSig (arity D)

instance : CoeOut Sig DataSig := ⟨Sig.toDataSig⟩

namespace Sig

variable (S : Sig) {m : ℕ}

/-- The multiplicity `μᵢ[π₁ … πₙ]` of field `i` of constructor `k` of `D π₁ … πₙ`. -/
def fieldMultAt (D : S.Name) (k : Fin (S.nctors D)) (ps : Fin (S.arity D) → Mult m)
    (i : Fin (S.nfields D k)) : Mult m :=
  Mult.bind ps (S.fieldMult D k i)

/-- The type `Aᵢ[π₁ … πₙ]` of field `i` of constructor `k` of `D π₁ … πₙ`. -/
def fieldTyAt (D : S.Name) (k : Fin (S.nctors D)) (ps : Fin (S.arity D) → Mult m)
    (i : Fin (S.nfields D k)) : Ty S m :=
  Ty.bind ps (S.fieldTy D k i)

end Sig

/-- Terms of `λq→` (Fig. 5) with at most `m` free multiplicity variables and at most `n`
free term variables.

* `lam π A t` is `λ_π (x : A). t` (binds the term variable `Fin.last n` in `t`);
* `mlam t` is `λ p. t` (binds the multiplicity variable `Fin.last m` in `t`);
* `mapp t π` is `t π`;
* `con D k ts` is `c_k t₁ … tₙ`, the `k`-th constructor of datatype `D`, applied to one
  argument per field;
* `case π t D bs` is `case_π t of {c_k x₁ … x_{n_k} → u_k}` on a scrutinee of datatype `D`:
  there is one branch `bs k` for each constructor `k`, which binds one variable per field
  (field `i` is the variable `Fin.natAdd n i`);
* `letin π j As ts u` is `let_π x₁ : A₁ = t₁ … x_j : A_j = t_j in u`; `u` binds the `j`
  variables `x₁ … x_j` (`xᵢ₊₁` is the variable `Fin.natAdd n i`). -/
inductive Tm (S : Sig) : ℕ → ℕ → Type
  | var {m n : ℕ} (x : Fin n) : Tm S m n
  | lam {m n : ℕ} (π : Mult m) (A : Ty S m) (t : Tm S m (n + 1)) : Tm S m n
  | app {m n : ℕ} (t u : Tm S m n) : Tm S m n
  | mlam {m n : ℕ} (t : Tm S (m + 1) n) : Tm S m n
  | mapp {m n : ℕ} (t : Tm S m n) (π : Mult m) : Tm S m n
  | con {m n : ℕ} (D : S.Name) (k : Fin (S.nctors D)) (ts : Fin (S.nfields D k) → Tm S m n) :
      Tm S m n
  | case {m n : ℕ} (π : Mult m) (t : Tm S m n) (D : S.Name)
      (bs : (k : Fin (S.nctors D)) → Tm S m (n + S.nfields D k)) : Tm S m n
  | letin {m n : ℕ} (π : Mult m) (j : ℕ) (As : Fin j → Ty S m) (ts : Fin j → Tm S m n)
      (u : Tm S m (n + j)) : Tm S m n

namespace Tm

variable {S : Sig}

/-- Substitution of multiplicity variables in a term. -/
def mbind : {m m' n : ℕ} → (Fin m → Mult m') → Tm S m n → Tm S m' n
  | _, _, _, _, var x => var x
  | _, _, _, σ, lam π A t => lam (Mult.bind σ π) (Ty.bind σ A) (mbind σ t)
  | _, _, _, σ, app t u => app (mbind σ t) (mbind σ u)
  | _, _, _, σ, mlam t => mlam (mbind (Mult.up σ) t)
  | _, _, _, σ, mapp t π => mapp (mbind σ t) (Mult.bind σ π)
  | _, _, _, σ, con D k ts => con D k (fun i => mbind σ (ts i))
  | _, _, _, σ, case π t D bs => case (Mult.bind σ π) (mbind σ t) D (fun k => mbind σ (bs k))
  | _, _, _, σ, letin π j As ts u =>
      letin (Mult.bind σ π) j (fun i => Ty.bind σ (As i)) (fun i => mbind σ (ts i)) (mbind σ u)

/-- Weakening of a term by one multiplicity variable. -/
def mshift {m n : ℕ} (t : Tm S m n) : Tm S (m + 1) n := mbind (fun i => Mult.var i.castSucc) t

/-- Lift a renaming under `k` binders. -/
def liftR {n n' : ℕ} (k : ℕ) (ξ : Fin n → Fin n') : Fin (n + k) → Fin (n' + k) :=
  Fin.append (fun x => Fin.castAdd k (ξ x)) (Fin.natAdd n')

/-- Renaming of term variables. -/
def rename : {m n n' : ℕ} → (Fin n → Fin n') → Tm S m n → Tm S m n'
  | _, _, _, ξ, var x => var (ξ x)
  | _, _, _, ξ, lam π A t => lam π A (rename (liftR 1 ξ) t)
  | _, _, _, ξ, app t u => app (rename ξ t) (rename ξ u)
  | _, _, _, ξ, mlam t => mlam (rename ξ t)
  | _, _, _, ξ, mapp t π => mapp (rename ξ t) π
  | _, _, _, ξ, con D k ts => con D k (fun i => rename ξ (ts i))
  | _, _, _, ξ, case π t D bs => case π (rename ξ t) D (fun k => rename (liftR _ ξ) (bs k))
  | _, _, _, ξ, letin π j As ts u =>
      letin π j As (fun i => rename ξ (ts i)) (rename (liftR j ξ) u)

/-- Lift a substitution under `k` binders. -/
def liftS {m n n' : ℕ} (k : ℕ) (σ : Fin n → Tm S m n') : Fin (n + k) → Tm S m (n' + k) :=
  Fin.append (fun x => rename (Fin.castAdd k) (σ x)) (fun i => var (Fin.natAdd n' i))

/-- Simultaneous substitution of term variables. -/
def subst : {m n n' : ℕ} → (Fin n → Tm S m n') → Tm S m n → Tm S m n'
  | _, _, _, σ, var x => σ x
  | _, _, _, σ, lam π A t => lam π A (subst (liftS 1 σ) t)
  | _, _, _, σ, app t u => app (subst σ t) (subst σ u)
  | _, _, _, σ, mlam t => mlam (subst (fun x => mshift (σ x)) t)
  | _, _, _, σ, mapp t π => mapp (subst σ t) π
  | _, _, _, σ, con D k ts => con D k (fun i => subst σ (ts i))
  | _, _, _, σ, case π t D bs => case π (subst σ t) D (fun k => subst (liftS _ σ) (bs k))
  | _, _, _, σ, letin π j As ts u =>
      letin π j As (fun i => subst σ (ts i)) (subst (liftS j σ) u)

/-- `t[t₁/x₁ … t_k/x_k]`: substitute the `k` innermost variables of `t` by `ts`, leaving the
other variables unchanged. Used for β-reduction (`k = 1`), `case` and `let`. -/
def substTop {m n k : ℕ} (ts : Fin k → Tm S m n) (t : Tm S m (n + k)) : Tm S m n :=
  subst (Fin.append var ts) t

end Tm

end LinearHaskell
