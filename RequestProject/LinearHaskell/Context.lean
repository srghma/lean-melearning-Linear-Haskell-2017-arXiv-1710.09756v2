module

public import RequestProject.LinearHaskell.Syntax

/-!
# Typing contexts and their operations (Section 3.2)

A typing context `Γ = x₁ :_{π₁} A₁, …, xₙ :_{πₙ} Aₙ` of the paper consists of the *types* of
the variables (the inputs of the typing judgement) and their *multiplicities* (its outputs).
For terms with `n` free variables (`Tm S m n`) we represent a context by two vectors indexed
by `Fin n`:

* a type environment `E : TyEnv S m n = Fin n → Ty S m`, and
* a usage vector `U : Usage m n = Fin n → MZ m`, where `U x = 0` means that `x` does not
  occur in the context, and `U x = π` means that the context contains `x :_π (E x)`.

With this representation the paper's context addition
`(x :_π A, Γ) + (x :_μ A, Δ) = x :_{π+μ} A, (Γ + Δ)`,
`(x :_π A, Γ) + Δ = x :_π A, (Γ + Δ)` (if `x ∉ Δ`), `() + Δ = Δ`
is exactly pointwise addition in `MZ` (absent variables count as `0`), and scaling
`π (x :_μ A, Γ) = x :_{πμ} A, πΓ` is pointwise multiplication. Contexts form a module over
the multiplicities, which gives the laws listed in Section 3.2.

Extending a context with new variables `Γ, x₁ :_{π₁} A₁, …, x_k :_{π_k} A_k` is `Fin.append`.
-/

@[expose] public section

namespace LinearHaskell

/-- Usage vectors: the multiplicity part of a typing context with `n` variables. -/
abbrev Usage (m n : ℕ) : Type := Fin n → MZ m

/-- Type environments: the type part of a typing context with `n` variables. -/
abbrev TyEnv (S : Sig) (m n : ℕ) : Type := Fin n → Ty S m

/-- The unrestricted multiplicity as a scalar. -/
scoped notation "ω'" => MZ.omega

/-! ### The laws of Section 3.2 -/

section Laws

variable {m n : ℕ} (Γ Δ : Usage m n) (π μ : Mult m)

/-- `Γ + Δ = Δ + Γ`. -/
theorem ctx_add_comm : Γ + Δ = Δ + Γ := add_comm Γ Δ

/-- `π (Γ + Δ) = π Γ + π Δ`. -/
theorem ctx_smul_add : (MZ.of π) • (Γ + Δ) = MZ.of π • Γ + MZ.of π • Δ := smul_add _ Γ Δ

/-- `(π + μ) Γ = π Γ + μ Γ`. -/
theorem ctx_add_smul : (MZ.of (π + μ)) • Γ = MZ.of π • Γ + MZ.of μ • Γ := by
  rw [MZ.of_add, add_smul]

/-- `(π μ) Γ = π (μ Γ)`. -/
theorem ctx_mul_smul : (MZ.of (π * μ)) • Γ = MZ.of π • (MZ.of μ • Γ) := by
  rw [MZ.of_mul, mul_smul]

/-- `1 Γ = Γ`. -/
theorem ctx_one_smul : (MZ.of (1 : Mult m)) • Γ = Γ := by
  rw [MZ.of_one, one_smul]

end Laws

/-! ### Extension of contexts -/

section Append

variable {m n k : ℕ}

@[simp] theorem castAdd_ne_natAdd' (x : Fin n) (i : Fin k) : Fin.castAdd k x ≠ Fin.natAdd n i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

@[simp] theorem natAdd_ne_castAdd' (x : Fin n) (i : Fin k) : Fin.natAdd n i ≠ Fin.castAdd k x :=
  fun h => castAdd_ne_natAdd' x i h.symm

theorem append_apply' {α : Type*} (U : Fin n → α) (W : Fin k → α) (i : Fin (n + k)) :
    Fin.append U W i = if h : (i : ℕ) < n then U ⟨i, h⟩ else W ⟨i - n, by omega⟩ := by
  induction i using Fin.addCases with
  | left i => simp
  | right i => simp

theorem append_add (U U' : Usage m n) (W W' : Usage m k) :
    Fin.append U W + Fin.append U' W' = Fin.append (U + U') (W + W') := by
  funext i
  induction i using Fin.addCases <;> simp

theorem smul_append (c : MZ m) (U : Usage m n) (W : Usage m k) :
    c • Fin.append U W = Fin.append (c • U) (c • W) := by
  funext i
  induction i using Fin.addCases <;> simp

theorem append_zero_zero : Fin.append (0 : Usage m n) (0 : Usage m k) = 0 := by
  funext i
  induction i using Fin.addCases <;> simp

theorem sum_append_zero {ι : Type*} (s : Finset ι) (U : ι → Usage m n) :
    ∑ j ∈ s, Fin.append (U j) (0 : Usage m k) = Fin.append (∑ j ∈ s, U j) 0 := by
  funext i
  induction i using Fin.addCases <;> simp [Finset.sum_apply]

theorem single_castAdd (x : Fin n) (c : MZ m) :
    (Pi.single (Fin.castAdd k x) c : Usage m (n + k)) = Fin.append (Pi.single x c) 0 := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    by_cases h : i = x
    · subst h; simp
    · simp [h, Fin.castAdd_inj]
  | right i => simp

theorem single_natAdd (j : Fin k) (c : MZ m) :
    (Pi.single (Fin.natAdd n j) c : Usage m (n + k)) = Fin.append 0 (Pi.single j c) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right i =>
    by_cases h : i = j
    · subst h; simp
    · simp [h, Fin.natAdd_inj]

theorem append_comp_castAdd {α : Type*} (U : Fin n → α) (W : Fin k → α) :
    Fin.append U W ∘ Fin.castAdd k = U := by
  funext i; simp

theorem comp_append {α β : Type*} (g : α → β) (U : Fin n → α) (W : Fin k → α) :
    g ∘ Fin.append U W = Fin.append (g ∘ U) (g ∘ W) := by
  funext i
  induction i using Fin.addCases <;> simp

end Append

/-! ### Pushing a usage vector forward along a renaming -/

/-- `push ξ U` is the usage vector `U` transported along the renaming `ξ`: the usage of `y`
is the sum of the usages of all `x` with `ξ x = y`. -/
def push {m n n' : ℕ} (ξ : Fin n → Fin n') (U : Usage m n) : Usage m n' :=
  fun y => ∑ x, if ξ x = y then U x else 0

section Push

variable {m n n' k : ℕ} (ξ : Fin n → Fin n')

/-- Pushing forward is linear. -/
def pushLin : Usage m n →ₗ[MZ m] Usage m n' where
  toFun := push ξ
  map_add' U V := by
    funext y; simp [push, Finset.sum_add_distrib, ite_add_zero]
  map_smul' c U := by
    funext y; simp [push, Finset.mul_sum]

theorem push_add (U V : Usage m n) : push ξ (U + V) = push ξ U + push ξ V :=
  (pushLin ξ).map_add U V

theorem push_smul (c : MZ m) (U : Usage m n) : push ξ (c • U) = c • push ξ U :=
  (pushLin ξ).map_smul c U

theorem push_sum {ι : Type*} (s : Finset ι) (U : ι → Usage m n) :
    push ξ (∑ i ∈ s, U i) = ∑ i ∈ s, push ξ (U i) := map_sum (pushLin ξ) U s

theorem push_zero : push ξ (0 : Usage m n) = 0 := (pushLin ξ).map_zero

theorem push_single (x : Fin n) (c : MZ m) : push ξ (Pi.single x c) = Pi.single (ξ x) c := by
  funext y
  simp only [push]
  rw [Finset.sum_eq_single x]
  · by_cases h : ξ x = y
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro b _ hb; simp [hb]
  · simp

theorem push_liftR (U : Usage m n) (W : Usage m k) :
    push (Tm.liftR k ξ) (Fin.append U W) = Fin.append (push ξ U) W := by
  funext y
  simp only [push, Fin.sum_univ_add, Tm.liftR, Fin.append_left, Fin.append_right]
  induction y using Fin.addCases with
  | left y =>
    simp [Fin.castAdd_inj, push]
  | right y =>
    simp only [castAdd_ne_natAdd', Fin.natAdd_inj, if_false, Finset.sum_const_zero, zero_add,
      Fin.append_right]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · simp

theorem push_castAdd (U : Usage m n) :
    push (Fin.castAdd k) U = Fin.append U (0 : Usage m k) := by
  funext y
  simp only [push]
  induction y using Fin.addCases with
  | left y =>
    simp only [Fin.castAdd_inj, Fin.append_left]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  | right y => simp

end Push

end LinearHaskell
