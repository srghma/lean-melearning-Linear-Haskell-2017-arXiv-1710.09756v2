module

public import RequestProject.LinearHaskell.Syntax

/-!
# Typing contexts and their operations (Section 3.2)

A typing context `Γ = x₁ :_{π₁} A₁, …` of the paper consists of the *types* of the
variables (the inputs of the typing judgement) and their *multiplicities* (its outputs).
With de Bruijn indices we represent a context by two vectors indexed by variables:

* a type environment `E : ℕ → Ty`, and
* a usage vector `U : ℕ → MZ`, where `U x = 0` means that `x` does not occur in the
  context, and `U x = π` means that the context contains `x :_π (E x)`.

With this representation the paper's context addition
`(x :_π A, Γ) + (x :_μ A, Δ) = x :_{π+μ} A, (Γ + Δ)`,
`(x :_π A, Γ) + Δ = x :_π A, (Γ + Δ)` (if `x ∉ Δ`), `() + Δ = Δ`
is exactly pointwise addition in `MZ` (absent variables count as `0`), and scaling
`π (x :_μ A, Γ) = x :_{πμ} A, πΓ` is pointwise multiplication. Contexts form a module over
the multiplicities, which gives the laws listed in Section 3.2.
-/

@[expose] public section

namespace LinearHaskell

/-- Usage vectors: the multiplicity part of a typing context. -/
abbrev Usage : Type := ℕ → MZ

/-- Type environments: the type part of a typing context. -/
abbrev TyEnv : Type := ℕ → Ty

/-- The unrestricted multiplicity as a scalar. -/
scoped notation "ω'" => MZ.omega

/-! ### The laws of Section 3.2 -/

section Laws

variable (Γ Δ : Usage) (π μ : Mult)

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
theorem ctx_one_smul : (MZ.of 1) • Γ = Γ := by
  rw [MZ.of_one, one_smul]

end Laws

/-! ### Extension of contexts by a list of bindings -/

section Prep

variable {α : Type*}

@[simp] theorem prep_lt (l : List α) (f : ℕ → α) (i : ℕ) (h : i < l.length) :
    prep l f i = l[i] := by simp [prep, h]

@[simp] theorem prep_add_length (l : List α) (f : ℕ → α) (i : ℕ) :
    prep l f (i + l.length) = f i := by simp [prep]

theorem prep_ge (l : List α) (f : ℕ → α) (i : ℕ) (h : l.length ≤ i) :
    prep l f i = f (i - l.length) := by simp [prep, Nat.not_lt.mpr h]

@[simp] theorem prep_nil (f : ℕ → α) : prep [] f = f := by
  funext i; simp [prep]

theorem prep_cons (a : α) (l : List α) (f : ℕ → α) :
    prep (a :: l) f = prep [a] (prep l f) := by
  funext i
  rcases i with _ | i
  · simp [prep]
  · simp only [prep, List.length_cons]
    by_cases h : i < l.length
    · simp [h]
    · simp [h]

theorem comp_prep {β : Type*} (g : α → β) (l : List α) (f : ℕ → α) :
    g ∘ prep l f = prep (l.map g) (g ∘ f) := by
  funext i
  by_cases h : i < l.length
  · simp [prep, h]
  · simp [prep, h]

theorem prep_add (l₁ l₂ : List MZ) (U V : Usage) (h : l₁.length = l₂.length) :
    prep l₁ U + prep l₂ V = prep (List.zipWith (· + ·) l₁ l₂) (U + V) := by
  funext i
  by_cases hi : i < l₁.length
  · simp [prep, hi, h ▸ hi]
  · simp [prep, h ▸ hi, h]

theorem prep_add_zeros (l : List MZ) (U V : Usage) :
    prep l U + prep (List.replicate l.length 0) V = prep l (U + V) := by
  funext i
  by_cases hi : i < l.length
  · simp [prep, hi]
  · simp [prep, hi]

theorem smul_prep (c : MZ) (l : List MZ) (U : Usage) :
    c • prep l U = prep (l.map (c * ·)) (c • U) := by
  funext i
  by_cases hi : i < l.length
  · simp [prep, hi]
  · simp [prep, hi]

theorem prep_zeros_zero (n : ℕ) : prep (List.replicate n (0 : MZ)) (0 : Usage) = 0 := by
  funext i
  by_cases hi : i < n
  · simp [prep, hi]
  · simp [prep, hi]

theorem sum_prep_zeros {ι : Type*} (s : Finset ι) (n : ℕ) (V : ι → Usage) :
    ∑ j ∈ s, prep (List.replicate n (0 : MZ)) (V j) =
      prep (List.replicate n 0) (∑ j ∈ s, V j) := by
  funext i
  by_cases hi : i < n
  · simp [prep, hi, Finset.sum_apply]
  · simp [prep, hi, Finset.sum_apply]

end Prep

/-! ### Deleting a variable -/

/-- The renaming that skips index `k`. `U ∘ skip k` is the context `U` with variable `k`
removed. -/
def skip (k : ℕ) (i : ℕ) : ℕ := if i < k then i else i + 1

theorem prep_comp_skip {α : Type*} (l : List α) (f : ℕ → α) (k : ℕ) :
    prep l f ∘ skip (k + l.length) = prep l (f ∘ skip k) := by
  funext i
  simp only [Function.comp, skip, prep]
  by_cases h : i < l.length
  · simp [h, show i < k + l.length by omega]
  · simp only [h, dite_false]
    by_cases h' : i < k + l.length
    · simp [h, h', show i - l.length < k by omega]
    · simp only [h', ite_false, show ¬ (i - l.length < k) by omega,
        show ¬ (i + 1 < l.length) by omega, dite_false]
      congr 1; omega

theorem prep_k_add {α : Type*} (l : List α) (f : ℕ → α) (k : ℕ) :
    prep l f (k + l.length) = f k := prep_add_length l f k

/-! ### Pushing a usage vector forward along an injective renaming -/

open Classical in
/-- `push ξ U` is the usage vector `U` transported along the renaming `ξ`: it assigns
`U x` to `ξ x` and `0` to variables outside the range of `ξ`. -/
noncomputable def push (ξ : ℕ → ℕ) (U : Usage) (y : ℕ) : MZ :=
  if h : ∃ x, ξ x = y then U h.choose else 0

section Push

variable {ξ : ℕ → ℕ}

theorem push_apply_self (hξ : Function.Injective ξ) (U : Usage) (x : ℕ) :
    push ξ U (ξ x) = U x := by
  have h : ∃ x', ξ x' = ξ x := ⟨x, rfl⟩
  simp only [push, h, dite_true]
  rw [hξ h.choose_spec]

theorem push_apply_not (U : Usage) (y : ℕ) (hy : ∀ x, ξ x ≠ y) : push ξ U y = 0 := by
  have h : ¬ ∃ x, ξ x = y := fun ⟨x, hx⟩ => hy x hx
  simp [push, h]

theorem push_ext (hξ : Function.Injective ξ) {U : Usage} {V : Usage}
    (h₁ : ∀ x, V (ξ x) = U x) (h₂ : ∀ y, (∀ x, ξ x ≠ y) → V y = 0) : push ξ U = V := by
  funext y
  by_cases hy : ∃ x, ξ x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [push_apply_self hξ, h₁]
  · push_neg at hy
    rw [push_apply_not U y hy, h₂ y hy]

/-- Pushing forward along an injective renaming is linear. -/
noncomputable def pushLin (hξ : Function.Injective ξ) : Usage →ₗ[MZ] Usage where
  toFun := push ξ
  map_add' U V := push_ext hξ (fun x => by simp [push_apply_self hξ])
    (fun y hy => by simp [push_apply_not _ y hy])
  map_smul' c U := push_ext hξ (fun x => by simp [push_apply_self hξ])
    (fun y hy => by simp [push_apply_not _ y hy])

theorem push_add (hξ : Function.Injective ξ) (U V : Usage) :
    push ξ (U + V) = push ξ U + push ξ V := (pushLin hξ).map_add U V

theorem push_smul (hξ : Function.Injective ξ) (c : MZ) (U : Usage) :
    push ξ (c • U) = c • push ξ U := (pushLin hξ).map_smul c U

theorem push_sum (hξ : Function.Injective ξ) {ι : Type*} (s : Finset ι) (U : ι → Usage) :
    push ξ (∑ i ∈ s, U i) = ∑ i ∈ s, push ξ (U i) := map_sum (pushLin hξ) U s

theorem push_single (hξ : Function.Injective ξ) (x : ℕ) (c : MZ) :
    push ξ (Pi.single x c) = Pi.single (ξ x) c := by
  refine push_ext hξ (fun x' => ?_) (fun y hy => ?_)
  · by_cases h : x' = x
    · subst h; simp
    · simp [h, hξ.ne_iff]
  · have : y ≠ ξ x := fun h => hy x h.symm
    simp [this]

theorem push_comp (hξ : Function.Injective ξ) (g : MZ → MZ) (hg : g 0 = 0) (U : Usage) :
    push ξ (g ∘ U) = g ∘ push ξ U := by
  refine push_ext hξ (fun x => ?_) (fun y hy => ?_)
  · simp [push_apply_self hξ]
  · simp [push_apply_not _ y hy, hg]

end Push

theorem upR_injective {ξ : ℕ → ℕ} (hξ : Function.Injective ξ) (n : ℕ) :
    Function.Injective (Tm.upR n ξ) := by
  intro i j h
  simp only [Tm.upR] at h
  split_ifs at h with hi hj hj
  · exact h
  · omega
  · omega
  · have := hξ (by omega : ξ (i - n) = ξ (j - n)); omega

theorem prep_upR {α : Type*} {ξ : ℕ → ℕ} {f g : ℕ → α} (h : ∀ x, g (ξ x) = f x)
    (l : List α) (i : ℕ) : prep l g (Tm.upR l.length ξ i) = prep l f i := by
  simp only [Tm.upR]
  by_cases hi : i < l.length
  · simp [hi]
  · simp [hi, prep_ge _ _ _ (Nat.le_of_not_lt hi)]
    exact h _

theorem push_upR {ξ : ℕ → ℕ} (hξ : Function.Injective ξ) (l : List MZ) (U : Usage) :
    push (Tm.upR l.length ξ) (prep l U) = prep l (push ξ U) := by
  refine push_ext (upR_injective hξ _) (fun x => ?_) (fun y hy => ?_)
  · rw [prep_upR (f := U) (g := push ξ U) (fun x => push_apply_self hξ U x)]
  · have hy' : l.length ≤ y := by
      by_contra h
      exact hy y (by simp [Tm.upR, Nat.lt_of_not_le h])
    rw [prep_ge _ _ _ hy']
    apply push_apply_not
    intro x hx
    apply hy (x + l.length)
    simp [Tm.upR, hx]; omega

theorem push_add_right (n : ℕ) (U : Usage) :
    push (· + n) U = prep (List.replicate n 0) U := by
  refine push_ext (fun a b h => by simpa using h) (fun x => ?_) (fun y hy => ?_)
  · simpa using prep_add_length (List.replicate n (0 : MZ)) U x
  · have : y < n := by
      by_contra h
      exact hy (y - n) (by omega)
    simp [prep, this]

end LinearHaskell
