module

public import RequestProject.LinearHaskell.Rename

/-!
# The substitution lemma

The general (simultaneous, linear) substitution lemma: if `Γ ⊢ t : A` and each variable `x`
of `Γ` is substituted by a term `σ x` with `Δₓ ⊢ σ x : Γ(x)`, then
`Σₓ Γ(x) Δₓ ⊢ t[σ] : A`, where `Γ(x)` is the multiplicity of `x` in `Γ`.

As a special case we get the substitution lemma for the innermost variables used by
β-reduction, `case` and `let`: from `Γ, x₁ :_{q₁} A₁, …, x_k :_{q_k} A_k ⊢ t : B` and
`Δᵢ ⊢ tᵢ : Aᵢ` infer `Γ + Σᵢ qᵢ Δᵢ ⊢ t[t₁/x₁ … t_k/x_k] : B`.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

/-- The usage of `t[σ]` when `t` has usage `U` and each `σ x` has usage `Δ x`:
`Σₓ U(x) Δₓ`. -/
def substUsage {m n n' : ℕ} (Δ : Fin n → Usage m n') : Usage m n →ₗ[MZ m] Usage m n' where
  toFun U := ∑ x, U x • Δ x
  map_add' U V := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c U := by simp [mul_smul, Finset.smul_sum]

theorem substUsage_apply {m n n' : ℕ} (Δ : Fin n → Usage m n') (U : Usage m n) :
    substUsage Δ U = ∑ x, U x • Δ x := rfl

theorem substUsage_single {m n n' : ℕ} (Δ : Fin n → Usage m n') (x : Fin n) (c : MZ m) :
    substUsage Δ (Pi.single x c) = c • Δ x := by
  rw [substUsage_apply, Finset.sum_eq_single x]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem substUsage_var {m n : ℕ} (U : Usage m n) :
    substUsage (fun x => (Pi.single x 1 : Usage m n)) U = U := by
  funext y
  rw [substUsage_apply, Finset.sum_apply, Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-- The usages of a substitution lifted under `k` binders. -/
def liftΔ {m n n' : ℕ} (k : ℕ) (Δ : Fin n → Usage m n') : Fin (n + k) → Usage m (n' + k) :=
  Fin.append (fun x => Fin.append (Δ x) 0) (fun i => Pi.single (Fin.natAdd n' i) 1)

theorem substUsage_liftΔ {m n n' k : ℕ} (Δ : Fin n → Usage m n') (U : Usage m n)
    (W : Usage m k) :
    substUsage (liftΔ k Δ) (Fin.append U W) = Fin.append (substUsage Δ U) W := by
  simp only [substUsage_apply, Fin.sum_univ_add, liftΔ, Fin.append_left, Fin.append_right]
  simp only [single_natAdd, smul_append, smul_zero, sum_append_zero]
  rw [show ∑ i : Fin k, Fin.append (0 : Usage m n') (W i • (Pi.single i 1 : Usage m k)) =
      Fin.append 0 W from ?_]
  · rw [append_add]; simp
  · funext y
    induction y using Fin.addCases with
    | left y => simp [Finset.sum_apply]
    | right y =>
      simp only [Finset.sum_apply, Fin.append_right]
      rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp

theorem substUsage_shift {m n n' : ℕ} (Δ : Fin n → Usage m n') (U : Usage m n) :
    substUsage (fun x => MZ.shift ∘ Δ x) (MZ.shift ∘ U) = MZ.shift ∘ substUsage Δ U := by
  funext y
  simp [substUsage_apply, Finset.sum_apply, MZ.shift, MZ.bind_sum]

theorem typed_liftS {m n n' k : ℕ} {σ : Fin n → Tm S m n'} {E : TyEnv S m n}
    {E' : TyEnv S m n'} {Δ : Fin n → Usage m n'} (hσ : ∀ x, Typed S E' (Δ x) (σ x) (E x))
    (Es : TyEnv S m k) (y : Fin (n + k)) :
    Typed S (Fin.append E' Es) (liftΔ k Δ y) (Tm.liftS k σ y) (Fin.append E Es y) := by
  induction y using Fin.addCases with
  | left x =>
    simp only [liftΔ, Tm.liftS, Fin.append_left]
    exact (hσ x).weakenFresh Es
  | right i =>
    simp only [liftΔ, Tm.liftS, Fin.append_right]
    refine ((Typed.var 0 (Fin.natAdd n' i)).ofEq (by simp)).ofEqTy (by simp)

theorem Typed.subst {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) :
    ∀ {n' : ℕ} (σ : Fin n → Tm S m n') (E' : TyEnv S m n') (Δ : Fin n → Usage m n'),
      (∀ x, Typed S E' (Δ x) (σ x) (E x)) →
      Typed S E' (substUsage Δ U) (t.subst σ) A := by
  induction h with
  | @var m n E Γ x =>
    intro n' σ E' Δ hσ
    refine ((hσ x).weaken (substUsage Δ Γ)).ofEq ?_
    rw [map_add, map_smul, substUsage_single, one_smul, add_comm]
  | abs _ ih =>
    intro n' σ E' Δ hσ
    refine Typed.abs ?_
    have := ih (Tm.liftS 1 σ) _ (liftΔ 1 Δ) (typed_liftS hσ _)
    rwa [substUsage_liftΔ] at this
  | app _ _ ih₁ ih₂ =>
    intro n' σ E' Δ hσ
    refine (Typed.app (ih₁ σ E' Δ hσ) (ih₂ σ E' Δ hσ)).ofEq ?_
    rw [map_add, map_smul]
  | con Γ ps Δs _ ih =>
    intro n' σ E' Δ hσ
    refine (Typed.con (substUsage Δ Γ) ps (fun i => substUsage Δ (Δs i))
      (fun i => ih i σ E' Δ hσ)).ofEq ?_
    rw [map_add, map_smul, map_sum]
    simp only [map_smul]
  | @case m n E Γ Δc π t D ps bs C _ _ iht ih =>
    intro n' σ E' Δ hσ
    refine (Typed.case (Δ := substUsage Δ Δc) (iht σ E' Δ hσ) (fun k => ?_)).ofEq ?_
    · have := ih k (Tm.liftS _ σ) _ (liftΔ _ Δ) (typed_liftS hσ _)
      rwa [substUsage_liftΔ] at this
    · rw [map_add, map_smul]
  | @letin m n E Δl π j As ts u C Γ _ _ ihts ihu =>
    intro n' σ E' Δ hσ
    refine (Typed.letin (Δ := substUsage Δ Δl) (fun i => substUsage Δ (Γ i))
      (fun i => ihts i σ E' Δ hσ) ?_).ofEq ?_
    · have := ihu (Tm.liftS _ σ) _ (liftΔ _ Δ) (typed_liftS hσ _)
      rwa [substUsage_liftΔ] at this
    · rw [map_add, map_smul, map_sum]
  | mabs _ ih =>
    intro n' σ E' Δ hσ
    refine Typed.mabs ?_
    have := ih (fun x => (σ x).mshift) (Ty.shift ∘ E') (fun x => MZ.shift ∘ Δ x)
      (fun x => (hσ x).mshift)
    rwa [substUsage_shift] at this
  | mapp π _ ih =>
    intro n' σ E' Δ hσ
    exact Typed.mapp π (ih σ E' Δ hσ)

/-- The substitution lemma for the innermost variables: from
`Γ, x₁ :_{q₁} A₁, …, x_k :_{q_k} A_k ⊢ t : B` and `Δᵢ ⊢ tᵢ : Aᵢ` infer
`Γ + Σᵢ qᵢ Δᵢ ⊢ t[t₁/x₁ … t_k/x_k] : B`. For `k = 1` this is the paper's linear substitution
lemma `Γ, x :_q A ⊢ t : B`, `Δ ⊢ u : A` ⟹ `Γ + qΔ ⊢ t[u/x] : B`. -/
theorem Typed.substTop {m n k : ℕ} {E : TyEnv S m n} {As : TyEnv S m k} {U : Usage m n}
    {W : Usage m k} {t : Tm S m (n + k)} {B : Ty S m}
    (h : Typed S (Fin.append E As) (Fin.append U W) t B) {ts : Fin k → Tm S m n}
    {Δ : Fin k → Usage m n} (hts : ∀ i, Typed S E (Δ i) (ts i) (As i)) :
    Typed S E (U + ∑ i, W i • Δ i) (Tm.substTop ts t) B := by
  have := h.subst (Fin.append Tm.var ts) E (Fin.append (fun x => Pi.single x 1) Δ) (by
    intro y
    induction y using Fin.addCases with
    | left x => simpa using (Typed.var (E := E) 0 x).ofEq (by simp)
    | right i => simpa using hts i)
  refine this.ofEq ?_
  rw [substUsage_apply, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← substUsage_apply, substUsage_var]

/-- The single-variable substitution lemma: `Γ, x :_q A ⊢ t : B` and `Δ ⊢ u : A` imply
`Γ + qΔ ⊢ t[u/x] : B`. -/
theorem Typed.substTop1 {m n : ℕ} {E : TyEnv S m n} {A B : Ty S m} {U : Usage m n} {q : MZ m}
    {t : Tm S m (n + 1)} (h : Typed S (Fin.append E ![A]) (Fin.append U ![q]) t B)
    {u : Tm S m n} {Δ : Usage m n} (hu : Typed S E Δ u A) :
    Typed S E (U + q • Δ) (Tm.substTop ![u] t) B := by
  have := h.substTop (ts := ![u]) (Δ := ![Δ]) (fun i => by fin_cases i; simpa using hu)
  simpa using this

end LinearHaskell
