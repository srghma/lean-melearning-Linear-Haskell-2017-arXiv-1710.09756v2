module

public import RequestProject.LinearHaskell.Weakening

/-!
# Substitution of multiplicity variables preserves typing

If `Γ ⊢ t : A` then `Γ[σ] ⊢ t[σ] : A[σ]` for every substitution `σ` of multiplicity variables.
This is used for the (m.app)/β-reduction case of preservation and for going under `λ p`.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

theorem MZ.bind_single {m m' n : ℕ} (σ : Fin m → Mult m') (x : Fin n) :
    MZ.bind σ ∘ (Pi.single x 1 : Usage m n) = Pi.single x 1 := by
  funext i
  by_cases h : i = x
  · subst h; simp
  · simp [h]

theorem MZ.bind_up_shift {m m' : ℕ} (σ : Fin m → Mult m') (a : MZ m) :
    MZ.bind (Mult.up σ) (MZ.shift a) = MZ.shift (MZ.bind σ a) := by
  simp only [MZ.shift, MZ.bind_bind]
  congr 1
  funext i
  simp [Mult.shift]

theorem MZ.bind_inst_shift {m : ℕ} (π : Mult m) (a : MZ m) :
    MZ.bind (Mult.inst π) (MZ.shift a) = a := by
  simp only [MZ.shift, MZ.bind_bind]
  simp

theorem Sig.fieldTyAt_bind {m m' : ℕ} (σ : Fin m → Mult m') (D : S.Name) (k : Fin (S.nctors D))
    (ps : Fin (S.arity D) → Mult m) (i : Fin (S.nfields D k)) :
    S.fieldTyAt D k (fun j => Mult.bind σ (ps j)) i = Ty.bind σ (S.fieldTyAt D k ps i) := by
  simp [Sig.fieldTyAt, Ty.bind_bind]

theorem Sig.fieldMultAt_bind {m m' : ℕ} (σ : Fin m → Mult m') (D : S.Name)
    (k : Fin (S.nctors D)) (ps : Fin (S.arity D) → Mult m) (i : Fin (S.nfields D k)) :
    S.fieldMultAt D k (fun j => Mult.bind σ (ps j)) i = Mult.bind σ (S.fieldMultAt D k ps i) := by
  simp [Sig.fieldMultAt, Mult.bind_bind]

theorem Typed.mbind {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) :
    ∀ {m' : ℕ} (σ : Fin m → Mult m'),
      Typed S (Ty.bind σ ∘ E) (MZ.bind σ ∘ U) (t.mbind σ) (A.bind σ) := by
  induction h with
  | var Γ x =>
    intro m' σ
    refine (Typed.var (MZ.bind σ ∘ Γ) x).ofEq ?_
    funext i
    by_cases h : i = x
    · subst h; simp [MZ.omega]
    · simp [h, MZ.omega]
  | abs _ ih =>
    intro m' σ
    refine Typed.abs (((ih σ).ofEqEnv ?_).ofEq ?_)
    · rw [comp_append]; congr 1; funext i; fin_cases i; rfl
    · rw [comp_append]; congr 1; funext i; fin_cases i; rfl
  | app _ _ ih₁ ih₂ =>
    intro m' σ
    refine (Typed.app (ih₁ σ) (ih₂ σ)).ofEq ?_
    funext i
    simp
  | @con m n E Γ D k ps ts Δ _ ih =>
    intro m' σ
    refine (Typed.con (MZ.bind σ ∘ Γ) (fun j => Mult.bind σ (ps j)) (fun i => MZ.bind σ ∘ Δ i)
      (fun i => (ih i σ).ofEqTy (Sig.fieldTyAt_bind σ D k ps i).symm)).ofEq ?_
    funext x
    simp [MZ.bind_sum, Finset.sum_apply, Sig.fieldMultAt_bind, MZ.omega]
  | @case m n E Γ Δ π t D ps bs C _ _ iht ih =>
    intro m' σ
    refine (Typed.case (Γ := MZ.bind σ ∘ Γ) (Δ := MZ.bind σ ∘ Δ) (π := Mult.bind σ π)
      (ps := fun j => Mult.bind σ (ps j)) (iht σ)
      (fun k => (((ih k σ).ofEqEnv ?_).ofEq ?_))).ofEq ?_
    · rw [comp_append]; congr 1; funext i; exact (Sig.fieldTyAt_bind σ D k ps i).symm
    · rw [comp_append]; congr 1; funext i; simp [Sig.fieldMultAt_bind]
    · funext i; simp
  | @letin m n E Δ π j As ts u C Γ _ _ ihts ihu =>
    intro m' σ
    refine (Typed.letin (Δ := MZ.bind σ ∘ Δ) (π := Mult.bind σ π) (As := fun i => Ty.bind σ (As i))
      (fun i => MZ.bind σ ∘ Γ i) (fun i => ihts i σ) (((ihu σ).ofEqEnv ?_).ofEq ?_)).ofEq ?_
    · rw [comp_append]; rfl
    · rw [comp_append]; rfl
    · funext i; simp [MZ.bind_sum, Finset.sum_apply]
  | mabs _ ih =>
    intro m' σ
    refine Typed.mabs (((ih (Mult.up σ)).ofEqEnv ?_).ofEq ?_)
    · funext i; exact Ty.bind_up_shift σ _
    · funext i; exact MZ.bind_up_shift σ _
  | mapp π _ ih =>
    intro m' σ
    exact (Typed.mapp (Mult.bind σ π) (ih σ)).ofEqTy (Ty.bind_inst σ π _).symm

/-- Weakening by a multiplicity variable: a term typed in context `Γ` is typed in `Γ`
viewed in the scope with one more multiplicity variable. -/
theorem Typed.mshift {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) : Typed S (Ty.shift ∘ E) (MZ.shift ∘ U) t.mshift A.shift :=
  h.mbind _

/-- Instantiating the bound multiplicity variable of a term typed under `λ p`. -/
theorem Typed.minst {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S (m + 1) n}
    {A : Ty S (m + 1)} (h : Typed S (Ty.shift ∘ E) (MZ.shift ∘ U) t A) (π : Mult m) :
    Typed S E U (t.mbind (Mult.inst π)) (A.inst π) := by
  refine ((h.mbind (Mult.inst π)).ofEqEnv ?_).ofEq ?_
  · funext i; exact Ty.bind_inst_shift π _
  · funext i; exact MZ.bind_inst_shift π _

end LinearHaskell
