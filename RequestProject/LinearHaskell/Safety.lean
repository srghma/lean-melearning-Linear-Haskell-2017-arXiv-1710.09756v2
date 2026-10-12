module

public import RequestProject.LinearHaskell.Subst

/-!
# Type safety: preservation (Theorem 3.5) and progress (Theorem 3.6)

Both are stated for the call-by-name semantics of `Semantics.lean` (see the caveat there).

* `preservation`: reduction preserves typing *in the same context*, i.e. with the same
  multiplicities for every free variable.
* `progress`: a well-typed closed term (a term of type `Tm S m 0`, which has no free term
  variables by construction) is a value or can take a step.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

/-! ### Inversion lemmas -/

theorem Typed.var_inv {S : Sig} {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {x : Fin n}
    {A : Ty S m} (h : Typed S E U (.var x) A) :
    ∃ Γ, U = (ω' : MZ m) • Γ + Pi.single x 1 ∧ A = E x := by
  cases h; exact ⟨_, rfl, rfl⟩

theorem Typed.con_inv {S : Sig} {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {D : S.Name}
    {k : Fin (S.nctors D)} {ts : Fin (S.nfields D k) → Tm S m n} {A : Ty S m}
    (h : Typed S E U (.con D k ts) A) :
    ∃ (Γ : Usage m n) (ps : Fin (S.arity D) → Mult m) (Δ : Fin (S.nfields D k) → Usage m n),
      (∀ i, Typed S E (Δ i) (ts i) (S.fieldTyAt D k ps i)) ∧
      U = (ω' : MZ m) • Γ + ∑ i, MZ.of (S.fieldMultAt D k ps i) • Δ i ∧ A = .data D ps := by
  cases h with
  | con Γ ps Δ hts => exact ⟨Γ, ps, Δ, hts, rfl, rfl⟩

theorem Typed.case_inv {S : Sig} {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {π : Mult m}
    {t : Tm S m n} {D : S.Name} {bs : (k : Fin (S.nctors D)) → Tm S m (n + S.nfields D k)}
    {C : Ty S m} (h : Typed S E U (.case π t D bs) C) :
    ∃ Γ Δ ps, Typed S E Γ t (.data D ps) ∧
      (∀ k, Typed S (Fin.append E (S.fieldTyAt D k ps))
          (Fin.append Δ (fun i => MZ.of (π * S.fieldMultAt D k ps i))) (bs k) C) ∧
      U = MZ.of π • Γ + Δ := by
  cases h with
  | case ht hbs => exact ⟨_, _, _, ht, hbs, rfl⟩

theorem Typed.abs_inv {S : Sig} {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {π : Mult m}
    {A : Ty S m} {t : Tm S m (n + 1)} {T : Ty S m} (h : Typed S E U (.lam π A t) T) :
    ∃ B, T = .arr π A B ∧ Typed S (Fin.append E ![A]) (Fin.append U ![MZ.of π]) t B := by
  cases h with
  | abs h => exact ⟨_, rfl, h⟩

/-- **Theorem 3.5 (type preservation).** If `Γ ⊢ t : A` and `t ⟶ t'` then `Γ ⊢ t' : A`. -/
theorem preservation {m n : ℕ} {t t' : Tm S m n} (hs : Step t t') :
    ∀ {E : TyEnv S m n} {U : Usage m n} {A : Ty S m}, Typed S E U t A → Typed S E U t' A := by
  induction hs with
  | beta π A t u =>
    intro E U B h
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | abs hb => exact hb.substTop1 h₂
  | appL u _ ih =>
    intro E U B h
    cases h with
    | app h₁ h₂ => exact Typed.app (ih h₁) h₂
  | mbeta t π =>
    intro E U B h
    cases h with
    | mapp _ h =>
      cases h with
      | mabs h => exact h.minst π
  | mappL π _ ih =>
    intro E U B h
    cases h with
    | mapp _ h => exact Typed.mapp π (ih h)
  | caseCon π D k ts bs =>
    intro E U C h
    cases h with
    | @case _ _ _ Γ Δ _ _ _ ps _ _ ht hbs =>
      cases ht with
      | con Γ' _ Δs hts =>
        refine (((hbs k).substTop hts).weaken (MZ.of π • Γ')).ofEq ?_
        rw [smul_add, Finset.smul_sum, smul_smul]
        simp only [smul_smul, MZ.of_mul]
        rw [mul_comm (MZ.of π) ω']
        abel
  | caseL π D bs _ ih =>
    intro E U C h
    cases h with
    | case ht hbs => exact Typed.case (ih ht) hbs
  | letin π j As ts u =>
    intro E U C h
    cases h with
    | letin Γ hts hu =>
      refine (hu.substTop hts).ofEq ?_
      rw [Finset.smul_sum]

/-- Preservation along any number of reduction steps. -/
theorem preservation_steps {m n : ℕ} {t t' : Tm S m n} (hs : Steps t t') {E : TyEnv S m n}
    {U : Usage m n} {A : Ty S m} (h : Typed S E U t A) : Typed S E U t' A := by
  induction hs with
  | refl => exact h
  | tail _ hst ih => exact preservation hst ih

theorem progress_aux {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) (hn : n = 0) : Value t ∨ ∃ t', Step t t' := by
  induction h with
  | var Γ x => subst hn; exact x.elim0
  | abs _ => exact Or.inl (Value.lam _ _ _)
  | app h₁ _ ih₁ _ =>
    rcases ih₁ hn with hv | ⟨t', hs⟩
    · cases hv with
      | lam π A t => exact Or.inr ⟨_, Step.beta _ _ _ _⟩
      | mlam t => cases h₁
      | con D k ts => cases h₁
    · exact Or.inr ⟨_, Step.appL _ hs⟩
  | con _ _ _ _ _ => exact Or.inl (Value.con _ _ _)
  | case ht _ iht _ =>
    rcases iht hn with hv | ⟨t', hs⟩
    · cases hv with
      | lam π A t => cases ht
      | mlam t => cases ht
      | con D k ts =>
        cases ht
        exact Or.inr ⟨_, Step.caseCon _ _ _ _ _⟩
    · exact Or.inr ⟨_, Step.caseL _ _ _ hs⟩
  | letin _ _ _ _ _ => exact Or.inr ⟨_, Step.letin _ _ _ _ _⟩
  | mabs _ _ => exact Or.inl (Value.mlam _)
  | mapp π h ih =>
    rcases ih hn with hv | ⟨t', hs⟩
    · cases hv with
      | lam π A t => cases h
      | mlam t => exact Or.inr ⟨_, Step.mbeta _ _⟩
      | con D k ts => cases h
    · exact Or.inr ⟨_, Step.mappL _ hs⟩

/-- **Theorem 3.6 (progress).** A well-typed closed term (no free term variables, which is
expressed by its type `Tm S m 0`) is a value or can take a reduction step. -/
theorem progress {m : ℕ} {E : TyEnv S m 0} {U : Usage m 0} {t : Tm S m 0} {A : Ty S m}
    (h : Typed S E U t A) : Value t ∨ ∃ t', Step t t' :=
  progress_aux h rfl

/-- Type safety: a well-typed closed term never gets stuck. -/
theorem type_safety {m : ℕ} {E : TyEnv S m 0} {U : Usage m 0} {t t' : Tm S m 0} {A : Ty S m}
    (h : Typed S E U t A) (hs : Steps t t') :
    Typed S E U t' A ∧ (Value t' ∨ ∃ t'', Step t' t'') := by
  have h' := preservation_steps hs h
  exact ⟨h', progress h'⟩

end LinearHaskell
