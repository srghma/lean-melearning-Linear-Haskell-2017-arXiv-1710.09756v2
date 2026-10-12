module

public import RequestProject.LinearHaskell.Subst

/-!
# Type safety: preservation and progress (Theorems 3.5 and 3.6)

* `preservation`: if `Γ ⊢ t : A` and `t ⟶ t'` then `Γ ⊢ t' : A` — with the *same* context
  `Γ`, i.e. the same multiplicities: reduction never changes how many times the free
  variables of a term are consumed.
* `progress`: a closed well-typed term (all variables have multiplicity `0`, i.e. do not
  occur) is a value or can take a step.
* `type_safety`: combining both, evaluation of a closed well-typed term never gets stuck.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

/-- Simultaneous substitution for `case` and `let`: if `Δ, x₁ :_{q₁} A₁, …, xₙ :_{qₙ} Aₙ ⊢ b : C`
and `Γᵢ ⊢ tᵢ : Aᵢ` then `Δ + Σᵢ qᵢ Γᵢ ⊢ b[t₁/x₁ … tₙ/xₙ] : C`. -/
theorem Typed.substList (ts : List Tm) :
    ∀ (As : List Ty) (qs : List MZ) (E : TyEnv) (Δ₀ : Usage) (b : Tm) (C : Ty)
      (Γ : ℕ → Usage),
      As.length = ts.length → qs.length = ts.length →
      Typed S (prep As E) (prep qs Δ₀) b C →
      (∀ i < ts.length, Typed S E (Γ i) (ts.getD i default) (As.getD i default)) →
      Typed S E (Δ₀ + ∑ i ∈ Finset.range ts.length, qs.getD i 0 • Γ i) (Tm.substList ts b) C := by
  induction ts with
  | nil =>
    intro As qs E Δ₀ b C Γ hA hq hb _
    rw [List.length_nil, List.length_eq_zero_iff] at hA hq
    subst hA hq
    simpa [Tm.substList] using hb
  | cons t ts ih =>
    intro As qs E Δ₀ b C Γ hA hq hb hts
    obtain _ | ⟨A, As⟩ := As
    · simp at hA
    obtain _ | ⟨q, qs⟩ := qs
    · simp at hq
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hA hq
    rw [prep_cons, prep_cons (a := q)] at hb
    have ht := hts 0 (by simp)
    simp only [List.getD_cons_zero] at ht
    have ht' := ht.shiftN As
    rw [hA] at ht'
    have h1 := hb.substAt 0 (t.shiftN ts.length) (prep (List.replicate ts.length 0) (Γ 0))
      (by rw [prep_singleton_skip_zero]; exact ht')
    rw [prep_singleton_skip_zero, prep_singleton_skip_zero] at h1
    have h2 : Typed S (prep As E) (prep qs (Δ₀ + q • Γ 0))
        (Tm.substAt 0 (t.shiftN ts.length) b) C :=
      h1.ofEq (prep_add_smul_zeros qs ts.length hq _ _ _)
    have := ih As qs E (Δ₀ + q • Γ 0) _ C (fun i => Γ (i + 1)) hA hq h2 (fun i hi => by
      have := hts (i + 1) (by simp; omega)
      simpa using this)
    simp only [Tm.substList, List.length_cons]
    refine this.ofEq ?_
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    abel

theorem MZ.of_mul_ne_zero (π : Mult) (a : MZ) (h : MZ.of π * a = 0) : a = 0 := by
  rcases (MZ.mul_eq_zero_iff _ _).mp h with h | h
  · exact absurd h (MZ.of_ne_zero π)
  · exact h

theorem usage_add_eq_zero {U V : Usage} (h : U + V = 0) : U = 0 ∧ V = 0 := by
  constructor <;> funext i <;> have := congrFun h i <;>
    simp only [Pi.add_apply, Pi.zero_apply, MZ.add_eq_zero_iff] at this ⊢
  · exact this.1
  · exact this.2

theorem usage_smul_eq_zero {π : Mult} {U : Usage} (h : MZ.of π • U = 0) : U = 0 := by
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact MZ.of_mul_ne_zero π _ this

/-- **Type preservation** (Theorem 3.5): reduction preserves typing, in the same context. -/
theorem preservation {t t' : Tm} (hs : Step t t') :
    ∀ {E : TyEnv} {U : Usage} {A : Ty}, Typed S E U t A → Typed S E U t' A := by
  induction hs with
  | beta π A t u =>
    intro E U B h
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | abs hb =>
        have := hb.substAt 0 u _ (by rw [prep_singleton_skip_zero]; exact h₂)
        rw [prep_singleton_skip_zero, prep_singleton_skip_zero] at this
        exact this
  | appL u _ ih =>
    intro E U B h
    cases h with
    | app h₁ h₂ => exact Typed.app (ih h₁) h₂
  | mbeta t π =>
    intro E U B h
    cases h with
    | mapp _ h₁ =>
      cases h₁ with
      | mabs hb =>
        have := hb.mbind (Mult.inst π)
        have e1 : Ty.bind (Mult.inst π) ∘ Ty.shift ∘ E = E :=
          funext fun i => Ty.bind_inst_shift π (E i)
        have e2 : MZ.bind (Mult.inst π) ∘ MZ.bind mshiftσ ∘ U = U := by
          funext i
          simp only [Function.comp, MZ.bind_bind]
          exact MZ.bind_var_eq _
        rw [e1, e2] at this
        exact this
  | mappL π _ ih =>
    intro E U B h
    cases h with
    | mapp _ h₁ => exact Typed.mapp π (ih h₁)
  | caseCon π D k ts bs hk =>
    intro E U C h
    cases h with
    | @case _ Γ Δ _ _ _ ps _ _ ht hl hn hbs =>
      cases ht with
      | con Γ₀ Δs hp hk' hlt hts =>
        have hb := hbs k hk
        have hlenT : (S.fieldTys D k ps).length = ts.length := by
          simp [Sig.fieldTys, hlt]
        have hlenM : ((S.fieldMults D k ps).map (fun μ => MZ.of (π * μ))).length =
            ts.length := by
          simp [Sig.fieldMults, hlt]
        have := Typed.substList ts _ _ E Δ _ C Δs hlenT hlenM hb (fun i hi => hts i hi)
        refine (this.weaken (MZ.of π • Γ₀)).ofEq ?_
        funext j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        have hsum : ∑ i ∈ Finset.range ts.length,
            ((S.fieldMults D k ps).map (fun μ => MZ.of (π * μ))).getD i 0 * Δs i j =
            ∑ i ∈ Finset.range ts.length,
              MZ.of π * (MZ.of (S.fieldMult D k ps i) * Δs i j) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have hi' : i < (S.fieldMults D k ps).length := by
            simpa [Sig.fieldMults, hlt] using hi
          rw [List.getD_eq_getElem _ _ (by simpa using hi'), Sig.fieldMult,
            List.getD_eq_getElem _ _ hi']
          rw [List.getElem_map, MZ.of_mul, mul_assoc]
        rw [hsum, ← Finset.mul_sum]
        simp only [MZ.omega]
        ring
  | caseL π bs _ ih =>
    intro E U C h
    cases h with
    | case ht hl hn hbs => exact Typed.case (ih ht) hl hn hbs
  | letin π bs u =>
    intro E U C h
    cases h with
    | @letin _ Δ _ _ _ _ Γ hts hu =>
      have := Typed.substList (bs.map Prod.snd) (bs.map Prod.fst)
        (List.replicate bs.length (MZ.of π)) E Δ u C Γ (by simp) (by simp) hu
        (fun i hi => by
          rw [List.length_map] at hi
          rw [List.getD_map_of_lt _ _ default _ _ hi, List.getD_map_of_lt _ _ default _ _ hi]
          exact hts i hi)
      refine this.ofEq ?_
      rw [List.length_map, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp

/-- Preservation along any number of steps. -/
theorem preservation_steps {t t' : Tm} (hs : Steps t t') {E : TyEnv} {U : Usage} {A : Ty}
    (h : Typed S E U t A) : Typed S E U t' A := by
  induction hs with
  | refl => exact h
  | tail _ hst ih => exact preservation hst ih

theorem canonical_arr {E : TyEnv} {U : Usage} {t : Tm} {π : Mult} {A B : Ty}
    (hv : Value t) (h : Typed S E U t (.arr π A B)) : ∃ t', t = .lam π A t' := by
  cases hv with
  | lam π' A' t' => cases h; exact ⟨t', rfl⟩
  | mlam t' => cases h
  | con D k ts => cases h

theorem canonical_all {E : TyEnv} {U : Usage} {t : Tm} {A : Ty}
    (hv : Value t) (h : Typed S E U t (.all A)) : ∃ t', t = .mlam t' := by
  cases hv with
  | lam π' A' t' => cases h
  | mlam t' => exact ⟨t', rfl⟩
  | con D k ts => cases h

theorem canonical_data {E : TyEnv} {U : Usage} {t : Tm} {D : ℕ} {ps : List Mult}
    (hv : Value t) (h : Typed S E U t (.data D ps)) :
    ∃ k ts, t = .con D k ts ∧ k < (S.ctors D).length := by
  cases hv with
  | lam π' A' t' => cases h
  | mlam t' => cases h
  | con D' k ts =>
    cases h with
    | con _ _ _ hk _ _ => exact ⟨k, ts, rfl, hk⟩

/-- **Progress** (Theorem 3.6): a closed well-typed term is a value or reduces. Here
"closed" means that no variable occurs in the context: the usage vector is `0`. -/
theorem progress {E : TyEnv} {U : Usage} {t : Tm} {A : Ty} (h : Typed S E U t A) :
    U = 0 → Value t ∨ ∃ t', Step t t' := by
  induction h with
  | var Γ x =>
    intro hU
    exfalso
    have := congrFun hU x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.zero_apply] at this
    exact MZ.add_one_ne_zero _ this
  | abs _ _ => exact fun _ => Or.inl (Value.lam _ _ _)
  | @app E Γ Δ π A B t u ht _ iht _ =>
    intro hU
    right
    rcases iht (usage_add_eq_zero hU).1 with hv | ⟨t', hst⟩
    · obtain ⟨t', rfl⟩ := canonical_arr hv ht
      exact ⟨_, Step.beta π A t' u⟩
    · exact ⟨_, Step.appL u hst⟩
  | con _ _ _ _ _ _ _ => exact fun _ => Or.inl (Value.con _ _ _)
  | @case E Γ Δ π t D ps bs C ht hl _ _ iht _ =>
    intro hU
    right
    rcases iht (usage_smul_eq_zero (usage_add_eq_zero hU).1) with hv | ⟨t', hst⟩
    · obtain ⟨k, ts, rfl, hk⟩ := canonical_data hv ht
      exact ⟨_, Step.caseCon π D k ts bs (hl ▸ hk)⟩
    · exact ⟨_, Step.caseL π bs hst⟩
  | letin _ _ _ _ _ => exact fun _ => Or.inr ⟨_, Step.letin _ _ _⟩
  | mabs _ _ => exact fun _ => Or.inl (Value.mlam _)
  | @mapp E U t A π ht iht =>
    intro hU
    right
    rcases iht hU with hv | ⟨t', hst⟩
    · obtain ⟨t', rfl⟩ := canonical_all hv ht
      exact ⟨_, Step.mbeta t' π⟩
    · exact ⟨_, Step.mappL π hst⟩

/-- **Type safety**: evaluation of a closed well-typed term never gets stuck: every term
reachable from it is well typed (with the same type) and is either a value or can reduce
further. -/
theorem type_safety {E : TyEnv} {t t' : Tm} {A : Ty} (h : Typed S E 0 t A) (hs : Steps t t') :
    Typed S E 0 t' A ∧ (Value t' ∨ ∃ t'', Step t' t'') := by
  have h' := preservation_steps hs h
  exact ⟨h', progress h' rfl⟩

end LinearHaskell
