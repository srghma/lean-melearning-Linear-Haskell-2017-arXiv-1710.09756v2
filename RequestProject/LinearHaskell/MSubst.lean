module

public import RequestProject.LinearHaskell.Weakening

/-!
# Substitution of multiplicity variables preserves typing

If `Γ ⊢ t : A` then `Γ[σ] ⊢ t[σ] : A[σ]` for any substitution `σ` of multiplicity
variables. This is what makes rule (m.app) sound: `(λ p. t) π ⟶ t[π/p]`.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

theorem MZ.bind_sum (σ : ℕ → Mult) {ι : Type*} (s : Finset ι) (f : ι → MZ) :
    MZ.bind σ (∑ i ∈ s, f i) = ∑ i ∈ s, MZ.bind σ (f i) :=
  map_sum (MZ.bindHom σ) f s

@[simp] theorem Ty.bind_default (σ : ℕ → Mult) : Ty.bind σ default = default := rfl

theorem Sig.fieldTys_bind (σ : ℕ → Mult) (D k : ℕ) (ps : List Mult) :
    S.fieldTys D k (ps.map (Mult.bind σ)) = (S.fieldTys D k ps).map (Ty.bind σ) := by
  simp only [Sig.fieldTys, List.map_map]
  congr 1
  funext f
  simp only [Function.comp, Ty.bind_bind]
  congr 1
  funext n
  exact (bind_psSubst σ ps n).symm

theorem Sig.fieldMults_bind (σ : ℕ → Mult) (D k : ℕ) (ps : List Mult) :
    S.fieldMults D k (ps.map (Mult.bind σ)) = (S.fieldMults D k ps).map (Mult.bind σ) := by
  simp only [Sig.fieldMults, List.map_map]
  congr 1
  funext f
  simp only [Function.comp, Mult.bind_bind]
  congr 1
  funext n
  exact (bind_psSubst σ ps n).symm

theorem List.getD_map_default {α β : Type*} (f : α → β) (l : List α) (d : α) (d' : β)
    (h : f d = d') (i : ℕ) : (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [h]

theorem List.getD_map_of_lt {α β : Type*} (f : α → β) (l : List α) (d : α) (d' : β) (i : ℕ)
    (hi : i < l.length) : (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

theorem Sig.fieldTy_bind (σ : ℕ → Mult) (D k : ℕ) (ps : List Mult) (i : ℕ) :
    S.fieldTy D k (ps.map (Mult.bind σ)) i = Ty.bind σ (S.fieldTy D k ps i) := by
  simp only [Sig.fieldTy, Sig.fieldTys_bind]
  exact List.getD_map_default (Ty.bind σ) _ default default rfl i

theorem Sig.fieldMult_bind (σ : ℕ → Mult) (D k : ℕ) (ps : List Mult) (i : ℕ) :
    S.fieldMult D k (ps.map (Mult.bind σ)) i = Mult.bind σ (S.fieldMult D k ps i) := by
  simp only [Sig.fieldMult, Sig.fieldMults_bind]
  exact List.getD_map_default (Mult.bind σ) _ 1 1 rfl i

theorem MZ.bind_single (σ : ℕ → Mult) (x : ℕ) :
    MZ.bind σ ∘ (Pi.single x 1 : Usage) = Pi.single x 1 := by
  funext i
  by_cases h : i = x
  · subst h; simp
  · simp [h]

theorem Typed.mbind {E : TyEnv} {U : Usage} {t : Tm} {A : Ty} (h : Typed S E U t A) :
    ∀ σ : ℕ → Mult, Typed S (Ty.bind σ ∘ E) (MZ.bind σ ∘ U) (t.mbind σ) (A.bind σ) := by
  induction h with
  | var Γ x =>
    intro σ
    simp only [Tm.mbind]
    refine (Typed.var (MZ.bind σ ∘ Γ) x).ofEq ?_
    funext i
    by_cases hi : i = x
    · subst hi; simp [MZ.omega]
    · simp [hi, MZ.omega]
  | @abs E U π A B t _ ih =>
    intro σ
    simp only [Tm.mbind]
    have := ih σ
    rw [comp_prep, comp_prep] at this
    exact Typed.abs (by simpa using this)
  | @app E Γ Δ π A B t u _ _ ih₁ ih₂ =>
    intro σ
    simp only [Tm.mbind]
    refine (Typed.app (ih₁ σ) (ih₂ σ)).ofEq ?_
    funext i
    simp
  | @con E Γ D k ps ts Δ hp hk hl _ ih =>
    intro σ
    simp only [Tm.mbind]
    have := Typed.con (S := S) (E := Ty.bind σ ∘ E) (MZ.bind σ ∘ Γ) (D := D) (k := k)
      (ps := ps.map (Mult.bind σ)) (ts := ts.map (fun t => Tm.mbind σ t))
      (fun i => MZ.bind σ ∘ Δ i) (by simpa using hp) hk (by simpa using hl) (by
        intro i hi
        rw [List.length_map] at hi
        rw [List.getD_map_of_lt _ _ default _ _ hi, Sig.fieldTy_bind]
        exact ih i hi σ)
    refine this.ofEq ?_
    funext i
    simp [Finset.sum_apply, MZ.bind_sum, Sig.fieldMult_bind, MZ.omega]
  | @case E Γ Δ π t D ps bs C ht hl hn _ iht ih =>
    intro σ
    simp only [Tm.mbind]
    have := Typed.case (S := S) (E := Ty.bind σ ∘ E) (Γ := MZ.bind σ ∘ Γ) (Δ := MZ.bind σ ∘ Δ)
      (π := Mult.bind σ π) (bs := bs.map (fun b => (b.1, Tm.mbind σ b.2))) (C := C.bind σ)
      (iht σ) (by simpa using hl)
      (by
        intro k hk
        rw [List.length_map] at hk
        rw [List.getD_map_of_lt _ _ default _ _ hk]
        exact hn k hk)
      (by
        intro k hk
        rw [List.length_map] at hk
        rw [List.getD_map_of_lt _ _ default _ _ hk]
        have := ih k hk σ
        rw [comp_prep, comp_prep] at this
        rw [Sig.fieldTys_bind, Sig.fieldMults_bind]
        simpa [List.map_map, Function.comp_def] using this)
    refine this.ofEq ?_
    funext i
    simp
  | @letin E Δ π bs u C Γ _ _ ih ihu =>
    intro σ
    simp only [Tm.mbind]
    have := Typed.letin (S := S) (E := Ty.bind σ ∘ E) (Δ := MZ.bind σ ∘ Δ)
      (π := Mult.bind σ π) (bs := bs.map (fun b => (Ty.bind σ b.1, Tm.mbind σ b.2)))
      (u := u.mbind σ) (C := C.bind σ) (fun i => MZ.bind σ ∘ Γ i)
      (by
        intro i hi
        rw [List.length_map] at hi
        rw [List.getD_map_of_lt _ _ default _ _ hi]
        exact ih i hi σ)
      (by
        have := ihu σ
        rw [comp_prep, comp_prep] at this
        simpa [List.map_map, Function.comp_def, List.map_replicate] using this)
    refine this.ofEq ?_
    funext i
    simp [Finset.sum_apply, MZ.bind_sum]
  | @mabs E U t A _ ih =>
    intro σ
    simp only [Tm.mbind]
    refine Typed.mabs ?_
    have := ih (Mult.up σ)
    have e1 : Ty.bind (Mult.up σ) ∘ Ty.shift ∘ E = Ty.shift ∘ (Ty.bind σ ∘ E) :=
      funext fun i => Ty.bind_up_shift σ (E i)
    have e2 : MZ.bind (Mult.up σ) ∘ MZ.bind mshiftσ ∘ U = MZ.bind mshiftσ ∘ (MZ.bind σ ∘ U) :=
      funext fun i => by simp only [Function.comp, MZ.bind_bind]; rfl
    rw [e1, e2] at this
    exact this
  | @mapp E U t A π _ ih =>
    intro σ
    simp only [Tm.mbind]
    exact (Typed.mapp (Mult.bind σ π) (ih σ)).ofEqTy (Ty.bind_inst σ π A).symm

end LinearHaskell
