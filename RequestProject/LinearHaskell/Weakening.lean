module

public import RequestProject.LinearHaskell.Semantics

/-!
# Weakening by unrestricted variables

If `Γ ⊢ t : A` then `Γ + ωΔ ⊢ t : A`: variables of multiplicity `ω` may always be added.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

theorem Typed.ofEq {E : TyEnv} {U U' : Usage} {t : Tm} {A : Ty} (h : Typed S E U t A)
    (hU : U = U') : Typed S E U' t A := hU ▸ h

theorem Typed.ofEqTy {E : TyEnv} {U : Usage} {t : Tm} {A A' : Ty} (h : Typed S E U t A)
    (hA : A = A') : Typed S E U t A' := hA ▸ h

theorem Typed.weaken {E : TyEnv} {U : Usage} {t : Tm} {A : Ty} (h : Typed S E U t A) :
    ∀ V : Usage, Typed S E (U + ω' • V) t A := by
  induction h with
  | var Γ x =>
    intro V
    refine (Typed.var (Γ + V) x).ofEq ?_
    rw [smul_add]; abel
  | abs _ ih =>
    intro V
    refine Typed.abs ((ih (prep [0] V)).ofEq ?_)
    rw [smul_prep, ← prep_add_zeros]
    simp
  | app _ _ ih₁ _ =>
    intro V
    refine (Typed.app (ih₁ V) ‹_›).ofEq ?_
    abel
  | con Γ Δ hp hk hl _ _ =>
    intro V
    refine (Typed.con (Γ + V) Δ hp hk hl ‹_›).ofEq ?_
    rw [smul_add]; abel
  | @case E Γ Δ π t D ps bs C ht hl hn _ _ ih =>
    intro V
    refine (Typed.case (Δ := Δ + ω' • V) ht hl hn (fun k hk => (ih k hk (prep (List.replicate
      (S.fieldTys D k ps).length 0) V)).ofEq ?_)).ofEq ?_
    · rw [smul_prep, ← prep_add_zeros]
      simp [Sig.fieldTys, Sig.fieldMults]
    · abel
  | @letin E Δ π bs u C Γ _ _ _ ih =>
    intro V
    refine (Typed.letin (Δ := Δ + ω' • V) Γ ‹_› ((ih (prep (List.replicate bs.length 0) V)).ofEq ?_)).ofEq ?_
    · rw [smul_prep, ← prep_add_zeros]
      simp
    · abel
  | mabs _ ih =>
    intro V
    refine Typed.mabs ((ih (MZ.bind mshiftσ ∘ V)).ofEq ?_)
    funext i
    simp [MZ.bind_add, MZ.bind_mul]
  | mapp π _ ih =>
    intro V
    exact Typed.mapp π (ih V)

end LinearHaskell
