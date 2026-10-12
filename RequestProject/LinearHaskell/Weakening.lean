module

public import RequestProject.LinearHaskell.Semantics

/-!
# Weakening by unrestricted variables

If `Γ ⊢ t : A` then `Γ + ωΔ ⊢ t : A`: variables of multiplicity `ω` may always be added.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

theorem Typed.ofEq {m n : ℕ} {E : TyEnv S m n} {U U' : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) (hU : U = U') : Typed S E U' t A := hU ▸ h

theorem Typed.ofEqTy {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A A' : Ty S m}
    (h : Typed S E U t A) (hA : A = A') : Typed S E U t A' := hA ▸ h

theorem Typed.ofEqEnv {m n : ℕ} {E E' : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) (hE : E = E') : Typed S E' U t A := hE ▸ h

theorem MZ.shift_add {m : ℕ} (a b : MZ m) : MZ.shift (a + b) = MZ.shift a + MZ.shift b :=
  MZ.bind_add _ a b

theorem MZ.shift_mul {m : ℕ} (a b : MZ m) : MZ.shift (a * b) = MZ.shift a * MZ.shift b :=
  MZ.bind_mul _ a b

@[simp] theorem MZ.shift_omega {m : ℕ} : MZ.shift (ω' : MZ m) = ω' := rfl

theorem Typed.weaken {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) : ∀ V : Usage m n, Typed S E (U + (ω' : MZ m) • V) t A := by
  induction h with
  | var Γ x =>
    intro V
    refine (Typed.var (Γ + V) x).ofEq ?_
    rw [smul_add]; abel
  | abs _ ih =>
    intro V
    refine Typed.abs ((ih (Fin.append V 0)).ofEq ?_)
    rw [smul_append, append_add]
    simp
  | app _ _ ih₁ _ =>
    intro V
    refine (Typed.app (ih₁ V) ‹_›).ofEq ?_
    abel
  | con Γ ps Δ hts _ =>
    intro V
    refine (Typed.con (Γ + V) ps Δ hts).ofEq ?_
    rw [smul_add]; abel
  | @case m n E Γ Δ π t D ps bs C ht _ _ ih =>
    intro V
    refine (Typed.case (Δ := Δ + (ω' : MZ m) • V) ht (fun k => (ih k (Fin.append V 0)).ofEq ?_)).ofEq ?_
    · rw [smul_append, append_add]
      simp
    · abel
  | @letin m n E Δ π j As ts u C Γ hts _ _ ih =>
    intro V
    refine (Typed.letin (Δ := Δ + (ω' : MZ m) • V) Γ hts ((ih (Fin.append V 0)).ofEq ?_)).ofEq ?_
    · rw [smul_append, append_add]
      simp
    · abel
  | mabs _ ih =>
    intro V
    refine Typed.mabs ((ih (MZ.shift ∘ V)).ofEq ?_)
    funext i
    simp [MZ.shift_add, MZ.shift_mul]
  | mapp π _ ih =>
    intro V
    exact Typed.mapp π (ih V)

end LinearHaskell
