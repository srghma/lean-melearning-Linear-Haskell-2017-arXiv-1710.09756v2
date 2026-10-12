module

public import RequestProject.LinearHaskell.MSubst

/-!
# Renaming of term variables preserves typing

If `Γ ⊢ t : A` and `ξ` is a renaming of variables compatible with the types, then `t` renamed
by `ξ` is typed in the context obtained by transporting the usages of `Γ` along `ξ` (the
usage of a variable is the sum of the usages of the variables mapped to it). In particular,
weakening by fresh variables that do not occur preserves typing.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

@[simp] theorem Tm.liftR_castAdd {n n' : ℕ} (k : ℕ) (ξ : Fin n → Fin n') (x : Fin n) :
    Tm.liftR k ξ (Fin.castAdd k x) = Fin.castAdd k (ξ x) := by
  simp [Tm.liftR]

@[simp] theorem Tm.liftR_natAdd {n n' : ℕ} (k : ℕ) (ξ : Fin n → Fin n') (i : Fin k) :
    Tm.liftR k ξ (Fin.natAdd n i) = Fin.natAdd n' i := by
  simp [Tm.liftR]

theorem append_liftR {α : Type*} {n n' k : ℕ} {ξ : Fin n → Fin n'} {E : Fin n → α}
    {E' : Fin n' → α} (hE : ∀ x, E' (ξ x) = E x) (W : Fin k → α) (y : Fin (n + k)) :
    Fin.append E' W (Tm.liftR k ξ y) = Fin.append E W y := by
  induction y using Fin.addCases <;> simp [hE]

theorem push_shift {m n n' : ℕ} (ξ : Fin n → Fin n') (U : Usage m n) :
    push ξ (MZ.shift ∘ U) = MZ.shift ∘ push ξ U := by
  funext y
  simp only [push, Function.comp, MZ.shift, MZ.bind_sum]
  congr 1; funext x
  split_ifs <;> rfl

theorem Typed.rename {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S m}
    (h : Typed S E U t A) :
    ∀ {n' : ℕ} (ξ : Fin n → Fin n') (E' : TyEnv S m n'), (∀ x, E' (ξ x) = E x) →
      Typed S E' (push ξ U) (t.rename ξ) A := by
  induction h with
  | var Γ x =>
    intro n' ξ E' hE
    refine ((Typed.var (push ξ Γ) (ξ x)).ofEq ?_).ofEqTy (hE x)
    rw [push_add, push_smul, push_single]
  | abs _ ih =>
    intro n' ξ E' hE
    refine Typed.abs ?_
    have := ih (Tm.liftR 1 ξ) _ (append_liftR hE _)
    rwa [push_liftR] at this
  | app _ _ ih₁ ih₂ =>
    intro n' ξ E' hE
    refine (Typed.app (ih₁ ξ E' hE) (ih₂ ξ E' hE)).ofEq ?_
    rw [push_add, push_smul]
  | con Γ ps Δ _ ih =>
    intro n' ξ E' hE
    refine (Typed.con (push ξ Γ) ps (fun i => push ξ (Δ i)) (fun i => ih i ξ E' hE)).ofEq ?_
    rw [push_add, push_smul, push_sum]
    simp only [push_smul]
  | @case m n E Γ Δ π t D ps bs C _ _ iht ih =>
    intro n' ξ E' hE
    refine (Typed.case (Δ := push ξ Δ) (iht ξ E' hE) (fun k => ?_)).ofEq ?_
    · have := ih k (Tm.liftR _ ξ) _ (append_liftR hE _)
      rwa [push_liftR] at this
    · rw [push_add, push_smul]
  | @letin m n E Δ π j As ts u C Γ _ _ ihts ihu =>
    intro n' ξ E' hE
    refine (Typed.letin (Δ := push ξ Δ) (fun i => push ξ (Γ i)) (fun i => ihts i ξ E' hE) ?_).ofEq ?_
    · have := ihu (Tm.liftR _ ξ) _ (append_liftR hE _)
      rwa [push_liftR] at this
    · rw [push_add, push_smul, push_sum]
  | mabs _ ih =>
    intro n' ξ E' hE
    refine Typed.mabs ?_
    have := ih ξ (Ty.shift ∘ E') (fun x => by simp [hE])
    rwa [push_shift] at this
  | mapp π _ ih =>
    intro n' ξ E' hE
    exact Typed.mapp π (ih ξ E' hE)

/-- Weakening by `k` fresh variables (which do not occur). -/
theorem Typed.weakenFresh {m n k : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n}
    {A : Ty S m} (h : Typed S E U t A) (Es : TyEnv S m k) :
    Typed S (Fin.append E Es) (Fin.append U 0) (t.rename (Fin.castAdd k)) A := by
  have := h.rename (Fin.castAdd k) (Fin.append E Es) (fun x => by simp)
  rwa [push_castAdd] at this

end LinearHaskell
