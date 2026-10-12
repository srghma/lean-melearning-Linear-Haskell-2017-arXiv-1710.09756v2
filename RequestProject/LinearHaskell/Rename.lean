module

public import RequestProject.LinearHaskell.MSubst

/-!
# Renaming of term variables preserves typing

If `Γ ⊢ t : A` and `ξ` is an injective renaming, then `t` renamed by `ξ` is typed in the
context obtained by transporting `Γ` along `ξ` (variables outside the range of `ξ` do not
occur). In particular, shifting (weakening by fresh variables that do not occur) preserves
typing.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

theorem Typed.rename {E : TyEnv} {U : Usage} {t : Tm} {A : Ty} (h : Typed S E U t A) :
    ∀ (ξ : ℕ → ℕ) (E' : TyEnv), Function.Injective ξ → (∀ x, E' (ξ x) = E x) →
      Typed S E' (push ξ U) (t.rename ξ) A := by
  induction h with
  | @var E Γ x =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    refine ((Typed.var (push ξ Γ) (ξ x)).ofEq ?_).ofEqTy (hE x)
    rw [push_add hξ, push_smul hξ, push_single hξ]
  | @abs E U π A B t _ ih =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    refine Typed.abs ?_
    have := ih (Tm.upR 1 ξ) (prep [A] E') (upR_injective hξ 1)
      (fun x => prep_upR (f := E) (g := E') hE [A] x)
    rwa [show push (Tm.upR 1 ξ) (prep [MZ.of π] U) = prep [MZ.of π] (push ξ U) from
      push_upR hξ [MZ.of π] U] at this
  | @app E Γ Δ π A B t u _ _ ih₁ ih₂ =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    refine (Typed.app (ih₁ ξ E' hξ hE) (ih₂ ξ E' hξ hE)).ofEq ?_
    rw [push_add hξ, push_smul hξ]
  | @con E Γ D k ps ts Δ hp hk hl _ ih =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    have := Typed.con (S := S) (E := E') (push ξ Γ) (D := D) (k := k)
      (ps := ps) (ts := ts.map (fun t => Tm.rename ξ t))
      (fun i => push ξ (Δ i)) hp hk (by simpa using hl) (by
        intro i hi
        rw [List.length_map] at hi
        rw [List.getD_map_of_lt _ _ default _ _ hi]
        exact ih i hi ξ E' hξ hE)
    refine this.ofEq ?_
    rw [push_add hξ, push_smul hξ, push_sum hξ, List.length_map]
    simp only [push_smul hξ]
  | @case E Γ Δ π t D ps bs C ht hl hn _ iht ih =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    have := Typed.case (S := S) (E := E') (Γ := push ξ Γ) (Δ := push ξ Δ)
      (π := π) (bs := bs.map (fun b => (b.1, Tm.rename (Tm.upR b.1 ξ) b.2))) (C := C)
      (iht ξ E' hξ hE) (by simpa using hl)
      (by
        intro k hk
        rw [List.length_map] at hk
        rw [List.getD_map_of_lt _ _ default _ _ hk]
        exact hn k hk)
      (by
        intro k hk
        rw [List.length_map] at hk
        rw [List.getD_map_of_lt _ _ default _ _ hk]
        have hlen : (bs.getD k default).1 = (S.fieldTys D k ps).length := by
          rw [hn k hk]; simp [Sig.fieldTys]
        have hlen' : (bs.getD k default).1 =
            ((S.fieldMults D k ps).map (fun μ => MZ.of (π * μ))).length := by
          rw [hn k hk]; simp [Sig.fieldMults]
        have := ih k hk (Tm.upR (bs.getD k default).1 ξ) (prep (S.fieldTys D k ps) E')
          (upR_injective hξ _)
          (fun x => by rw [hlen]; exact prep_upR (f := E) (g := E') hE _ x)
        dsimp only
        rw [hlen'] at this ⊢
        rwa [push_upR hξ] at this)
    refine this.ofEq ?_
    rw [push_add hξ, push_smul hξ]
  | @letin E Δ π bs u C Γ _ _ ih ihu =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    have := Typed.letin (S := S) (E := E') (Δ := push ξ Δ)
      (π := π) (bs := bs.map (fun b => (b.1, Tm.rename ξ b.2)))
      (u := u.rename (Tm.upR bs.length ξ)) (C := C) (fun i => push ξ (Γ i))
      (by
        intro i hi
        rw [List.length_map] at hi
        rw [List.getD_map_of_lt _ _ default _ _ hi]
        exact ih i hi ξ E' hξ hE)
      (by
        have h1 : bs.length = (bs.map Prod.fst).length := by simp
        have := ihu (Tm.upR bs.length ξ) (prep (bs.map Prod.fst) E') (upR_injective hξ _)
          (fun x => by rw [h1]; exact prep_upR (f := E) (g := E') hE _ x)
        have e := push_upR hξ (List.replicate bs.length (MZ.of π)) Δ
        rw [List.length_replicate] at e
        rw [e] at this
        simpa [List.map_map, Function.comp_def] using this)
    refine this.ofEq ?_
    rw [push_add hξ, push_smul hξ, push_sum hξ, List.length_map]
  | @mabs E U t A _ ih =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    refine Typed.mabs ?_
    have := ih ξ (Ty.shift ∘ E') hξ (fun x => by simp [hE x])
    rwa [push_comp hξ _ rfl] at this
  | @mapp E U t A π _ ih =>
    intro ξ E' hξ hE
    simp only [Tm.rename]
    exact Typed.mapp π (ih ξ E' hξ hE)

/-- Shifting a term by `n` places it in a context extended by `n` variables that do not
occur. -/
theorem Typed.shiftN {E : TyEnv} {U : Usage} {t : Tm} {A : Ty} (h : Typed S E U t A)
    (l : List Ty) :
    Typed S (prep l E) (prep (List.replicate l.length 0) U) (t.shiftN l.length) A := by
  have := h.rename (· + l.length) (prep l E) (fun a b h => by simpa using h)
    (fun x => prep_add_length l E x)
  rwa [push_add_right] at this

end LinearHaskell
