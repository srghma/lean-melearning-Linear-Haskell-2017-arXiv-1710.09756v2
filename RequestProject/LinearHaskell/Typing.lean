module

public import RequestProject.LinearHaskell.Context

/-!
# Typing rules of `λq→` (Fig. 6)

The judgement `Typed S E U t A` stands for the paper's `Γ ⊢ t : A`, where the context `Γ`
is given by the type environment `E` and the usage vector `U` (see `Context.lean`), in the
signature `S` of datatype declarations.

Notes on the transcription:

* (abs): the paper's figure concludes `Γ ⊢ λ_π (x:A). t : A →_q B`; the `q` is a typo for
  `π` (the text explains that the arrow carries the annotation of the λ).
* (m.abs): "`p` fresh for `Γ`" is expressed with de Bruijn indices by typing the body in
  the shifted context (the bound multiplicity variable is `0`, which does not occur in a
  shifted context).
* (con), (case): the field types `Aᵢ` of a constructor are instantiated at the parameters
  `π₁ … πₙ` just like the field multiplicities `μᵢ`. (If the `Aᵢ` do not mention the
  parameters, as in the paper's examples, this instantiation does nothing.)
* (con) checks that the number of multiplicity arguments matches the declaration and the
  number of arguments matches the arity of the constructor; (case) checks that there is one
  branch per constructor, each binding as many variables as the constructor has fields.
-/

@[expose] public section

namespace LinearHaskell

/-- The substitution shifting multiplicity variables. -/
def mshiftσ : ℕ → Mult := fun n => Mult.var (n + 1)

/-- The typing judgement `Γ ⊢ t : A` of Fig. 6 (with `Γ` given by `E` and `U`). -/
inductive Typed (S : Sig) : TyEnv → Usage → Tm → Ty → Prop
  /-- (var) `ωΓ + x :_1 A ⊢ x : A`. -/
  | var {E : TyEnv} (Γ : Usage) (x : ℕ) :
      Typed S E (ω' • Γ + Pi.single x 1) (.var x) (E x)
  /-- (abs) from `Γ, x :_π A ⊢ t : B` infer `Γ ⊢ λ_π (x:A). t : A →_π B`. -/
  | abs {E : TyEnv} {U : Usage} {π : Mult} {A B : Ty} {t : Tm} :
      Typed S (prep [A] E) (prep [MZ.of π] U) t B →
      Typed S E U (.lam π A t) (.arr π A B)
  /-- (app) from `Γ ⊢ t : A →_π B` and `Δ ⊢ u : A` infer `Γ + πΔ ⊢ t u : B`. -/
  | app {E : TyEnv} {Γ Δ : Usage} {π : Mult} {A B : Ty} {t u : Tm} :
      Typed S E Γ t (.arr π A B) → Typed S E Δ u A →
      Typed S E (Γ + MZ.of π • Δ) (.app t u) B
  /-- (con) from `Δᵢ ⊢ tᵢ : Aᵢ` infer `ωΓ + Σᵢ μᵢ[π₁ … πₙ] Δᵢ ⊢ c_k t₁ … t_{n_k} : D π₁ … πₙ`. -/
  | con {E : TyEnv} (Γ : Usage) {D k : ℕ} {ps : List Mult} {ts : List Tm} (Δ : ℕ → Usage) :
      ps.length = S.nparams D → k < (S.ctors D).length →
      ts.length = (S.fields D k).length →
      (∀ i < ts.length, Typed S E (Δ i) (ts.getD i default) (S.fieldTy D k ps i)) →
      Typed S E (ω' • Γ + ∑ i ∈ Finset.range ts.length, MZ.of (S.fieldMult D k ps i) • Δ i)
        (.con D k ts) (.data D ps)
  /-- (case) from `Γ ⊢ t : D π₁ … πₙ` and, for each constructor `c_k`,
  `Δ, x₁ :_{π μ₁[π₁ … πₙ]} A₁, … ⊢ u_k : C`, infer
  `πΓ + Δ ⊢ case_π t of {c_k x₁ … x_{n_k} → u_k} : C`. -/
  | case {E : TyEnv} {Γ Δ : Usage} {π : Mult} {t : Tm} {D : ℕ} {ps : List Mult}
      {bs : List (ℕ × Tm)} {C : Ty} :
      Typed S E Γ t (.data D ps) →
      bs.length = (S.ctors D).length →
      (∀ k < bs.length, (bs.getD k default).1 = (S.fields D k).length) →
      (∀ k < bs.length, Typed S (prep (S.fieldTys D k ps) E)
          (prep ((S.fieldMults D k ps).map (fun μ => MZ.of (π * μ))) Δ)
          (bs.getD k default).2 C) →
      Typed S E (MZ.of π • Γ + Δ) (.case π t bs) C
  /-- (let) from `Γᵢ ⊢ tᵢ : Aᵢ` and `Δ, x₁ :_π A₁ … xₙ :_π Aₙ ⊢ u : C` infer
  `Δ + π Σᵢ Γᵢ ⊢ let_π x₁ : A₁ = t₁ … xₙ : Aₙ = tₙ in u : C`. -/
  | letin {E : TyEnv} {Δ : Usage} {π : Mult} {bs : List (Ty × Tm)} {u : Tm} {C : Ty}
      (Γ : ℕ → Usage) :
      (∀ i < bs.length, Typed S E (Γ i) (bs.getD i default).2 (bs.getD i default).1) →
      Typed S (prep (bs.map Prod.fst) E) (prep (List.replicate bs.length (MZ.of π)) Δ) u C →
      Typed S E (Δ + MZ.of π • ∑ i ∈ Finset.range bs.length, Γ i) (.letin π bs u) C
  /-- (m.abs) from `Γ ⊢ t : A` with `p` fresh for `Γ` infer `Γ ⊢ λ p. t : ∀ p. A`. -/
  | mabs {E : TyEnv} {U : Usage} {t : Tm} {A : Ty} :
      Typed S (Ty.shift ∘ E) (MZ.bind mshiftσ ∘ U) t A →
      Typed S E U (.mlam t) (.all A)
  /-- (m.app) from `Γ ⊢ t : ∀ p. A` infer `Γ ⊢ t π : A[π/p]`. -/
  | mapp {E : TyEnv} {U : Usage} {t : Tm} {A : Ty} (π : Mult) :
      Typed S E U t (.all A) →
      Typed S E U (.mapp t π) (A.inst π)

end LinearHaskell
