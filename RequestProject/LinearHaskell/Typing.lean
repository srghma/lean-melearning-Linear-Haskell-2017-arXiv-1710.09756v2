module

public import RequestProject.LinearHaskell.Context

/-!
# Typing rules of `λq→` (Fig. 6)

The judgement `Typed S E U t A` stands for the paper's `Γ ⊢ t : A`, where the context `Γ`
is given by the type environment `E` and the usage vector `U` (see `Context.lean`), in the
signature `S` of datatype declarations. The term `t : Tm S m n`, the context and the type
all live in the same scope (`m` multiplicity variables, `n` term variables).

Notes on the transcription:

* (abs): the paper's figure concludes `Γ ⊢ λ_π (x:A). t : A →_q B`; the `q` is a typo for
  `π` (the text explains that the arrow carries the annotation of the λ).
* (m.abs): "`p` fresh for `Γ`" is expressed by typing the body in the weakened context
  `Γ` viewed in the scope with one more multiplicity variable `p` (which therefore cannot
  occur in `Γ`).
* (con), (case): the field types `Aᵢ` of a constructor are instantiated at the parameters
  `π₁ … πₙ` just like the field multiplicities `μᵢ`. (If the `Aᵢ` do not mention the
  parameters, as in the paper's examples, this instantiation does nothing.)
* The side conditions on numbers of arguments, branches and bound variables in (con) and
  (case) are enforced by the scoped syntax of terms.
-/

@[expose] public section

namespace LinearHaskell

/-- The typing judgement `Γ ⊢ t : A` of Fig. 6 (with `Γ` given by `E` and `U`). -/
inductive Typed (S : Sig) : {m n : ℕ} → TyEnv S m n → Usage m n → Tm S m n → Ty S m → Prop
  /-- (var) `ωΓ + x :_1 A ⊢ x : A`. -/
  | var {m n : ℕ} {E : TyEnv S m n} (Γ : Usage m n) (x : Fin n) :
      Typed S E ((ω' : MZ m) • Γ + Pi.single x 1) (.var x) (E x)
  /-- (abs) from `Γ, x :_π A ⊢ t : B` infer `Γ ⊢ λ_π (x:A). t : A →_π B`. -/
  | abs {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {π : Mult m} {A B : Ty S m}
      {t : Tm S m (n + 1)} :
      Typed S (Fin.append E ![A]) (Fin.append U ![MZ.of π]) t B →
      Typed S E U (.lam π A t) (.arr π A B)
  /-- (app) from `Γ ⊢ t : A →_π B` and `Δ ⊢ u : A` infer `Γ + πΔ ⊢ t u : B`. -/
  | app {m n : ℕ} {E : TyEnv S m n} {Γ Δ : Usage m n} {π : Mult m} {A B : Ty S m}
      {t u : Tm S m n} :
      Typed S E Γ t (.arr π A B) → Typed S E Δ u A →
      Typed S E (Γ + MZ.of π • Δ) (.app t u) B
  /-- (con) from `Δᵢ ⊢ tᵢ : Aᵢ[π₁ … πₙ]` infer
  `ωΓ + Σᵢ μᵢ[π₁ … πₙ] Δᵢ ⊢ c_k t₁ … t_{n_k} : D π₁ … πₙ`. -/
  | con {m n : ℕ} {E : TyEnv S m n} (Γ : Usage m n) {D : S.Name} {k : Fin (S.nctors D)}
      (ps : Fin (S.arity D) → Mult m) {ts : Fin (S.nfields D k) → Tm S m n}
      (Δ : Fin (S.nfields D k) → Usage m n) :
      (∀ i, Typed S E (Δ i) (ts i) (S.fieldTyAt D k ps i)) →
      Typed S E ((ω' : MZ m) • Γ + ∑ i, MZ.of (S.fieldMultAt D k ps i) • Δ i) (.con D k ts) (.data D ps)
  /-- (case) from `Γ ⊢ t : D π₁ … πₙ` and, for each constructor `c_k`,
  `Δ, x₁ :_{π μ₁[π₁ … πₙ]} A₁[π₁ … πₙ], … ⊢ u_k : C`, infer
  `πΓ + Δ ⊢ case_π t of {c_k x₁ … x_{n_k} → u_k} : C`. -/
  | case {m n : ℕ} {E : TyEnv S m n} {Γ Δ : Usage m n} {π : Mult m} {t : Tm S m n}
      {D : S.Name} {ps : Fin (S.arity D) → Mult m}
      {bs : (k : Fin (S.nctors D)) → Tm S m (n + S.nfields D k)} {C : Ty S m} :
      Typed S E Γ t (.data D ps) →
      (∀ k, Typed S (Fin.append E (S.fieldTyAt D k ps))
          (Fin.append Δ (fun i => MZ.of (π * S.fieldMultAt D k ps i))) (bs k) C) →
      Typed S E (MZ.of π • Γ + Δ) (.case π t D bs) C
  /-- (let) from `Γᵢ ⊢ tᵢ : Aᵢ` and `Δ, x₁ :_π A₁ … x_j :_π A_j ⊢ u : C` infer
  `Δ + π Σᵢ Γᵢ ⊢ let_π x₁ : A₁ = t₁ … x_j : A_j = t_j in u : C`. -/
  | letin {m n : ℕ} {E : TyEnv S m n} {Δ : Usage m n} {π : Mult m} {j : ℕ} {As : Fin j → Ty S m}
      {ts : Fin j → Tm S m n} {u : Tm S m (n + j)} {C : Ty S m} (Γ : Fin j → Usage m n) :
      (∀ i, Typed S E (Γ i) (ts i) (As i)) →
      Typed S (Fin.append E As) (Fin.append Δ (fun _ => MZ.of π)) u C →
      Typed S E (Δ + MZ.of π • ∑ i, Γ i) (.letin π j As ts u) C
  /-- (m.abs) from `Γ ⊢ t : A` with `p` fresh for `Γ` infer `Γ ⊢ λ p. t : ∀ p. A`. -/
  | mabs {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S (m + 1) n} {A : Ty S (m + 1)} :
      Typed S (Ty.shift ∘ E) (MZ.shift ∘ U) t A →
      Typed S E U (.mlam t) (.all A)
  /-- (m.app) from `Γ ⊢ t : ∀ p. A` infer `Γ ⊢ t π : A[π/p]`. -/
  | mapp {m n : ℕ} {E : TyEnv S m n} {U : Usage m n} {t : Tm S m n} {A : Ty S (m + 1)}
      (π : Mult m) :
      Typed S E U t (.all A) →
      Typed S E U (.mapp t π) (A.inst π)

end LinearHaskell
