# Formalization of *Linear Haskell* (core calculus `λq→`)

This Lean 4 / Mathlib development formalizes the core calculus `λq→` of the paper
*Linear Haskell: Practical Linearity in a Higher-Order Polymorphic Language* (`hlt.typ`),
Section 3, together with the examples of Sections 2–3 that concern it. Everything
builds without `sorry` (`lake build`); the main theorems use only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

Entry point: `RequestProject/LinearHaskell.lean` (imports everything).

## Well-scoped, correct-by-construction syntax

All syntax is indexed by its scope, so ill-scoped objects cannot be written down:

| Lean type | Meaning |
|---|---|
| `MExpr m`, `Mult m` | multiplicity expressions / multiplicities with at most `m` free multiplicity variables (`var : Fin m → MExpr m`) |
| `MZ m` | `Mult m` with a zero ("variable does not occur") |
| `Ty Δ m` | types with at most `m` free multiplicity variables; `all : Ty Δ (m+1) → Ty Δ m`; `data D ps` takes exactly `ps : Fin (arity D) → Mult m` |
| `Sig` | datatype declarations: constructor counts `nctors D`, field counts `nfields D k`, and for each field `Fin (nfields D k)` a multiplicity and a type in scope `arity D` (only the parameters may occur) |
| `Tm S m n` | terms with at most `m` free multiplicity variables and `n` free term variables: `var : Fin n → Tm S m n` |
| `TyEnv S m n`, `Usage m n` | contexts for `Tm S m n`: `Fin n → Ty S m` and `Fin n → MZ m` |

Consequences:

* `Tm S m 0` is the type of terms with no free term variable, and `Tm S 0 0` the type of
  fully closed terms. Progress is stated for `t : Tm S m 0`, with no extra hypothesis.
* Binders change the index: `lam π A (t : Tm S m (n+1))`, `mlam (t : Tm S (m+1) n)`,
  `letin π j As ts (u : Tm S m (n+j))`.
* `con D k ts` has exactly one argument per field (`ts : Fin (nfields D k) → Tm S m n`), and
  `case π t D bs` has exactly one branch per constructor, each binding exactly as many
  variables as the constructor has fields
  (`bs : (k : Fin (nctors D)) → Tm S m (n + nfields D k)`). The arity side conditions of the
  typing rules (con)/(case) are therefore enforced by the syntax itself.
* Substitutions are total maps between scopes: `Mult.bind : (Fin m → Mult m') → Mult m → Mult m'`,
  `Tm.rename : (Fin n → Fin n') → …`, `Tm.subst : (Fin n → Tm S m n') → Tm S m n → Tm S m n'`.

Variables of both kinds are de Bruijn **levels**: a binder in scope `n` binds `Fin.last n`
(and `k` binders bind `Fin.natAdd n i`), while outer variables keep their numbers
(`Fin.castAdd`). This matches the paper's convention of extending contexts on the right,
`Γ, x :_π A`, which is `Fin.append` on environments and usages. In a closed term the
outermost bound variable is `0`, the next `1`, etc.

## Correspondence with the paper

| Paper | Lean | File |
|---|---|---|
| Multiplicities `1 \| ω \| p \| π+μ \| π·μ` (Fig. 5) | `MExpr m` | `Mult.lean` |
| Def. 3.4, equivalence of multiplicities | `MExpr.Equiv`, quotient `Mult m` | `Mult.lean` |
| "multiplicities form a semiring without zero" | `AddCommSemigroup (Mult m)`, `CommMonoid (Mult m)`, `Distrib (Mult m)` | `Mult.lean` |
| (consistency of Def. 3.4) | `Mult.one_ne_omega`, `Mult.var_ne_one`, `Mult.add_ne_one`, … | `Mult.lean` |
| Types `A →_π B \| ∀p.A \| D π₁…πₙ`, datatype declarations | `Ty`, `DataSig`, `Sig` | `Syntax.lean` |
| Terms (Fig. 5) | `Tm` | `Syntax.lean` |
| Contexts, context addition and scaling (Sec. 3.2) | `TyEnv`, `Usage` (`Fin n → MZ m`), pointwise `+`, `•` | `Context.lean` |
| Laws `Γ+Δ=Δ+Γ`, `π(Γ+Δ)=πΓ+πΔ`, `(π+μ)Γ=πΓ+μΓ`, `(πμ)Γ=π(μΓ)`, `1Γ=Γ` | `ctx_add_comm`, `ctx_smul_add`, `ctx_add_smul`, `ctx_mul_smul`, `ctx_one_smul` | `Context.lean` |
| Typing rules (Fig. 6) | `Typed` | `Typing.lean` |
| Operational semantics | `Step`, `Steps`, `Value` (see caveat below) | `Semantics.lean` |
| Theorem 3.5 (type preservation) | `preservation`, `preservation_steps` | `Safety.lean` |
| Theorem 3.6 (progress) | `progress`, `type_safety` | `Safety.lean` |
| Linear substitution lemma (`Γ, x:_q A ⊢ t:B`, `Δ ⊢ u:A` ⟹ `Γ+qΔ ⊢ t[u/x]:B`) | `Typed.substTop1`, `Typed.substTop` (k variables at once), `Typed.subst` (general simultaneous substitution) | `Subst.lean` |
| Weakening of `ω`-variables, renaming, multiplicity substitution | `Typed.weaken`, `Typed.rename`, `Typed.weakenFresh`, `Typed.mbind` | `Weakening.lean`, `Rename.lean`, `MSubst.lean` |
| `swap`/`f2 : Pair ⊸ Pair` (Secs. 2.4, 3.3) | `swap_typed` | `Examples.lean` |
| `fst : Pair → Int` via `case_ω` (Sec. 3.3) | `fst_typed` | `Examples.lean` |
| `fst` impossible with `case₁` | `fst_case1_untypable` | `Examples.lean` |
| `f1` is not linear (Sec. 2.4) | `f1_not_linear`, `dup_not_linear` | `Examples.lean` |
| `Unrestricted (a,b) ⊸ (Unrestricted a, Unrestricted b)` via `case_ω` (Sec. 3.5) | `urDist_typed` | `Examples.lean` |
| `(∘) : ∀p q. (b →_p c) ⊸ (a →_q b) →_p a →_{p·q} c` (Sec. 2.6) | `compose_typed` (for arbitrary types `a b c`) | `Examples.lean` |
| `x :_ω A ⊢ x : A`, `x :_1 A, y :_ω B ⊢ x : A` (Sec. 3.2) | `var_omega`, `var_weak` | `Examples.lean` |
| `x :_p A ⊬ x : A`, so `λp. λ_p x. x : ∀p. A →_p A` is rejected (Sec. 3.5) | `var_mult_var_untypable`, `id_mult_poly_untypable` | `Examples.lean` |

## Representation choices

* **Contexts** `Γ` are split into a type environment `E : Fin n → Ty S m` (inputs of the
  judgement) and a usage vector `U : Fin n → MZ m` (outputs), where `MZ m` adjoins a zero
  ("the variable does not occur") to the multiplicities. Then the paper's context addition
  and scaling are pointwise operations and the laws of Sec. 3.2 are module laws.
* **(m.abs)**: "`p` fresh for `Γ`" becomes "the body is typed in `Γ` weakened to the scope
  with one more multiplicity variable", so `p` cannot occur in `Γ` by construction.
* **Renaming** need not be injective: usages are pushed forward by summing
  (`push ξ U y = Σ_{ξ x = y} U x`). **Substitution** `t[σ]` has usage `Σₓ U(x) Δₓ`, where
  `Δₓ` is the usage of `σ x`.
* **`case` carries its datatype** `D` (`case π t D bs`); the paper's `case` does not mention
  it, but it is determined by the scrutinee's type and is what makes the branches
  well-scoped by construction.
* **Equivalence of multiplicities.** Def. 3.4 says "the smallest transitive and
  reflexive relation" satisfying the laws; we take the smallest *congruence* (also
  symmetric and compatible with `+`, `·`), which is clearly what is meant since the
  relation is used to quotient expressions.
* **Typo in (abs).** Fig. 6 concludes `A →_q B`; we use `A →_π B` as the text intends.
* **Constructor field types** are instantiated at the datatype parameters, like the field
  multiplicities (a no-op when they do not mention the parameters, as in all examples).

## Caveats / what is not formalized

* The paper states Theorems 3.5–3.6 for a Launchbury-style lazy big-step semantics with
  multiplicity-annotated environments, defined in an appendix (A.1–A.3) that is **not
  part of the provided source**. We prove preservation and progress for a standard
  small-step **call-by-name** semantics (arguments, `let` bindings and constructor fields
  are never evaluated eagerly). Preservation holds with the *same* usage context, so
  reduction never changes how many times a free variable is consumed.
* Theorems 3.7–3.9 (the semantics with in-place mutation and typestates, its bisimilarity
  with the pure semantics, and observational equivalence) rely entirely on that missing
  appendix (the mutable semantics is only sketched in prose), so they are not formalized.
* Sections 4–7 (implementation in GHC, benchmarks, case studies, related and future work)
  are not mathematical statements and are not formalized.
