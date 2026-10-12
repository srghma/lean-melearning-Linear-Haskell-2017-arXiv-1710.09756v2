# Formalization of *Linear Haskell* (core calculus `λq→`)

This Lean 4 / Mathlib development formalizes the core calculus `λq→` of the paper
*Linear Haskell: Practical Linearity in a Higher-Order Polymorphic Language* (`hlt.typ`),
Section 3, together with the examples of Sections 2–3 that concern it. Everything
builds without `sorry` (`lake build`); the main theorems use only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

Entry point: `RequestProject/LinearHaskell.lean` (imports everything).

## Correspondence with the paper

| Paper | Lean | File |
|---|---|---|
| Multiplicities `1 \| ω \| p \| π+μ \| π·μ` (Fig. 5) | `MExpr` | `Mult.lean` |
| Def. 3.4, equivalence of multiplicities | `MExpr.Equiv`, quotient `Mult` | `Mult.lean` |
| "multiplicities form a semiring without zero" | `AddCommSemigroup Mult`, `CommMonoid Mult`, `Distrib Mult` | `Mult.lean` |
| (consistency of Def. 3.4) | `Mult.one_ne_omega`, `Mult.var_ne_one`, `Mult.add_ne_one`, … | `Mult.lean` |
| Types `A →_π B \| ∀p.A \| D π₁…πₙ`, datatype declarations | `Ty`, `Sig` | `Syntax.lean` |
| Terms (Fig. 5) | `Tm` | `Syntax.lean` |
| Contexts, context addition and scaling (Sec. 3.2) | `TyEnv`, `Usage` (`ℕ → MZ`), pointwise `+`, `•` | `Context.lean` |
| Laws `Γ+Δ=Δ+Γ`, `π(Γ+Δ)=πΓ+πΔ`, `(π+μ)Γ=πΓ+μΓ`, `(πμ)Γ=π(μΓ)`, `1Γ=Γ` | `ctx_add_comm`, `ctx_smul_add`, `ctx_add_smul`, `ctx_mul_smul`, `ctx_one_smul` | `Context.lean` |
| Typing rules (Fig. 6) | `Typed` | `Typing.lean` |
| Operational semantics | `Step`, `Steps`, `Value` (see caveat below) | `Semantics.lean` |
| Theorem 3.5 (type preservation) | `preservation`, `preservation_steps` | `Safety.lean` |
| Theorem 3.6 (progress) | `progress`, `type_safety` | `Safety.lean` |
| Linear substitution lemma (`Γ, x:_q A ⊢ t:B`, `Δ ⊢ u:A` ⟹ `Γ+qΔ ⊢ t[u/x]:B`) | `Typed.substAt`, `Typed.substList` | `Subst.lean`, `Safety.lean` |
| Weakening of `ω`-variables, renaming, multiplicity substitution | `Typed.weaken`, `Typed.rename`, `Typed.mbind` | `Weakening.lean`, `Rename.lean`, `MSubst.lean` |
| `swap`/`f2 : Pair ⊸ Pair` (Secs. 2.4, 3.3) | `swap_typed` | `Examples.lean` |
| `fst : Pair → Int` via `case_ω` (Sec. 3.3) | `fst_typed` | `Examples.lean` |
| `fst` impossible with `case₁` | `fst_case1_untypable` | `Examples.lean` |
| `f1` is not linear (Sec. 2.4) | `f1_not_linear`, `dup_not_linear` | `Examples.lean` |
| `Unrestricted (a,b) ⊸ (Unrestricted a, Unrestricted b)` via `case_ω` (Sec. 3.5) | `urDist_typed` | `Examples.lean` |
| `(∘) : ∀p q. (b →_p c) ⊸ (a →_q b) →_p a →_{p·q} c` (Sec. 2.6) | `compose_typed` | `Examples.lean` |
| `x :_ω A ⊢ x : A`, `x :_1 A, y :_ω B ⊢ x : A` (Sec. 3.2) | `var_omega`, `var_weak` | `Examples.lean` |
| `x :_p Int ⊬ x : Int`, so `id : ∀p. Int →_p Int` is rejected (Sec. 3.5) | `var_mult_var_untypable`, `id_mult_poly_untypable` | `Examples.lean` |

## Representation choices

* **De Bruijn indices** for both term variables and multiplicity variables. The side
  condition "`p` fresh for `Γ`" of (m.abs) becomes "the body is typed in the shifted
  context".
* **Contexts** `Γ` are split into a type environment `E : ℕ → Ty` (inputs of the
  judgement) and a usage vector `U : ℕ → MZ` (outputs), where `MZ` adjoins a zero
  ("the variable does not occur") to the multiplicities. Then the paper's context addition
  and scaling are pointwise operations and the laws of Sec. 3.2 are module laws.
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
