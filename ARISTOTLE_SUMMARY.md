# Summary of changes for run 1eb92b39-f3c1-45c0-bb69-bad16de0275a
I formalized the core calculus of *Linear Haskell* (`λq→`, Section 3 of `hlt.typ`) in Lean, along with the paper's examples that are about it. Type preservation and progress are proved, but for a lazy semantics I defined myself: the paper defines its own semantics in Appendix A, which is not in the uploaded source. The project builds without `sorry`. The main theorems depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Everything is under `RequestProject/LinearHaskell/`, and `RequestProject/LinearHaskell.lean` imports it all. `LINEAR_HASKELL_FORMALIZATION.md` maps each paper item to its Lean name.

**Definitions** (Sections 3.1–3.3):
- **Multiplicities** (`Mult.lean`): expressions `1 | ω | p | π+μ | π·μ`, taken up to the equivalence of Definition 3.4. A small two-value model shows this equivalence doesn't collapse everything: for example \(1 \ne \omega\).
- **Types, datatype declarations and terms** (`Syntax.lean`). Variables are numbered by position (de Bruijn indices), so "`p` fresh for `Γ`" becomes a shift of indices.
- **Contexts** (`Context.lean`): a context is a type for each variable plus a vector of multiplicities, where 0 means the variable doesn't occur. The paper's context addition and scaling are then pointwise, and all five laws of Section 3.2 are proved.
- **Typing rules** of Fig. 6 (`Typing.lean`).

**Metatheory:**
- Supporting lemmas: weakening by unrestricted (`ω`) variables, renaming, and substitution of multiplicity variables.
- The linear substitution lemma, `Typed.substAt`: if \(\Gamma, x:_q A \vdash t : B\) and \(\Delta \vdash u : A\), then \(\Gamma + q\Delta \vdash t[u/x] : B\).
- **Theorem 3.5 (preservation):** `preservation` and `preservation_steps`. A step keeps exactly the same context, so variable multiplicities never change.
- **Theorem 3.6 (progress):** `progress`, combined with preservation in `type_safety`.

**Examples** (`Examples.lean`), checked against a small sample set of datatypes:
- `swap : Pair ⊸ Pair` type-checks using `case₁`, and `fst : Pair → Int` using `case_ω`.
- `f1` has no linear type, whatever multiplicity its `case` carries.
- A linear variable can't be duplicated, and with `case₁` a linear field can't be discarded.
- `Unrestricted (a,b) ⊸ (Unrestricted a, Unrestricted b)` has an inhabitant thanks to `case_ω`.
- Composition has the type `∀p q. (b →_p c) ⊸ (a →_q b) →_p a →_{p·q} c`.
- `x :_ω A ⊢ x : A` and `x :_1 A, y :_ω B ⊢ x : A` hold.
- `x :_p Int ⊬ x : Int`, so `λp. λ_p x. x` does not get type `∀p. Int →_p Int`.

**How I read the paper:**
- **Equivalence of multiplicities:** I took it to be closed under `+` and `·` (a congruence). The paper only says "transitive and reflexive", but it uses the relation to identify expressions.
- **Typo in (abs):** the rule concludes `A →_q B`; I read this as `A →_π B`.
- **Constructor field types** are instantiated at the datatype's parameters, like the field multiplicities. This changes nothing in any of the paper's examples.

**Not formalized:**
- **The paper's own semantics:** the Launchbury-style lazy semantics it states Theorems 3.5–3.6 for is defined only in the missing appendix.
- **Theorems 3.7–3.9:** in-place mutation, typestates, the bisimulation and observational equivalence rely entirely on that appendix. They are listed in the properties table as still in progress.
- **Sections 4–7:** implementation, case studies, related and future work contain no mathematical claims.