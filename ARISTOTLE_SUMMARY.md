# Summary of changes for run 7807dc16-8ae6-4b50-ac90-1dffd97609da
I rebuilt the formalization so that scoping is part of the types: ill-scoped syntax can no longer be written down. All the earlier results are proved again on the new representation. The project builds with no `sorry`, no warnings and no added axioms. The main theorems use only `propext`, `Classical.choice` and `Quot.sound`.

**The new datatypes** (`Mult.lean`, `Syntax.lean`, `Context.lean`):
- **Multiplicities:** `MExpr m` and `Mult m` have at most `m` free multiplicity variables, with `var : Fin m → MExpr m`.
- **Types:** `Ty Δ m`. The binder `all` takes a body of type `Ty Δ (m+1)`, and `data D ps` needs exactly one argument per parameter (`ps : Fin (arity D) → Mult m`).
- **Signatures:** `Sig` lists, for each datatype, its constructors and, for each constructor, its fields. A field's multiplicity and type can only mention the datatype's parameters.
- **Terms:** `Tm S m n` has at most `m` free multiplicity variables and `n` free term variables, with `var : Fin n → Tm S m n`.
  - Terms need two indices because `λ p. t` binds a multiplicity variable and `λ x. t` binds a term variable. So `Tm S m 0` means "no free term variables" and `Tm S 0 0` means fully closed.
  - Binders change the index: `lam` takes a body of type `Tm S m (n+1)`, `mlam` takes `Tm S (m+1) n`, and `letin` takes `Tm S m (n+j)`.
  - `con D k ts` takes exactly one argument per field.
  - `case π t D bs` has exactly one branch per constructor, each binding one variable per field. So the arity checks the typing rules used to need are now part of the syntax.
  - **Change from the paper:** `case` now names its datatype `D`. The paper's `case` doesn't mention it, but it is fixed by the scrutinee's type, and it is what lets each branch's number of bound variables be part of its type.
- **Contexts:** `TyEnv S m n = Fin n → Ty S m` and `Usage m n = Fin n → MZ m`. Extending a context is `Fin.append`.
- **Substitutions:** these are now total maps between scopes, for example `Tm.subst : (Fin n → Tm S m n') → Tm S m n → Tm S m n'`.
- **Variable numbering:** variables count from the outside in (de Bruijn levels), matching the paper's habit of extending contexts on the right. In a closed term the outermost bound variable is `0`.

**Results re-proved:**
- Weakening by unrestricted (`ω`) variables, multiplicity substitution, and renaming.
- A general simultaneous substitution lemma, `Typed.subst`, with the paper's single-variable lemma as `Typed.substTop1`.
- **Theorem 3.5 (preservation):** `preservation`.
- **Theorem 3.6 (progress):** `progress`, now stated for `t : Tm S m 0`. The old side condition "usage = 0" is gone, because the type itself says the term has no free variables.
- **Examples:** `swap_typed`, `fst_typed`, `urDist_typed`, `compose_typed` (now for arbitrary types `a b c`), `fst_case1_untypable`, `dup_not_linear`, `f1_not_linear`, `var_omega`, `var_weak`, `var_mult_var_untypable` and `id_mult_poly_untypable`.

The caveats from before still apply. Preservation and progress are proved for a call-by-name semantics I defined, because the paper's own semantics is in an appendix that isn't in the source. Theorems 3.7–3.9 are not formalized. `LINEAR_HASKELL_FORMALIZATION.md` now describes the new representation and maps each paper item to its Lean name, and the properties table is updated to the new statements.

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