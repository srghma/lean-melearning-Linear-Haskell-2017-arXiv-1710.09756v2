module

public import RequestProject.LinearHaskell.Typing

/-!
# Operational semantics

The paper (Section 3.4) states its metatheory for a Launchbury-style big-step semantics
for lazy evaluation that is described in an appendix; that appendix is not part of the
provided source. We therefore formalise type safety with respect to a standard small-step,
call-by-name (lazy: arguments, `let` right-hand sides and constructor fields are never
evaluated before they are needed) reduction relation on terms.

Values are λ-abstractions, multiplicity abstractions and constructor applications (whose
fields are unevaluated, as in a lazy language).

Reduction is defined on terms in any scope; it never changes the scope. Progress is stated
for closed terms, i.e. terms of type `Tm S m 0`.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

/-- Values (weak head normal forms). -/
inductive Value {m n : ℕ} : Tm S m n → Prop
  | lam (π : Mult m) (A : Ty S m) (t : Tm S m (n + 1)) : Value (.lam π A t)
  | mlam (t : Tm S (m + 1) n) : Value (.mlam t)
  | con (D : S.Name) (k : Fin (S.nctors D)) (ts : Fin (S.nfields D k) → Tm S m n) :
      Value (.con D k ts)

/-- One step of call-by-name reduction. -/
inductive Step : {m n : ℕ} → Tm S m n → Tm S m n → Prop
  /-- `(λ_π (x:A). t) u ⟶ t[u/x]` -/
  | beta {m n : ℕ} (π : Mult m) (A : Ty S m) (t : Tm S m (n + 1)) (u : Tm S m n) :
      Step (.app (.lam π A t) u) (Tm.substTop ![u] t)
  | appL {m n : ℕ} {t t' : Tm S m n} (u : Tm S m n) : Step t t' → Step (.app t u) (.app t' u)
  /-- `(λ p. t) π ⟶ t[π/p]` -/
  | mbeta {m n : ℕ} (t : Tm S (m + 1) n) (π : Mult m) :
      Step (.mapp (.mlam t) π) (t.mbind (Mult.inst π))
  | mappL {m n : ℕ} {t t' : Tm S m n} (π : Mult m) : Step t t' → Step (.mapp t π) (.mapp t' π)
  /-- `case_π (c_k t₁ … tₙ) of {…; c_k x₁ … xₙ → u_k; …} ⟶ u_k[t₁/x₁ … tₙ/xₙ]` -/
  | caseCon {m n : ℕ} (π : Mult m) (D : S.Name) (k : Fin (S.nctors D))
      (ts : Fin (S.nfields D k) → Tm S m n)
      (bs : (k : Fin (S.nctors D)) → Tm S m (n + S.nfields D k)) :
      Step (.case π (.con D k ts) D bs) (Tm.substTop ts (bs k))
  | caseL {m n : ℕ} {t t' : Tm S m n} (π : Mult m) (D : S.Name)
      (bs : (k : Fin (S.nctors D)) → Tm S m (n + S.nfields D k)) :
      Step t t' → Step (.case π t D bs) (.case π t' D bs)
  /-- `let_π x₁ : A₁ = t₁ … xⱼ : Aⱼ = tⱼ in u ⟶ u[t₁/x₁ … tⱼ/xⱼ]` -/
  | letin {m n : ℕ} (π : Mult m) (j : ℕ) (As : Fin j → Ty S m) (ts : Fin j → Tm S m n)
      (u : Tm S m (n + j)) :
      Step (.letin π j As ts u) (Tm.substTop ts u)

/-- Reflexive-transitive closure of `Step`. -/
abbrev Steps {m n : ℕ} : Tm S m n → Tm S m n → Prop := Relation.ReflTransGen Step

end LinearHaskell
