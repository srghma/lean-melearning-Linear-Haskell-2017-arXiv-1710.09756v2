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
-/

@[expose] public section

namespace LinearHaskell

/-- Values (weak head normal forms). -/
inductive Value : Tm → Prop
  | lam (π : Mult) (A : Ty) (t : Tm) : Value (.lam π A t)
  | mlam (t : Tm) : Value (.mlam t)
  | con (D k : ℕ) (ts : List Tm) : Value (.con D k ts)

/-- One step of call-by-name reduction. -/
inductive Step : Tm → Tm → Prop
  /-- `(λ_π (x:A). t) u ⟶ t[u/x]` -/
  | beta (π : Mult) (A : Ty) (t u : Tm) : Step (.app (.lam π A t) u) (Tm.substAt 0 u t)
  | appL {t t' : Tm} (u : Tm) : Step t t' → Step (.app t u) (.app t' u)
  /-- `(λ p. t) π ⟶ t[π/p]` -/
  | mbeta (t : Tm) (π : Mult) : Step (.mapp (.mlam t) π) (t.mbind (Mult.inst π))
  | mappL {t t' : Tm} (π : Mult) : Step t t' → Step (.mapp t π) (.mapp t' π)
  /-- `case_π (c_k t₁ … tₙ) of {…; c_k x₁ … xₙ → u_k; …} ⟶ u_k[t₁/x₁ … tₙ/xₙ]` -/
  | caseCon (π : Mult) (D k : ℕ) (ts : List Tm) (bs : List (ℕ × Tm)) :
      k < bs.length →
      Step (.case π (.con D k ts) bs) (Tm.substList ts (bs.getD k default).2)
  | caseL {t t' : Tm} (π : Mult) (bs : List (ℕ × Tm)) :
      Step t t' → Step (.case π t bs) (.case π t' bs)
  /-- `let_π x₁ : A₁ = t₁ … xₙ : Aₙ = tₙ in u ⟶ u[t₁/x₁ … tₙ/xₙ]` -/
  | letin (π : Mult) (bs : List (Ty × Tm)) (u : Tm) :
      Step (.letin π bs u) (Tm.substList (bs.map Prod.snd) u)

/-- Reflexive-transitive closure of `Step`. -/
abbrev Steps : Tm → Tm → Prop := Relation.ReflTransGen Step

end LinearHaskell
