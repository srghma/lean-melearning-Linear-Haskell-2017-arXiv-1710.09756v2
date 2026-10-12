module

public import Mathlib

/-!
# Multiplicities of `λq→` (Section 3.1 and Definition 3.4)

The paper's multiplicities are the expressions
`π, μ ::= 1 | ω | p | π + μ | π · μ`, quotiented by the equivalence of Definition 3.4.

* `MExpr` is the raw syntax.  Multiplicity variables `p` are represented by de Bruijn
  indices (natural numbers), so that the binder `∀ p. A` and the side condition
  "`p` fresh for `Γ`" of rule (m.abs) can be expressed by shifting.
* `MEquiv` is the equivalence of Definition 3.4.  The paper describes it as "the smallest
  transitive and reflexive relation" obeying the listed laws; we take (as is evidently
  intended, since it is called an *equivalence relation* and is used to quotient
  expressions) the smallest *congruence* (equivalence relation compatible with `+` and `·`)
  containing those laws.
* `Mult` is the quotient.  It is a commutative semiring *without zero*.
* `MZ` is `Mult` with a zero adjoined (`none`).  The zero plays the role of "the variable
  does not occur in the context" when contexts are represented as vectors of
  multiplicities, see `Context.lean`.  `MZ` is a genuine commutative semiring.
-/

@[expose] public section

namespace LinearHaskell

/-- Raw multiplicity expressions: `1 | ω | p | π + μ | π · μ` (Fig. 5). Variables are
de Bruijn indices. -/
inductive MExpr : Type
  | one : MExpr
  | omega : MExpr
  | var : ℕ → MExpr
  | add : MExpr → MExpr → MExpr
  | mul : MExpr → MExpr → MExpr
  deriving DecidableEq, Inhabited

namespace MExpr

/-- The equivalence of multiplicities (Definition 3.4): the smallest congruence such that
`+` and `·` are associative and commutative, `1` is the unit of `·`, `·` distributes over
`+`, `ω · ω = ω`, and `1 + 1 = 1 + ω = ω + ω = ω`. -/
inductive Equiv : MExpr → MExpr → Prop
  | refl (a) : Equiv a a
  | symm {a b} : Equiv a b → Equiv b a
  | trans {a b c} : Equiv a b → Equiv b c → Equiv a c
  | add_congr {a a' b b'} : Equiv a a' → Equiv b b' → Equiv (add a b) (add a' b')
  | mul_congr {a a' b b'} : Equiv a a' → Equiv b b' → Equiv (mul a b) (mul a' b')
  | add_assoc (a b c) : Equiv (add (add a b) c) (add a (add b c))
  | add_comm (a b) : Equiv (add a b) (add b a)
  | mul_assoc (a b c) : Equiv (mul (mul a b) c) (mul a (mul b c))
  | mul_comm (a b) : Equiv (mul a b) (mul b a)
  | one_mul (a) : Equiv (mul one a) a
  | mul_add (a b c) : Equiv (mul a (add b c)) (add (mul a b) (mul a c))
  | omega_mul_omega : Equiv (mul omega omega) omega
  | one_add_one : Equiv (add one one) omega
  | one_add_omega : Equiv (add one omega) omega
  | omega_add_omega : Equiv (add omega omega) omega

instance setoid : Setoid MExpr where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end MExpr

/-- Multiplicities: multiplicity expressions up to the equivalence of Definition 3.4. -/
def Mult : Type := Quotient MExpr.setoid

namespace Mult

/-- The class of a raw expression. -/
def mk (e : MExpr) : Mult := Quotient.mk _ e

instance : One Mult := ⟨mk .one⟩
/-- The unrestricted multiplicity `ω`. -/
def omega : Mult := mk .omega
/-- The multiplicity variable with de Bruijn index `n`. -/
def var (n : ℕ) : Mult := mk (.var n)

@[inherit_doc] scoped notation "ω" => Mult.omega

instance : Inhabited Mult := ⟨1⟩

instance : Add Mult :=
  ⟨Quotient.map₂ MExpr.add (fun _ _ h₁ _ _ h₂ => MExpr.Equiv.add_congr h₁ h₂)⟩

instance : Mul Mult :=
  ⟨Quotient.map₂ MExpr.mul (fun _ _ h₁ _ _ h₂ => MExpr.Equiv.mul_congr h₁ h₂)⟩

theorem mk_add (a b : MExpr) : mk (.add a b) = mk a + mk b := rfl
theorem mk_mul (a b : MExpr) : mk (.mul a b) = mk a * mk b := rfl
theorem mk_one : mk .one = 1 := rfl
theorem mk_omega : mk .omega = ω := rfl

theorem sound {a b : MExpr} (h : MExpr.Equiv a b) : mk a = mk b := Quotient.sound h

@[elab_as_elim]
theorem ind {motive : Mult → Prop} (h : ∀ e, motive (mk e)) (m : Mult) : motive m :=
  Quotient.ind h m

instance : AddCommSemigroup Mult where
  add_assoc := by
    intro a b c
    induction a using ind; induction b using ind; induction c using ind
    exact sound (.add_assoc _ _ _)
  add_comm := by
    intro a b
    induction a using ind; induction b using ind
    exact sound (.add_comm _ _)

instance : CommMonoid Mult where
  mul_assoc := by
    intro a b c
    induction a using ind; induction b using ind; induction c using ind
    exact sound (.mul_assoc _ _ _)
  mul_comm := by
    intro a b
    induction a using ind; induction b using ind
    exact sound (.mul_comm _ _)
  one_mul := by
    intro a
    induction a using ind
    exact sound (.one_mul _)
  mul_one := by
    intro a
    induction a using ind
    exact sound (.trans (.mul_comm _ _) (.one_mul _))

theorem mul_add' (a b c : Mult) : a * (b + c) = a * b + a * c := by
  induction a using ind; induction b using ind; induction c using ind
  exact sound (.mul_add _ _ _)

instance : Distrib Mult where
  left_distrib := mul_add'
  right_distrib a b c := by
    rw [mul_comm, mul_add', mul_comm c a, mul_comm c b]

theorem omega_mul_omega : ω * ω = ω := sound .omega_mul_omega
theorem one_add_one : (1 : Mult) + 1 = ω := sound .one_add_one
theorem one_add_omega : 1 + ω = ω := sound .one_add_omega
theorem omega_add_one : ω + 1 = ω := by rw [add_comm]; exact one_add_omega
theorem omega_add_omega : ω + ω = ω := sound .omega_add_omega

/-! ### Evaluation of expressions and substitution of multiplicity variables -/

/-- Interpret an expression in `Mult`, sending the variable `n` to `σ n`. -/
def evalE (σ : ℕ → Mult) : MExpr → Mult
  | .one => 1
  | .omega => ω
  | .var n => σ n
  | .add a b => evalE σ a + evalE σ b
  | .mul a b => evalE σ a * evalE σ b

theorem evalE_respects (σ : ℕ → Mult) {a b : MExpr} (h : MExpr.Equiv a b) :
    evalE σ a = evalE σ b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add_congr _ _ ih₁ ih₂ => simp only [evalE, ih₁, ih₂]
  | mul_congr _ _ ih₁ ih₂ => simp only [evalE, ih₁, ih₂]
  | add_assoc => exact add_assoc _ _ _
  | add_comm => exact add_comm _ _
  | mul_assoc => exact mul_assoc _ _ _
  | mul_comm => exact mul_comm _ _
  | one_mul => exact one_mul _
  | mul_add => exact mul_add' _ _ _
  | omega_mul_omega => exact omega_mul_omega
  | one_add_one => exact one_add_one
  | one_add_omega => exact one_add_omega
  | omega_add_omega => exact omega_add_omega

/-- Simultaneous substitution of multiplicity variables: `π[σ]` replaces every variable `n`
by `σ n`. This is the operation `π[π₁ … πₙ]` of Section 3.1 (and `A[π/p]` of rule (m.app)). -/
def bind (σ : ℕ → Mult) : Mult → Mult :=
  Quotient.lift (evalE σ) (fun _ _ h => evalE_respects σ h)

@[simp] theorem bind_mk (σ : ℕ → Mult) (e : MExpr) : bind σ (mk e) = evalE σ e := rfl
@[simp] theorem bind_one (σ : ℕ → Mult) : bind σ 1 = 1 := rfl
@[simp] theorem bind_omega (σ : ℕ → Mult) : bind σ ω = ω := rfl
@[simp] theorem bind_var (σ : ℕ → Mult) (n : ℕ) : bind σ (var n) = σ n := rfl
@[simp] theorem bind_add (σ : ℕ → Mult) (a b : Mult) : bind σ (a + b) = bind σ a + bind σ b := by
  induction a using ind; induction b using ind; rfl
@[simp] theorem bind_mul (σ : ℕ → Mult) (a b : Mult) : bind σ (a * b) = bind σ a * bind σ b := by
  induction a using ind; induction b using ind; rfl

theorem evalE_var (e : MExpr) : evalE var e = mk e := by
  induction e with
  | one => rfl
  | omega => rfl
  | var n => rfl
  | add a b iha ihb => simp only [evalE, iha, ihb]; rfl
  | mul a b iha ihb => simp only [evalE, iha, ihb]; rfl

@[simp] theorem bind_var_eq (a : Mult) : bind var a = a := by
  induction a using ind with | h e => exact evalE_var e

theorem evalE_bind (σ τ : ℕ → Mult) (e : MExpr) :
    bind τ (evalE σ e) = evalE (fun n => bind τ (σ n)) e := by
  induction e with
  | one => rfl
  | omega => rfl
  | var n => rfl
  | add a b iha ihb => simp only [evalE, bind_add, iha, ihb]
  | mul a b iha ihb => simp only [evalE, bind_mul, iha, ihb]

theorem bind_bind (σ τ : ℕ → Mult) (a : Mult) :
    bind τ (bind σ a) = bind (fun n => bind τ (σ n)) a := by
  induction a using ind with | h e => exact evalE_bind σ τ e

theorem bind_congr {σ τ : ℕ → Mult} (h : ∀ n, σ n = τ n) (a : Mult) : bind σ a = bind τ a := by
  rw [show σ = τ from funext h]

/-- Shift all multiplicity variables up by one (going under a `∀ p` binder). -/
def shift (a : Mult) : Mult := bind (fun n => var (n + 1)) a

/-- Lifting a substitution under a binder. -/
def up (σ : ℕ → Mult) : ℕ → Mult
  | 0 => var 0
  | n + 1 => shift (σ n)

/-- The substitution `[π/0]` used by rule (m.app): replace variable `0` by `π` and lower
all other variables. -/
def inst (π : Mult) : ℕ → Mult
  | 0 => π
  | n + 1 => var n

theorem bind_up_shift (σ : ℕ → Mult) (a : Mult) : bind (up σ) (shift a) = shift (bind σ a) := by
  unfold shift
  rw [bind_bind, bind_bind]
  rfl

theorem bind_inst_shift (π a : Mult) : bind (inst π) (shift a) = a := by
  unfold shift
  rw [bind_bind]
  exact bind_var_eq a

theorem up_bind (σ τ : ℕ → Mult) (n : ℕ) :
    bind (up τ) (up σ n) = up (fun m => bind τ (σ m)) n := by
  cases n with
  | zero => rfl
  | succ n => exact bind_up_shift τ (σ n)

theorem inst_bind (σ : ℕ → Mult) (π : Mult) (n : ℕ) :
    bind (inst (bind σ π)) (up σ n) = bind σ (inst π n) := by
  cases n with
  | zero => rfl
  | succ n => exact bind_inst_shift _ _

/-! ### Consistency: a two-element model

Interpreting `1 ↦ false`, `ω ↦ true`, `+ ↦ (fun _ _ => true)` and `· ↦ (· || ·)` gives a model
of Definition 3.4 (the "linear / unrestricted" model `{1, ω}`). It shows that the
equivalence is not trivial. -/

/-- Interpretation of expressions in the model `{1 ↦ false, ω ↦ true}`. -/
def evalBool (v : ℕ → Bool) : MExpr → Bool
  | .one => false
  | .omega => true
  | .var n => v n
  | .add _ _ => true
  | .mul a b => evalBool v a || evalBool v b

theorem evalBool_respects (v : ℕ → Bool) {a b : MExpr} (h : MExpr.Equiv a b) :
    evalBool v a = evalBool v b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add_congr => rfl
  | mul_congr _ _ ih₁ ih₂ => simp only [evalBool, ih₁, ih₂]
  | add_assoc => rfl
  | add_comm => rfl
  | mul_assoc => simp only [evalBool, Bool.or_assoc]
  | mul_comm => simp only [evalBool, Bool.or_comm]
  | one_mul => simp [evalBool]
  | mul_add => simp [evalBool]
  | omega_mul_omega => rfl
  | one_add_one => rfl
  | one_add_omega => rfl
  | omega_add_omega => rfl

/-- The model, as a function on `Mult`. -/
def toBool (v : ℕ → Bool) : Mult → Bool :=
  Quotient.lift (evalBool v) (fun _ _ h => evalBool_respects v h)

@[simp] theorem toBool_one (v : ℕ → Bool) : toBool v 1 = false := rfl
@[simp] theorem toBool_omega (v : ℕ → Bool) : toBool v ω = true := rfl
@[simp] theorem toBool_var (v : ℕ → Bool) (n : ℕ) : toBool v (var n) = v n := rfl
@[simp] theorem toBool_add (v : ℕ → Bool) (a b : Mult) : toBool v (a + b) = true := by
  induction a using ind; induction b using ind; rfl
@[simp] theorem toBool_mul (v : ℕ → Bool) (a b : Mult) :
    toBool v (a * b) = (toBool v a || toBool v b) := by
  induction a using ind; induction b using ind; rfl

/-- The multiplicities `1` and `ω` are distinct. -/
theorem one_ne_omega : (1 : Mult) ≠ ω := fun h => by
  simpa using congrArg (toBool fun _ => false) h

/-- A sum of multiplicities is never `1`: in particular a variable used twice cannot be
linear. -/
theorem add_ne_one (a b : Mult) : a + b ≠ 1 := fun h => by
  simpa using congrArg (toBool fun _ => false) h

/-- A multiplicity variable is not equivalent to `1`. -/
theorem var_ne_one (n : ℕ) : var n ≠ 1 := fun h => by
  simpa using congrArg (toBool fun _ => true) h

/-- A multiplicity variable is not equivalent to `ω`. -/
theorem var_ne_omega (n : ℕ) : var n ≠ ω := fun h => by
  simpa using congrArg (toBool fun _ => false) h

/-- A multiplicity variable is not equivalent to any sum. -/
theorem add_ne_var (a b : Mult) (n : ℕ) : a + b ≠ var n := fun h => by
  simpa using congrArg (toBool fun _ => false) h

end Mult

/-! ### Multiplicities with a zero -/

/-- Multiplicities extended with a zero `none`, standing for "does not occur". -/
def MZ : Type := Option Mult

namespace MZ

/-- Embedding of a (nonzero) multiplicity. -/
def of (a : Mult) : MZ := some a

instance : Coe Mult MZ := ⟨of⟩

instance : Zero MZ := ⟨(none : Option Mult)⟩
instance : One MZ := ⟨of 1⟩

instance : Add MZ where
  add a b := match a, b with
    | none, b => b
    | some a, none => some a
    | some a, some b => some (a + b)

instance : Mul MZ where
  mul a b := match a, b with
    | some a, some b => some (a * b)
    | _, _ => none

@[elab_as_elim]
theorem cases' {motive : MZ → Prop} (h0 : motive 0) (h : ∀ a : Mult, motive (of a)) (x : MZ) :
    motive x := by
  rcases x with _ | a
  · exact h0
  · exact h a

@[simp] theorem zero_add' (a : MZ) : 0 + a = a := rfl
@[simp] theorem add_zero' (a : MZ) : a + 0 = a := by induction a using cases' <;> rfl
@[simp] theorem of_add_of (a b : Mult) : (of a : MZ) + of b = of (a + b) := rfl
@[simp] theorem zero_mul' (a : MZ) : 0 * a = 0 := rfl
@[simp] theorem mul_zero' (a : MZ) : a * 0 = 0 := by induction a using cases' <;> rfl
@[simp] theorem of_mul_of (a b : Mult) : (of a : MZ) * of b = of (a * b) := rfl
@[simp] theorem of_ne_zero (a : Mult) : (of a : MZ) ≠ 0 := Option.some_ne_none a
theorem of_injective : Function.Injective of := Option.some_injective _
theorem one_def : (1 : MZ) = of 1 := rfl

instance : CommSemiring MZ where
  add_assoc a b c := by
    induction a using cases' <;> induction b using cases' <;> induction c using cases' <;>
      simp [add_assoc]
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm a b := by
    induction a using cases' <;> induction b using cases' <;> simp [add_comm]
  mul_assoc a b c := by
    induction a using cases' <;> induction b using cases' <;> induction c using cases' <;>
      simp [mul_assoc]
  one_mul a := by induction a using cases' <;> simp [one_def]
  mul_one a := by induction a using cases' <;> simp [one_def]
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  left_distrib a b c := by
    induction a using cases' <;> induction b using cases' <;> induction c using cases' <;>
      simp [mul_add]
  right_distrib a b c := by
    induction a using cases' <;> induction b using cases' <;> induction c using cases' <;>
      simp [add_mul]
  mul_comm a b := by
    induction a using cases' <;> induction b using cases' <;> simp [mul_comm]
  nsmul := nsmulRec
  natCast := Nat.unaryCast
  natCast_zero := rfl
  natCast_succ _ := rfl

theorem of_add (a b : Mult) : (of (a + b) : MZ) = of a + of b := rfl
theorem of_mul (a b : Mult) : (of (a * b) : MZ) = of a * of b := rfl
@[simp] theorem of_one : (of 1 : MZ) = 1 := rfl

/-- `MZ` has no zero divisors. -/
theorem mul_eq_zero_iff (a b : MZ) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  induction a using cases' <;> induction b using cases' <;> simp

/-- `MZ` is zero-sum free. -/
theorem add_eq_zero_iff (a b : MZ) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  induction a using cases' <;> induction b using cases' <;> simp

theorem add_one_ne_zero (a : MZ) : a + 1 ≠ 0 := by
  rw [Ne, add_eq_zero_iff, one_def]; exact fun h => of_ne_zero _ h.2

/-- Substitution of multiplicity variables, extended to `MZ` (it fixes `0`). -/
def bind (σ : ℕ → Mult) : MZ → MZ
  | none => none
  | some a => some (Mult.bind σ a)

/-- `MZ.bind σ` is a ring homomorphism. -/
def bindHom (σ : ℕ → Mult) : MZ →+* MZ where
  toFun := bind σ
  map_one' := rfl
  map_mul' a b := by
    induction a using cases' <;> induction b using cases' <;> simp [bind, of] <;> rfl
  map_zero' := rfl
  map_add' a b := by
    induction a using cases' <;> induction b using cases' <;> simp [bind, of] <;> rfl

@[simp] theorem bindHom_apply (σ : ℕ → Mult) (a : MZ) : bindHom σ a = bind σ a := rfl
@[simp] theorem bind_of (σ : ℕ → Mult) (a : Mult) : bind σ (of a) = of (Mult.bind σ a) := rfl
@[simp] theorem bind_zero (σ : ℕ → Mult) : bind σ 0 = 0 := rfl
@[simp] theorem bind_one (σ : ℕ → Mult) : bind σ 1 = 1 := rfl
@[simp] theorem bind_add (σ : ℕ → Mult) (a b : MZ) : bind σ (a + b) = bind σ a + bind σ b :=
  (bindHom σ).map_add a b
@[simp] theorem bind_mul (σ : ℕ → Mult) (a b : MZ) : bind σ (a * b) = bind σ a * bind σ b :=
  (bindHom σ).map_mul a b

theorem bind_bind (σ τ : ℕ → Mult) (a : MZ) :
    bind τ (bind σ a) = bind (fun n => Mult.bind τ (σ n)) a := by
  induction a using cases' with
  | h0 => rfl
  | h a => simp [Mult.bind_bind]

@[simp] theorem bind_var_eq (a : MZ) : bind Mult.var a = a := by
  induction a using cases' with
  | h0 => rfl
  | h a => simp

/-- The unrestricted multiplicity in `MZ`. -/
def omega : MZ := of Mult.omega

@[simp] theorem bind_omega (σ : ℕ → Mult) : bind σ omega = omega := rfl

end MZ

end LinearHaskell
