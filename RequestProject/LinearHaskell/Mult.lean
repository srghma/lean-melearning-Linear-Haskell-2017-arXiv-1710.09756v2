module

public import Mathlib

/-!
# Multiplicities of `λq→` (Section 3.1 and Definition 3.4)

The paper's multiplicities are the expressions
`π, μ ::= 1 | ω | p | π + μ | π · μ`, quotiented by the equivalence of Definition 3.4.

All syntax in this development is *well scoped by construction*: the type of an object
records how many variables may occur free in it.

* `MExpr m` is the raw syntax of multiplicities with at most `m` free multiplicity
  variables, `var : Fin m → MExpr m`. Variables are de Bruijn *levels*: in a scope of size
  `m`, the binder `∀ p` introduces the variable `Fin.last m`, and the older variables keep
  their numbers (`Fin.castSucc`). In particular `MExpr 0` contains only closed expressions.
* `MExpr.Equiv` is the equivalence of Definition 3.4. The paper describes it as "the
  smallest transitive and reflexive relation" obeying the listed laws; we take (as is
  evidently intended, since it is called an *equivalence relation* and is used to quotient
  expressions) the smallest *congruence* containing those laws.
* `Mult m` is the quotient. It is a commutative semiring *without zero*.
* `MZ m` is `Mult m` with a zero adjoined (`none`). The zero plays the role of "the variable
  does not occur in the context" when contexts are represented as vectors of
  multiplicities, see `Context.lean`. `MZ m` is a genuine commutative semiring.
-/

@[expose] public section

namespace LinearHaskell

/-- Raw multiplicity expressions `1 | ω | p | π + μ | π · μ` (Fig. 5) with at most `m` free
multiplicity variables. -/
inductive MExpr (m : ℕ) : Type
  | one : MExpr m
  | omega : MExpr m
  | var : Fin m → MExpr m
  | add : MExpr m → MExpr m → MExpr m
  | mul : MExpr m → MExpr m → MExpr m
  deriving DecidableEq, Inhabited

namespace MExpr

variable {m : ℕ}

/-- The equivalence of multiplicities (Definition 3.4): the smallest congruence such that
`+` and `·` are associative and commutative, `1` is the unit of `·`, `·` distributes over
`+`, `ω · ω = ω`, and `1 + 1 = 1 + ω = ω + ω = ω`. -/
inductive Equiv : MExpr m → MExpr m → Prop
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

instance setoid (m : ℕ) : Setoid (MExpr m) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end MExpr

/-- Multiplicities with at most `m` free multiplicity variables: multiplicity expressions
up to the equivalence of Definition 3.4. -/
def Mult (m : ℕ) : Type := Quotient (MExpr.setoid m)

namespace Mult

variable {m m' m'' : ℕ}

/-- The class of a raw expression. -/
def mk (e : MExpr m) : Mult m := Quotient.mk _ e

instance : One (Mult m) := ⟨mk .one⟩
/-- The unrestricted multiplicity `ω`. -/
def omega : Mult m := mk .omega
/-- The multiplicity variable `i`. -/
def var (i : Fin m) : Mult m := mk (.var i)

@[inherit_doc] scoped notation "ω" => Mult.omega

instance : Inhabited (Mult m) := ⟨1⟩

instance : Add (Mult m) :=
  ⟨Quotient.map₂ MExpr.add (fun _ _ h₁ _ _ h₂ => MExpr.Equiv.add_congr h₁ h₂)⟩

instance : Mul (Mult m) :=
  ⟨Quotient.map₂ MExpr.mul (fun _ _ h₁ _ _ h₂ => MExpr.Equiv.mul_congr h₁ h₂)⟩

theorem mk_add (a b : MExpr m) : mk (.add a b) = mk a + mk b := rfl
theorem mk_mul (a b : MExpr m) : mk (.mul a b) = mk a * mk b := rfl
theorem mk_one : mk .one = (1 : Mult m) := rfl
theorem mk_omega : mk .omega = (ω : Mult m) := rfl

theorem sound {a b : MExpr m} (h : MExpr.Equiv a b) : mk a = mk b := Quotient.sound h

@[elab_as_elim]
theorem ind {motive : Mult m → Prop} (h : ∀ e, motive (mk e)) (a : Mult m) : motive a :=
  Quotient.ind h a

instance : AddCommSemigroup (Mult m) where
  add_assoc := by
    intro a b c
    induction a using ind; induction b using ind; induction c using ind
    exact sound (.add_assoc _ _ _)
  add_comm := by
    intro a b
    induction a using ind; induction b using ind
    exact sound (.add_comm _ _)

instance : CommMonoid (Mult m) where
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

theorem mul_add' (a b c : Mult m) : a * (b + c) = a * b + a * c := by
  induction a using ind; induction b using ind; induction c using ind
  exact sound (.mul_add _ _ _)

instance : Distrib (Mult m) where
  left_distrib := mul_add'
  right_distrib a b c := by
    rw [mul_comm, mul_add', mul_comm c a, mul_comm c b]

theorem omega_mul_omega : (ω : Mult m) * ω = ω := sound .omega_mul_omega
theorem one_add_one : (1 : Mult m) + 1 = ω := sound .one_add_one
theorem one_add_omega : (1 : Mult m) + ω = ω := sound .one_add_omega
theorem omega_add_one : (ω : Mult m) + 1 = ω := by rw [add_comm]; exact one_add_omega
theorem omega_add_omega : (ω : Mult m) + ω = ω := sound .omega_add_omega

/-! ### Evaluation of expressions and substitution of multiplicity variables -/

/-- Interpret an expression, sending the variable `i` to `σ i`. -/
def evalE (σ : Fin m → Mult m') : MExpr m → Mult m'
  | .one => 1
  | .omega => ω
  | .var i => σ i
  | .add a b => evalE σ a + evalE σ b
  | .mul a b => evalE σ a * evalE σ b

theorem evalE_respects (σ : Fin m → Mult m') {a b : MExpr m} (h : MExpr.Equiv a b) :
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

/-- Simultaneous substitution of multiplicity variables: `π[σ]` replaces every variable `i`
by `σ i`. This is the operation `π[π₁ … πₙ]` of Section 3.1 (and `A[π/p]` of rule (m.app)).
The scopes make sure that every variable of `π` is substituted. -/
def bind (σ : Fin m → Mult m') : Mult m → Mult m' :=
  Quotient.lift (evalE σ) (fun _ _ h => evalE_respects σ h)

@[simp] theorem bind_mk (σ : Fin m → Mult m') (e : MExpr m) : bind σ (mk e) = evalE σ e := rfl
@[simp] theorem bind_one (σ : Fin m → Mult m') : bind σ 1 = 1 := rfl
@[simp] theorem bind_omega (σ : Fin m → Mult m') : bind σ ω = ω := rfl
@[simp] theorem bind_var (σ : Fin m → Mult m') (i : Fin m) : bind σ (var i) = σ i := rfl
@[simp] theorem bind_add (σ : Fin m → Mult m') (a b : Mult m) :
    bind σ (a + b) = bind σ a + bind σ b := by
  induction a using ind; induction b using ind; rfl
@[simp] theorem bind_mul (σ : Fin m → Mult m') (a b : Mult m) :
    bind σ (a * b) = bind σ a * bind σ b := by
  induction a using ind; induction b using ind; rfl

theorem evalE_var (e : MExpr m) : evalE var e = mk e := by
  induction e with
  | one => rfl
  | omega => rfl
  | var n => rfl
  | add a b iha ihb => simp only [evalE, iha, ihb]; rfl
  | mul a b iha ihb => simp only [evalE, iha, ihb]; rfl

@[simp] theorem bind_var_eq (a : Mult m) : bind var a = a := by
  induction a using ind with | h e => exact evalE_var e

theorem evalE_bind (σ : Fin m → Mult m') (τ : Fin m' → Mult m'') (e : MExpr m) :
    bind τ (evalE σ e) = evalE (fun i => bind τ (σ i)) e := by
  induction e with
  | one => rfl
  | omega => rfl
  | var n => rfl
  | add a b iha ihb => simp only [evalE, bind_add, iha, ihb]
  | mul a b iha ihb => simp only [evalE, bind_mul, iha, ihb]

theorem bind_bind (σ : Fin m → Mult m') (τ : Fin m' → Mult m'') (a : Mult m) :
    bind τ (bind σ a) = bind (fun i => bind τ (σ i)) a := by
  induction a using ind with | h e => exact evalE_bind σ τ e

theorem bind_congr {σ τ : Fin m → Mult m'} (h : ∀ i, σ i = τ i) (a : Mult m) :
    bind σ a = bind τ a := by
  rw [show σ = τ from funext h]

/-- Weakening: view a multiplicity in a scope with one more variable (going under a
`∀ p` binder). -/
def shift (a : Mult m) : Mult (m + 1) := bind (fun i => var i.castSucc) a

/-- Lifting a substitution under a binder: the new variable is sent to the new variable. -/
def up (σ : Fin m → Mult m') : Fin (m + 1) → Mult (m' + 1) :=
  Fin.lastCases (var (Fin.last m')) (fun i => shift (σ i))

/-- The substitution `[π/p]` used by rule (m.app), where `p` is the last variable. -/
def inst (π : Mult m) : Fin (m + 1) → Mult m :=
  Fin.lastCases π var

@[simp] theorem up_last (σ : Fin m → Mult m') : up σ (Fin.last m) = var (Fin.last m') := by
  simp [up]
@[simp] theorem up_castSucc (σ : Fin m → Mult m') (i : Fin m) :
    up σ i.castSucc = shift (σ i) := by
  simp [up]
@[simp] theorem inst_last (π : Mult m) : inst π (Fin.last m) = π := by simp [inst]
@[simp] theorem inst_castSucc (π : Mult m) (i : Fin m) : inst π i.castSucc = var i := by
  simp [inst]

theorem bind_up_shift (σ : Fin m → Mult m') (a : Mult m) :
    bind (up σ) (shift a) = shift (bind σ a) := by
  unfold shift
  rw [bind_bind, bind_bind]
  simp [shift]

theorem bind_inst_shift (π a : Mult m) : bind (inst π) (shift a) = a := by
  unfold shift
  rw [bind_bind]
  simp

theorem up_bind (σ : Fin m → Mult m') (τ : Fin m' → Mult m'') (i : Fin (m + 1)) :
    bind (up τ) (up σ i) = up (fun j => bind τ (σ j)) i := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [bind_up_shift]

theorem inst_bind (σ : Fin m → Mult m') (π : Mult m) (i : Fin (m + 1)) :
    bind (inst (bind σ π)) (up σ i) = bind σ (inst π i) := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [bind_inst_shift]

/-! ### Consistency: a two-element model

Interpreting `1 ↦ false`, `ω ↦ true`, `+ ↦ (fun _ _ => true)` and `· ↦ (· || ·)` gives a model
of Definition 3.4 (the "linear / unrestricted" model `{1, ω}`). It shows that the
equivalence is not trivial. -/

/-- Interpretation of expressions in the model `{1 ↦ false, ω ↦ true}`. -/
def evalBool (v : Fin m → Bool) : MExpr m → Bool
  | .one => false
  | .omega => true
  | .var n => v n
  | .add _ _ => true
  | .mul a b => evalBool v a || evalBool v b

theorem evalBool_respects (v : Fin m → Bool) {a b : MExpr m} (h : MExpr.Equiv a b) :
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

/-- The model, as a function on `Mult m`. -/
def toBool (v : Fin m → Bool) : Mult m → Bool :=
  Quotient.lift (evalBool v) (fun _ _ h => evalBool_respects v h)

@[simp] theorem toBool_one (v : Fin m → Bool) : toBool v 1 = false := rfl
@[simp] theorem toBool_omega (v : Fin m → Bool) : toBool v ω = true := rfl
@[simp] theorem toBool_var (v : Fin m → Bool) (n : Fin m) : toBool v (var n) = v n := rfl
@[simp] theorem toBool_add (v : Fin m → Bool) (a b : Mult m) : toBool v (a + b) = true := by
  induction a using ind; induction b using ind; rfl
@[simp] theorem toBool_mul (v : Fin m → Bool) (a b : Mult m) :
    toBool v (a * b) = (toBool v a || toBool v b) := by
  induction a using ind; induction b using ind; rfl

/-- The multiplicities `1` and `ω` are distinct. -/
theorem one_ne_omega : (1 : Mult m) ≠ ω := fun h => by
  simpa using congrArg (toBool fun _ => false) h

/-- A sum of multiplicities is never `1`: in particular a variable used twice cannot be
linear. -/
theorem add_ne_one (a b : Mult m) : a + b ≠ 1 := fun h => by
  simpa using congrArg (toBool fun _ => false) h

/-- A multiplicity variable is not equivalent to `1`. -/
theorem var_ne_one (n : Fin m) : var n ≠ 1 := fun h => by
  simpa using congrArg (toBool fun _ => true) h

/-- A multiplicity variable is not equivalent to `ω`. -/
theorem var_ne_omega (n : Fin m) : var n ≠ ω := fun h => by
  simpa using congrArg (toBool fun _ => false) h

/-- A multiplicity variable is not equivalent to any sum. -/
theorem add_ne_var (a b : Mult m) (n : Fin m) : a + b ≠ var n := fun h => by
  simpa using congrArg (toBool fun _ => false) h

end Mult

/-! ### Multiplicities with a zero -/

/-- Multiplicities extended with a zero `none`, standing for "does not occur". -/
def MZ (m : ℕ) : Type := Option (Mult m)

namespace MZ

variable {m m' m'' : ℕ}

/-- Embedding of a (nonzero) multiplicity. -/
def of (a : Mult m) : MZ m := some a

instance : Coe (Mult m) (MZ m) := ⟨of⟩

instance : Zero (MZ m) := ⟨(none : Option (Mult m))⟩
instance : One (MZ m) := ⟨of 1⟩

instance : Add (MZ m) where
  add a b := match a, b with
    | none, b => b
    | some a, none => some a
    | some a, some b => some (a + b)

instance : Mul (MZ m) where
  mul a b := match a, b with
    | some a, some b => some (a * b)
    | _, _ => none

@[elab_as_elim]
theorem cases' {motive : MZ m → Prop} (h0 : motive 0) (h : ∀ a : Mult m, motive (of a))
    (x : MZ m) : motive x := by
  rcases x with _ | a
  · exact h0
  · exact h a

@[simp] theorem zero_add' (a : MZ m) : 0 + a = a := rfl
@[simp] theorem add_zero' (a : MZ m) : a + 0 = a := by induction a using cases' <;> rfl
@[simp] theorem of_add_of (a b : Mult m) : (of a : MZ m) + of b = of (a + b) := rfl
@[simp] theorem zero_mul' (a : MZ m) : 0 * a = 0 := rfl
@[simp] theorem mul_zero' (a : MZ m) : a * 0 = 0 := by induction a using cases' <;> rfl
@[simp] theorem of_mul_of (a b : Mult m) : (of a : MZ m) * of b = of (a * b) := rfl
@[simp] theorem of_ne_zero (a : Mult m) : (of a : MZ m) ≠ 0 := Option.some_ne_none a
theorem of_injective : Function.Injective (of : Mult m → MZ m) := Option.some_injective _
theorem one_def : (1 : MZ m) = of 1 := rfl

instance : CommSemiring (MZ m) where
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

theorem of_add (a b : Mult m) : (of (a + b) : MZ m) = of a + of b := rfl
theorem of_mul (a b : Mult m) : (of (a * b) : MZ m) = of a * of b := rfl
@[simp] theorem of_one : (of 1 : MZ m) = 1 := rfl

/-- `MZ m` has no zero divisors. -/
theorem mul_eq_zero_iff (a b : MZ m) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  induction a using cases' <;> induction b using cases' <;> simp

/-- `MZ m` is zero-sum free. -/
theorem add_eq_zero_iff (a b : MZ m) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  induction a using cases' <;> induction b using cases' <;> simp

theorem add_one_ne_zero (a : MZ m) : a + 1 ≠ 0 := by
  rw [Ne, add_eq_zero_iff, one_def]; exact fun h => of_ne_zero _ h.2

/-- Substitution of multiplicity variables, extended to `MZ` (it fixes `0`). -/
def bind (σ : Fin m → Mult m') : MZ m → MZ m'
  | none => none
  | some a => some (Mult.bind σ a)

/-- `MZ.bind σ` is a ring homomorphism. -/
def bindHom (σ : Fin m → Mult m') : MZ m →+* MZ m' where
  toFun := bind σ
  map_one' := rfl
  map_mul' a b := by
    induction a using cases' <;> induction b using cases' <;> simp [bind, of] <;> rfl
  map_zero' := rfl
  map_add' a b := by
    induction a using cases' <;> induction b using cases' <;> simp [bind, of] <;> rfl

@[simp] theorem bindHom_apply (σ : Fin m → Mult m') (a : MZ m) : bindHom σ a = bind σ a := rfl
@[simp] theorem bind_of (σ : Fin m → Mult m') (a : Mult m) :
    bind σ (of a) = of (Mult.bind σ a) := rfl
@[simp] theorem bind_zero (σ : Fin m → Mult m') : bind σ 0 = 0 := rfl
@[simp] theorem bind_one (σ : Fin m → Mult m') : bind σ 1 = 1 := rfl
@[simp] theorem bind_add (σ : Fin m → Mult m') (a b : MZ m) :
    bind σ (a + b) = bind σ a + bind σ b :=
  (bindHom σ).map_add a b
@[simp] theorem bind_mul (σ : Fin m → Mult m') (a b : MZ m) :
    bind σ (a * b) = bind σ a * bind σ b :=
  (bindHom σ).map_mul a b

theorem bind_sum (σ : Fin m → Mult m') {ι : Type*} (s : Finset ι) (f : ι → MZ m) :
    bind σ (∑ i ∈ s, f i) = ∑ i ∈ s, bind σ (f i) :=
  map_sum (bindHom σ) f s

theorem bind_bind (σ : Fin m → Mult m') (τ : Fin m' → Mult m'') (a : MZ m) :
    bind τ (bind σ a) = bind (fun i => Mult.bind τ (σ i)) a := by
  induction a using cases' with
  | h0 => rfl
  | h a => simp [Mult.bind_bind]

@[simp] theorem bind_var_eq (a : MZ m) : bind Mult.var a = a := by
  induction a using cases' with
  | h0 => rfl
  | h a => simp

/-- Weakening of an `MZ` (going under a `∀ p` binder). -/
def shift (a : MZ m) : MZ (m + 1) := bind (fun i => Mult.var i.castSucc) a

/-- The unrestricted multiplicity in `MZ`. -/
def omega : MZ m := of Mult.omega

@[simp] theorem bind_omega (σ : Fin m → Mult m') : bind σ omega = omega := rfl

end MZ

end LinearHaskell
