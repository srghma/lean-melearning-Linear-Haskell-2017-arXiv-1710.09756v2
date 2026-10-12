module

public import RequestProject.LinearHaskell.Safety

/-!
# Examples from Sections 2 and 3

We fix a small signature with the following datatypes (no multiplicity parameters):

* `Pair`: `data Pair where Pair : Int ⊸ Int ⊸ Pair` (both fields linear, as for
  every Haskell-98 datatype, Section 2.4);
* `Int`: an abstract base type (no constructors);
* `Bool`: `data Bool where False : Bool; True : Bool`;
* `Ur`: `data Ur where Ur : Int → Ur` (an unrestricted field, Section 2.5);
* `UrPair`: `data UrPair where UrPair : Pair → UrPair`;
* `PairUr`: `data PairUr where PairUr : Ur ⊸ Ur ⊸ PairUr`.

and check the claims of the paper about them:

* `swap : Pair ⊸ Pair` is well typed using `case₁` (Section 3.3, also `f2` of Section 2.4);
* `f1 = λ x. case x of (a, b) → (a, a)` does not have a linear type, whatever the
  multiplicity of its `case` (Section 2.4);
* using `case_ω`, `UrPair ⊸ PairUr` (i.e. `Unrestricted (a, b) ⊸ (Unrestricted a,
  Unrestricted b)`) is inhabited (Section 3.5, "Case rule");
* `fst : Pair → Int` is well typed using `case_ω` (Section 3.3);
* composition has the multiplicity-polymorphic type
  `∀ p q. (b →_p c) ⊸ (a →_q b) →_p a →_{p·q} c` (Section 2.6);
* with `case₁` the second (linear) component cannot be discarded: no `case₁ … → a` is well
  typed, whatever the context (Section 3.3);
* a linear variable cannot be used twice: `x :_1 Int ⊬ Pair x x` (Section 2.4, `f1`);
* the judgements `x :_ω A ⊢ x : A` and `x :_1 A, y :_ω B ⊢ x : A` hold (Section 3.2);
* `x :_p A ⊢ x : A` does not hold for a multiplicity variable `p`, hence
  `λ p. λ_p (x : A). x` does not have type `∀ p. A →_p A` (Section 3.5).

Since variables are de Bruijn levels, in a closed term the variable bound by the outermost
binder is `0`, the next one `1`, and so on.
-/

@[expose] public section

namespace LinearHaskell

open Mult

/-- The datatypes of the example signature. -/
inductive ExData : Type
  | pair | int | bool | ur | urPair | pairUr

/-- Names and arities (all `0`) of the example datatypes. -/
def exData : DataSig := ⟨ExData, fun _ => 0⟩

/-- The type `Int`. -/
def IntT {m : ℕ} : Ty exData m := .data ExData.int Fin.elim0
/-- The type `Pair`. -/
def PairT {m : ℕ} : Ty exData m := .data ExData.pair Fin.elim0
/-- The type `Ur`. -/
def UrT {m : ℕ} : Ty exData m := .data ExData.ur Fin.elim0
/-- The type `UrPair`. -/
def UrPairT {m : ℕ} : Ty exData m := .data ExData.urPair Fin.elim0
/-- The type `PairUr`. -/
def PairUrT {m : ℕ} : Ty exData m := .data ExData.pairUr Fin.elim0

/-- Number of constructors. -/
@[simp] def exNctors : ExData → ℕ
  | .pair => 1 | .int => 0 | .bool => 2 | .ur => 1 | .urPair => 1 | .pairUr => 1

/-- Number of fields of each constructor. -/
@[simp] def exNfields : (D : ExData) → Fin (exNctors D) → ℕ
  | .pair, _ => 2 | .int, _ => 0 | .bool, _ => 0 | .ur, _ => 1 | .urPair, _ => 1
  | .pairUr, _ => 2

/-- Multiplicities of the fields. -/
def exFieldMult : (D : ExData) → (k : Fin (exNctors D)) → Fin (exNfields D k) → Mult 0
  | .ur, _, _ => ω
  | .urPair, _, _ => ω
  | _, _, _ => 1

/-- Types of the fields. -/
def exFieldTy : (D : ExData) → (k : Fin (exNctors D)) → Fin (exNfields D k) → Ty exData 0
  | .urPair, _, _ => PairT
  | .pairUr, _, _ => UrT
  | _, _, _ => IntT

/-- The example signature. -/
abbrev exSig : Sig where
  toDataSig := exData
  nctors := exNctors
  nfields := exNfields
  fieldMult := exFieldMult
  fieldTy := exFieldTy

/-- A term variable given by a numeral. -/
abbrev v {S : Sig} {m n : ℕ} (i : ℕ) (h : i < n := by simp [exSig, exNfields]) : Tm S m n :=
  .var ⟨i, h⟩

/-- A constructor of the example signature given by a numeral. -/
abbrev ck {D : ExData} (k : ℕ) (h : k < exSig.nctors D := by decide) : Fin (exSig.nctors D) :=
  ⟨k, h⟩

/-- `swap = λ₁ (x : Pair). case₁ x of { Pair a b → Pair b a }`. -/
def swapTm : Tm exSig 0 0 :=
  .lam 1 PairT (.case 1 (v 0) ExData.pair (fun _ => .con ExData.pair (ck 0) ![v 2, v 1]))

/-- `fst = λ_ω (x : Pair). case_ω x of { Pair a b → a }`. -/
def fstTm : Tm exSig 0 0 :=
  .lam ω PairT (.case ω (v 0) ExData.pair (fun _ => v 1))

@[simp] theorem exSig_fieldTyAt_pair {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldTyAt ExData.pair k ps i = IntT := by
  simp only [Sig.fieldTyAt, exSig, exFieldTy, IntT, Ty.bind]
  congr 1; funext i; exact i.elim0

@[simp] theorem exSig_fieldMultAt_pair {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldMultAt ExData.pair k ps i = 1 := by
  simp [Sig.fieldMultAt, exSig, exFieldMult]

theorem typed_var_single {S : Sig} {m n : ℕ} {E : TyEnv S m n} (x : Fin n) {A : Ty S m}
    (hA : E x = A) : Typed S E (Pi.single x 1) (.var x) A :=
  ((Typed.var 0 x).ofEq (by simp)).ofEqTy hA

/-- `swap : Pair ⊸ Pair`. -/
theorem swap_typed : Typed exSig ![] 0 swapTm (.arr 1 PairT PairT) := by
  refine Typed.abs ?_
  refine (Typed.case (Γ := Pi.single 0 1) (Δ := 0) (ps := Fin.elim0)
    (typed_var_single _ rfl) (fun k => ?_)).ofEq ?_
  · refine (Typed.con (D := ExData.pair) (k := ck 0) 0 Fin.elim0 ![(Pi.single 2 1 : Usage 0 3), Pi.single 1 1] ?_).ofEq ?_
    · intro i
      fin_cases i
      · exact typed_var_single _ rfl
      · exact typed_var_single _ rfl
    · funext j
      fin_cases j <;> simp <;> rfl
  · funext j
    fin_cases j
    simp
    rfl

@[simp] theorem exSig_fieldTyAt_ur {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldTyAt ExData.ur k ps i = IntT := by
  simp only [Sig.fieldTyAt, exSig, exFieldTy, IntT, Ty.bind]
  congr 1; funext i; exact i.elim0

@[simp] theorem exSig_fieldMultAt_ur {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldMultAt ExData.ur k ps i = ω := by
  simp [Sig.fieldMultAt, exSig, exFieldMult]

@[simp] theorem exSig_fieldTyAt_urPair {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldTyAt ExData.urPair k ps i = PairT := by
  simp only [Sig.fieldTyAt, exSig, exFieldTy, PairT, Ty.bind]
  congr 1; funext i; exact i.elim0

@[simp] theorem exSig_fieldMultAt_urPair {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldMultAt ExData.urPair k ps i = ω := by
  simp [Sig.fieldMultAt, exSig, exFieldMult]

@[simp] theorem exSig_fieldTyAt_pairUr {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldTyAt ExData.pairUr k ps i = UrT := by
  simp only [Sig.fieldTyAt, exSig, exFieldTy, UrT, Ty.bind]
  congr 1; funext i; exact i.elim0

@[simp] theorem exSig_fieldMultAt_pairUr {m : ℕ} (k) (ps : Fin 0 → Mult m) (i) :
    exSig.fieldMultAt ExData.pairUr k ps i = 1 := by
  simp [Sig.fieldMultAt, exSig, exFieldMult]

/-- `fst : Pair → Int`. -/
theorem fst_typed : Typed exSig ![] 0 fstTm (.arr ω PairT IntT) := by
  refine Typed.abs ?_
  refine (Typed.case (Γ := Pi.single 0 1) (Δ := 0) (ps := Fin.elim0)
    (typed_var_single _ rfl) (fun k => ?_)).ofEq ?_
  · refine ((Typed.var ![0, 1, 1] _).ofEq ?_).ofEqTy (by simp [append_apply'])
    funext j
    fin_cases j <;> simp [append_apply', MZ.omega]
    exact congrArg MZ.of Mult.omega_add_one
  · funext j
    fin_cases j
    simp [append_apply']

/-- `λ₁ (x : UrPair). case₁ x of { UrPair p → case_ω p of { Pair a b → PairUr (Ur a) (Ur b) } }`
(Section 3.5). -/
def urDistTm : Tm exSig 0 0 :=
  .lam 1 UrPairT (.case 1 (v 0) ExData.urPair (fun _ =>
    .case ω (v 1) ExData.pair (fun _ =>
      .con ExData.pairUr (ck 0) ![.con ExData.ur (ck 0) ![v 2], .con ExData.ur (ck 0) ![v 3]])))

theorem typed_ur {n : ℕ} {E : TyEnv exSig 0 n} (x : Fin n) (hx : E x = IntT) :
    Typed exSig E ((MZ.omega : MZ 0) • (Pi.single x 1 : Usage 0 n)) (.con ExData.ur (ck 0) ![.var x]) UrT := by
  refine ((Typed.con (D := ExData.ur) (k := ck 0) 0 Fin.elim0 ![(Pi.single x 1 : Usage 0 n)]
    (fun i => ?_)).ofEq ?_).ofEqTy ?_
  · fin_cases i
    exact typed_var_single _ (by simpa using hx)
  · simp [MZ.omega]
  · rfl

/-- `UrPair ⊸ PairUr` is inhabited, thanks to `case_ω` (Section 3.5). -/
theorem urDist_typed : Typed exSig ![] 0 urDistTm (.arr 1 UrPairT PairUrT) := by
  refine Typed.abs ?_
  refine (Typed.case (Γ := Pi.single 0 1) (Δ := 0) (ps := Fin.elim0)
    (typed_var_single _ rfl) (fun k => ?_)).ofEq ?_
  · refine (Typed.case (Γ := Pi.single 1 1) (Δ := 0) (ps := Fin.elim0)
      (typed_var_single _ (by simp [append_apply', PairT])) (fun k => ?_)).ofEq ?_
    · refine ((Typed.con (D := ExData.pairUr) (k := ck 0) 0 Fin.elim0
        ![(MZ.omega : MZ 0) • (Pi.single 2 1 : Usage 0 4), (MZ.omega : MZ 0) • (Pi.single 3 1 : Usage 0 4)] (fun i => ?_)).ofEq
        ?_).ofEqTy ?_
      · fin_cases i
        · refine (typed_ur (2 : Fin 4) ?_).ofEqTy (by simp); simp [append_apply', IntT]
        · refine (typed_ur (3 : Fin 4) ?_).ofEqTy (by simp); simp [append_apply', IntT]
      · funext j
        fin_cases j <;> (simp [append_apply', MZ.omega]; try rfl)
      · rfl
    · funext j
      fin_cases j <;> (simp [append_apply']; try rfl)
  · funext j
    fin_cases j
    simp [append_apply']

section Compose

variable {S : Sig} {m : ℕ} (a b c : Ty S m)

/-- Function composition `λ p q. λ₁ f. λ_p g. λ_{p·q} x. f (g x)` (Section 2.6), at types
`a`, `b`, `c`. Under the two binders, `p` is the multiplicity variable `m` and `q` is `m + 1`. -/
def composeTm : Tm S m 0 :=
  .mlam (.mlam (.lam 1 (.arr (Mult.var (Fin.last m).castSucc) b.shift.shift c.shift.shift)
    (.lam (Mult.var (Fin.last m).castSucc) (.arr (Mult.var (Fin.last (m + 1))) a.shift.shift b.shift.shift)
      (.lam (Mult.var (Fin.last m).castSucc * Mult.var (Fin.last (m + 1))) a.shift.shift
        (.app (v 0) (.app (v 1) (v 2)))))))

/-- `(∘) : ∀ p q. (b →_p c) ⊸ (a →_q b) →_p a →_{p·q} c` (Section 2.6). -/
theorem compose_typed :
    Typed S ![] 0 (composeTm a b c)
      (.all (.all (.arr 1 (.arr (Mult.var (Fin.last m).castSucc) b.shift.shift c.shift.shift)
        (.arr (Mult.var (Fin.last m).castSucc)
          (.arr (Mult.var (Fin.last (m + 1))) a.shift.shift b.shift.shift)
          (.arr (Mult.var (Fin.last m).castSucc * Mult.var (Fin.last (m + 1)))
            a.shift.shift c.shift.shift))))) := by
  refine Typed.mabs (Typed.mabs (Typed.abs (Typed.abs (Typed.abs ?_))))
  refine (Typed.app (typed_var_single _ rfl)
    (Typed.app (typed_var_single _ rfl) (typed_var_single _ rfl))).ofEq ?_
  funext j
  fin_cases j <;> simp <;> rfl

end Compose

/-! ### Negative examples -/

/-- The three-point abstraction `{0, 1, ω}` of `MZ` (`none`, `some false`, `some true`),
interpreting multiplicity variables as `1`. -/
def MZ.ev {m : ℕ} (a : MZ m) : Option Bool := Option.map (Mult.toBool fun _ => false) a

/-- Addition in the abstraction. -/
def addT : Option Bool → Option Bool → Option Bool
  | none, b => b
  | a, none => a
  | some _, some _ => some true

/-- Multiplication in the abstraction. -/
def mulT : Option Bool → Option Bool → Option Bool
  | some a, some b => some (a || b)
  | _, _ => none

theorem MZ.ev_add {m : ℕ} (a b : MZ m) : MZ.ev (a + b) = addT (MZ.ev a) (MZ.ev b) := by
  induction a using MZ.cases' <;> induction b using MZ.cases' <;>
    first | rfl | (simp only [MZ.of_add_of]; simp [MZ.ev, MZ.of, addT])

theorem MZ.ev_mul {m : ℕ} (a b : MZ m) : MZ.ev (a * b) = mulT (MZ.ev a) (MZ.ev b) := by
  induction a using MZ.cases' <;> induction b using MZ.cases' <;>
    first | rfl | (simp only [MZ.of_mul_of]; simp [MZ.ev, MZ.of, mulT])

@[simp] theorem MZ.ev_zero {m : ℕ} : MZ.ev (0 : MZ m) = none := rfl
@[simp] theorem MZ.ev_one {m : ℕ} : MZ.ev (1 : MZ m) = some false := rfl
@[simp] theorem MZ.ev_omega {m : ℕ} : MZ.ev (MZ.omega : MZ m) = some true := rfl
@[simp] theorem MZ.ev_of_one {m : ℕ} : MZ.ev (MZ.of (1 : Mult m)) = some false := rfl

theorem MZ.ev_omega_mul {m : ℕ} (g : MZ m) : MZ.ev ((ω' : MZ m) * g) ≠ some false := by
  rw [MZ.ev_mul]; cases MZ.ev g <;> simp [mulT]

/-- In a `case₁` on a pair, the second (linear) component cannot be discarded:
`case₁ t of { Pair a b → a }` is not well typed, whatever the context and the type
(Section 3.3: discarding a field forces `case_ω`). -/
theorem fst_case1_untypable {m n : ℕ} (E : TyEnv exSig m n) (U : Usage m n) (t : Tm exSig m n)
    (C : Ty exSig m) :
    ¬ Typed exSig E U (.case 1 t ExData.pair (fun _ => .var (Fin.natAdd n ⟨0, by simp⟩))) C := by
  intro h
  obtain ⟨Γ, Δ, ps, -, hbs, -⟩ := h.case_inv
  obtain ⟨Γ', hU, -⟩ := (hbs (ck 0)).var_inv
  have := congrArg MZ.ev (congrFun hU (Fin.natAdd n ⟨1, by simp⟩))
  simp only [Fin.append_right, exSig_fieldMultAt_pair, mul_one, MZ.ev_of_one, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at this
  rw [Pi.single_eq_of_ne (by simp [Fin.natAdd_inj]), add_zero] at this
  exact MZ.ev_omega_mul _ this.symm

/-- A linear variable cannot be duplicated: `x :_1 Int ⊬ Pair x x : Pair` (compare `f1` in
Section 2.4). -/
theorem dup_not_linear {m n : ℕ} (E : TyEnv exSig m n) (x : Fin n) (A : Ty exSig m) :
    ¬ Typed exSig E (Pi.single x 1) (.con ExData.pair (ck 0) ![.var x, .var x]) A := by
  intro h
  obtain ⟨Γ, ps, Δ, hts, hU, -⟩ := h.con_inv
  obtain ⟨Γ0, h0, -⟩ := (hts ⟨0, by simp⟩).var_inv
  obtain ⟨Γ1, h1, -⟩ := (hts ⟨1, by simp⟩).var_inv
  have hU' : (Pi.single x 1 : Usage m n) =
      (ω' : MZ m) • Γ + (Δ ⟨0, by simp⟩ + Δ ⟨1, by simp⟩) := by
    rw [hU]; simp only [exSig_fieldMultAt_pair, MZ.of_one, one_smul]
    congr 1
    exact Fin.sum_univ_two Δ
  rw [h0, h1] at hU'
  have := congrArg MZ.ev (congrFun hU' x)
  simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, smul_eq_mul, MZ.ev_one] at this
  have key : ∀ a b c : MZ m, MZ.ev (a + (b + 1 + (c + 1))) ≠ some false := by
    intro a b c
    simp only [MZ.ev_add, MZ.ev_one]
    cases MZ.ev a <;> cases MZ.ev b <;> cases MZ.ev c <;> simp [addT]
  exact key _ _ _ this.symm

/-- `f1 = λ₁ (x : Pair). case_π x of { Pair a b → Pair a a }` (Section 2.4). -/
def f1Tm {m : ℕ} (π : Mult m) : Tm exSig m 0 :=
  .lam 1 PairT (.case π (v 0) ExData.pair (fun _ => .con ExData.pair (ck 0) ![v 1, v 1]))

/-- `f1` does not have the linear type `Pair ⊸ Pair`, whatever the multiplicity annotation `π`
of its `case` (Section 2.4): the component `a` is used twice. -/
theorem f1_not_linear {m : ℕ} (E : TyEnv exSig m 0) (U : Usage m 0) (π : Mult m) :
    ¬ Typed exSig E U (f1Tm π) (.arr 1 PairT PairT) := by
  intro h
  obtain ⟨B, -, hb⟩ := h.abs_inv
  obtain ⟨Γ, Δ, ps, ht, hbs, hU⟩ := hb.case_inv
  obtain ⟨Γx, hΓ, -⟩ := ht.var_inv
  obtain ⟨Γc, ps', Δs, hts, hV, -⟩ := (hbs (ck 0)).con_inv
  obtain ⟨Γ0, h0, -⟩ := (hts ⟨0, by simp⟩).var_inv
  obtain ⟨Γ1, h1, -⟩ := (hts ⟨1, by simp⟩).var_inv
  have hV' : (Fin.append Δ fun i => MZ.of (π * exSig.fieldMultAt ExData.pair (ck 0) ps i)) =
      (ω' : MZ m) • Γc + (Δs ⟨0, by simp⟩ + Δs ⟨1, by simp⟩) := by
    refine hV.trans ?_
    simp only [exSig_fieldMultAt_pair, MZ.of_one, one_smul]
    congr 1
    exact Fin.sum_univ_two Δs
  rw [h0, h1] at hV'
  -- in the branch, `a` is used twice, so the `case` must be unrestricted
  have e1 := congrArg MZ.ev (congrFun hV' ⟨1, by simp⟩)
  simp [append_apply'] at e1
  have key1 : ∀ a b c : MZ m, MZ.ev (a + (b + 1 + (c + 1))) = some true := by
    intro a b c
    simp only [MZ.ev_add, MZ.ev_one]
    cases MZ.ev a <;> cases MZ.ev b <;> cases MZ.ev c <;> simp [addT]
  have hπ : MZ.ev (MZ.of π) = some true := e1.trans (key1 _ _ _)
  -- but then the linear variable `x` is consumed `ω` times
  have e0 := congrArg MZ.ev (congrFun hU 0)
  rw [hΓ] at e0
  simp [append_apply'] at e0
  revert e0
  simp only [MZ.ev_add, MZ.ev_mul, hπ]
  cases MZ.ev (Γx 0) <;> cases MZ.ev (Δ 0) <;> simp [addT, mulT]

/-- The judgement `x :_ω A ⊢ x : A` is an instance of the variable rule (Section 3.2). -/
theorem var_omega (S : Sig) {m n : ℕ} (E : TyEnv S m n) (x : Fin n) :
    Typed S E (Pi.single x (MZ.of ω)) (.var x) (E x) := by
  refine (Typed.var (Pi.single x 1) x).ofEq ?_
  funext i
  by_cases hi : i = x
  · subst hi; simp [MZ.omega]; exact congrArg MZ.of Mult.omega_add_one
  · simp [hi]

/-- `x :_1 A, y :_ω B ⊢ x : A`: variables of multiplicity `ω` can be ignored (Section 3.2). -/
theorem var_weak (S : Sig) {m : ℕ} (E : TyEnv S m 2) :
    Typed S E ((Pi.single 0 1 : Usage m 2) + (Pi.single 1 (MZ.of (ω : Mult m)) : Usage m 2))
      (.var 0) (E 0) := by
  refine (Typed.var (Pi.single 1 1) 0).ofEq ?_
  funext i
  fin_cases i <;> simp [MZ.omega]

/-- With a multiplicity variable `p`, `x :_p A ⊢ x : A` does not hold (Section 3.5). -/
theorem var_mult_var_untypable (S : Sig) {m n : ℕ} (E : TyEnv S m (n + 1)) (V : Usage m n)
    (p : Fin m) (A : Ty S m) :
    ¬ Typed S E (Fin.append V ![MZ.of (Mult.var p)]) (.var (Fin.last n)) A := by
  intro h
  obtain ⟨Γ, hU, -⟩ := h.var_inv
  have := congrFun hU (Fin.last n)
  simp [append_apply'] at this
  induction h : Γ (Fin.last n) using MZ.cases' with
  | h0 =>
    rw [h] at this
    simp at this
    exact Mult.var_ne_one p (MZ.of_injective this)
  | h a =>
    rw [h] at this
    exact Mult.add_ne_var _ _ p (MZ.of_injective this).symm

/-- Hence `λ p. λ_p (x : A). x` does not have type `∀ p. A →_p A` (Section 3.5). -/
theorem id_mult_poly_untypable (S : Sig) {m n : ℕ} (E : TyEnv S m n) (U : Usage m n)
    (A : Ty S (m + 1)) :
    ¬ Typed S E U (.mlam (.lam (Mult.var (Fin.last m)) A (.var (Fin.last n))))
      (.all (.arr (Mult.var (Fin.last m)) A A)) := by
  intro h
  cases h with
  | mabs h =>
    obtain ⟨B, -, hb⟩ := h.abs_inv
    exact var_mult_var_untypable S _ _ _ _ hb

end LinearHaskell
