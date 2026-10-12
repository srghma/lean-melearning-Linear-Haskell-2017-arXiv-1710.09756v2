module

public import RequestProject.LinearHaskell.Safety

/-!
# Examples from Sections 2 and 3

We fix a small signature with the following datatypes (no type polymorphism, as in `λq→`):

* `Pair` (index `0`): `data Pair where Pair : Int ⊸ Int ⊸ Pair` (both fields linear, as for
  every Haskell-98 datatype, Section 2.4);
* `Int` (index `1`): an abstract base type (no constructors);
* `Bool` (index `2`): `data Bool where False : Bool; True : Bool`;
* `Ur` (index `3`): `data Ur where Ur : Int → Ur` (an unrestricted field, Section 2.5);
* `UrPair` (index `4`): `data UrPair where UrPair : Pair → UrPair`;
* `PairUr` (index `5`): `data PairUr where PairUr : Ur ⊸ Ur ⊸ PairUr`.

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
* `x :_p Int ⊢ x : Int` does not hold for a multiplicity variable `p`, hence
  `λ p. λ_p (x : Int). x` does not have type `∀ p. Int →_p Int` (Section 3.5).
-/

@[expose] public section

namespace LinearHaskell

open Mult

/-- The type `Int`. -/
def IntT : Ty := .data 1 []
/-- The type `Pair`. -/
def PairT : Ty := .data 0 []
/-- The type `Ur`. -/
def UrT : Ty := .data 3 []

/-- The example signature. -/
def exSig : Sig where
  nparams _ := 0
  ctors
    | 0 => [[(1, IntT), (1, IntT)]]
    | 2 => [[], []]
    | 3 => [[(ω, IntT)]]
    | 4 => [[(ω, .data 0 [])]]
    | 5 => [[(1, .data 3 []), (1, .data 3 [])]]
    | _ => []

@[simp] theorem exSig_fieldTys_pair : exSig.fieldTys 0 0 [] = [IntT, IntT] := rfl
@[simp] theorem exSig_fieldMults_pair : exSig.fieldMults 0 0 [] = [1, 1] := rfl
@[simp] theorem exSig_fieldTy_pair_0 : exSig.fieldTy 0 0 [] 0 = IntT := rfl
@[simp] theorem exSig_fieldTy_pair_1 : exSig.fieldTy 0 0 [] 1 = IntT := rfl
@[simp] theorem exSig_fieldMult_pair_0 : exSig.fieldMult 0 0 [] 0 = 1 := rfl
@[simp] theorem exSig_fieldMult_pair_1 : exSig.fieldMult 0 0 [] 1 = 1 := rfl

/-- `swap = λ₁ (x : Pair). case₁ x of { Pair a b → Pair b a }`. -/
def swapTm : Tm := .lam 1 PairT (.case 1 (.var 0) [(2, .con 0 0 [.var 1, .var 0])])

/-- `fst = λ_ω (x : Pair). case_ω x of { Pair a b → a }`. -/
def fstTm : Tm := .lam ω PairT (.case ω (.var 0) [(2, .var 0)])

theorem typed_var_single (E : TyEnv) (x : ℕ) :
    Typed exSig E (Pi.single x 1) (.var x) (E x) :=
  (Typed.var 0 x).ofEq (by simp)

/-- `swap : Pair ⊸ Pair`. -/
theorem swap_typed (E : TyEnv) : Typed exSig E 0 swapTm (.arr 1 PairT PairT) := by
  refine Typed.abs ?_
  refine (Typed.case (Γ := Pi.single 0 1) (Δ := 0) (D := 0) (ps := [])
    ((typed_var_single _ 0).ofEqTy rfl) rfl ?_ ?_).ofEq ?_
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    rfl
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    refine (Typed.con (S := exSig) 0 (D := 0) (k := 0) (ps := []) (ts := [.var 1, .var 0])
      (fun i => Pi.single (1 - i) 1) rfl (by decide) rfl ?_).ofEq ?_
    · intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by simp at hi; omega
      · exact typed_var_single _ 1
      · exact typed_var_single _ 0
    · funext j
      rcases j with _ | _ | j <;> simp [prep, Finset.sum_range_succ]
  · funext j
    rcases j with _ | j <;> simp [prep]

/-- `f1 = λ₁ (x : Pair). case_π x of { Pair a b → Pair a a }` (Section 2.4). -/
def f1Tm (π : Mult) : Tm := .lam 1 PairT (.case π (.var 0) [(2, .con 0 0 [.var 0, .var 0])])

/-- `λ₁ (x : UrPair). case₁ x of { UrPair p → case_ω p of { Pair a b → PairUr (Ur a) (Ur b) } }`
(Section 3.5). -/
def urDistTm : Tm :=
  .lam 1 (.data 4 []) (.case 1 (.var 0)
    [(1, .case ω (.var 0) [(2, .con 5 0 [.con 3 0 [.var 0], .con 3 0 [.var 1]])])])

/-- `fst : Pair → Int`. -/
theorem fst_typed (E : TyEnv) : Typed exSig E 0 fstTm (.arr ω PairT IntT) := by
  refine Typed.abs ?_
  refine (Typed.case (Γ := Pi.single 0 1) (Δ := 0) (D := 0) (ps := [])
    ((typed_var_single _ 0).ofEqTy rfl) rfl ?_ ?_).ofEq ?_
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    rfl
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    refine (Typed.var (fun i => if i < 2 then 1 else 0) 0).ofEq ?_
    funext j
    rcases j with _ | _ | j
    · simp [prep, MZ.omega]; exact congrArg MZ.of Mult.omega_add_one
    · simp [prep, MZ.omega]
    · simp [prep, show ¬ (j + 1 + 1 < 2) by omega]
  · funext j
    rcases j with _ | j <;> simp [prep]

/-- `UrPair ⊸ PairUr` is inhabited, thanks to `case_ω` (Section 3.5). -/
theorem urDist_typed (E : TyEnv) :
    Typed exSig E 0 urDistTm (.arr 1 (.data 4 []) (.data 5 [])) := by
  refine Typed.abs ?_
  refine (Typed.case (Γ := Pi.single 0 1) (Δ := 0) (D := 4) (ps := [])
    ((typed_var_single _ 0).ofEqTy rfl) rfl ?_ ?_).ofEq ?_
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    rfl
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    refine (Typed.case (Γ := Pi.single 0 1) (Δ := 0) (D := 0) (ps := [])
      ((typed_var_single _ 0).ofEqTy rfl) rfl ?_ ?_).ofEq ?_
    · intro k hk
      obtain rfl : k = 0 := by simpa using hk
      rfl
    · intro k hk
      obtain rfl : k = 0 := by simpa using hk
      have hUr : ∀ (E' : TyEnv) (x : ℕ), E' x = IntT →
          Typed exSig E' (MZ.omega • (Pi.single x 1 : Usage)) (.con 3 0 [.var x]) (.data 3 []) := by
        intro E' x hx
        refine (Typed.con (S := exSig) 0 (D := 3) (k := 0) (ps := []) (ts := [.var x])
          (fun _ => Pi.single x 1) rfl (by decide) rfl ?_).ofEq ?_
        · intro i hi
          obtain rfl : i = 0 := by simpa using hi
          exact (typed_var_single _ x).ofEqTy hx
        · funext j
          simp [Sig.fieldMult, Sig.fieldMults, Sig.fields, exSig, MZ.omega]
      refine (Typed.con (S := exSig) 0 (D := 5) (k := 0) (ps := [])
        (ts := [.con 3 0 [.var 0], .con 3 0 [.var 1]])
        (fun i => MZ.omega • (Pi.single i 1 : Usage)) rfl (by decide) rfl ?_).ofEq ?_
      · intro i hi
        obtain rfl | rfl : i = 0 ∨ i = 1 := by simp at hi; omega
        · exact hUr _ 0 rfl
        · exact hUr _ 1 rfl
      · funext j
        rcases j with _ | _ | j <;>
          simp [prep, Finset.sum_range_succ, Sig.fieldMult, Sig.fieldMults, Sig.fields, exSig,
            MZ.omega]
    · funext j
      rcases j with _ | j <;> simp [prep, Sig.fieldMults, Sig.fields, exSig]
  · funext j
    rcases j with _ | j <;> simp [prep]

/-- Function composition `λ p q. λ₁ f. λ_p g. λ_{p·q} x. f (g x)` (Section 2.6), here at the
base type `Int`. Under the two binders, `q` is the multiplicity variable `0` and `p` is `1`. -/
def composeTm : Tm :=
  .mlam (.mlam (.lam 1 (.arr (Mult.var 1) IntT IntT)
    (.lam (Mult.var 1) (.arr (Mult.var 0) IntT IntT)
      (.lam (Mult.var 1 * Mult.var 0) IntT (.app (.var 2) (.app (.var 1) (.var 0)))))))

/-- `(∘) : ∀ p q. (b →_p c) ⊸ (a →_q b) →_p a →_{p·q} c` (Section 2.6). -/
theorem compose_typed (S : Sig) (E : TyEnv) :
    Typed S E 0 composeTm
      (.all (.all (.arr 1 (.arr (Mult.var 1) IntT IntT)
        (.arr (Mult.var 1) (.arr (Mult.var 0) IntT IntT)
          (.arr (Mult.var 1 * Mult.var 0) IntT IntT))))) := by
  refine Typed.mabs (Typed.mabs ?_)
  simp only [Function.comp_def]
  refine Typed.abs (Typed.abs (Typed.abs ?_))
  have hf := Typed.var (S := S)
    (E := prep [IntT] (prep [Ty.arr (Mult.var 0) IntT IntT]
      (prep [Ty.arr (Mult.var 1) IntT IntT] fun x => (E x).shift.shift))) 0 2
  have hg := Typed.var (S := S)
    (E := prep [IntT] (prep [Ty.arr (Mult.var 0) IntT IntT]
      (prep [Ty.arr (Mult.var 1) IntT IntT] fun x => (E x).shift.shift))) 0 1
  have hx := Typed.var (S := S)
    (E := prep [IntT] (prep [Ty.arr (Mult.var 0) IntT IntT]
      (prep [Ty.arr (Mult.var 1) IntT IntT] fun x => (E x).shift.shift))) 0 0
  refine (Typed.app hf (Typed.app hg hx)).ofEq ?_
  funext j
  rcases j with _ | _ | _ | j <;>
    simp [prep]

/-! ### Negative examples -/

/-- The three-point abstraction `{0, 1, ω}` of `MZ` (`none`, `some false`, `some true`),
interpreting multiplicity variables as `1`. -/
def MZ.ev (a : MZ) : Option Bool := Option.map (Mult.toBool fun _ => false) a

/-- Addition in the abstraction. -/
def addT : Option Bool → Option Bool → Option Bool
  | none, b => b
  | a, none => a
  | some _, some _ => some true

/-- Multiplication in the abstraction. -/
def mulT : Option Bool → Option Bool → Option Bool
  | some a, some b => some (a || b)
  | _, _ => none

theorem MZ.ev_add (a b : MZ) : MZ.ev (a + b) = addT (MZ.ev a) (MZ.ev b) := by
  induction a using MZ.cases' <;> induction b using MZ.cases' <;>
    first | rfl | (simp only [MZ.of_add_of]; simp [MZ.ev, MZ.of, addT])

theorem MZ.ev_mul (a b : MZ) : MZ.ev (a * b) = mulT (MZ.ev a) (MZ.ev b) := by
  induction a using MZ.cases' <;> induction b using MZ.cases' <;>
    first | rfl | (simp only [MZ.of_mul_of]; simp [MZ.ev, MZ.of, mulT])

@[simp] theorem MZ.ev_zero : MZ.ev 0 = none := rfl
@[simp] theorem MZ.ev_one : MZ.ev 1 = some false := rfl
@[simp] theorem MZ.ev_omega : MZ.ev MZ.omega = some true := rfl

/-- In a `case₁` on a pair, the second (linear) component cannot be discarded:
`case₁ t of { Pair a b → a }` is not well typed, whatever the context and the type
(Section 3.3: discarding a field forces `case_ω`). -/
theorem fst_case1_untypable (E : TyEnv) (U : Usage) (t : Tm) (C : Ty) :
    ¬ Typed exSig E U (.case 1 t [(2, .var 0)]) C := by
  intro h
  cases h with
  | @case _ Γ Δ _ _ D ps _ _ ht hl hn hbs =>
    have h2 := hn 0 (by simp)
    have hb := hbs 0 (by simp)
    -- the scrutinee must be a datatype with one constructor with two linear fields
    obtain rfl | rfl : D = 0 ∨ D = 5 := by
      rcases D with _ | _ | _ | _ | _ | _ | D
      · simp
      all_goals simp [exSig, Sig.fields] at h2 ⊢
    all_goals
      simp only [List.getD_cons_zero] at hb
      generalize hU : prep _ Δ = U' at hb
      cases hb with
      | var Γ' x =>
        have := congrArg MZ.ev (congrFun hU 1)
        simp [prep, Sig.fieldMults, Sig.fields, exSig, MZ.ev_mul] at this
        cases h : MZ.ev (Γ' 1) <;> simp [h, mulT] at this

/-- A linear variable cannot be duplicated: `x :_1 Int ⊬ Pair x x : Pair` (compare `f1` in
Section 2.4). -/
theorem dup_not_linear (E : TyEnv) (A : Ty) :
    ¬ Typed exSig E (Pi.single 0 1) (.con 0 0 [.var 0, .var 0]) A := by
  intro h
  generalize hU : (Pi.single 0 1 : Usage) = U at h
  cases h with
  | con Γ Δ hp hk hl hts =>
    have h0 := hts 0 (by simp)
    have h1 := hts 1 (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
    generalize hΔ0 : Δ 0 = V0 at h0
    generalize hΔ1 : Δ 1 = V1 at h1
    generalize exSig.fieldTy 0 0 _ 0 = A0 at h0
    generalize exSig.fieldTy 0 0 _ 1 = A1 at h1
    cases h0 with
    | var Γ0 _ =>
      cases h1 with
      | var Γ1 _ =>
        have := congrArg MZ.ev (congrFun hU 0)
        simp [Finset.sum_range_succ, hΔ0, hΔ1, MZ.ev_add, MZ.ev_mul, Sig.fieldMult,
          Sig.fieldMults, Sig.fields, exSig] at this
        cases h1 : MZ.ev (Γ 0) <;> cases h2 : MZ.ev (Γ0 0) <;> cases h3 : MZ.ev (Γ1 0) <;>
          simp [h1, h2, h3, addT, mulT] at this

/-- `f1` does not have the linear type `Pair ⊸ Pair`, whatever the multiplicity annotation `π`
of its `case` (Section 2.4): the component `a` is used twice. -/
theorem f1_not_linear (E : TyEnv) (U : Usage) (π : Mult) :
    ¬ Typed exSig E U (f1Tm π) (.arr 1 PairT PairT) := by
  intro h
  cases h with
  | abs h =>
    generalize hU : prep [MZ.of 1] U = U' at h
    cases h with
    | @case _ Γ Δ _ _ D ps _ _ ht hl hn hbs =>
      have hb := hbs 0 (by simp)
      simp only [List.getD_cons_zero] at hb
      -- the scrutinee `x` is used at least once
      generalize hΓ : Γ = Γ' at ht
      generalize hT : Ty.data D ps = T at ht
      cases ht with
      | var Γx _ =>
        obtain ⟨rfl, rfl⟩ : D = 0 ∧ ps = [] := by simpa [prep, PairT] using hT
        -- in the branch, `a` (index 0) is used twice
        generalize hV : prep _ Δ = V at hb
        generalize PairT = T' at hb
        cases hb with
        | con Γc Δs hp hk hl' hts =>
          have h0 := hts 0 (by simp)
          have h1 := hts 1 (by simp)
          simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
          generalize hΔ0 : Δs 0 = V0 at h0
          generalize hΔ1 : Δs 1 = V1 at h1
          generalize exSig.fieldTy 0 0 _ 0 = A0 at h0
          generalize exSig.fieldTy 0 0 _ 1 = A1 at h1
          cases h0 with
          | var Γ0 _ =>
            cases h1 with
            | var Γ1 _ =>
              have ea := congrArg MZ.ev (congrFun hV 0)
              simp [prep, Finset.sum_range_succ, hΔ0, hΔ1, MZ.ev_add, MZ.ev_mul, Sig.fieldMult,
                Sig.fieldMults, Sig.fields, exSig] at ea
              have ex := congrArg MZ.ev (congrFun hU 0)
              simp [prep, hΓ, MZ.ev_add, MZ.ev_mul] at ex
              cases h1 : MZ.ev (Γc 0) <;> cases h2 : MZ.ev (Γ0 0) <;>
                cases h3 : MZ.ev (Γ1 0) <;> cases h4 : MZ.ev (Γx 0) <;>
                cases h5 : MZ.ev (Δ 0) <;> cases h6 : MZ.ev (MZ.of π) <;>
                simp [h1, h2, h3, h4, h5, h6, addT, mulT] at ea ex <;> simp [ea] at ex

/-- The judgement `x :_ω A ⊢ x : A` is an instance of the variable rule (Section 3.2). -/
theorem var_omega (S : Sig) (E : TyEnv) :
    Typed S E (Pi.single 0 (MZ.of ω)) (.var 0) (E 0) := by
  refine (Typed.var (Pi.single 0 1) 0).ofEq ?_
  funext i
  by_cases hi : i = 0
  · subst hi; simp [MZ.omega]; exact congrArg MZ.of Mult.omega_add_one
  · simp [hi]

/-- `x :_1 A, y :_ω B ⊢ x : A`: variables of multiplicity `ω` can be ignored (Section 3.2). -/
theorem var_weak (S : Sig) (E : TyEnv) :
    Typed S E (Pi.single 0 1 + Pi.single 1 (MZ.of ω)) (.var 0) (E 0) := by
  refine (Typed.var (Pi.single 1 1) 0).ofEq ?_
  funext i
  rcases i with _ | _ | i <;> simp [MZ.omega]

/-- With a multiplicity variable `p`, `x :_p Int ⊢ x : Int` does not hold (Section 3.5). -/
theorem var_mult_var_untypable (S : Sig) (E : TyEnv) (V : Usage) (n : ℕ) (A : Ty) :
    ¬ Typed S E (prep [MZ.of (Mult.var n)] V) (.var 0) A := by
  intro h
  generalize hU : prep [MZ.of (Mult.var n)] V = U at h
  cases h with
  | var Γ _ =>
    have := congrFun hU 0
    simp [prep] at this
    induction h : Γ 0 using MZ.cases' with
    | h0 =>
      rw [h] at this
      simp at this
      exact Mult.var_ne_one n (MZ.of_injective this)
    | h a =>
      rw [h] at this
      exact Mult.add_ne_var _ _ n (MZ.of_injective this).symm

/-- Hence `λ p. λ_p (x : Int). x` does not have type `∀ p. Int →_p Int` (Section 3.5). -/
theorem id_mult_poly_untypable (S : Sig) (E : TyEnv) (U : Usage) :
    ¬ Typed S E U (.mlam (.lam (Mult.var 0) IntT (.var 0))) (.all (.arr (Mult.var 0) IntT IntT)) := by
  intro h
  cases h with
  | mabs h =>
    generalize MZ.bind mshiftσ ∘ U = U' at h
    cases h with
    | abs h => exact var_mult_var_untypable S _ U' 0 _ h

end LinearHaskell
