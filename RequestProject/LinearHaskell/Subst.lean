module

public import RequestProject.LinearHaskell.Rename

/-!
# The substitution lemma

The key lemma of the type-preservation proof, in its linear form: if
`Γ, x :_q A ⊢ t : B` and `Δ ⊢ u : A` then `Γ + qΔ ⊢ t[u/x] : B`.
The free variables of `u` are used as many times as `x` was used in `t`, which is expressed
by scaling the context `Δ` of `u` by the multiplicity `q` of `x`.
-/

@[expose] public section

namespace LinearHaskell

variable {S : Sig}

namespace Tm

theorem shiftN_var (n x : ℕ) : shiftN n (var x) = var (x + n) := by
  simp [shiftN, rename]

theorem mshift_var (x : ℕ) : mshift (var x) = var x := by
  simp [mshift, mbind]

theorem upS_substAtFun (n k : ℕ) (u : Tm) :
    upS n (substAtFun k u) = substAtFun (k + n) (shiftN n u) := by
  funext i
  simp only [upS, substAtFun]
  by_cases h₁ : i < n
  · simp [h₁, show i < k + n by omega]
  · simp only [h₁, if_false]
    by_cases h₂ : i - n < k
    · simp [h₂, show i < k + n by omega, shiftN_var, show i - n + n = i by omega]
    · by_cases h₃ : i - n = k
      · simp [show i = k + n by omega]
      · simp [h₂, h₃, show ¬ i < k + n by omega, show i ≠ k + n by omega, shiftN_var,
          show i - n - 1 + n = i - 1 by omega]

theorem mshift_substAtFun (k : ℕ) (u : Tm) :
    (fun i => mshift (substAtFun k u i)) = substAtFun k (mshift u) := by
  funext i
  simp only [substAtFun]
  split_ifs <;> simp [mshift_var]

end Tm

theorem single_comp_skip_lt {k x : ℕ} (h : x < k) :
    (Pi.single x 1 : Usage) ∘ skip k = Pi.single x 1 := by
  funext i
  simp only [Function.comp, skip, Pi.single_apply]
  split_ifs <;> first | rfl | omega

theorem single_comp_skip_gt {k x : ℕ} (h : k < x) :
    (Pi.single x 1 : Usage) ∘ skip k = Pi.single (x - 1) 1 := by
  funext i
  simp only [Function.comp, skip, Pi.single_apply]
  split_ifs <;> first | rfl | omega

theorem single_comp_skip_self (k : ℕ) : (Pi.single k 1 : Usage) ∘ skip k = 0 := by
  funext i
  simp only [Function.comp, skip, Pi.single_apply, Pi.zero_apply]
  split_ifs <;> first | rfl | omega

theorem skip_lt {k x : ℕ} (h : x < k) : skip k x = x := by simp [skip, h]
theorem skip_gt {k x : ℕ} (h : k < x) : skip k (x - 1) = x := by
  simp [skip, show ¬ x - 1 < k by omega]; omega

theorem prep_singleton_skip_zero {α : Type*} (a : α) (f : ℕ → α) : prep [a] f ∘ skip 0 = f := by
  funext i
  simp [skip, prep]

theorem prep_comp_skip' {α : Type*} (l : List α) (f : ℕ → α) (k n : ℕ) (h : l.length = n) :
    prep l f ∘ skip (k + n) = prep l (f ∘ skip k) := by
  subst h; exact prep_comp_skip l f k

theorem prep_k_add' {α : Type*} (l : List α) (f : ℕ → α) (k n : ℕ) (h : l.length = n) :
    prep l f (k + n) = f k := by
  subst h; exact prep_k_add l f k

theorem prep_add_smul_zeros (l : List MZ) (n : ℕ) (h : l.length = n) (U V : Usage) (c : MZ) :
    prep l U + c • prep (List.replicate n 0) V = prep l (U + c • V) := by
  subst h
  rw [smul_prep, List.map_replicate, mul_zero, prep_add_zeros]

/-- **Substitution lemma.** If `Γ ⊢ t : B`, where `Γ` contains the variable `k` with type `A`
and multiplicity `q`, and `Δ ⊢ u : A`, then `t[u/k]` is typed in `Γ - k + qΔ`. -/
theorem Typed.substAt {E : TyEnv} {U : Usage} {t : Tm} {B : Ty} (h : Typed S E U t B) :
    ∀ (k : ℕ) (u : Tm) (Δ : Usage), Typed S (E ∘ skip k) Δ u (E k) →
      Typed S (E ∘ skip k) (U ∘ skip k + U k • Δ) (Tm.substAt k u t) B := by
  induction h with
  | @var E Γ x =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst, Tm.substAtFun]
    rcases lt_trichotomy x k with hx | hx | hx
    · simp only [hx, if_true]
      refine ((Typed.var (Γ ∘ skip k + Γ k • Δ) x).ofEq ?_).ofEqTy ?_
      · have hk : (Pi.single x 1 : Usage) k = 0 := by simp [hx.ne']
        rw [show (ω' • Γ + Pi.single x 1) ∘ skip k = ω' • (Γ ∘ skip k) + Pi.single x 1 ∘ skip k
          from rfl, single_comp_skip_lt hx]
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk]
        ring
      · simp [skip_lt hx]
    · subst hx
      simp only [lt_irrefl, if_false, if_true]
      refine (hu.weaken (Γ ∘ skip x + Γ x • Δ)).ofEq ?_
      rw [show (ω' • Γ + Pi.single x 1) ∘ skip x = ω' • (Γ ∘ skip x) + Pi.single x 1 ∘ skip x
          from rfl, single_comp_skip_self]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, Pi.zero_apply]
      ring
    · simp only [show ¬ x < k by omega, show x ≠ k by omega, if_false]
      refine ((Typed.var (Γ ∘ skip k + Γ k • Δ) (x - 1)).ofEq ?_).ofEqTy ?_
      · have hk : (Pi.single x 1 : Usage) k = 0 := by simp [hx.ne]
        rw [show (ω' • Γ + Pi.single x 1) ∘ skip k = ω' • (Γ ∘ skip k) + Pi.single x 1 ∘ skip k
          from rfl, single_comp_skip_gt hx]
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk]
        ring
      · simp [skip_gt hx]
  | @abs E U π A B t _ ih =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst, Tm.upS_substAtFun]
    refine Typed.abs ?_
    have hu' : Typed S (prep [A] (E ∘ skip k)) (prep [0] Δ) (u.shiftN 1) (E k) := hu.shiftN [A]
    have e1 : prep [A] E ∘ skip (k + 1) = prep [A] (E ∘ skip k) := prep_comp_skip [A] E k
    have e2 : prep [MZ.of π] U ∘ skip (k + 1) = prep [MZ.of π] (U ∘ skip k) :=
      prep_comp_skip [MZ.of π] U k
    have e3 : prep [A] E (k + 1) = E k := prep_k_add [A] E k
    have e4 : prep [MZ.of π] U (k + 1) = U k := prep_k_add [MZ.of π] U k
    have := ih (k + 1) (u.shiftN 1) (prep [0] Δ) (by rw [e1, e3]; exact hu')
    rw [e1, e2, e4] at this
    refine this.ofEq ?_
    exact prep_add_smul_zeros [MZ.of π] 1 rfl _ _ _
  | @app E Γ Δ' π A B t u' _ _ ih₁ ih₂ =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst]
    refine (Typed.app (ih₁ k u Δ hu) (ih₂ k u Δ hu)).ofEq ?_
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp]
    ring
  | @con E Γ D k' ps ts Δ' hp hk hl _ ih =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst]
    have := Typed.con (S := S) (E := E ∘ skip k) (Γ ∘ skip k + Γ k • Δ) (D := D) (k := k')
      (ps := ps) (ts := ts.map (fun t => Tm.subst (Tm.substAtFun k u) t))
      (fun i => Δ' i ∘ skip k + Δ' i k • Δ) hp hk (by simpa using hl) (by
        intro i hi
        rw [List.length_map] at hi
        rw [List.getD_map_of_lt _ _ default _ _ hi]
        exact ih i hi k u Δ hu)
    refine this.ofEq ?_
    rw [List.length_map]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp, Finset.sum_apply,
      mul_add, Finset.sum_add_distrib]
    simp only [mul_assoc, add_mul, Finset.sum_mul]
    ring
  | @case E Γ Δ' π t D ps bs C ht hl hn _ iht ih =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst, Tm.upS_substAtFun]
    have := Typed.case (S := S) (E := E ∘ skip k) (Γ := Γ ∘ skip k + Γ k • Δ)
      (Δ := Δ' ∘ skip k + Δ' k • Δ)
      (π := π) (bs := bs.map (fun b => (b.1, Tm.subst (Tm.substAtFun (k + b.1) (u.shiftN b.1))
        b.2))) (C := C)
      (iht k u Δ hu) (by simpa using hl)
      (by
        intro k' hk'
        rw [List.length_map] at hk'
        rw [List.getD_map_of_lt _ _ default _ _ hk']
        exact hn k' hk')
      (by
        intro k' hk'
        rw [List.length_map] at hk'
        rw [List.getD_map_of_lt _ _ default _ _ hk']
        dsimp only
        have hlen : (bs.getD k' default).1 = (S.fieldTys D k' ps).length := by
          rw [hn k' hk']; simp [Sig.fieldTys]
        have hlen' : (S.fieldTys D k' ps).length =
            ((S.fieldMults D k' ps).map (fun μ => MZ.of (π * μ))).length := by
          simp [Sig.fieldMults, Sig.fieldTys]
        rw [hlen]
        set n := (S.fieldTys D k' ps).length with hn'
        set ms := (S.fieldMults D k' ps).map (fun μ => MZ.of (π * μ))
        have hu' := hu.shiftN (S.fieldTys D k' ps)
        have e1 : prep (S.fieldTys D k' ps) E ∘ skip (k + n) =
            prep (S.fieldTys D k' ps) (E ∘ skip k) := prep_comp_skip' _ _ _ _ rfl
        have e2 : prep ms Δ' ∘ skip (k + n) = prep ms (Δ' ∘ skip k) :=
          prep_comp_skip' _ _ _ _ hlen'.symm
        have e3 : prep (S.fieldTys D k' ps) E (k + n) = E k := prep_k_add' _ _ _ _ rfl
        have e4 : prep ms Δ' (k + n) = Δ' k := prep_k_add' _ _ _ _ hlen'.symm
        have := ih k' hk' (k + n) (u.shiftN n) (prep (List.replicate n 0) Δ)
          (by rw [e1, e3]; exact hu')
        rw [e1, e2, e4] at this
        refine this.ofEq ?_
        exact prep_add_smul_zeros ms n hlen'.symm _ _ _)
    refine this.ofEq ?_
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp]
    ring
  | @letin E Δ' π bs u' C Γ _ _ ih ihu =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst, Tm.upS_substAtFun]
    have := Typed.letin (S := S) (E := E ∘ skip k) (Δ := Δ' ∘ skip k + Δ' k • Δ)
      (π := π) (bs := bs.map (fun b => (b.1, Tm.subst (Tm.substAtFun k u) b.2)))
      (u := Tm.subst (Tm.substAtFun (k + bs.length) (u.shiftN bs.length)) u') (C := C)
      (fun i => Γ i ∘ skip k + Γ i k • Δ)
      (by
        intro i hi
        rw [List.length_map] at hi
        rw [List.getD_map_of_lt _ _ default _ _ hi]
        exact ih i hi k u Δ hu)
      (by
        set n := bs.length with hn'
        have hA : (bs.map Prod.fst).length = n := by simp [hn']
        have hR : (List.replicate n (MZ.of π)).length = n := by simp
        have hu' := hu.shiftN (bs.map Prod.fst)
        rw [hA] at hu'
        have e1 : prep (bs.map Prod.fst) E ∘ skip (k + n) =
            prep (bs.map Prod.fst) (E ∘ skip k) := prep_comp_skip' _ _ _ _ hA
        have e2 : prep (List.replicate n (MZ.of π)) Δ' ∘ skip (k + n) =
            prep (List.replicate n (MZ.of π)) (Δ' ∘ skip k) := prep_comp_skip' _ _ _ _ hR
        have e3 : prep (bs.map Prod.fst) E (k + n) = E k := prep_k_add' _ _ _ _ hA
        have e4 : prep (List.replicate n (MZ.of π)) Δ' (k + n) = Δ' k := prep_k_add' _ _ _ _ hR
        have := ihu (k + n) (u.shiftN n) (prep (List.replicate n 0) Δ)
          (by rw [e1, e3]; exact hu')
        rw [e1, e2, e4] at this
        simp only [List.map_map, Function.comp_def, List.length_map]
        refine this.ofEq ?_
        exact prep_add_smul_zeros _ n hR _ _ _)
    refine this.ofEq ?_
    rw [List.length_map]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp, Finset.sum_apply,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    simp only [add_mul, Finset.sum_mul, mul_assoc]
    ring
  | @mabs E U t A _ ih =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst, Tm.mshift_substAtFun]
    refine Typed.mabs ?_
    have := ih k u.mshift (MZ.bind mshiftσ ∘ Δ) (hu.mbind mshiftσ)
    refine this.ofEq ?_
    funext i
    simp [Function.comp]
  | @mapp E U t A π _ ih =>
    intro k u Δ hu
    simp only [Tm.substAt, Tm.subst]
    exact Typed.mapp π (ih k u Δ hu)

end LinearHaskell
