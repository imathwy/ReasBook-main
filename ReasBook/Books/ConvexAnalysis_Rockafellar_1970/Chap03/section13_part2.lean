/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part8

open scoped Pointwise

section Chap03
section Section13

/-- If `x ∉ closure C` and `C` is a nonempty convex set, then for any real `μ` there exists an
affine map bounded above by `indicatorFunction C` whose value at `x` exceeds `μ`. -/
lemma section13_exists_affineMap_le_indicatorFunction_gt_of_not_mem_closure {n : Nat}
    (C : Set (Fin n → Real)) (hC : Convex ℝ C) (hCne : C.Nonempty) {x : Fin n → Real}
    (hx : x ∉ closure C) (μ : Real) :
    ∃ h : AffineMap ℝ (Fin n → Real) Real,
      (∀ y : Fin n → Real, (h y : EReal) ≤ indicatorFunction C y) ∧
        (μ : EReal) < (h x : EReal) := by
  classical
  have hdisj :
      Disjoint (closure ({x} : Set (Fin n → Real))) (closure C) := by
    have : Disjoint ({x} : Set (Fin n → Real)) (closure C) :=
      Set.disjoint_singleton_left.2 hx
    simpa [closure_singleton] using this
  rcases
      exists_hyperplaneSeparatesStrongly_of_disjoint_closure_convex_of_bounded (n := n)
        ({x} : Set (Fin n → Real)) C (Set.singleton_nonempty x) hCne
        (convex_singleton (𝕜 := Real) (c := x)) hC hdisj
        (Or.inl Bornology.isBounded_singleton) with
    ⟨H, hH⟩
  rcases hH with ⟨_h₁ne, _h₂ne, b, β, _hb0, _hHdef, ε, _hεpos, hcases⟩
  let B : Set (Fin n → Real) := {z | ‖z‖ ≤ (1 : Real)}
  have h0B : (0 : Fin n → Real) ∈ ε • B := by
    refine ⟨0, ?_, by simp⟩
    simp [B]
  have hx_thick : x ∈ ({x} : Set (Fin n → Real)) + (ε • B) := by
    refine ⟨x, by simp, 0, h0B, by simp⟩
  have hexists :
      ∃ (b0 : Fin n → Real) (β0 : Real),
        (∀ y ∈ C, dotProduct y b0 < β0) ∧ β0 < dotProduct x b0 := by
    cases hcases with
    | inl h =>
        have hx_lt : dotProduct x b < β := by
          simpa [B] using h.1 hx_thick
        have hC_gt : ∀ y ∈ C, β < dotProduct y b := by
          intro y hyC
          have hy_thick : y ∈ C + (ε • B) := by
            refine ⟨y, hyC, 0, h0B, by simp⟩
          simpa [B] using h.2 hy_thick
        refine ⟨-b, -β, ?_, ?_⟩
        · intro y hyC
          simpa [dotProduct_neg] using (neg_lt_neg (hC_gt y hyC))
        · simpa [dotProduct_neg] using (neg_lt_neg hx_lt)
    | inr h =>
        have hx_gt : β < dotProduct x b := by
          simpa [B] using h.2 hx_thick
        have hC_lt : ∀ y ∈ C, dotProduct y b < β := by
          intro y hyC
          have hy_thick : y ∈ C + (ε • B) := by
            refine ⟨y, hyC, 0, h0B, by simp⟩
          simpa [B] using h.1 hy_thick
        exact ⟨b, β, hC_lt, hx_gt⟩
  rcases hexists with ⟨b0, β0, hC_lt, hx_gt⟩
  set d : Real := dotProduct x b0 - β0
  have hd_pos : 0 < d := by
    exact sub_pos.2 hx_gt
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  set t : Real := (|μ| + 1) / d
  have ht_pos : 0 < t := by
    have hnum : 0 < |μ| + 1 := by
      have habs : 0 ≤ |μ| := abs_nonneg μ
      linarith
    exact div_pos hnum hd_pos
  -- Build the affine map `y ↦ ⟪y, t • b0⟫ - tβ0`.
  let b1 : Fin n → Real := t • b0
  let β1 : Real := t * β0
  let φ : (Fin n → Real) →ₗ[ℝ] Real :=
    { toFun := fun y => y ⬝ᵥ b1
      map_add' := by
        intro y z
        simp [add_dotProduct]
      map_smul' := by
        intro c y
        simp [smul_dotProduct, smul_eq_mul] }
  let hAff : AffineMap ℝ (Fin n → Real) Real :=
    { toFun := fun y => y ⬝ᵥ b1 - β1
      linear := φ
      map_vadd' := by
        intro p v
        simp [φ, sub_eq_add_neg, add_left_comm, add_comm] }
  have hb1 : ∀ y : Fin n → Real, dotProduct y b1 = t * dotProduct y b0 := by
    intro y
    simp [b1, dotProduct_comm, dotProduct_smul, smul_eq_mul, mul_comm]
  have hhAff : ∀ y : Fin n → Real, (hAff y : EReal) ≤ indicatorFunction C y := by
    intro y
    by_cases hyC : y ∈ C
    · have hy_lt : dotProduct y b0 < β0 := hC_lt y hyC
      have hy_mul : t * dotProduct y b0 < t * β0 := by
        exact (mul_lt_mul_of_pos_left hy_lt ht_pos)
      have hy_le0 : hAff y ≤ 0 := by
        have : dotProduct y b1 < β1 := by
          simpa [hb1 y, β1] using hy_mul
        have : dotProduct y b1 - β1 < 0 := sub_lt_zero.2 this
        simpa [hAff] using (le_of_lt this)
      have : (hAff y : EReal) ≤ (0 : EReal) := (EReal.coe_le_coe_iff).2 hy_le0
      simpa [indicatorFunction, hyC] using this
    · simp [indicatorFunction, hyC]
  have hx_eq : hAff x = |μ| + 1 := by
    have hx1 : hAff x = t * (dotProduct x b0 - β0) := by
      calc
        hAff x = dotProduct x b1 - β1 := by rfl
        _ = t * dotProduct x b0 - t * β0 := by
            simp [hb1 x, β1]
        _ = t * (dotProduct x b0 - β0) := by
            ring
    have ht_mul : t * d = |μ| + 1 := by
      dsimp [t, d]
      simpa using (div_mul_cancel₀ (a := (|μ| + 1)) (b := d) hd_ne)
    calc
      hAff x = t * (dotProduct x b0 - β0) := hx1
      _ = t * d := by simp [d]
      _ = |μ| + 1 := ht_mul
  have hμ_lt : (μ : EReal) < (hAff x : EReal) := by
    have hμle : μ ≤ |μ| := le_abs_self μ
    have hμlt : μ < |μ| + 1 := lt_of_le_of_lt hμle (by linarith)
    simpa [hx_eq] using (EReal.coe_lt_coe_iff.2 hμlt)
  exact ⟨hAff, hhAff, hμ_lt⟩

/-- Under directional boundedness, the conjugate of the (Real-valued) support function is the
closed convex envelope of the indicator function. -/
lemma section13_fenchelConjugate_deltaStar_eq_clConv_indicatorFunction {n : Nat}
    (C : Set (Fin n → Real)) (hCne : C.Nonempty)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) :
    fenchelConjugate n (fun xStar : Fin n → Real => ((deltaStar C xStar : ℝ) : EReal)) =
      clConv n (indicatorFunction C) := by
  have hfun :
      fenchelConjugate n (indicatorFunction C) =
        fun xStar : Fin n → Real => ((deltaStar C xStar : ℝ) : EReal) :=
    section13_fenchelConjugate_indicatorFunction_eq_deltaStar_fun (C := C) hCne hCbd
  calc
    fenchelConjugate n (fun xStar : Fin n → Real => ((deltaStar C xStar : ℝ) : EReal))
        =
        fenchelConjugate n (fenchelConjugate n (indicatorFunction C)) := by
          simpa using congrArg (fun f : (Fin n → Real) → EReal => fenchelConjugate n f) hfun.symm
    _ = clConv n (indicatorFunction C) := by
        simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := indicatorFunction C))

/-- For a nonempty convex set `C`, the closed convex envelope of `indicatorFunction C` is the
indicator function of `closure C`. -/
lemma section13_clConv_indicatorFunction_eq_indicatorFunction_closure {n : Nat}
    (C : Set (Fin n → Real)) (hC : Convex ℝ C) (hCne : C.Nonempty) :
    clConv n (indicatorFunction C) = indicatorFunction (closure C) := by
  classical
  funext x
  by_cases hxcl : x ∈ closure C
  · -- On `closure C`, every affine minorant is ≤ 0, and the constant `0` affine map attains `0`.
    have hle : clConv n (indicatorFunction C) x ≤ (0 : EReal) := by
      unfold clConv
      refine sSup_le ?_
      rintro y ⟨h, hh, rfl⟩
      have hxle0 : h x ≤ 0 :=
        section13_affine_le_indicatorFunction_le_zero_on_closure (C := C) (h := h) hh x hxcl
      exact (EReal.coe_le_coe_iff).2 hxle0
    have hge : (0 : EReal) ≤ clConv n (indicatorFunction C) x := by
      -- Use the constant affine map `0`.
      let h0 : AffineMap ℝ (Fin n → Real) Real :=
        { toFun := fun _ => 0
          linear := 0
          map_vadd' := by
            intro p v
            simp }
      have hh0 : ∀ y : Fin n → Real, (h0 y : EReal) ≤ indicatorFunction C y := by
        intro y
        by_cases hyC : y ∈ C
        · simp [h0, indicatorFunction, hyC]
        · simp [h0, indicatorFunction, hyC]
      have hxmem :
          (h0 x : EReal) ∈
            (fun h : AffineMap ℝ (Fin n → Real) Real => (h x : EReal)) '' {h |
              ∀ y : Fin n → Real, (h y : EReal) ≤ indicatorFunction C y} := by
        refine ⟨h0, hh0, rfl⟩
      -- `h0 x = 0`, hence `0 ≤ sSup …`.
      simpa [clConv, h0] using (le_sSup hxmem)
    have : clConv n (indicatorFunction C) x = (0 : EReal) := le_antisymm hle hge
    simp [indicatorFunction, hxcl, this]
  · -- Off `closure C`, the supremum is `⊤` by strong separation.
    have hxTop : clConv n (indicatorFunction C) x = ⊤ := by
      refine (EReal.eq_top_iff_forall_lt _).2 ?_
      intro μ
      rcases
          section13_exists_affineMap_le_indicatorFunction_gt_of_not_mem_closure (C := C) hC hCne
            (x := x) hxcl μ with
        ⟨h, hh, hμlt⟩
      have hxmem :
          (h x : EReal) ∈
            (fun h : AffineMap ℝ (Fin n → Real) Real => (h x : EReal)) '' {h |
              ∀ y : Fin n → Real, (h y : EReal) ≤ indicatorFunction C y} := by
        exact ⟨h, hh, rfl⟩
      have hxle : (h x : EReal) ≤ clConv n (indicatorFunction C) x := by
        simpa [clConv] using (le_sSup hxmem)
      exact lt_of_lt_of_le hμlt hxle
    simp [indicatorFunction, hxcl, hxTop]

/-- Text 13.1.5: Let `C ⊆ ℝ^n` be a convex set and let `δ(· | C)` be its indicator function. Then

`(δ^*(· | C))^* = cl δ(· | C) = δ(· | cl C)`.

In this development, `cl δ(·|C)` is represented by `clConv n (indicatorFunction C)`. -/
theorem fenchelConjugate_deltaStar_eq_clConv_indicatorFunction_eq_indicatorFunction_closure
    {n : Nat} (C : Set (Fin n → Real)) (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hCbd : ∀ xStar : Fin n → Real,
      BddAbove (Set.image (fun x : Fin n → Real => dotProduct x xStar) C)) :
    fenchelConjugate n (fun xStar : Fin n → Real => ((deltaStar C xStar : ℝ) : EReal)) =
        clConv n (indicatorFunction C) ∧
      clConv n (indicatorFunction C) = indicatorFunction (closure C) := by
  constructor
  · exact section13_fenchelConjugate_deltaStar_eq_clConv_indicatorFunction (C := C) hCne hCbd
  · exact section13_clConv_indicatorFunction_eq_indicatorFunction_closure (C := C) hC hCne

/-- Auxiliary definition: the `EReal`-valued support function
`xStar ↦ sup_{x ∈ C} ⟪x, xStar⟫`. -/
noncomputable def supportFunctionEReal {n : Nat} (C : Set (Fin n → Real)) :
    (Fin n → Real) → EReal :=
  fun xStar => sSup {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : Real) : EReal)}

/-- Text 13.1.4 (EReal version): the Fenchel conjugate of an indicator function is the
`EReal`-valued support function. -/
lemma section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal {n : Nat}
    (C : Set (Fin n → Real)) :
    fenchelConjugate n (indicatorFunction C) = supportFunctionEReal C := by
  classical
  funext xStar
  have hSup :
      fenchelConjugate n (indicatorFunction C) xStar =
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' C) :=
    section13_fenchelConjugate_indicatorFunction_eq_sSup_image_dotProduct (C := C) (xStar := xStar)
  have hset :
      ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' C) =
        {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : Real) : EReal)} := by
    ext z
    constructor
    · rintro ⟨x, hxC, rfl⟩
      exact ⟨x, hxC, rfl⟩
    · rintro ⟨x, hxC, rfl⟩
      exact ⟨x, hxC, rfl⟩
  simpa [supportFunctionEReal, hset] using hSup

/-! Auxiliary lemmas about scaling suprema in `EReal`. -/

/-- For `a > 0`, multiplication by `(a : EReal)` cancels with multiplication by `(a⁻¹ : EReal)`. -/
lemma section13_mul_mul_inv_cancel_pos_real {a : Real} (ha : 0 < a) (z : EReal) :
    ((a : Real) : EReal) * (((a⁻¹ : Real) : EReal) * z) = z := by
  cases z using EReal.rec with
  | bot =>
      simp [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_bot_of_pos (inv_pos.2 ha)]
  | top =>
      simp [EReal.coe_mul_top_of_pos ha, EReal.coe_mul_top_of_pos (inv_pos.2 ha)]
  | coe r =>
      have ha0 : a ≠ 0 := ha.ne'
      have hreal : a * (a⁻¹ * r) = r := by
        simp [ha0]
      -- Reduce to a real identity.
      change ((a * (a⁻¹ * r) : Real) : EReal) = (r : EReal)
      simp [hreal]

/-- For `a > 0`, multiplication by `(a⁻¹ : EReal)` cancels with multiplication by `(a : EReal)`. -/
lemma section13_mul_inv_mul_cancel_pos_real {a : Real} (ha : 0 < a) (z : EReal) :
    ((a⁻¹ : Real) : EReal) * (((a : Real) : EReal) * z) = z := by
  cases z using EReal.rec with
  | bot =>
      simp [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_bot_of_pos (inv_pos.2 ha)]
  | top =>
      simp [EReal.coe_mul_top_of_pos ha, EReal.coe_mul_top_of_pos (inv_pos.2 ha)]
  | coe r =>
      have ha0 : a ≠ 0 := ha.ne'
      have hreal : a⁻¹ * (a * r) = r := by
        simp [ha0]
      change ((a⁻¹ * (a * r) : Real) : EReal) = (r : EReal)
      simp [hreal]

/-- Multiplying by `(a : EReal)` for `a > 0` commutes with `iSup`. -/
lemma section13_ereal_mul_iSup_of_pos {ι : Sort _} (a : Real) (ha : 0 < a) (f : ι → EReal) :
    ((a : Real) : EReal) * iSup f = iSup fun i => ((a : Real) : EReal) * f i := by
  classical
  have ha0 : (0 : EReal) ≤ ((a : Real) : EReal) := by
    exact_mod_cast (le_of_lt ha)
  have hainv0 : (0 : EReal) ≤ ((a⁻¹ : Real) : EReal) := by
    exact_mod_cast (le_of_lt (inv_pos.2 ha))
  refine le_antisymm ?_ ?_
  · -- `a * iSup f ≤ iSup (a * f i)` by multiplying the inequality
    -- `iSup f ≤ a⁻¹ * iSup (a * f i)` with `a` on the left.
    have hle :
        iSup f ≤ ((a⁻¹ : Real) : EReal) * (iSup fun i => ((a : Real) : EReal) * f i) := by
      refine iSup_le ?_
      intro i
      have hfi : ((a : Real) : EReal) * f i ≤ iSup (fun i => ((a : Real) : EReal) * f i) :=
        le_iSup (fun i => ((a : Real) : EReal) * f i) i
      have hmul :
          f i =
            ((a⁻¹ : Real) : EReal) * (((a : Real) : EReal) * f i) := by
        simpa using (section13_mul_inv_mul_cancel_pos_real (a := a) ha (z := f i)).symm
      have : ((a⁻¹ : Real) : EReal) * (((a : Real) : EReal) * f i) ≤
          ((a⁻¹ : Real) : EReal) * (iSup fun i => ((a : Real) : EReal) * f i) :=
        mul_le_mul_of_nonneg_left hfi hainv0
      -- Rewrite `f i` using `hmul` to finish.
      calc
        f i = ((a⁻¹ : Real) : EReal) * (((a : Real) : EReal) * f i) := hmul
        _ ≤ ((a⁻¹ : Real) : EReal) * (iSup fun i => ((a : Real) : EReal) * f i) := this
    have : ((a : Real) : EReal) * iSup f ≤
        ((a : Real) : EReal) *
          (((a⁻¹ : Real) : EReal) * (iSup fun i => ((a : Real) : EReal) * f i)) :=
      mul_le_mul_of_nonneg_left hle ha0
    simpa [mul_assoc, section13_mul_mul_inv_cancel_pos_real (a := a) ha] using this
  · -- `iSup (a * f i) ≤ a * iSup f` by monotonicity of multiplication by `a ≥ 0`.
    refine iSup_le ?_
    intro i
    have hfi : f i ≤ iSup f := le_iSup (fun i => f i) i
    exact mul_le_mul_of_nonneg_left hfi ha0

/-- The Fenchel conjugate of a positive scalar multiple is the corresponding right scalar multiple
of the Fenchel conjugate. -/
lemma section13_fenchelConjugate_smul_eq_rightScalarMultiple {n : Nat}
    (f : (Fin n → Real) → EReal) (lam : Real) (hlam : 0 < lam) :
    fenchelConjugate n (fun x => ((lam : Real) : EReal) * f x) =
      rightScalarMultiple (fenchelConjugate n f) lam := by
  classical
  funext xStar
  have hconvStar : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) := by
    have : ConvexFunction (fenchelConjugate n f) := (fenchelConjugate_closedConvex (n := n) (f := f)).2
    simpa [ConvexFunction] using this
  -- Use the explicit `rightScalarMultiple` formula, and compute the conjugate as an `iSup`.
  have hxstar :
      rightScalarMultiple (fenchelConjugate n f) lam xStar =
        ((lam : Real) : EReal) * fenchelConjugate n f (lam⁻¹ • xStar) :=
    rightScalarMultiple_pos (f := fenchelConjugate n f) (lam := lam) hconvStar hlam xStar
  -- The `iSup` termwise scaling identity.
  have hterm :
      ∀ x : Fin n → Real,
        ((x ⬝ᵥ xStar : Real) : EReal) - ((lam : Real) : EReal) * f x =
          ((lam : Real) : EReal) *
            (((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - f x) := by
    intro x
    cases hx : f x using EReal.rec with
    | bot =>
        -- Both sides simplify to `⊤`.
        have hmul : ((lam : Real) : EReal) * (⊥ : EReal) = (⊥ : EReal) := by
          simp [EReal.coe_mul_bot_of_pos hlam]
        have hL :
            ((x ⬝ᵥ xStar : Real) : EReal) - ((lam : Real) : EReal) * (⊥ : EReal) = (⊤ : EReal) := by
          simp [hmul, sub_eq_add_neg]
        have hR :
            ((lam : Real) : EReal) * (((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - (⊥ : EReal)) =
              (⊤ : EReal) := by
          have : (((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - (⊥ : EReal)) = (⊤ : EReal) := by
            -- `a - ⊥ = a + ⊤ = ⊤` for `a ≠ ⊥`.
            have hne : ((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) ≠ (⊥ : EReal) :=
              EReal.coe_ne_bot (x ⬝ᵥ (lam⁻¹ • xStar) : Real)
            simpa [sub_eq_add_neg] using
              (EReal.add_top_of_ne_bot (x := ((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal)) hne)
          simpa [this] using (EReal.coe_mul_top_of_pos (x := lam) hlam)
        exact hL.trans hR.symm
    | top =>
        -- Both sides simplify to `⊥`.
        have hmul : ((lam : Real) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
          simpa using (EReal.coe_mul_top_of_pos (x := lam) hlam)
        have hL :
            ((x ⬝ᵥ xStar : Real) : EReal) - ((lam : Real) : EReal) * (⊤ : EReal) = (⊥ : EReal) := by
          simp [hmul, sub_eq_add_neg]
        have hR :
            ((lam : Real) : EReal) * (((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - (⊤ : EReal)) =
              (⊥ : EReal) := by
          have : (((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - (⊤ : EReal)) = (⊥ : EReal) := by
            simp [sub_eq_add_neg]
          simpa [this] using (EReal.coe_mul_bot_of_pos (x := lam) hlam)
        exact hL.trans hR.symm
    | coe r =>
        -- Reduce to a real identity.
        have hdot :
            (x ⬝ᵥ xStar : Real) = lam * (x ⬝ᵥ (lam⁻¹ • xStar) : Real) := by
          have : (x ⬝ᵥ (lam⁻¹ • xStar) : Real) = lam⁻¹ * (x ⬝ᵥ xStar : Real) := by
            simp [dotProduct_smul, smul_eq_mul, mul_comm]
          have hlam0 : lam ≠ 0 := ne_of_gt hlam
          calc
            (x ⬝ᵥ xStar : Real) = lam * (lam⁻¹ * (x ⬝ᵥ xStar : Real)) := by
              simp [hlam0]
            _ = lam * (x ⬝ᵥ (lam⁻¹ • xStar) : Real) := by
              simp [this]
        have hreal :
            (x ⬝ᵥ xStar : Real) - lam * r =
              lam * ((x ⬝ᵥ (lam⁻¹ • xStar) : Real) - r) := by
          have hstep : (x ⬝ᵥ xStar : Real) - lam * r =
              (lam * (x ⬝ᵥ (lam⁻¹ • xStar) : Real)) - lam * r :=
            congrArg (fun t : Real => t - lam * r) hdot
          exact hstep.trans (by ring)
        have hcoeE :
            (((x ⬝ᵥ xStar : Real) - lam * r : Real) : EReal) =
              ((lam * ((x ⬝ᵥ (lam⁻¹ • xStar) : Real) - r) : Real) : EReal) :=
          congrArg (fun t : Real => (t : EReal)) hreal
        -- Rewrite both sides as coercions of reals.
        simpa [hx, EReal.coe_mul, EReal.coe_sub] using hcoeE
  calc
    fenchelConjugate n (fun x => ((lam : Real) : EReal) * f x) xStar =
        iSup (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) -
          ((lam : Real) : EReal) * f x) := by
          simpa using (fenchelConjugate_eq_iSup (n := n) (f := fun x => ((lam : Real) : EReal) * f x)
            (xStar := xStar))
    _ = iSup fun x : Fin n → Real =>
          ((lam : Real) : EReal) * (((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - f x) := by
          simp [hterm]
    _ = ((lam : Real) : EReal) *
          iSup (fun x : Fin n → Real => ((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - f x) := by
          simpa using
            (section13_ereal_mul_iSup_of_pos (a := lam) hlam
              (f := fun x : Fin n → Real => ((x ⬝ᵥ (lam⁻¹ • xStar) : Real) : EReal) - f x)).symm
    _ = ((lam : Real) : EReal) * fenchelConjugate n f (lam⁻¹ • xStar) := by
          simp [fenchelConjugate_eq_iSup]
    _ = rightScalarMultiple (fenchelConjugate n f) lam xStar := by
          simpa using hxstar.symm

/-- A closed proper convex function is `0`/`⊤`-valued iff its Fenchel conjugate is positively
homogeneous. -/
lemma section13_only_zero_top_iff_fenchelConjugate_posHom {n : Nat}
    (f : (Fin n → Real) → EReal) (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (∀ x : Fin n → Real, f x = 0 ∨ f x = ⊤) ↔ PositivelyHomogeneous (fenchelConjugate n f) := by
  classical
  have hconvStar : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) := by
    have : ConvexFunction (fenchelConjugate n f) := (fenchelConjugate_closedConvex (n := n) (f := f)).2
    simpa [ConvexFunction] using this
  constructor
  · intro hzeroTop
    have hscale : ∀ lam : Real, 0 < lam → rightScalarMultiple (fenchelConjugate n f) lam = fenchelConjugate n f := by
      intro lam hlam
      have hmul : (fun x => ((lam : Real) : EReal) * f x) = f := by
        funext x
        rcases hzeroTop x with hx | hx
        · simp [hx]
        · simp [hx, EReal.coe_mul_top_of_pos hlam]
      calc
        rightScalarMultiple (fenchelConjugate n f) lam =
            fenchelConjugate n (fun x => ((lam : Real) : EReal) * f x) := by
              symm
              exact (section13_fenchelConjugate_smul_eq_rightScalarMultiple (n := n) (f := f) (lam := lam) hlam)
        _ = fenchelConjugate n f := by simp [hmul]
    exact
      (positivelyHomogeneous_iff_rightScalarMultiple_eq (n := n) (f := fenchelConjugate n f) hconvStar).2
        hscale
  · intro hpos
    have hscale :
        ∀ lam : Real, 0 < lam → rightScalarMultiple (fenchelConjugate n f) lam = fenchelConjugate n f :=
      (positivelyHomogeneous_iff_rightScalarMultiple_eq (n := n) (f := fenchelConjugate n f) hconvStar).1 hpos
    have hclEq : clConv n f = f :=
      clConv_eq_of_closedProperConvex (n := n) (f := f) hf_closed.2 hf_proper
    have hbiconj : fenchelConjugate n (fenchelConjugate n f) = f := by
      simpa [hclEq] using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f))
    intro x
    have hx_ne_bot : f x ≠ (⊥ : EReal) := hf_proper.2.2 x (by simp)
    -- First show `f x ≤ (lam : EReal) * f x` for all `lam > 0`.
    have hle : ∀ lam : Real, 0 < lam → f x ≤ ((lam : Real) : EReal) * f x := by
      intro lam hlam
      have hconj :
          fenchelConjugate n (fun y => ((lam : Real) : EReal) * f y) = fenchelConjugate n f := by
        calc
          fenchelConjugate n (fun y => ((lam : Real) : EReal) * f y) =
              rightScalarMultiple (fenchelConjugate n f) lam :=
            section13_fenchelConjugate_smul_eq_rightScalarMultiple (n := n) (f := f) (lam := lam) hlam
          _ = fenchelConjugate n f := hscale lam hlam
      have hcl :
          clConv n (fun y => ((lam : Real) : EReal) * f y) = f := by
        have hbi :=
          congrArg (fun g => fenchelConjugate n g) hconj
        have : clConv n (fun y => ((lam : Real) : EReal) * f y) = clConv n f := by
          simpa [fenchelConjugate_biconjugate_eq_clConv (n := n) (f := fun y => ((lam : Real) : EReal) * f y),
            fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)] using hbi
        simpa [hclEq] using this
      -- Now use `clConv ≤` scaled function.
      have : clConv n (fun y => ((lam : Real) : EReal) * f y) x ≤ ((lam : Real) : EReal) * f x :=
        clConv_le (n := n) (f := fun y => ((lam : Real) : EReal) * f y) x
      simpa [hcl] using this
    -- Deduce `f x` is `0` or `⊤` by case analysis on `f x`.
    cases hx : f x using EReal.rec with
    | bot =>
        exact (hx_ne_bot hx).elim
    | top =>
        exact Or.inr rfl
    | coe r =>
        have hle₂ : ((r : Real) : EReal) ≤ ((2 : Real) : EReal) * ((r : Real) : EReal) := by
          simpa [hx] using hle 2 (by norm_num)
        have hle_half :
            ((r : Real) : EReal) ≤ ((1 / 2 : Real) : EReal) * ((r : Real) : EReal) := by
          simpa [hx] using hle (1 / 2) (by norm_num)
        have hle₂' : r ≤ 2 * r := by
          have : ((r : Real) : EReal) ≤ ((2 * r : Real) : EReal) := by
            simpa [EReal.coe_mul, mul_assoc] using hle₂
          exact (EReal.coe_le_coe_iff.1 this)
        have hle_half' : r ≤ (1 / 2 : Real) * r := by
          have : ((r : Real) : EReal) ≤ (((1 / 2 : Real) * r : Real) : EReal) := by
            simpa [EReal.coe_mul, mul_assoc] using hle_half
          exact (EReal.coe_le_coe_iff.1 this)
        have hr0 : r = 0 := by linarith
        left
        simp [hr0]

/-- A `0`/`⊤`-valued function with no `⊥` values is an indicator function of its `0`-sublevel. -/
lemma section13_eq_indicatorFunction_setOf_le_zero_of_only_zero_top {n : Nat}
    (g : (Fin n → Real) → EReal) (hzeroTop : ∀ x : Fin n → Real, g x = 0 ∨ g x = ⊤) :
    g = indicatorFunction {x : Fin n → Real | g x ≤ (0 : EReal)} := by
  classical
  funext x
  by_cases hx : g x ≤ (0 : EReal)
  · have : g x = 0 := by
      rcases hzeroTop x with hx0 | hxtop
      · exact hx0
      · exfalso
        have hx' := hx
        simp [hxtop] at hx'
    simp [indicatorFunction, this]
  · have : g x = ⊤ := by
      rcases hzeroTop x with hx0 | hxtop
      · exfalso
        have : g x ≤ (0 : EReal) := by simp [hx0]
        exact hx this
      · exact hxtop
    simp [indicatorFunction, this]

/-- Theorem 13.2: The indicator function and the support function of a closed convex set are
conjugate to each other. The functions which are the support functions of non-empty convex sets
are the closed proper convex functions which are positively homogeneous. -/
theorem indicatorFunction_conjugate_supportFunctionEReal_of_isClosed {n : Nat}
    (C : Set (Fin n → Real)) (hC : Convex ℝ C) (hCclosed : IsClosed C) :
    fenchelConjugate n (indicatorFunction C) = supportFunctionEReal C ∧
      fenchelConjugate n (supportFunctionEReal C) = indicatorFunction C := by
  classical
  constructor
  · exact section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C)
  · by_cases hCempty : C = ∅
    · subst hCempty
      -- `supportFunctionEReal ∅ = ⊥` and `indicatorFunction ∅ = ⊤`.
      funext x
      simp [supportFunctionEReal, indicatorFunction, fenchelConjugate]
    · have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
      have hsupp :
          supportFunctionEReal C = fenchelConjugate n (indicatorFunction C) := by
        simpa using
          (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C)).symm
      calc
        fenchelConjugate n (supportFunctionEReal C) =
            fenchelConjugate n (fenchelConjugate n (indicatorFunction C)) := by
              simp [hsupp]
        _ = clConv n (indicatorFunction C) := by
              simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := indicatorFunction C))
        _ = indicatorFunction (closure C) :=
              section13_clConv_indicatorFunction_eq_indicatorFunction_closure (C := C) hC hCne
        _ = indicatorFunction C := by
              simp

/-- Theorem 13.2 (characterization of support functions): an `EReal`-valued function on `ℝ^n` is a
support function of a nonempty convex set iff it is closed, proper, convex, and positively
homogeneous. -/
theorem exists_supportFunctionEReal_iff_closedProperConvex_posHom {n : Nat}
    (f : (Fin n → Real) → EReal) :
    (∃ C : Set (Fin n → Real), Set.Nonempty C ∧ Convex ℝ C ∧ f = supportFunctionEReal C) ↔
      (ClosedConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f ∧ PositivelyHomogeneous f) := by
  classical
  constructor
  · rintro ⟨C, hCne, hCconv, rfl⟩
    have hindConv : ConvexFunction (indicatorFunction C) :=
      convexFunction_indicator_of_convex (C := C) hCconv
    have hindConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction C) := by
      simpa [ConvexFunction] using hindConv
    have hproper_ind : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction C) := by
      refine ⟨hindConvOn, ?_, ?_⟩
      · rcases hCne with ⟨x0, hx0C⟩
        refine ⟨(x0, 0), ?_⟩
        exact (mem_epigraph_univ_iff (f := indicatorFunction C)).2 (by simp [indicatorFunction, hx0C])
      · intro x hxuniv
        by_cases hxC : x ∈ C
        · simp [indicatorFunction, hxC]
        · simp [indicatorFunction, hxC]
    have h12 :=
      fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n := n) (f := indicatorFunction C)
        hindConv
    have hclosed_conv : ClosedConvexFunction (supportFunctionEReal C) := by
      have hEq := section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C)
      refine ⟨?_, ?_⟩
      · -- convexity
        have : ConvexFunction (fenchelConjugate n (indicatorFunction C)) := h12.1.2
        simpa [hEq] using this
      · -- lower semicontinuity
        have : LowerSemicontinuous (fenchelConjugate n (indicatorFunction C)) := h12.1.1
        simpa [hEq] using this
    have hproper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (supportFunctionEReal C) := by
      have hEq := section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C)
      have hproperStar :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
            (fenchelConjugate n (indicatorFunction C)) := (h12.2.1).2 hproper_ind
      simpa [hEq] using hproperStar
    -- Positive homogeneity via the `0/⊤`-valued closure of the indicator function.
    set g : (Fin n → Real) → EReal := clConv n (indicatorFunction C)
    have hg_closed : ClosedConvexFunction g := by
      have hgdef : g = fenchelConjugate n (fenchelConjugate n (indicatorFunction C)) := by
        symm
        simpa [g] using
          (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := indicatorFunction C))
      have hcc := fenchelConjugate_closedConvex (n := n) (f := fenchelConjugate n (indicatorFunction C))
      refine ⟨?_, ?_⟩
      · simpa [hgdef] using hcc.2
      · simpa [hgdef] using hcc.1
    have hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g := by
      -- Properness is preserved under taking Fenchel conjugates.
      have hproperStar : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
            (fenchelConjugate n (indicatorFunction C)) := (h12.2.1).2 hproper_ind
      have hgdef : g = fenchelConjugate n (fenchelConjugate n (indicatorFunction C)) := by
        symm
        simpa [g] using
          (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := indicatorFunction C))
      have : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
            (fenchelConjugate n (fenchelConjugate n (indicatorFunction C))) :=
        proper_fenchelConjugate_of_proper (n := n) (f := fenchelConjugate n (indicatorFunction C)) hproperStar
      simpa [hgdef] using this
    have hzeroTop_g : ∀ x : Fin n → Real, g x = 0 ∨ g x = ⊤ := by
      intro x
      -- `g` is an indicator function of `closure C`.
      have hCne' : (C : Set (Fin n → Real)).Nonempty := hCne
      have hg : g = indicatorFunction (closure C) :=
        section13_clConv_indicatorFunction_eq_indicatorFunction_closure (C := C) hCconv hCne'
      by_cases hxcl : x ∈ closure C
      · simp [hg, indicatorFunction, hxcl]
      · simp [hg, indicatorFunction, hxcl]
    have hpos :
        PositivelyHomogeneous (supportFunctionEReal C) := by
      have hEqConj :
          fenchelConjugate n g = supportFunctionEReal C := by
        -- `g` is a closure of the indicator, so it has the same conjugate.
        have hcl : fenchelConjugate n g = fenchelConjugate n (indicatorFunction C) := by
          simpa [g] using (fenchelConjugate_clConv_eq (n := n) (f := indicatorFunction C))
        simpa [section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C)] using hcl
      have hpos_conj : PositivelyHomogeneous (fenchelConjugate n g) :=
        (section13_only_zero_top_iff_fenchelConjugate_posHom (n := n) (f := g) hg_closed hg_proper).1
          hzeroTop_g
      simpa [hEqConj] using hpos_conj
    exact ⟨hclosed_conv, hproper, hpos⟩
  · rintro ⟨hf_closed, hf_proper, hf_pos⟩
    -- Let `g := f*`.
    set g : (Fin n → Real) → EReal := fenchelConjugate n f
    have hf_conv : ConvexFunction f := hf_closed.1
    have h12 :=
      fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n := n) (f := f) hf_conv
    have hg_closed : ClosedConvexFunction g := by
      refine ⟨?_, ?_⟩
      · simpa [g] using h12.1.2
      · simpa [g] using h12.1.1
    have hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g := by
      -- Properness is preserved by Fenchel conjugation.
      have : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g ↔
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
        simpa [g] using h12.2.1
      exact this.2 hf_proper
    have hg_conj_eq : fenchelConjugate n g = f := by
      have hclEq : clConv n f = f :=
        clConv_eq_of_closedProperConvex (n := n) (f := f) hf_closed.2 hf_proper
      have : fenchelConjugate n (fenchelConjugate n f) = clConv n f := h12.2.2.2
      simpa [g, hclEq] using this
    have hzeroTop_g : ∀ x : Fin n → Real, g x = 0 ∨ g x = ⊤ := by
      have hpos_conj : PositivelyHomogeneous (fenchelConjugate n g) := by simpa [hg_conj_eq] using hf_pos
      exact
        (section13_only_zero_top_iff_fenchelConjugate_posHom (n := n) (f := g) hg_closed hg_proper).2
          hpos_conj
    have hnotbot_g : ∀ x : Fin n → Real, g x ≠ ⊥ := by
      intro x
      exact hg_proper.2.2 x (by simp)
    -- Identify `g` as an indicator function of a nonempty convex set.
    set C : Set (Fin n → Real) := {x : Fin n → Real | g x ≤ (0 : EReal)}
    have hg_indicator : g = indicatorFunction C :=
      section13_eq_indicatorFunction_setOf_le_zero_of_only_zero_top (n := n) (g := g) hzeroTop_g
    have hCconv : Convex ℝ C := by
      have : ConvexFunction g := hg_closed.1
      simpa [C] using (convexFunction_level_sets_convex (f := g) this (0 : EReal)).2
    have hCne : Set.Nonempty C := by
      rcases hg_proper.2.1 with ⟨p, hp⟩
      rcases hp with ⟨_hp1, hp2⟩
      refine ⟨p.1, ?_⟩
      -- `g p.1` is not `⊤`, so it must be `0`.
      have hlt : g p.1 < (⊤ : EReal) := lt_of_le_of_lt hp2 (by simp)
      have hne_top : g p.1 ≠ (⊤ : EReal) := ne_of_lt hlt
      rcases hzeroTop_g p.1 with hp0 | hptop
      · simp [C, hp0]
      · exact (hne_top hptop).elim
    -- Conclude `f` is the support function of `C`.
    refine ⟨C, hCne, hCconv, ?_⟩
    have : fenchelConjugate n g = supportFunctionEReal C := by
      -- Use `g = indicatorFunction C`.
      simpa [hg_indicator] using
        (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (n := n) (C := C))
    -- `fenchelConjugate n g = f`.
    calc
      f = fenchelConjugate n g := hg_conj_eq.symm
      _ = supportFunctionEReal C := this

/-- The set `{xStar | ∀ x, ⟪x, xStar⟫ ≤ f x}` is the `0`-sublevel set of the Fenchel conjugate
`f*`. -/
lemma section13_setOf_forall_dotProduct_le_eq_setOf_fenchelConjugate_le_zero {n : Nat}
    (f : (Fin n → Real) → EReal) :
    {xStar : Fin n → Real |
        ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ f x} =
      {xStar : Fin n → Real | fenchelConjugate n f xStar ≤ (0 : EReal)} := by
  classical
  ext xStar
  constructor
  · intro h
    refine (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := 0)).2 ?_
    intro x
    simpa [sub_zero] using h x
  · intro h
    have hAff :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := 0)).1 h
    intro x
    simpa [sub_zero] using hAff x

/-- If there exists a strict supporting violation `f x < ⟪x, xStar⟫`, then `f*(xStar) = ⊤`. -/
lemma section13_fenchelConjugate_eq_top_of_exists_dotProduct_gt {n : Nat}
    (f : (Fin n → Real) → EReal) (hpos : PositivelyHomogeneous f) (xStar : Fin n → Real)
    (hx : ∃ x : Fin n → Real, f x < ((dotProduct x xStar : Real) : EReal)) :
    fenchelConjugate n f xStar = (⊤ : EReal) := by
  classical
  rcases hx with ⟨x0, hx0⟩
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro μ
  -- Split on whether `f x0` is `⊥` or a real value.
  cases hfx0 : f x0 using EReal.rec with
  | bot =>
      have hterm_top :
          ((dotProduct x0 xStar : Real) : EReal) - f x0 = (⊤ : EReal) := by
        simp [hfx0, sub_eq_add_neg]
      have hxmem :
          ((⊤ : EReal)) ∈ Set.range (fun x : Fin n → Real =>
              ((x ⬝ᵥ xStar : Real) : EReal) - f x) := by
        refine ⟨x0, ?_⟩
        simpa [dotProduct, hterm_top]
      have hle : (⊤ : EReal) ≤ fenchelConjugate n f xStar := by
        unfold fenchelConjugate
        exact le_sSup hxmem
      have : (μ : EReal) < (⊤ : EReal) := by simp
      exact lt_of_lt_of_le this hle
  | top =>
      -- Contradiction: `f x0 = ⊤` cannot be strictly less than a finite dot product.
      exfalso
      rw [hfx0] at hx0
      exact
        (not_lt_of_ge (le_top : ((dotProduct x0 xStar : Real) : EReal) ≤ (⊤ : EReal))) hx0
  | coe r =>
      have hr_lt : r < dotProduct x0 xStar := by
        have : ((r : Real) : EReal) < ((dotProduct x0 xStar : Real) : EReal) := by
          simpa [hfx0] using hx0
        exact (EReal.coe_lt_coe_iff.1 this)
      set d : Real := dotProduct x0 xStar - r
      have hd_pos : 0 < d := sub_pos.2 hr_lt
      have hd_ne : d ≠ 0 := ne_of_gt hd_pos
      set t : Real := (|μ| + 1) / d
      have ht_pos : 0 < t := by
        have hnum : 0 < |μ| + 1 := by
          have habs : 0 ≤ |μ| := abs_nonneg μ
          linarith
        exact div_pos hnum hd_pos
      -- Compute the scaled term and compare it with `μ`.
      have ht_mul : t * d = |μ| + 1 := by
        dsimp [t]
        simpa using (div_mul_cancel₀ (a := (|μ| + 1)) (b := d) hd_ne)
      have hμ_lt : μ < |μ| + 1 := by
        have habs : μ ≤ |μ| := le_abs_self μ
        linarith
      have hμ_lt' : (μ : EReal) < ((|μ| + 1 : Real) : EReal) :=
        (EReal.coe_lt_coe_iff).2 hμ_lt
      have hterm :
          ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0) =
            ((|μ| + 1 : Real) : EReal) := by
        have hfscale : f (t • x0) = ((t : Real) : EReal) * ((r : Real) : EReal) := by
          simpa [hfx0] using (hpos x0 t ht_pos)
        have hdot : dotProduct (t • x0) xStar = t * dotProduct x0 xStar := by
          simp [smul_eq_mul]
        have hreal :
            t * dotProduct x0 xStar - t * r = t * d := by
          dsimp [d]
          ring
        calc
          ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0)
              = ((t * dotProduct x0 xStar : Real) : EReal) - ((t * r : Real) : EReal) := by
                  simp [hdot, hfscale, EReal.coe_mul]
          _ = ((t * dotProduct x0 xStar - t * r : Real) : EReal) := by
                  simp
          _ = ((t * d : Real) : EReal) := by simp [hreal]
          _ = ((|μ| + 1 : Real) : EReal) := by simp [ht_mul]
      have hμlt_term :
          (μ : EReal) < ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0) := by
        exact lt_of_lt_of_eq hμ_lt' hterm.symm
      have hxmem :
          (((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0)) ∈
            Set.range (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) := by
        refine ⟨t • x0, ?_⟩
        simp [dotProduct_comm]
      have hle :
          ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0) ≤ fenchelConjugate n f xStar := by
        unfold fenchelConjugate
        exact le_sSup hxmem
      exact lt_of_lt_of_le hμlt_term hle

/-- If all supporting inequalities `⟪x, xStar⟫ ≤ f x` hold (and `f` is not identically `⊤`), then
`f*(xStar) = 0`. -/
lemma section13_fenchelConjugate_eq_zero_of_forall_dotProduct_le {n : Nat}
    (f : (Fin n → Real) → EReal) (hpos : PositivelyHomogeneous f)
    (hnotTop : ¬ (∀ x : Fin n → Real, f x = ⊤)) (xStar : Fin n → Real)
    (hx : ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ f x) :
    fenchelConjugate n f xStar = (0 : EReal) := by
  classical
  -- First, `f*(xStar) ≤ 0` from the affine-minorant characterization (μ = 0).
  have hle0 : fenchelConjugate n f xStar ≤ (0 : EReal) := by
    refine (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := 0)).2 ?_
    intro x
    simpa [sub_zero] using hx x
  -- Choose a point where `f` is not `⊤`; under `hx` this value must be a real number.
  rcases not_forall.1 hnotTop with ⟨x0, hx0_ne_top⟩
  have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := by
    intro hbot
    have : ((dotProduct x0 xStar : Real) : EReal) ≤ (⊥ : EReal) := by simpa [hbot] using hx x0
    have hne : ((dotProduct x0 xStar : Real) : EReal) ≠ (⊥ : EReal) :=
      EReal.coe_ne_bot (dotProduct x0 xStar)
    exact hne ((le_bot_iff).1 this)
  -- Reduce to the case `f x0 = r`.
  cases hfx0 : f x0 using EReal.rec with
  | bot => exact (hx0_ne_bot hfx0).elim
  | top => exact (hx0_ne_top hfx0).elim
  | coe r =>
      -- Use order characterization against all real bounds.
      refine (EReal.eq_of_forall_le_coe_iff (a := fenchelConjugate n f xStar) (b := (0 : EReal)) ?_)
      intro μ
      constructor
      · intro hμ
        -- If `μ < 0`, we show `μ < f*(xStar)` by scaling `x0` down, contradicting `f*(xStar) ≤ μ`.
        by_contra hμ0
        have hμ0' : ¬ 0 ≤ μ := by
          intro h
          apply hμ0
          exact_mod_cast h
        have hμlt0 : μ < 0 := lt_of_not_ge hμ0'
        -- Let `d = ⟪x0, xStar⟫ - r ≤ 0`.
        set d : Real := dotProduct x0 xStar - r
        have hd_le0 : d ≤ 0 := sub_nonpos.2 (EReal.coe_le_coe_iff.1 (by simpa [hfx0] using hx x0))
        have hμlt : (μ : EReal) < fenchelConjugate n f xStar := by
          by_cases hd0 : d = 0
          · -- Then the term at `x0` is `0`, hence `μ < 0 ≤ f*(xStar)`.
            have hd0' : dotProduct x0 xStar = r := by
              have : dotProduct x0 xStar - r = 0 := by
                simpa [d] using hd0
              linarith
            have hterm0 : ((dotProduct x0 xStar : Real) : EReal) - f x0 = (0 : EReal) := by
              calc
                ((dotProduct x0 xStar : Real) : EReal) - f x0 =
                    ((dotProduct x0 xStar - r : Real) : EReal) := by
                      simp [hfx0]
                _ = (0 : EReal) := by simp [hd0']
            have hxmem :
                ((0 : EReal)) ∈ Set.range (fun x : Fin n → Real =>
                    ((x ⬝ᵥ xStar : Real) : EReal) - f x) := by
              refine ⟨x0, ?_⟩
              simpa [dotProduct, hterm0]
            have hle : (0 : EReal) ≤ fenchelConjugate n f xStar := by
              unfold fenchelConjugate
              exact le_sSup hxmem
            have : (μ : EReal) < (0 : EReal) := by
              exact (EReal.coe_lt_coe_iff).2 hμlt0
            exact lt_of_lt_of_le this hle
          · -- If `d < 0`, pick a small `t > 0` so that `μ < t*d`.
            have hd_lt0 : d < 0 := lt_of_le_of_ne hd_le0 hd0
            -- `t := (μ / d) / 2` gives `t*d = μ/2 > μ`.
            set t : Real := (μ / d) / 2
            have ht_pos : 0 < t := by
              have hquot : 0 < μ / d := div_pos_of_neg_of_neg hμlt0 hd_lt0
              have : (0 : Real) < (2 : Real) := by norm_num
              exact div_pos hquot this
            have hμltμhalf : μ < μ / 2 := by linarith
            have hterm :
                ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0) =
                  ((μ / 2 : Real) : EReal) := by
              have hfscale : f (t • x0) = ((t : Real) : EReal) * ((r : Real) : EReal) := by
                simpa [hfx0] using (hpos x0 t ht_pos)
              have hdot : dotProduct (t • x0) xStar = t * dotProduct x0 xStar := by
                simp [smul_eq_mul]
              have ht_mul : t * d = μ / 2 := by
                dsimp [t]
                field_simp [hd0]
              have hreal :
                  t * dotProduct x0 xStar - t * r = t * d := by
                dsimp [d]
                ring
              calc
                ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0)
                    = ((t * dotProduct x0 xStar : Real) : EReal) - ((t * r : Real) : EReal) := by
                        simp [hdot, hfscale, EReal.coe_mul]
                _ = ((t * dotProduct x0 xStar - t * r : Real) : EReal) := by
                        simp
                _ = ((t * d : Real) : EReal) := by simp [hreal]
                _ = ((μ / 2 : Real) : EReal) := by simp [ht_mul]
            have hμlt_term : (μ : EReal) < ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0) := by
              have : (μ : EReal) < ((μ / 2 : Real) : EReal) := (EReal.coe_lt_coe_iff).2 hμltμhalf
              exact lt_of_lt_of_eq this hterm.symm
            have hxmem :
                (((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0)) ∈
                  Set.range (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) := by
              refine ⟨t • x0, ?_⟩
              simp [dotProduct_comm]
            have hle :
                ((dotProduct (t • x0) xStar : Real) : EReal) - f (t • x0) ≤
                    fenchelConjugate n f xStar := by
              unfold fenchelConjugate
              exact le_sSup hxmem
            exact lt_of_lt_of_le hμlt_term hle
        exact (not_lt_of_ge hμ hμlt)
      · intro hμ0
        -- If `0 ≤ μ`, then `f*(xStar) ≤ 0 ≤ μ`.
        have h0leμ : (0 : EReal) ≤ (μ : EReal) := by exact_mod_cast hμ0
        exact le_trans hle0 h0leμ

/-- Corollary 13.2.1. Let `f` be a positively homogeneous convex function which is not identically
`⊤` (`+∞`). Then `cl f` (here represented by `clConv n f`) is the support function of the closed
convex set

`C = { xStar | ∀ x, ⟪x, xStar⟫ ≤ f x }`. -/
theorem clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le {n : Nat}
    (f : (Fin n → Real) → EReal) (hpos : PositivelyHomogeneous f) (_hconv : ConvexFunction f)
    (hnotTop : ¬ (∀ x : Fin n → Real, f x = ⊤)) :
    ∃ C : Set (Fin n → Real),
      IsClosed C ∧ Convex ℝ C ∧
        clConv n f = supportFunctionEReal C ∧
          C =
            {xStar : Fin n → Real |
              ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ f x} := by
  classical
  -- Define the polar set `C` from the supporting inequalities.
  let C : Set (Fin n → Real) :=
    {xStar : Fin n → Real | ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ f x}
  have hCeq :
      C = {xStar : Fin n → Real | fenchelConjugate n f xStar ≤ (0 : EReal)} := by
    simpa [C] using (section13_setOf_forall_dotProduct_le_eq_setOf_fenchelConjugate_le_zero (n := n) f)
  -- Closedness and convexity of `C` follow from lower semicontinuity/convexity of the conjugate.
  set g : (Fin n → Real) → EReal := fenchelConjugate n f
  have hg_lsc : LowerSemicontinuous g := (fenchelConjugate_closedConvex (n := n) (f := f)).1
  have hg_conv : ConvexFunction g := (fenchelConjugate_closedConvex (n := n) (f := f)).2
  have hCclosed : IsClosed C := by
    have hclosed_pre : IsClosed (g ⁻¹' Set.Iic (0 : EReal)) :=
      hg_lsc.isClosed_preimage (y := (0 : EReal))
    -- Rewrite the preimage as the comprehension defining `C`.
    have : IsClosed {xStar : Fin n → Real | g xStar ≤ (0 : EReal)} := by
      simpa [Set.preimage, Set.mem_Iic] using hclosed_pre
    simpa [hCeq, g] using this
  have hCconv : Convex ℝ C := by
    have : Convex ℝ {xStar : Fin n → Real | g xStar ≤ (0 : EReal)} := by
      simpa using (convexFunction_level_sets_convex (f := g) hg_conv (0 : EReal)).2
    simpa [hCeq, g] using this
  -- Identify `g = f*` as an indicator function of `C`.
  have hzeroTop : ∀ xStar : Fin n → Real, g xStar = 0 ∨ g xStar = ⊤ := by
    intro xStar
    by_cases hxC :
        ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ f x
    · left
      simpa [g] using
        section13_fenchelConjugate_eq_zero_of_forall_dotProduct_le (n := n) (f := f) hpos hnotTop xStar hxC
    · right
      rcases not_forall.1 hxC with ⟨x, hx⟩
      have hxlt : f x < ((dotProduct x xStar : Real) : EReal) := lt_of_not_ge hx
      simpa [g] using
        section13_fenchelConjugate_eq_top_of_exists_dotProduct_gt (n := n) (f := f) hpos xStar ⟨x, hxlt⟩
  have hg_indicator :
      g = indicatorFunction C := by
    -- `g` is a `0/⊤`-valued function, hence an indicator of its `0`-sublevel.
    have hg0 :
        g = indicatorFunction {xStar : Fin n → Real | g xStar ≤ (0 : EReal)} :=
      section13_eq_indicatorFunction_setOf_le_zero_of_only_zero_top (n := n) (g := g) hzeroTop
    simpa [hCeq, g] using hg0
  -- Conclude `clConv f = (f*)* = δ^*(·|C)`.
  refine ⟨C, hCclosed, hCconv, ?_, rfl⟩
  calc
    clConv n f = fenchelConjugate n (fenchelConjugate n f) := by
      symm
      simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f))
    _ = fenchelConjugate n (indicatorFunction C) := by
      -- Rewrite `f*` as an indicator.
      simpa [g] using congrArg (fun h => fenchelConjugate n h) hg_indicator
    _ = supportFunctionEReal C := by
      simpa using (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (n := n) (C := C))

end Section13
end Chap03
