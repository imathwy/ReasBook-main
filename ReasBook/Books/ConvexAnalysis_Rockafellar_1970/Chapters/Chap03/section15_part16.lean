/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section10_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part15

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise

theorem lpNormEReal_isClosedGauge_and_polar {n : ℕ} {p q : ℝ} (hp : 1 < p)
    (hpq : (1 / p) + (1 / q) = 1) :
    let k : (Fin n → ℝ) → EReal := lpNormEReal (n := n) p
    let kPolar : (Fin n → ℝ) → EReal := lpNormEReal (n := n) q
    IsClosedGauge k ∧ polarGauge k = kPolar ∧ polarGauge kPolar = k ∧ IsNormGauge k ∧ IsNormGauge kPolar := by
  dsimp
  rcases lpNormEReal_isClosedGauge_and_polarGauge_eq (n := n) (p := p) (q := q) hp hpq with
    ⟨hk, hpol⟩
  have hpol' :
      polarGauge (lpNormEReal (n := n) q) = lpNormEReal (n := n) p :=
    lpNormEReal_polarGauge_eq_self_of_closedGauge (k := lpNormEReal (n := n) p)
      (kPolar := lpNormEReal (n := n) q) hk hpol
  have hnorm_p : IsNormGauge (lpNormEReal (n := n) p) :=
    lpNormEReal_isNormGauge_of_isGauge (n := n) (p := p) hk.1
  have hnorm_q : IsNormGauge (lpNormEReal (n := n) q) := by
    have hqg : IsGauge (lpNormEReal (n := n) q) := by
      simpa [hpol] using (polarGauge_isGauge (k := lpNormEReal (n := n) p))
    exact lpNormEReal_isNormGauge_of_isGauge (n := n) (p := q) hqg
  refine ⟨hk, ?_⟩
  refine ⟨hpol, ?_⟩
  refine ⟨hpol', ?_⟩
  exact ⟨hnorm_p, hnorm_q⟩

/-- Rewrite the quadratic form using `quadraticHalfLinear` and `Matrix.toLin'`. -/
lemma matrix_quadraticHalf_eq_quadraticHalfLinear {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    (fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal)) =
      quadraticHalfLinear n (Matrix.toLin' Q) := by
  funext x
  simp [quadraticHalfLinear]

/-- The quadratic form is positively homogeneous of degree `2`. -/
lemma matrix_quadratic_posHomogeneous {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    PositivelyHomogeneousOfDegree (n := n) 2
      (fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal)) := by
  intro x t ht
  have hdot :
      (t • x) ⬝ᵥ Q.mulVec (t • x) = t ^ 2 * (x ⬝ᵥ Q.mulVec x) := by
    calc
      (t • x) ⬝ᵥ Q.mulVec (t • x) = t • (x ⬝ᵥ Q.mulVec (t • x)) := by
        simp [smul_dotProduct]
      _ = t • (x ⬝ᵥ t • Q.mulVec x) := by
        simp [Matrix.mulVec_smul]
      _ = t • (t • (x ⬝ᵥ Q.mulVec x)) := by
        simp [dotProduct_smul]
      _ = t ^ 2 * (x ⬝ᵥ Q.mulVec x) := by
        simp [smul_eq_mul, pow_two, mul_assoc]
  have hreal :
      (1 / 2 : ℝ) * ((t • x) ⬝ᵥ Q.mulVec (t • x)) =
        Real.rpow t 2 * ((1 / 2 : ℝ) * (x ⬝ᵥ Q.mulVec x)) := by
    calc
      (1 / 2 : ℝ) * ((t • x) ⬝ᵥ Q.mulVec (t • x)) =
          (1 / 2 : ℝ) * (t ^ 2 * (x ⬝ᵥ Q.mulVec x)) := by
            simp [hdot]
      _ = Real.rpow t 2 * ((1 / 2 : ℝ) * (x ⬝ᵥ Q.mulVec x)) := by
            calc
              (1 / 2 : ℝ) * (t ^ 2 * (x ⬝ᵥ Q.mulVec x)) =
                  t ^ 2 * ((1 / 2 : ℝ) * (x ⬝ᵥ Q.mulVec x)) := by
                    simp [mul_assoc, mul_left_comm, mul_comm]
              _ = Real.rpow t 2 * ((1 / 2 : ℝ) * (x ⬝ᵥ Q.mulVec x)) := by
                    simp
  have hreal' :
      (((1 / 2 : ℝ) * ((t • x) ⬝ᵥ Q.mulVec (t • x)) : ℝ) : EReal) =
        (((Real.rpow t 2) * ((1 / 2 : ℝ) * (x ⬝ᵥ Q.mulVec x)) : ℝ) : EReal) := by
    exact_mod_cast hreal
  calc
    (((1 / 2 : ℝ) * ((t • x) ⬝ᵥ Q.mulVec (t • x)) : ℝ) : EReal) =
        (((Real.rpow t 2) * ((1 / 2 : ℝ) * (x ⬝ᵥ Q.mulVec x)) : ℝ) : EReal) := hreal'
    _ =
        ((Real.rpow t 2 : ℝ) : EReal) *
          (((1 / 2 : ℝ) * (x ⬝ᵥ Q.mulVec x) : ℝ) : EReal) := by
        simp [EReal.coe_mul]

/-- The quadratic form from a positive definite matrix is closed, convex, and proper. -/
lemma matrix_quadratic_closedConvex_and_proper {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQpos : Matrix.PosDef Q) :
    ClosedConvexFunction (fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal)) := by
  classical
  let g0 : (Fin n → ℝ) → ℝ := fun x => (1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g0 (x : Fin n → ℝ)
  let gLin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := Fin n → ℝ)).toLinearMap
  have hconv0 :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) g0 := by
    simpa [g0] using
      (posSemidef_implies_convexity_quadratic (n := n) (Q := Q) (a := 0) (α := 0)
        (hpos := hQpos.posSemidef))
  have hconv :
      ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) g := by
    have hconv' :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (Fin n → ℝ))) (f := g0) hconv0 gLin
    simpa [g, g0, gLin, WithLp.coe_linearEquiv] using hconv'
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ => (g (WithLp.toLp (p := 2) x) : EReal)) :=
    Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn (n := n) (f := g) hconv
  have hclosed :
      ClosedConvexFunction
        (fun x : Fin n → ℝ => (g (WithLp.toLp (p := 2) x) : EReal)) :=
    Section10.closedConvexFunction_coe_comp_toLp_of_convexOn (n := n) (f := g) hconv
  have hsimpa :
      (fun x : Fin n → ℝ => (g (WithLp.toLp (p := 2) x) : EReal)) =
        fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal) := by
    funext x
    simp [g, g0, EReal.coe_mul]
  refine ⟨?_, ?_⟩
  · simpa [hsimpa] using hclosed
  · simpa [hsimpa] using hproper

/-- The Fenchel conjugate of the quadratic form under positive definiteness. -/
lemma fenchelConjugate_matrix_quadraticHalf_of_posDef {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q) :
    fenchelConjugate n (fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal)) =
      fun xStar => (((1 / 2 : ℝ) * (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar))) : EReal) := by
  classical
  haveI : Invertible Q := (Matrix.PosDef.isUnit (M := Q) hQpos).invertible
  let Qlin : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' Q
  let QlinInv : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' (Q⁻¹)
  let L : Submodule ℝ (Fin n → ℝ) := LinearMap.range Qlin
  let P_L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := LinearMap.id
  have hQQ' : Qlin.comp QlinInv = P_L := by
    simp [Qlin, QlinInv, P_L, (Matrix.toLin'_mul Q (Q⁻¹)).symm,
      Matrix.mul_inv_of_invertible, Matrix.toLin'_one]
  have hQ'Q : QlinInv.comp Qlin = P_L := by
    simp [Qlin, QlinInv, P_L, (Matrix.toLin'_mul (Q⁻¹) Q).symm,
      Matrix.inv_mul_of_invertible, Matrix.toLin'_one]
  have hP_L_id :
      ∀ xStar : Fin n → ℝ, xStar ∈ L → P_L xStar = xStar := by
    intro xStar hxStar
    simp [P_L]
  have hQsymm' : ∀ x y : Fin n → ℝ, (Qlin x) ⬝ᵥ y = x ⬝ᵥ Qlin y := by
    intro x y
    calc
      (Qlin x) ⬝ᵥ y = y ⬝ᵥ (Qlin x) := by simp [dotProduct_comm]
      _ = (Matrix.vecMul y Q) ⬝ᵥ x := by
        simp [Qlin, Matrix.dotProduct_mulVec]
      _ = (Q.transpose.mulVec y) ⬝ᵥ x := by
        simpa using congrArg (fun v => v ⬝ᵥ x) (Matrix.mulVec_transpose Q y).symm
      _ = (Q.mulVec y) ⬝ᵥ x := by
        simp [Matrix.IsSymm.eq hQsymm]
      _ = x ⬝ᵥ Qlin y := by simp [Qlin, dotProduct_comm]
  have hQpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ Qlin x := by
    intro x
    exact Matrix.PosSemidef.dotProduct_mulVec_nonneg hQpos.posSemidef x
  have hconj :=
    fenchelConjugate_quadraticHalfLinear_pseudoinverse (n := n) (Q := Qlin) (Q' := QlinInv)
      (P_L := P_L) (L := L) (hL := rfl) hQQ' hQ'Q hP_L_id hQsymm' hQpsd
  have hxStar_mem : ∀ xStar : Fin n → ℝ, xStar ∈ L := by
    intro xStar
    refine ⟨QlinInv xStar, ?_⟩
    have hcomp := congrArg (fun T => T xStar) hQQ'
    dsimp [P_L, LinearMap.comp_apply] at hcomp
    exact hcomp
  have hconj' :
      fenchelConjugate n (quadraticHalfLinear n Qlin) =
        fun xStar => quadraticHalfLinear n QlinInv xStar := by
    ext xStar
    have hxStar := hxStar_mem xStar
    simp [hconj, hxStar]
  have hQlin :
      quadraticHalfLinear n Qlin =
        fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal) := by
    simpa using (matrix_quadraticHalf_eq_quadraticHalfLinear (Q := Q)).symm
  have hQlinInv :
      quadraticHalfLinear n QlinInv =
        fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ ((Q⁻¹).mulVec x))) : EReal) := by
    simpa using (matrix_quadraticHalf_eq_quadraticHalfLinear (Q := Q⁻¹)).symm
  simpa [hQlin, hQlinInv] using hconj'

/-- Text 15.0.25: Let `Q` be a symmetric positive definite `n × n` matrix and define
`f(x) = (1/2) * ⟪x, Q x⟫`. Then `f` is a closed proper convex function on `ℝⁿ` and its Fenchel
conjugate satisfies `f^*(x⋆) = (1/2) * ⟪x⋆, Q⁻¹ x⋆⟫`.

Since `f` is positively homogeneous of degree `2`, Corollary 15.3.2 implies that
`k(x) = ⟪x, Q x⟫^{1/2}` is a closed gauge (in fact, a norm) whose polar is
`k^∘(x⋆) = ⟪x⋆, Q⁻¹ x⋆⟫^{1/2}`. -/
theorem matrix_quadratic_closedProperConvex_and_fenchelConjugate {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q) :
    let f : (Fin n → ℝ) → EReal := fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal)
    ClosedConvexFunction f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
        fenchelConjugate n f =
          fun xStar => (((1 / 2 : ℝ) * (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar))) : EReal) := by
  set f : (Fin n → ℝ) → EReal :=
    fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal) with hf
  have hf_closed_proper := matrix_quadratic_closedConvex_and_proper (Q := Q) hQpos
  have hconj := fenchelConjugate_matrix_quadraticHalf_of_posDef (Q := Q) hQsymm hQpos
  refine ⟨?_, ?_, ?_⟩
  · simpa [hf] using hf_closed_proper.1
  · simpa [hf] using hf_closed_proper.2
  · simpa [hf] using hconj

/-- Text 15.0.25 (gauge/polar): with `Q` symmetric positive definite, the map
`k(x) = ⟪x, Q x⟫^{1/2}` is a closed norm gauge and `kᵒ(x⋆) = ⟪x⋆, Q⁻¹ x⋆⟫^{1/2}`. -/
theorem matrix_quadraticGauge_isClosedGauge_isNormGauge_and_polar {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q) :
    let k : (Fin n → ℝ) → EReal := fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)
    let kStar : (Fin n → ℝ) → EReal :=
      fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal)
    IsClosedGauge k ∧ IsNormGauge k ∧ polarGauge k = kStar := by
  classical
  set f : (Fin n → ℝ) → EReal :=
    fun x => (((1 / 2 : ℝ) * (x ⬝ᵥ (Q.mulVec x))) : EReal) with hf
  have hf_closed_proper := matrix_quadratic_closedConvex_and_proper (Q := Q) hQpos
  have hf_hom := matrix_quadratic_posHomogeneous (Q := Q)
  have hf_props :
      ClosedConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
          PositivelyHomogeneousOfDegree (n := n) 2 f := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [hf] using hf_closed_proper.1
    · simpa [hf] using hf_closed_proper.2
    · simpa [hf] using hf_hom
  have hcor :=
    closedGauge_rpow_mul_and_polar_eq_of_closedProperConvex_posHomogeneous (n := n) (p := 2)
      (q := 2) (hp := by norm_num) (hpq := by norm_num) (f := f) hf_props.1 hf_props.2.1
      hf_props.2.2
  have hcor' :
      let k0 : (Fin n → ℝ) → EReal :=
        fun x => phiPow (1 / 2) (((2 : ℝ) : EReal) * f x)
      let kStar0 : (Fin n → ℝ) → EReal :=
        fun xStar => phiPow (1 / 2) (((2 : ℝ) : EReal) * fenchelConjugate n f xStar)
      IsClosedGauge k0 ∧ polarGauge k0 = kStar0 := by
    simpa using hcor
  rcases hcor' with ⟨hk0, hpol0⟩
  have hnonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ Q.mulVec x := by
    intro x
    exact Matrix.PosSemidef.dotProduct_mulVec_nonneg hQpos.posSemidef x
  have hnonneg_inv : ∀ xStar : Fin n → ℝ, 0 ≤ xStar ⬝ᵥ (Q⁻¹).mulVec xStar := by
    intro xStar
    have hQinv : Matrix.PosDef (Q⁻¹) := Matrix.PosDef.inv (M := Q) hQpos
    by_cases hx : xStar = 0
    · simp [hx]
    · have hpos : 0 < xStar ⬝ᵥ (Q⁻¹).mulVec xStar := by
        simpa using hQinv.dotProduct_mulVec_pos hx
      exact le_of_lt hpos
  have hk_eq :
      (fun x => phiPow (1 / 2) (((2 : ℝ) : EReal) * f x)) =
        fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) := by
    funext x
    have hmul : (((2 : ℝ) : EReal) * f x) = ((x ⬝ᵥ Q.mulVec x : ℝ) : EReal) := by
      set q : ℝ := x ⬝ᵥ Q.mulVec x
      simp [hf]
      rw [← EReal.coe_mul]
      have hmul_real : (2 : ℝ) * (2⁻¹ * q) = q := by
        simp
      exact_mod_cast hmul_real
    have hmax : max (x ⬝ᵥ Q.mulVec x) 0 = x ⬝ᵥ Q.mulVec x := by
      exact max_eq_left (hnonneg x)
    simp [hmul, phiPow, hmax, Real.sqrt_eq_rpow]
  have hconj :
      fenchelConjugate n f =
        fun xStar => (((1 / 2 : ℝ) * (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar))) : EReal) := by
    simpa [hf] using (fenchelConjugate_matrix_quadraticHalf_of_posDef (Q := Q) hQsymm hQpos)
  have hkStar_eq :
      (fun xStar => phiPow (1 / 2) (((2 : ℝ) : EReal) * fenchelConjugate n f xStar)) =
        fun xStar =>
          ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) := by
    funext xStar
    have hmul :
        (((2 : ℝ) : EReal) * fenchelConjugate n f xStar) =
          ((xStar ⬝ᵥ (Q⁻¹).mulVec xStar : ℝ) : EReal) := by
      set q : ℝ := xStar ⬝ᵥ (Q⁻¹).mulVec xStar
      simp [hconj]
      rw [← EReal.coe_mul]
      have hmul_real : (2 : ℝ) * (2⁻¹ * q) = q := by
        simp
      exact_mod_cast hmul_real
    have hmax : max (xStar ⬝ᵥ (Q⁻¹).mulVec xStar) 0 = xStar ⬝ᵥ (Q⁻¹).mulVec xStar := by
      exact max_eq_left (hnonneg_inv xStar)
    simp [hmul, phiPow, hmax, Real.sqrt_eq_rpow]
  have hk_eq' :
      (fun x => phiPow 2⁻¹ (((2 : ℝ) : EReal) * f x)) =
        fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) := by
    simpa [one_div] using hk_eq
  have hkStar_eq' :
      (fun xStar => phiPow 2⁻¹ (((2 : ℝ) : EReal) * fenchelConjugate n f xStar)) =
        fun xStar =>
          ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) := by
    simpa [one_div] using hkStar_eq
  have hk : IsClosedGauge (fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)) := by
    simpa [hk_eq'] using hk0
  have hpol :
      polarGauge (fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)) =
        fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) := by
    simpa [hk_eq', hkStar_eq'] using hpol0
  have hnorm :
      IsNormGauge (fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)) := by
    refine ⟨hk.1, ?_, ?_, ?_⟩
    · intro x
      simp
    · intro x
      have : (-x) ⬝ᵥ Q.mulVec (-x) = x ⬝ᵥ Q.mulVec x := by
        simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct]
      simp [this]
    · intro x hx
      have hpos : 0 < x ⬝ᵥ Q.mulVec x := by
        simpa using hQpos.dotProduct_mulVec_pos hx
      have hpos' : 0 < Real.sqrt (x ⬝ᵥ Q.mulVec x) := (Real.sqrt_pos.mpr hpos)
      exact (EReal.coe_lt_coe_iff.2 hpos')
  refine ⟨hk, hnorm, hpol⟩

/-- The quadratic sublevel set agrees with the unit sublevel of its square-root gauge. -/
lemma matrix_quadraticSublevel_eq_unitSublevel_sqrt {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    {x | x ⬝ᵥ (Q.mulVec x) ≤ (1 : ℝ)} =
      {x | ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) ≤ (1 : EReal)} := by
  ext x
  constructor
  · intro hx
    exact (EReal.coe_le_coe_iff).2 ((Real.sqrt_le_one).2 hx)
  · intro hx
    exact (Real.sqrt_le_one).1 ((EReal.coe_le_coe_iff).1 hx)

/-- The inverse quadratic sublevel set agrees with the unit sublevel of its square-root gauge. -/
lemma matrix_quadraticInvSublevel_eq_unitSublevel_sqrt {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    {xStar | ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) ≤ (1 : EReal)} =
      {xStar | xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ)} := by
  ext xStar
  constructor
  · intro hx
    exact (Real.sqrt_le_one).1 ((EReal.coe_le_coe_iff).1 hx)
  · intro hx
    exact (EReal.coe_le_coe_iff).2 ((Real.sqrt_le_one).2 hx)

/-- Text 15.0.26: Let `Q` be a symmetric positive definite `n × n` matrix. Define the convex set
`C = {x | ⟪x, Q x⟫ ≤ 1}`. Then its polar (with respect to the pairing `⟪x, x⋆⟫`) is
`C^∘ = {x⋆ | ⟪x⋆, Q⁻¹ x⋆⟫ ≤ 1}`. -/
theorem matrix_quadraticSublevel_polar {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm)
    (hQpos : Matrix.PosDef Q) :
    let C : Set (Fin n → ℝ) := {x | x ⬝ᵥ (Q.mulVec x) ≤ (1 : ℝ)}
    {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} = {xStar | xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ)} := by
  classical
  intro C
  set k : (Fin n → ℝ) → EReal := fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) with hk_def
  set kStar : (Fin n → ℝ) → EReal :=
    fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) with hkStar_def
  have hk_all :
      IsClosedGauge k ∧ IsNormGauge k ∧ polarGauge k = kStar := by
    simpa [hk_def, hkStar_def] using
      (matrix_quadraticGauge_isClosedGauge_isNormGauge_and_polar (Q := Q) hQsymm hQpos)
  rcases hk_all with ⟨-, hk_norm, hpol⟩
  have hk_gauge : IsGauge k := hk_norm.1
  have hC : C = {x | k x ≤ (1 : EReal)} := by
    simpa [C, hk_def] using (matrix_quadraticSublevel_eq_unitSublevel_sqrt (Q := Q))
  have hpolar :
      {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} =
        {xStar | polarGauge k xStar ≤ (1 : EReal)} := by
    simpa [hC] using (unitSublevel_polarGauge_eq_polarSet (k := k) hk_gauge).symm
  have hpol' :
      {xStar | polarGauge k xStar ≤ (1 : EReal)} = {xStar | kStar xStar ≤ (1 : EReal)} := by
    ext xStar
    simp [hpol]
  calc
    {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} =
        {xStar | polarGauge k xStar ≤ (1 : EReal)} := hpolar
    _ = {xStar | kStar xStar ≤ (1 : EReal)} := hpol'
    _ = {xStar | xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ)} := by
      simpa [hkStar_def] using (matrix_quadraticInvSublevel_eq_unitSublevel_sqrt (Q := Q))

/-- `Ring.inverse` on a unit-valued function agrees with pointwise inversion. -/
lemma ring_inverse_apply_of_isUnit {ι : Type*} (v : ι → ℝ) (hv : IsUnit v) (i : ι) :
    Ring.inverse v i = (v i)⁻¹ := by
  have h := Ring.inverse_of_isUnit (x := v) hv
  have h' := congrArg (fun f => f i) h
  simpa [IsUnit.val_inv_apply] using h'

/-- Quadratic form of a diagonal matrix on `Fin 2`. -/
lemma polar_ellipticDisk_quadraticForm_diagonal_fun_fin2 (v : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ ((Matrix.diagonal v).mulVec x) = v 0 * (x 0)^2 + v 1 * (x 1)^2 := by
  classical
  simp [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two, pow_two, mul_left_comm]

/-- The diagonal matrix for the elliptic disk is positive definite. -/
lemma polar_ellipticDisk_posDef_diagonal {α₁ α₂ : ℝ} (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0) :
    Matrix.PosDef (Matrix.diagonal ![(α₁ ^ 2)⁻¹, (α₂ ^ 2)⁻¹]) := by
  classical
  refine (Matrix.posDef_diagonal_iff).2 ?_
  intro i
  fin_cases i
  · have h : 0 < α₁ ^ 2 := sq_pos_of_ne_zero hα₁
    simpa using (inv_pos.mpr h)
  · have h : 0 < α₂ ^ 2 := sq_pos_of_ne_zero hα₂
    simpa using (inv_pos.mpr h)

/-- Quadratic form for the inverse diagonal matrix in the elliptic disk. -/
lemma polar_ellipticDisk_quadraticForm_inv_diagonal_fin2 {α₁ α₂ : ℝ} (hα₁ : α₁ ≠ 0)
    (hα₂ : α₂ ≠ 0) (x : Fin 2 → ℝ) :
    let Q : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![(α₁ ^ 2)⁻¹, (α₂ ^ 2)⁻¹]
    x ⬝ᵥ ((Q⁻¹).mulVec x) = α₁ ^ 2 * (x 0)^2 + α₂ ^ 2 * (x 1)^2 := by
  classical
  intro Q
  let v : Fin 2 → ℝ := ![(α₁ ^ 2)⁻¹, (α₂ ^ 2)⁻¹]
  have hunit : IsUnit v := by
    refine (Pi.isUnit_iff).2 ?_
    intro i
    fin_cases i
    · exact (isUnit_iff_ne_zero).2 (inv_ne_zero (pow_ne_zero 2 hα₁))
    · exact (isUnit_iff_ne_zero).2 (inv_ne_zero (pow_ne_zero 2 hα₂))
  have hdiag : Q⁻¹ = Matrix.diagonal (Ring.inverse v) := by
    simp [Q, v, Matrix.inv_diagonal]
  have hform :
      x ⬝ᵥ ((Matrix.diagonal (Ring.inverse v)).mulVec x) =
        Ring.inverse v 0 * (x 0)^2 + Ring.inverse v 1 * (x 1)^2 := by
    simpa using
      (polar_ellipticDisk_quadraticForm_diagonal_fun_fin2 (v := Ring.inverse v) (x := x))
  calc
    x ⬝ᵥ ((Q⁻¹).mulVec x) =
        Ring.inverse v 0 * (x 0)^2 + Ring.inverse v 1 * (x 1)^2 := by
          simpa [hdiag] using hform
    _ = α₁ ^ 2 * (x 0)^2 + α₂ ^ 2 * (x 1)^2 := by
      simp [v, ring_inverse_apply_of_isUnit, hunit, inv_inv]

/-- Text 15.0.27: Let `C ⊆ ℝ²` be the elliptic disk

`C = {(ξ₁, ξ₂) | (ξ₁^2 / α₁^2) + (ξ₂^2 / α₂^2) ≤ 1}`.

Then its polar set is the elliptic disk

`C^∘ = {(ξ₁⋆, ξ₂⋆) | α₁^2 * (ξ₁⋆)^2 + α₂^2 * (ξ₂⋆)^2 ≤ 1}`. -/
theorem polar_ellipticDisk {α₁ α₂ : ℝ} (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0) :
    let C : Set (Fin 2 → ℝ) :=
      {x | (x 0) ^ 2 / α₁ ^ 2 + (x 1) ^ 2 / α₂ ^ 2 ≤ (1 : ℝ)}
    {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} =
      {xStar | α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)} := by
  classical
  intro C
  let Q : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![(α₁ ^ 2)⁻¹, (α₂ ^ 2)⁻¹]
  have hQsymm : Q.IsSymm := by
    simp [Q]
  have hQpos : Matrix.PosDef Q := by
    simpa [Q] using (polar_ellipticDisk_posDef_diagonal (α₁ := α₁) (α₂ := α₂) hα₁ hα₂)
  have hC : {x | x ⬝ᵥ (Q.mulVec x) ≤ (1 : ℝ)} = C := by
    ext x
    simp [C, Q, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two, pow_two,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hpolar :
      {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} =
        {xStar | xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ)} := by
    rw [← hC]
    exact (matrix_quadraticSublevel_polar (Q := Q) hQsymm hQpos)
  have hQinv :
      {xStar | xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ)} =
        {xStar | α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)} := by
    ext xStar
    have hq :
        xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) =
          α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 := by
      simpa [Q] using
        (polar_ellipticDisk_quadraticForm_inv_diagonal_fin2 (α₁ := α₁) (α₂ := α₂)
          hα₁ hα₂ (x := xStar))
    constructor
    · intro hx
      change α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)
      have hx' : xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ) := hx
      calc
        α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 =
            xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) := by
              symm
              exact hq
        _ ≤ (1 : ℝ) := hx'
    · intro hx
      change xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ)
      have hx' : α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ) := hx
      calc
        xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) =
            α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 := hq
        _ ≤ (1 : ℝ) := hx'
  calc
    {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} =
        {xStar | xStar ⬝ᵥ ((Q⁻¹).mulVec xStar) ≤ (1 : ℝ)} := hpolar
    _ =
        {xStar | α₁ ^ 2 * (xStar 0) ^ 2 + α₂ ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)} := hQinv

/-- Convexity of the composition `g ∘ k` for the quadratic norm gauge. -/
lemma matrix_quadraticGauge_comp_convex {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q)
    (g : EReal → EReal)
    (hgζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥)
    (hg_mono : Monotone g)
    (hg_convex :
      ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))
    (hg_closed :
      IsClosed (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))) :
    let k : (Fin n → ℝ) → EReal := fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)
    let f : (Fin n → ℝ) → EReal := fun x => g (k x)
    ConvexFunction f := by
  classical
  set k : (Fin n → ℝ) → EReal :=
    fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) with hk_def
  set f : (Fin n → ℝ) → EReal := fun x => g (k x) with hf_def
  have hk_all :
      IsClosedGauge k ∧ IsNormGauge k ∧
        polarGauge k =
          fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) := by
    simpa [hk_def] using
      (matrix_quadraticGauge_isClosedGauge_isNormGauge_and_polar (Q := Q) hQsymm hQpos)
  rcases hk_all with ⟨-, hk_norm, -⟩
  have hk_gauge : IsGauge k := hk_norm.1
  have h0_ne_bot : g (0 : EReal) ≠ ⊥ :=
    g0_ne_bot_of_convex_closed_and_exists_finite_nonneg (g := g) hg_convex hg_closed hgζ
  have hnotbot_f : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f x ≠ ⊥ := by
    intro x hx
    have hk_nonneg : (0 : EReal) ≤ k x := hk_gauge.2.1 x
    exact monotone_ne_bot_of_nonneg (g := g) hg_mono h0_ne_bot (k x) hk_nonneg
  have hnotbot_k : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), k x ≠ ⊥ := by
    intro x hx
    exact IsGauge.ne_bot hk_gauge x
  have hseg_k :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)),
        ∀ y ∈ (Set.univ : Set (Fin n → ℝ)),
          ∀ t : ℝ, 0 < t → t < 1 →
            k ((1 - t) • x + t • y) ≤
              ((1 - t : ℝ) : EReal) * k x + ((t : ℝ) : EReal) * k y :=
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → ℝ))) (f := k)
        (hC := convex_univ) (hnotbot := hnotbot_k)).1 hk_gauge.1
  let S : Set (Fin 1 → ℝ) := {t : Fin 1 → ℝ | 0 ≤ t 0}
  have hSconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    have hx0 : 0 ≤ x 0 := hx
    have hy0 : 0 ≤ y 0 := hy
    have hcomb : 0 ≤ a * x 0 + b * y 0 := by nlinarith
    simpa [S, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcomb
  have hnotbot_g : ∀ t ∈ S, g (t 0 : EReal) ≠ ⊥ := by
    intro t ht
    have ht0 : 0 ≤ t 0 := by simpa [S] using ht
    have hmono_ne_bot := monotone_ne_bot_of_nonneg (g := g) hg_mono h0_ne_bot
    exact hmono_ne_bot (t 0 : EReal) (by exact_mod_cast ht0)
  have hseg_g :
      ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 < t → t < 1 →
        g (((1 - t) • x + t • y) 0 : EReal) ≤
          ((1 - t : ℝ) : EReal) * g (x 0 : EReal) + ((t : ℝ) : EReal) * g (y 0 : EReal) :=
    (convexFunctionOn_iff_segment_inequality (C := S)
        (f := fun t : Fin 1 → ℝ => g (t 0 : EReal)) (hC := hSconv) (hnotbot := hnotbot_g)).1
      hg_convex
  have hseg_f :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)),
        ∀ y ∈ (Set.univ : Set (Fin n → ℝ)),
          ∀ t : ℝ, 0 < t → t < 1 →
            f ((1 - t) • x + t • y) ≤
              ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
    intro x hx y hy t ht0 ht1
    have hk_ineq := hseg_k x (by simp) y (by simp) t ht0 ht1
    have hmono_ineq :
        g (k ((1 - t) • x + t • y)) ≤
          g (((1 - t : ℝ) : EReal) * k x + ((t : ℝ) : EReal) * k y) := hg_mono hk_ineq
    set rx : ℝ := Real.sqrt (x ⬝ᵥ (Q.mulVec x)) with hrx
    set ry : ℝ := Real.sqrt (y ⬝ᵥ (Q.mulVec y)) with hry
    have hkx : k x = (rx : EReal) := by simp [hk_def, hrx]
    have hky : k y = (ry : EReal) := by simp [hk_def, hry]
    have hcomb :
        ((1 - t : ℝ) : EReal) * k x + ((t : ℝ) : EReal) * k y =
          (((1 - t) * rx + t * ry : ℝ) : EReal) := by
      simp [hkx, hky, EReal.coe_mul, EReal.coe_add]
    let tx : Fin 1 → ℝ := fun _ => rx
    let ty : Fin 1 → ℝ := fun _ => ry
    have htx : tx ∈ S := by
      simp [S, tx, hrx, Real.sqrt_nonneg]
    have hty : ty ∈ S := by
      simp [S, ty, hry, Real.sqrt_nonneg]
    have hseg_g' := hseg_g tx htx ty hty t ht0 ht1
    have hconv_g' :
        g (((1 - t) * rx + t * ry : ℝ) : EReal) ≤
          ((1 - t : ℝ) : EReal) * g (rx : EReal) + ((t : ℝ) : EReal) * g (ry : EReal) := by
      simpa [tx, ty, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hseg_g'
    have hmono_ineq' :
        f ((1 - t) • x + t • y) ≤ g (((1 - t) * rx + t * ry : ℝ) : EReal) := by
      simpa [hf_def, hkx, hky, hcomb] using hmono_ineq
    have hconv_g'' :
        g (((1 - t) * rx + t * ry : ℝ) : EReal) ≤
          ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
      simpa [hf_def, hkx, hky] using hconv_g'
    exact hmono_ineq'.trans hconv_g''
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    refine (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → ℝ)))
        (f := f) (hC := convex_univ) (hnotbot := hnotbot_f)).2 ?_
    exact hseg_f
  simpa [ConvexFunction] using hconv_on

/-- Lower semicontinuity of `g ∘ k` from the closed epigraph of `g`. -/
lemma matrix_quadraticGauge_comp_lowerSemicontinuous {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q)
    (g : EReal → EReal)
    (hg_closed :
      IsClosed (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))) :
    let k : (Fin n → ℝ) → EReal := fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)
    let f : (Fin n → ℝ) → EReal := fun x => g (k x)
    LowerSemicontinuous f := by
  classical
  set k : (Fin n → ℝ) → EReal :=
    fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) with hk_def
  set f : (Fin n → ℝ) → EReal := fun x => g (k x) with hf_def
  have hk_all :
      IsClosedGauge k ∧ IsNormGauge k ∧
        polarGauge k =
          fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) := by
    simpa [hk_def] using
      (matrix_quadraticGauge_isClosedGauge_isNormGauge_and_polar (Q := Q) hQsymm hQpos)
  rcases hk_all with ⟨-, hk_norm, -⟩
  have hk_cont : Continuous k := normGauge_continuous (k := k) hk_norm
  have hmaps : Set.MapsTo k (Set.univ : Set (Fin n → ℝ)) ({⊥, ⊤}ᶜ : Set EReal) := by
    intro x hx
    have hne_top : k x ≠ (⊤ : EReal) := hk_norm.2.1 x
    have hne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk_norm.1 x
    simp [Set.mem_compl_iff, Set.mem_insert_iff, hne_bot, hne_top]
  have hkReal_cont : Continuous (fun x : Fin n → ℝ => (k x).toReal) := by
    have hcontOn :
        ContinuousOn (fun x : Fin n → ℝ => (k x).toReal) (Set.univ : Set (Fin n → ℝ)) :=
      (EReal.continuousOn_toReal).comp hk_cont.continuousOn hmaps
    simpa using (continuousOn_univ).1 hcontOn
  let Phi : ((Fin n → ℝ) × ℝ) → (Fin 1 → ℝ) × ℝ :=
    fun p => (fun _ : Fin 1 => (k p.1).toReal, p.2)
  have hcont_Phi : Continuous Phi := by
    have hcont_kReal :
        Continuous (fun p : (Fin n → ℝ) × ℝ => (k p.1).toReal) := by
      simpa using hkReal_cont.comp continuous_fst
    have hcont_first :
        Continuous (fun p : (Fin n → ℝ) × ℝ => (fun _ : Fin 1 => (k p.1).toReal)) := by
      refine continuous_pi ?_
      intro i
      simpa using hcont_kReal
    exact hcont_first.prodMk continuous_snd
  let S : Set (Fin 1 → ℝ) := {t : Fin 1 → ℝ | 0 ≤ t 0}
  have hpreimage :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) f =
        Phi ⁻¹' epigraph (S := S) (fun t => g (t 0 : EReal)) := by
    ext p
    rcases p with ⟨x, μ⟩
    constructor
    · intro hp
      have hle : f x ≤ (μ : EReal) := by
        have hp' : Set.univ x ∧ f x ≤ (μ : EReal) := by
          simpa [epigraph] using hp
        exact hp'.2
      have hkx_top : k x ≠ (⊤ : EReal) := hk_norm.2.1 x
      have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk_norm.1 x
      have hkx_coe : ((k x).toReal : EReal) = k x := EReal.coe_toReal hkx_top hkx_bot
      have hkx_nonneg : 0 ≤ (k x).toReal := by
        have hnonneg : (0 : EReal) ≤ k x := hk_norm.1.2.1 x
        have hnonneg' : (0 : EReal) ≤ ((k x).toReal : EReal) := by
          simpa [hkx_coe] using hnonneg
        exact (EReal.coe_le_coe_iff).1 hnonneg'
      have hle' : g ((k x).toReal : EReal) ≤ (μ : EReal) := by
        simpa [hf_def, hkx_coe] using hle
      refine ⟨?_, ?_⟩
      · simpa [Phi, S] using hkx_nonneg
      · simpa [Phi] using hle'
    · intro hp
      have hp' :
          (fun _ : Fin 1 => (k x).toReal) ∈ S ∧
            g (((fun _ : Fin 1 => (k x).toReal) 0 : ℝ) : EReal) ≤ (μ : EReal) := by
        simpa [Phi, epigraph, S] using hp
      have hkx_top : k x ≠ (⊤ : EReal) := hk_norm.2.1 x
      have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk_norm.1 x
      have hkx_coe : ((k x).toReal : EReal) = k x := EReal.coe_toReal hkx_top hkx_bot
      have hle : g (k x) ≤ (μ : EReal) := by
        simpa [hkx_coe] using hp'.2
      have hle' : f x ≤ (μ : EReal) := by
        simpa [hf_def] using hle
      exact ⟨by
        change True
        trivial, hle'⟩
  have hclosed_epi :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    simpa [hpreimage] using hg_closed.preimage hcont_Phi
  have hclosed_sub :
      ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).2.mpr hclosed_epi
  exact (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).1.mpr hclosed_sub

/-- Properness of `g ∘ k` once `g` is finite at the origin. -/
lemma matrix_quadraticGauge_comp_proper {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q)
    (g : EReal → EReal)
    (hgζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥)
    (hg_mono : Monotone g)
    (hg_convex :
      ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))
    (hg_closed :
      IsClosed (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))) :
    let k : (Fin n → ℝ) → EReal := fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)
    let f : (Fin n → ℝ) → EReal := fun x => g (k x)
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
  classical
  set k : (Fin n → ℝ) → EReal :=
    fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) with hk_def
  set f : (Fin n → ℝ) → EReal := fun x => g (k x) with hf_def
  have hk_all :
      IsClosedGauge k ∧ IsNormGauge k ∧
        polarGauge k =
          fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) := by
    simpa [hk_def] using
      (matrix_quadraticGauge_isClosedGauge_isNormGauge_and_polar (Q := Q) hQsymm hQpos)
  rcases hk_all with ⟨-, hk_norm, -⟩
  have hk_gauge : IsGauge k := hk_norm.1
  have h0_ne_bot : g (0 : EReal) ≠ ⊥ :=
    g0_ne_bot_of_convex_closed_and_exists_finite_nonneg (g := g) hg_convex hg_closed hgζ
  rcases hgζ with ⟨ζ, hζpos, hζtop, hζbot⟩
  have h0_ne_top : g (0 : EReal) ≠ ⊤ := by
    have hle : g (0 : EReal) ≤ g (ζ : EReal) := by
      have hz : (0 : EReal) ≤ (ζ : EReal) := by exact_mod_cast (le_of_lt hζpos)
      exact hg_mono hz
    intro h0top
    have htop : (⊤ : EReal) ≤ g (ζ : EReal) := by simpa [h0top] using hle
    exact hζtop (top_le_iff.mp htop)
  have hconv : ConvexFunction f :=
    matrix_quadraticGauge_comp_convex (Q := Q) hQsymm hQpos (g := g) ⟨ζ, hζpos, hζtop, hζbot⟩
      hg_mono hg_convex hg_closed
  have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [ConvexFunction] using hconv
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f x ≠ ⊥ := by
    intro x hx
    have hk_nonneg : (0 : EReal) ≤ k x := hk_gauge.2.1 x
    exact monotone_ne_bot_of_nonneg (g := g) hg_mono h0_ne_bot (k x) hk_nonneg
  have hne_epi : Set.Nonempty (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    refine ⟨(0, (g (0 : EReal)).toReal), ?_⟩
    have hco : ((g (0 : EReal)).toReal : EReal) = g (0 : EReal) := by
      simpa using (EReal.coe_toReal (x := g (0 : EReal)) h0_ne_top h0_ne_bot)
    have hk0 : k 0 = 0 := hk_gauge.2.2.2
    have hle0 : f 0 ≤ ((g (0 : EReal)).toReal : EReal) := by
      have : f 0 = g (0 : EReal) := by simp [hf_def, hk0]
      simp [this, hco]
    exact ⟨by
      change True
      trivial, hle0⟩
  exact ⟨hconv_on, hne_epi, hnotbot⟩

/-- Conjugate of `g ∘ k` for the quadratic norm gauge. -/
lemma matrix_quadraticGauge_comp_fenchelConjugate {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q)
    (g : EReal → EReal)
    (hgζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥)
    (hg_mono : Monotone g) (hg_top : g ⊤ = ⊤) :
    let k : (Fin n → ℝ) → EReal := fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)
    let f : (Fin n → ℝ) → EReal := fun x => g (k x)
    let kStar : (Fin n → ℝ) → EReal :=
      fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal)
    fenchelConjugate n f = fun xStar => monotoneConjugateERealNonneg g (kStar xStar) := by
  classical
  set k : (Fin n → ℝ) → EReal :=
    fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal) with hk_def
  set f : (Fin n → ℝ) → EReal := fun x => g (k x) with hf_def
  set kStar : (Fin n → ℝ) → EReal :=
    fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) with hkStar_def
  have hk_all :
      IsClosedGauge k ∧ IsNormGauge k ∧ polarGauge k = kStar := by
    simpa [hk_def, hkStar_def] using
      (matrix_quadraticGauge_isClosedGauge_isNormGauge_and_polar (Q := Q) hQsymm hQpos)
  rcases hk_all with ⟨hk_closed, -, hpol⟩
  have hformula :=
    (fenchelConjugate_eq_monotoneConjugate_polarGauge_of_comp (n := n) (f := f) (k := k)
        (g := g) hk_closed (by simp [hf_def]) hg_mono hg_top hgζ).2
  funext xStar
  simpa [hpol] using hformula xStar

/-- Text 15.0.28: Let `Q` be a symmetric positive definite matrix and define
`k(x) = ⟪x, Q x⟫^{1/2}`. Let `g : [0, +∞) → (-∞, +∞]` satisfy the hypotheses of Theorem 15.3, and
define `f(x) = g(k(x))`. Then `f` is a closed proper convex function and its conjugate satisfies
`f^*(x⋆) = g⁺(k^∘(x⋆)) = g⁺(⟪x⋆, Q⁻¹ x⋆⟫^{1/2})`, where `g⁺` is the monotone conjugate of `g` and
`k^∘` is the polar gauge of `k`. -/
theorem matrix_quadraticGauge_comp_closedProperConvex_and_fenchelConjugate {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQsymm : Q.IsSymm) (hQpos : Matrix.PosDef Q)
    (g : EReal → EReal)
    (hgζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥)
    (hg_mono : Monotone g)
    (hg_convex :
      ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))
    (hg_closed :
      IsClosed (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal))))
    (hg_top : g ⊤ = ⊤) :
    let k : (Fin n → ℝ) → EReal := fun x => ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)
    let f : (Fin n → ℝ) → EReal := fun x => g (k x)
    let kStar : (Fin n → ℝ) → EReal :=
      fun xStar => ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal)
    ClosedConvexFunction f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
        fenchelConjugate n f =
          fun xStar => monotoneConjugateERealNonneg g (kStar xStar) := by
  have hconv :
      ConvexFunction (fun x : Fin n → ℝ =>
        g ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)) :=
    matrix_quadraticGauge_comp_convex (Q := Q) hQsymm hQpos (g := g) hgζ hg_mono hg_convex
      hg_closed
  have hls :
      LowerSemicontinuous (fun x : Fin n → ℝ =>
        g ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)) :=
    matrix_quadraticGauge_comp_lowerSemicontinuous (Q := Q) hQsymm hQpos (g := g) hg_closed
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ => g ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)) :=
    matrix_quadraticGauge_comp_proper (Q := Q) hQsymm hQpos (g := g) hgζ hg_mono hg_convex
      hg_closed
  have hconj :
      fenchelConjugate n (fun x : Fin n → ℝ =>
        g ((Real.sqrt (x ⬝ᵥ (Q.mulVec x)) : ℝ) : EReal)) =
        fun xStar =>
          monotoneConjugateERealNonneg g
            ((Real.sqrt (xStar ⬝ᵥ ((Q⁻¹).mulVec xStar)) : ℝ) : EReal) :=
    matrix_quadraticGauge_comp_fenchelConjugate (Q := Q) hQsymm hQpos (g := g) hgζ hg_mono hg_top
  refine ⟨?_, hproper, ?_⟩
  · exact ⟨hconv, hls⟩
  · simpa using hconj

/-- Text 15.0.29: Let `f : ℝⁿ → [0, +∞]` be a convex function such that `f 0 = 0`. Its polar
`fᵒ : ℝⁿ → [0, +∞]` is defined by

`fᵒ x⋆ = inf { μ⋆ ≥ 0 | ⟪x, x⋆⟫ ≤ 1 + μ⋆ * f x for all x }`.

If `f` is a gauge, this reduces to the polar gauge (Text 15.0.5). If `f = δ(· | C)` for a closed
convex set `C` containing `0`, then `fᵒ = δ(· | Cᵒ)`. Furthermore, whenever `x ∈ dom f` and
`x⋆ ∈ dom fᵒ`, one has `⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆`.

In this development, we represent `[0, +∞]` by `EReal` together with explicit nonnegativity
assumptions, and effective-domain assumptions by `f x ≠ ⊤`. -/
noncomputable def polarConvex {n : ℕ} (f : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) : EReal :=
  sInf
    {μStar : EReal |
      0 ≤ μStar ∧
        ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μStar * f x}

/-- A `polarConvex` feasible multiplier is feasible for the polar gauge of a gauge. -/
lemma polarConvex_feasible_imp_polarGauge_feasible_of_isGauge {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf : IsGauge f) {xStar : Fin n → ℝ} {μ : EReal}
    (hμ :
      0 ≤ μ ∧
        ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μ * f x) :
    0 ≤ μ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * f x := by
  refine ⟨hμ.1, ?_⟩
  intro x
  by_cases htop : μ * f x = ⊤
  · simp [htop]
  have hnonneg : (0 : EReal) ≤ μ * f x := EReal.mul_nonneg hμ.1 (hf.2.1 x)
  have hbot : μ * f x ≠ (⊥ : EReal) := by
    intro hbot
    have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
      convert hnonneg using 1; simp [hbot]
    have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
    have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
    exact h0ne h0eq
  set b : ℝ := (μ * f x).toReal
  have hb : (b : EReal) = μ * f x := by
    simpa [b] using (EReal.coe_toReal (x := μ * f x) htop hbot)
  have hle_real : (x ⬝ᵥ xStar : ℝ) ≤ b := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    set t : ℝ := 1 / ε
    have ht0 : 0 ≤ t := by
      have hε0 : 0 ≤ ε := le_of_lt hε
      exact one_div_nonneg.mpr hε0
    have htpos : 0 < t := by
      exact one_div_pos.mpr hε
    have hineq := hμ.2 (t • x)
    have hdot : (t • x ⬝ᵥ xStar : ℝ) = t * (x ⬝ᵥ xStar : ℝ) := by
      simp [smul_eq_mul, smul_dotProduct]
    have hfhom : f (t • x) = (t : EReal) * f x := by
      simpa using (hf.2.2.1 x t ht0)
    have hmul : μ * f (t • x) = (t : EReal) * (μ * f x) := by
      calc
        μ * f (t • x) = μ * ((t : EReal) * f x) := by simp [hfhom]
        _ = (t : EReal) * (μ * f x) := by
          simp [mul_assoc, mul_comm]
    have hineq' :
        ((t * (x ⬝ᵥ xStar : ℝ) : ℝ) : EReal) ≤ ((1 + t * b : ℝ) : EReal) := by
      have hright :
          ((1 + t * b : ℝ) : EReal) = (1 : EReal) + (t : EReal) * (b : EReal) := by
        simp [EReal.coe_add, EReal.coe_mul]
      have hineq1 :
          ((t * (x ⬝ᵥ xStar : ℝ) : ℝ) : EReal) ≤
            (1 : EReal) + (t : EReal) * (b : EReal) := by
        simpa [hdot, hmul, hb] using hineq
      simpa [hright] using hineq1
    have hineq_real : t * (x ⬝ᵥ xStar : ℝ) ≤ 1 + t * b :=
      (EReal.coe_le_coe_iff).1 hineq'
    have htne : t ≠ 0 := ne_of_gt htpos
    have hmul' :
        (x ⬝ᵥ xStar : ℝ) ≤ t⁻¹ + b := by
      have hmul :=
        mul_le_mul_of_nonneg_left hineq_real (le_of_lt (inv_pos.mpr htpos))
      simpa [mul_add, mul_assoc, inv_mul_cancel, htne] using hmul
    simpa [t, one_div, add_comm, add_left_comm, add_assoc] using hmul'
  have hle : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (b : EReal) :=
    (EReal.coe_le_coe_iff).2 hle_real
  simpa [hb] using hle

/-- Text 15.0.29 (gauge case): if `f` is a gauge, then its polar (as in `polarConvex`) agrees with
the polar gauge `polarGauge`. -/
theorem polarConvex_eq_polarGauge_of_isGauge {n : ℕ} {f : (Fin n → ℝ) → EReal} (hf : IsGauge f) :
    polarConvex f = polarGauge f := by
  funext xStar
  unfold polarConvex polarGauge
  apply le_antisymm
  · refine le_sInf ?_
    intro μ hμ
    have hμ' :
        0 ≤ μ ∧
          ∀ x : Fin n → ℝ,
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μ * f x := by
      refine ⟨hμ.1, ?_⟩
      intro x
      have h0 : (0 : EReal) ≤ (1 : EReal) := by
        exact_mod_cast (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
      calc
        ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * f x := hμ.2 x
        _ ≤ (1 : EReal) + μ * f x := le_add_of_nonneg_left h0
    exact sInf_le hμ'
  · refine le_sInf ?_
    intro μ hμ
    exact
      sInf_le
        (polarConvex_feasible_imp_polarGauge_feasible_of_isGauge (f := f) hf (xStar := xStar) hμ)

/-- Text 15.0.29 (indicator case): if `f = δ(· | C)` for a closed convex set `C` containing `0`,
then `fᵒ = δ(· | Cᵒ)` where `Cᵒ = {x⋆ | ∀ x ∈ C, ⟪x, x⋆⟫ ≤ 1}`. -/
theorem polarConvex_erealIndicator_eq_erealIndicator_polar {n : ℕ} (C : Set (Fin n → ℝ)) :
    let Cpolar : Set (Fin n → ℝ) := {xStar | ∀ x ∈ C, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal)}
    polarConvex (erealIndicator C) = erealIndicator Cpolar := by
  classical
  intro Cpolar
  funext xStar
  by_cases hxStar : xStar ∈ Cpolar
  · have hxStar' :
        ∀ x ∈ C, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) := by
        simpa [Cpolar] using hxStar
    let M : Set EReal :=
      {μStar : EReal |
        0 ≤ μStar ∧
          ∀ x : Fin n → ℝ,
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μStar * erealIndicator C x}
    have h0le : (0 : EReal) ≤ sInf M := by
      refine le_sInf ?_
      intro μ hμ
      exact hμ.1
    have hle0 : sInf M ≤ (0 : EReal) := by
      refine (EReal.le_of_forall_lt_iff_le (x := (0 : EReal)) (y := sInf M)).1 ?_
      intro z hz
      have hzpos : (0 : ℝ) < z := by
        simpa using hz
      have hzmem : (z : EReal) ∈ M := by
        refine ⟨?_, ?_⟩
        · exact_mod_cast (le_of_lt hzpos)
        · intro x
          by_cases hx : x ∈ C
          · have hinner : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) := hxStar' x hx
            simpa [erealIndicator, hx] using hinner
          · have htop : ((z : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
              simpa using (EReal.coe_mul_top_of_pos (x := z) hzpos)
            have htop' : (1 : EReal) + ((z : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
              have hne : (1 : EReal) ≠ (⊥ : EReal) := EReal.coe_ne_bot (1 : ℝ)
              have htop'' : (1 : EReal) + (⊤ : EReal) = ⊤ :=
                (EReal.add_top_iff_ne_bot (x := (1 : EReal))).2 hne
              simpa [htop] using htop''
            have hle_top : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (⊤ : EReal) := le_top
            have hle' :
                ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
                  (1 : EReal) + ((z : ℝ) : EReal) * (⊤ : EReal) := by
              simp [htop']
            simpa [erealIndicator, hx, htop] using hle'
      exact sInf_le hzmem
    have hEq : sInf M = (0 : EReal) := le_antisymm hle0 h0le
    have hpol : polarConvex (erealIndicator C) xStar = (0 : EReal) := by
      simp [polarConvex, M, hEq]
    have hRhs : erealIndicator Cpolar xStar = (0 : EReal) := by
      simp [erealIndicator, hxStar]
    simp [hpol, hRhs]
  · have hxStar' :
        ¬ ∀ x ∈ C, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) := by
        simpa [Cpolar] using hxStar
    push_neg at hxStar'
    rcases hxStar' with ⟨x0, hx0C, hx0gt⟩
    let M : Set EReal :=
      {μStar : EReal |
        0 ≤ μStar ∧
          ∀ x : Fin n → ℝ,
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μStar * erealIndicator C x}
    have hMempty : M = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro μ hμ
      have hineq : ((x0 ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) := by
        simpa [erealIndicator, hx0C] using hμ.2 x0
      exact (not_le_of_gt hx0gt) hineq
    have hpol : polarConvex (erealIndicator C) xStar = (⊤ : EReal) := by
      simp [polarConvex, M, hMempty]
    have hRhs : erealIndicator Cpolar xStar = (⊤ : EReal) := by
      simp [erealIndicator, hxStar]
    simp [hpol, hRhs]

/-- Text 15.0.29 (polar inequality): whenever `x ∈ dom f` and `x⋆ ∈ dom fᵒ`,
`⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆`. -/
theorem inner_le_one_add_mul_polarConvex {n : ℕ} (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ)
    (hx : f x ≠ ⊤) (hxStar : polarConvex f xStar ≠ ⊤) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + f x * polarConvex f xStar := by
  classical
  let M : Set EReal :=
    {μStar : EReal |
      0 ≤ μStar ∧
        ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μStar * f x}
  have hMne : M.Nonempty := by
    by_cases hMempty : M = ∅
    · have htop : polarConvex f xStar = ⊤ := by
        simp [polarConvex, M, hMempty]
      exact (hxStar htop).elim
    · exact Set.nonempty_iff_ne_empty.mpr hMempty
  have h0le : (0 : EReal) ≤ sInf M := by
    refine le_sInf ?_
    intro μ hμ
    exact hμ.1
  have hbot : sInf M ≠ (⊥ : EReal) := by
    intro hbot
    have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
      convert h0le using 1; simp [hbot]
    have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
    have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
    exact h0ne h0eq
  set p : EReal := sInf M
  have hp : polarConvex f xStar = p := by
    simp [polarConvex, M, p]
  cases hfx : f x using EReal.rec with
  | top =>
      exact (hx hfx).elim
  | bot =>
      obtain ⟨μ0, hμ0⟩ := hMne
      have hμ0pos : ¬ 0 < μ0 := by
        intro hμ0pos
        have hmul_bot : μ0 * (⊥ : EReal) = ⊥ := EReal.mul_bot_of_pos hμ0pos
        have hineq : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μ0 * f x := hμ0.2 x
        have hle_bot : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (⊥ : EReal) := by
          convert hineq using 1; simp [hfx, hmul_bot]
        have hbot' : ((x ⬝ᵥ xStar : ℝ) : EReal) = (⊥ : EReal) := (le_bot_iff).1 hle_bot
        exact (EReal.coe_ne_bot _) hbot'
      have hμ0_le : μ0 ≤ (0 : EReal) := le_of_not_gt hμ0pos
      have hμ0_eq : μ0 = (0 : EReal) := le_antisymm hμ0_le hμ0.1
      have h0mem : (0 : EReal) ∈ M := by
        simpa [hμ0_eq] using hμ0
      have hle0 : p ≤ (0 : EReal) := sInf_le h0mem
      have hp_eq : p = (0 : EReal) := le_antisymm hle0 h0le
      have hineq : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + (0 : EReal) * f x := by
        simpa [hμ0_eq] using hμ0.2 x
      simpa [hp_eq, hfx, mul_comm, hp] using hineq
  | coe r =>
      have hp_top : p ≠ (⊤ : EReal) := by
        simpa [hp] using hxStar
      set pR : ℝ := p.toReal
      have hpR : (pR : EReal) = p := by
        simpa [pR] using (EReal.coe_toReal (x := p) hp_top hbot)
      by_cases hrpos : 0 < r
      · have hle_real : (x ⬝ᵥ xStar : ℝ) ≤ 1 + r * pR := by
          refine le_of_forall_pos_le_add ?_
          intro ε hε
          set ε' : ℝ := ε / r
          have hε' : 0 < ε' := by
            exact (div_pos hε hrpos)
          have hp_lt : p < ((pR + ε') : ℝ) := by
            have hp_lt' : (pR : EReal) < ((pR + ε') : ℝ) := by
              exact_mod_cast (by linarith [hε'])
            simpa [hpR] using hp_lt'
          rcases (sInf_lt_iff).1 hp_lt with ⟨μ, hμM, hμlt⟩
          have hμ0 : 0 ≤ μ := hμM.1
          have hμtop : μ ≠ ⊤ := by
            exact ne_of_lt (lt_of_lt_of_le hμlt le_top)
          have hμbot : μ ≠ (⊥ : EReal) := by
            intro hμbot
            have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
              convert hμ0 using 1; simp [hμbot]
            have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
            have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
            exact h0ne h0eq
          set μR : ℝ := μ.toReal
          have hμR : (μR : EReal) = μ := by
            simpa [μR] using (EReal.coe_toReal (x := μ) hμtop hμbot)
          have hμltR : μR < pR + ε' := by
            have hμlt' : (μR : EReal) < (pR + ε' : ℝ) := by
              simpa [hμR] using hμlt
            exact (EReal.coe_lt_coe_iff).1 hμlt'
          have hineqE : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μ * f x := hμM.2 x
          have hineqE' :
              ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μ * (r : EReal) := by
            simpa [hfx] using hineqE
          have hineqR : (x ⬝ᵥ xStar : ℝ) ≤ 1 + μR * r := by
            have hineqE'' :
                ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((1 + μR * r : ℝ) : EReal) := by
              simpa [hμR, EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using
                hineqE'
            exact (EReal.coe_le_coe_iff).1 hineqE''
          have hleR : 1 + μR * r ≤ 1 + (pR + ε') * r := by
            nlinarith [hμltR, hrpos]
          have hstep : 1 + (pR + ε') * r = (1 + r * pR) + ε := by
            calc
              1 + (pR + ε') * r = 1 + (pR * r + ε' * r) := by ring
              _ = 1 + (r * pR) + ε := by
                have hrne : r ≠ 0 := ne_of_gt hrpos
                have hε' : ε' * r = ε := by
                  simp [ε', div_eq_mul_inv, hrne]
                simp [hε', mul_comm, add_left_comm, add_comm]
              _ = (1 + r * pR) + ε := by ring
          have hcalc : (x ⬝ᵥ xStar : ℝ) ≤ (1 + r * pR) + ε := by
            calc
              (x ⬝ᵥ xStar : ℝ) ≤ 1 + μR * r := hineqR
              _ ≤ 1 + (pR + ε') * r := hleR
              _ = (1 + r * pR) + ε := hstep
          exact hcalc
        have hleE : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((1 + r * pR : ℝ) : EReal) := by
          exact_mod_cast hle_real
        have hgoal :
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + (r : EReal) * p := by
          simpa [hpR, EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hleE
        simpa [hfx, hp] using hgoal
      · have hrle : r ≤ 0 := le_of_not_gt hrpos
        have hp_lt : p < ((pR + 1) : ℝ) := by
          have hp_lt' : (pR : EReal) < ((pR + 1) : ℝ) := by
            exact_mod_cast (by linarith)
          simpa [hpR] using hp_lt'
        rcases (sInf_lt_iff).1 hp_lt with ⟨μ, hμM, hμlt⟩
        have hμ0 : 0 ≤ μ := hμM.1
        have hμtop : μ ≠ ⊤ := by
          exact ne_of_lt (lt_of_lt_of_le hμlt le_top)
        have hμbot : μ ≠ (⊥ : EReal) := by
          intro hμbot
          have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
            convert hμ0 using 1; simp [hμbot]
          have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
          have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
          exact h0ne h0eq
        set μR : ℝ := μ.toReal
        have hμR : (μR : EReal) = μ := by
          simpa [μR] using (EReal.coe_toReal (x := μ) hμtop hμbot)
        have hpleμ : p ≤ μ := sInf_le hμM
        have hpleμR : pR ≤ μR := by
          have hpleμ' : (pR : EReal) ≤ (μR : EReal) := by
            simpa [hpR, hμR] using hpleμ
          exact (EReal.coe_le_coe_iff).1 hpleμ'
        have hineqE : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μ * f x := hμM.2 x
        have hineqE' :
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μ * (r : EReal) := by
          simpa [hfx] using hineqE
        have hineqR : (x ⬝ᵥ xStar : ℝ) ≤ 1 + μR * r := by
          have hineqE'' :
              ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((1 + μR * r : ℝ) : EReal) := by
            simpa [hμR, EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using
              hineqE'
          exact (EReal.coe_le_coe_iff).1 hineqE''
        have hmulR : r * μR ≤ r * pR := by
          exact mul_le_mul_of_nonpos_left hpleμR hrle
        have hleR : 1 + μR * r ≤ 1 + r * pR := by
          have hmulR' : μR * r ≤ pR * r := by
            nlinarith [hmulR]
          nlinarith [hmulR']
        have hleE : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((1 + r * pR : ℝ) : EReal) := by
          exact_mod_cast (le_trans hineqR hleR)
        have hgoal :
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + (r : EReal) * p := by
          simpa [hpR, EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hleE
        simpa [hfx, hp] using hgoal

end Section15
end Chap03
