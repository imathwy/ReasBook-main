import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_12.Problem_2_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Projectivization Polynomial
open scoped Manifold ContDiff

-- This file reuses the chapter's affine inclusion owner from `Problem_2_8`; the textbook map
-- `G : ℂ → ℂP¹` is its one-dimensional specialization.

local notation "Icp1" => 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))
local notation "G" => complexProjectiveAffineInclusion 1 ∘ EuclideanSpace.single (0 : Fin 1)
local notation "CVec" => EuclideanSpace ℂ (Fin 2)

/-- Helper for Problem 2-9: the standard affine representative `[z, 1]` in `ℂ²`. -/
def complex_projective_line_affine_vector (z : ℂ) : CVec :=
  (EuclideanSpace.equiv (Fin 2) ℂ).symm ![z, 1]

/-- Helper for Problem 2-9: the affine representative `[z, 1]` is nonzero. -/
lemma complex_projective_line_affine_vector_ne_zero (z : ℂ) :
    complex_projective_line_affine_vector z ≠ 0 := by
  -- The second coordinate is literally `1`.
  intro hzero
  have hcoord : complex_projective_line_affine_vector z 1 = 0 := by
    simp [hzero]
  simp [complex_projective_line_affine_vector] at hcoord

/-- Helper for Problem 2-9: the first coordinate of `[z, 1]` is `z`. -/
lemma complex_projective_line_affine_vector_zero (z : ℂ) :
    complex_projective_line_affine_vector z 0 = z := by
  simp [complex_projective_line_affine_vector]

/-- Helper for Problem 2-9: the second coordinate of `[z, 1]` is `1`. -/
lemma complex_projective_line_affine_vector_one (z : ℂ) :
    complex_projective_line_affine_vector z 1 = 1 := by
  simp [complex_projective_line_affine_vector]

/-- Helper for Problem 2-9: evaluating the homogeneous pair attached to `p` on a nonzero
representative of `ℂP¹`. -/
def complex_projective_line_polynomial_tuple (p : Polynomial ℂ) :
    { v : CVec // v ≠ 0 } → CVec :=
  fun v ↦ (EuclideanSpace.equiv (Fin 2) ℂ).symm fun i ↦
    MvPolynomial.eval v.1 (p.toTupleMvPolynomial i)

/-- Helper for Problem 2-9: evaluating the homogenized numerator at `[z, 0]` picks out the leading
term. -/
lemma complex_projective_line_homogenize_eval_at_infinity (p : Polynomial ℂ) (z : ℂ) :
    MvPolynomial.eval ![z, 0] (p.toTupleMvPolynomial 0) = p.leadingCoeff * z ^ p.natDegree := by
  -- Expand the homogenization and note that every monomial except the leading one contains the
  -- second variable, hence vanishes at `[z, 0]`.
  rw [Polynomial.toTupleMvPolynomial_zero_eq, Polynomial.homogenize, MvPolynomial.eval_sum,
    Finset.sum_eq_single (p.natDegree, 0)]
  · simp [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single,
      Finsupp.prod_single_index, Polynomial.coeff_natDegree]
  · intro kl hkl hne
    rcases kl with ⟨k, l⟩
    simp only [Finset.mem_antidiagonal] at hkl
    have hl : l ≠ 0 := by
      intro hl0
      have hk : k = p.natDegree := by
        linarith [hkl]
      apply hne
      ext <;> simp [hk, hl0]
    simp [MvPolynomial.eval_monomial, hl, Finsupp.update_eq_add_single]
  · simp

/-- Helper for Problem 2-9: the second coordinate of the homogeneous pair is the pure monomial
`v₁ ^ deg p`. -/
lemma complex_projective_line_tuple_second_coord (p : Polynomial ℂ)
    (v : { w : CVec // w ≠ 0 }) :
    complex_projective_line_polynomial_tuple p v 1 = (v : CVec) 1 ^ p.natDegree := by
  -- The second slot of `p.toTupleMvPolynomial` is exactly `X₁ ^ deg p`.
  simp [complex_projective_line_polynomial_tuple, Polynomial.toTupleMvPolynomial_one_eq]

/-- Helper for Problem 2-9: the first coordinate of the homogeneous pair is the homogenized
polynomial numerator. -/
lemma complex_projective_line_tuple_first_coord (p : Polynomial ℂ)
    (v : { w : CVec // w ≠ 0 }) :
    complex_projective_line_polynomial_tuple p v 0 =
      MvPolynomial.eval (v : CVec) (p.toTupleMvPolynomial 0) := by
  simp [complex_projective_line_polynomial_tuple]

/-- Helper for Problem 2-9: if the second homogeneous coordinate vanishes, then the vector is the
canonical infinity representative `[(v₀), 0]`. -/
lemma complex_projective_line_vector_eq_of_second_coord_zero
    (v : { w : CVec // w ≠ 0 }) (h1 : (v : CVec) 1 = 0) :
    (v : CVec) = (EuclideanSpace.equiv (Fin 2) ℂ).symm ![(v : CVec) 0, 0] := by
  -- Normalize the representative coordinatewise so later evaluations can rewrite by one `rw`.
  ext i
  fin_cases i
  · simp
  · simp [h1]

/-- Helper for Problem 2-9: on the infinity representative, the homogenized numerator is the
leading term of `p`. -/
lemma complex_projective_line_eval_numerator_of_second_coord_zero (p : Polynomial ℂ)
    (v : { w : CVec // w ≠ 0 }) (h1 : (v : CVec) 1 = 0) :
    MvPolynomial.eval (v : CVec) (p.toTupleMvPolynomial 0) =
      p.leadingCoeff * (v : CVec) 0 ^ p.natDegree := by
  -- Rewrite to the canonical representative `[(v₀), 0]`, then use the homogenization formula.
  rw [complex_projective_line_vector_eq_of_second_coord_zero v h1]
  rw [Polynomial.toTupleMvPolynomial_zero_eq]
  simpa using complex_projective_line_homogenize_eval_at_infinity p ((v : CVec) 0)

/-- Helper for Problem 2-9: the evaluated homogeneous pair is never the zero vector. -/
lemma complex_projective_line_polynomial_tuple_ne_zero (p : Polynomial ℂ)
    (v : { w : CVec // w ≠ 0 }) :
    complex_projective_line_polynomial_tuple p v ≠ 0 := by
  -- Split exactly as in the source: affine points have nonzero second output coordinate, while
  -- the point at infinity is controlled by the leading term in the first output coordinate.
  by_cases h1 : (v : CVec) 1 = 0
  · -- At infinity, first decide whether the denominator exponent is zero or positive.
    by_cases hdeg : p.natDegree = 0
    · -- Degree-zero polynomials already have nonzero second output coordinate.
      have hsecond :
          complex_projective_line_polynomial_tuple p v 1 ≠ 0 := by
        rw [complex_projective_line_tuple_second_coord, hdeg, h1]
        simp
      intro hzero
      exact hsecond (by simp [hzero])
    · -- Positive degree forces the first input coordinate to be nonzero, so the leading term
      -- survives in the homogenized numerator.
      have hv0 : (v : CVec) 0 ≠ 0 := by
        intro hv0
        apply v.2
        ext i
        fin_cases i
        · simp [hv0]
        · simp [h1]
      have hlead : p.leadingCoeff ≠ 0 := by
        apply Polynomial.leadingCoeff_ne_zero.mpr
        intro hp0
        apply hdeg
        simp [hp0]
      have hfirst :
          complex_projective_line_polynomial_tuple p v 0 ≠ 0 := by
        rw [complex_projective_line_tuple_first_coord,
          complex_projective_line_eval_numerator_of_second_coord_zero p v h1]
        exact mul_ne_zero hlead (pow_ne_zero _ hv0)
      intro hzero
      exact hfirst (by simp [hzero])
  · -- On the affine chart, the denominator coordinate is the nonzero monomial `v₁ ^ deg p`.
    have hsecond :
        complex_projective_line_polynomial_tuple p v 1 ≠ 0 := by
      rw [complex_projective_line_tuple_second_coord]
      exact pow_ne_zero _ h1
    intro hzero
    exact hsecond (by simp [hzero])

/-- Helper for Problem 2-9: evaluating a homogeneous bivariate polynomial on a scaled vector
pulls out the expected scalar power. -/
lemma complex_projective_line_homogeneous_eval_smul
    (q : MvPolynomial (Fin 2) ℂ) (n : ℕ) (hq : q.IsHomogeneous n) (x : CVec) (t : ℂ) :
    MvPolynomial.eval (t • x) q = t ^ n * MvPolynomial.eval x q := by
  -- Expand into monomials and use homogeneity to identify the total exponent of `t`.
  have hEvalSmul :
      MvPolynomial.eval (t • x) q =
        ∑ d ∈ q.support, MvPolynomial.eval (t • x) (MvPolynomial.monomial d (q.coeff d)) := by
    calc
      MvPolynomial.eval (t • x) q
        = MvPolynomial.eval (t • x)
            (∑ d ∈ q.support, MvPolynomial.monomial d (q.coeff d)) := by
              rw [MvPolynomial.support_sum_monomial_coeff]
      _ = ∑ d ∈ q.support, MvPolynomial.eval (t • x) (MvPolynomial.monomial d (q.coeff d)) := by
            rw [MvPolynomial.eval_sum]
  have hEvalSum :
      MvPolynomial.eval x q =
        ∑ d ∈ q.support, MvPolynomial.eval x (MvPolynomial.monomial d (q.coeff d)) := by
    calc
      MvPolynomial.eval x q
        = MvPolynomial.eval x (∑ d ∈ q.support, MvPolynomial.monomial d (q.coeff d)) := by
            rw [MvPolynomial.support_sum_monomial_coeff]
      _ = ∑ d ∈ q.support, MvPolynomial.eval x (MvPolynomial.monomial d (q.coeff d)) := by
            rw [MvPolynomial.eval_sum]
  rw [hEvalSmul]
  calc
    ∑ d ∈ q.support, MvPolynomial.eval (t • x) (MvPolynomial.monomial d (q.coeff d))
      = ∑ d ∈ q.support, t ^ n * MvPolynomial.eval x (MvPolynomial.monomial d (q.coeff d)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd_degree : n = ∑ i ∈ d.support, d i := hq.degree_eq_sum_deg_support hd
          calc
            MvPolynomial.eval (t • x) (MvPolynomial.monomial d (q.coeff d))
                = q.coeff d * ∏ i ∈ d.support, ((t • x) i) ^ d i := by
                    rw [MvPolynomial.eval_monomial, Finsupp.prod]
            _ = q.coeff d * ∏ i ∈ d.support, (t * x i) ^ d i := by
                  simp [smul_eq_mul]
            _ = q.coeff d * ∏ i ∈ d.support, (t ^ d i * x i ^ d i) := by
                  simp_rw [mul_pow]
            _ = q.coeff d * ((∏ i ∈ d.support, t ^ d i) * ∏ i ∈ d.support, x i ^ d i) := by
                  rw [Finset.prod_mul_distrib]
            _ = q.coeff d * (t ^ (∑ i ∈ d.support, d i) * ∏ i ∈ d.support, x i ^ d i) := by
                  rw [Finset.prod_pow_eq_pow_sum]
            _ = q.coeff d * (t ^ n * ∏ i ∈ d.support, x i ^ d i) := by
                  rw [← hd_degree]
            _ = t ^ n * (q.coeff d * ∏ i ∈ d.support, x i ^ d i) := by
                  ring
            _ = t ^ n * MvPolynomial.eval x (MvPolynomial.monomial d (q.coeff d)) := by
                  rw [MvPolynomial.eval_monomial, Finsupp.prod]
    _ = t ^ n * ∑ d ∈ q.support, MvPolynomial.eval x (MvPolynomial.monomial d (q.coeff d)) := by
          rw [← Finset.mul_sum]
    _ = t ^ n * MvPolynomial.eval x q := by
          rw [← hEvalSum]

/-- Helper for Problem 2-9: scaling a homogeneous representative scales the evaluated numerator by
the expected degree factor. -/
lemma complex_projective_line_polynomial_numerator_smul (p : Polynomial ℂ)
    (a b : { w : CVec // w ≠ 0 }) (t : ℂ) (h : (a : CVec) = t • (b : CVec)) :
    complex_projective_line_polynomial_tuple p a 0 =
      t ^ p.natDegree * complex_projective_line_polynomial_tuple p b 0 := by
  -- Route correction: use the source-faithful homogeneous scaling law for the numerator instead
  -- of splitting affine and infinity representatives a second time.
  rw [complex_projective_line_tuple_first_coord, complex_projective_line_tuple_first_coord, h]
  -- The first coordinate is evaluation of the homogeneous polynomial `p.toTupleMvPolynomial 0`.
  simpa using
    complex_projective_line_homogeneous_eval_smul
      (q := p.toTupleMvPolynomial 0)
      (n := p.natDegree)
      (hq := Polynomial.isHomogeneous_toTupleMvPolynomial p 0)
      (x := (b : CVec))
      (t := t)

/-- Helper for Problem 2-9: the projectivized homogeneous pair depends only on the projective
class of the representative. -/
lemma complex_projective_line_polynomial_respects_projective_classes (p : Polynomial ℂ)
    (a b : { w : CVec // w ≠ 0 }) (t : ℂ) (h : (a : CVec) = t • (b : CVec)) :
    Projectivization.mk ℂ (complex_projective_line_polynomial_tuple p a)
        (complex_projective_line_polynomial_tuple_ne_zero p a) =
      Projectivization.mk ℂ (complex_projective_line_polynomial_tuple p b)
        (complex_projective_line_polynomial_tuple_ne_zero p b) := by
  -- The homogeneous pair scales by the common factor `t ^ deg p`.
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _
    (complex_projective_line_polynomial_tuple_ne_zero p a)
    (complex_projective_line_polynomial_tuple_ne_zero p b)).2
  refine ⟨t ^ p.natDegree, ?_⟩
  ext i
  fin_cases i
  · -- The numerator coordinate uses the dedicated scaling lemma.
    simpa [Pi.smul_apply, smul_eq_mul] using
      (complex_projective_line_polynomial_numerator_smul p a b t h).symm
  · -- The denominator coordinate is the pure monomial `v₁ ^ deg p`.
    have hsecond :
        complex_projective_line_polynomial_tuple p a 1 =
          t ^ p.natDegree * complex_projective_line_polynomial_tuple p b 1 := by
      rw [complex_projective_line_tuple_second_coord, complex_projective_line_tuple_second_coord, h]
      simp [smul_eq_mul, mul_pow]
    simpa [Pi.smul_apply, smul_eq_mul] using hsecond.symm

/-- Helper for Problem 2-9: the quotient lift of the homogeneous pair defines the polynomial map on
`ℂP¹`. -/
def complex_projective_line_polynomial_map (p : Polynomial ℂ) : ℂP[1] → ℂP[1] :=
  Projectivization.lift
    (fun v ↦ Projectivization.mk ℂ (complex_projective_line_polynomial_tuple p v)
      (complex_projective_line_polynomial_tuple_ne_zero p v))
    (complex_projective_line_polynomial_respects_projective_classes p)

/-- Helper for Problem 2-9: the projectivized polynomial map agrees with affine polynomial
evaluation on the chart `G(z) = [z, 1]`. -/
lemma complex_projective_line_affine_representative_eval (p : Polynomial ℂ) (z : ℂ) :
    complex_projective_line_polynomial_tuple p
        ⟨complex_projective_line_affine_vector z, complex_projective_line_affine_vector_ne_zero z⟩ =
      complex_projective_line_affine_vector (p.eval z) := by
  -- Compare coordinates: the numerator evaluates the homogenization at `[z, 1]`, and the
  -- denominator is the monomial `1 ^ deg p`.
  ext i
  fin_cases i
  · have hz1 : complex_projective_line_affine_vector z 1 ≠ 0 := by
      simp [complex_projective_line_affine_vector_one]
    change complex_projective_line_polynomial_tuple p
        ⟨complex_projective_line_affine_vector z,
          complex_projective_line_affine_vector_ne_zero z⟩ 0 =
      complex_projective_line_affine_vector (p.eval z) 0
    rw [complex_projective_line_tuple_first_coord, Polynomial.toTupleMvPolynomial_zero_eq]
    rw [Polynomial.eval_homogenize (p := p) (n := p.natDegree) le_rfl
      (complex_projective_line_affine_vector z) hz1]
    simp [complex_projective_line_affine_vector]
  · change complex_projective_line_polynomial_tuple p
        ⟨complex_projective_line_affine_vector z,
          complex_projective_line_affine_vector_ne_zero z⟩ 1 =
      complex_projective_line_affine_vector (p.eval z) 1
    rw [complex_projective_line_tuple_second_coord]
    simp [complex_projective_line_affine_vector]

/-- Helper for Problem 2-9: the inverse last-chart homogeneous vector is exactly `[z, 1]`. -/
lemma complex_projective_line_chart_last_invVector_eq_affine_vector (z : ℂ) :
    complexProjectiveChartInvVector 1 (Fin.last 1) (EuclideanSpace.single (0 : Fin 1) z) =
      complex_projective_line_affine_vector z := by
  -- Both sides are the same two-coordinate vector: `z` in the first slot and `1` in the last.
  ext i
  fin_cases i
  · -- The first coordinate comes from the unique affine coordinate of `Fin 1`.
    simpa [complexProjectiveChartInvVector, complex_projective_line_affine_vector] using
      (Fin.insertNth_apply_succAbove (α := fun _ : Fin 2 ↦ ℂ) (i := Fin.last 1) (x := (1 : ℂ))
        (p := EuclideanSpace.single (0 : Fin 1) z) 0)
  · -- The inserted last coordinate is exactly `1`.
    simp [complexProjectiveChartInvVector, complex_projective_line_affine_vector]

/-- Helper for Problem 2-9: the standard affine representative `[z, 1]` defines the affine point
`G z` in `ℂP¹`. -/
lemma complex_projective_line_affine_mk_eq_G (z : ℂ) :
    Projectivization.mk ℂ (complex_projective_line_affine_vector z)
      (complex_projective_line_affine_vector_ne_zero z) = G z := by
  -- Rewrite `G z` as the inverse last-chart point and identify the inserted vector with `[z, 1]`.
  change Projectivization.mk ℂ (complex_projective_line_affine_vector z)
      (complex_projective_line_affine_vector_ne_zero z) =
    (complexProjectiveChart 1 (Fin.last 1)).symm (EuclideanSpace.single (0 : Fin 1) z)
  rw [complexProjectiveChart_symm_apply]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _
    (complex_projective_line_affine_vector_ne_zero z)
    (complexProjectiveChartInvVector_ne_zero 1 (Fin.last 1)
      (EuclideanSpace.single (0 : Fin 1) z))).2
  refine ⟨1, ?_⟩
  simpa [one_smul] using complex_projective_line_chart_last_invVector_eq_affine_vector z

/-- Helper for Problem 2-9: the projectivized polynomial map agrees with affine polynomial
evaluation on the chart `G(z) = [z, 1]`. -/
lemma complex_projective_line_polynomial_affine_eq (p : Polynomial ℂ) (z : ℂ) :
    complex_projective_line_polynomial_map p (G z) = G (p.eval z) := by
  -- Route correction: use the source-faithful affine representative `[z, 1]` directly instead
  -- of unfolding extra chart transport in the main proof.
  rw [← complex_projective_line_affine_mk_eq_G z]
  -- Evaluate the quotient lift on the affine representative.
  rw [complex_projective_line_polynomial_map, Projectivization.lift_mk]
  -- The homogeneous pair at `[z, 1]` is exactly the affine representative of `p(z)`.
  simpa [complex_projective_line_affine_representative_eval] using
    (complex_projective_line_affine_mk_eq_G (p.eval z))

/-- Helper for Problem 2-9: evaluating the homogeneous pair varies continuously with the chosen
nonzero representative. -/
lemma complex_projective_line_polynomial_tuple_continuous (p : Polynomial ℂ) :
    Continuous (fun v : { w : CVec // w ≠ 0 } ↦ complex_projective_line_polynomial_tuple p v) := by
  -- Each coordinate is a multivariate polynomial evaluation in the representative coordinates.
  have hval :
      Continuous (fun v : { w : CVec // w ≠ 0 } ↦ ((v : CVec) : Fin 2 → ℂ)) := by
    exact
      (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 2 ↦ ℂ)).comp
        continuous_subtype_val
  have hcoord :
      Continuous (fun v : { w : CVec // w ≠ 0 } ↦
        fun i : Fin 2 ↦ MvPolynomial.eval v.1 (p.toTupleMvPolynomial i)) := by
    exact continuous_pi fun i : Fin 2 ↦
      (MvPolynomial.continuous_eval (p := p.toTupleMvPolynomial i)).comp hval
  -- Transport the coordinatewise statement back through the Euclidean-space equivalence.
  simpa [complex_projective_line_polynomial_tuple] using
    (EuclideanSpace.equiv (Fin 2) ℂ).symm.continuous.comp hcoord

/-- Helper for Problem 2-9: the lifted polynomial map is continuous, since it descends from the
continuous polynomial map on nonzero homogeneous representatives. -/
lemma complex_projective_line_polynomial_map_continuous (p : Polynomial ℂ) :
    Continuous (complex_projective_line_polynomial_map p) := by
  -- Descend continuity from the representative-level homogeneous polynomial map.
  let f : { v : CVec // v ≠ 0 } → ℂP[1] := fun v ↦
    Projectivization.mk ℂ (complex_projective_line_polynomial_tuple p v)
      (complex_projective_line_polynomial_tuple_ne_zero p v)
  have hf : Continuous f := by
    -- The quotient projection is continuous, so composing it with the continuous tuple map stays
    -- continuous.
    simpa [f, Projectivization.mk'] using
      (continuous_quotient_mk'.comp <|
        Continuous.subtype_mk (complex_projective_line_polynomial_tuple_continuous p)
          (fun v ↦ complex_projective_line_polynomial_tuple_ne_zero p v))
  -- `complex_projective_line_polynomial_map` is exactly the quotient lift of `f`.
  simpa [complex_projective_line_polynomial_map, f] using
    hf.quotient_lift fun a b hab ↦ by
      rcases hab with ⟨t, h⟩
      exact complex_projective_line_polynomial_respects_projective_classes p a b (t : ℂ) h.symm

/-- Helper for Problem 2-9: the inverse of the chart at index `1` is exactly the affine inclusion
`G` in one complex dimension. -/
lemma complex_projective_line_chart_one_symm_eq_G (u : EuclideanSpace ℂ (Fin 1)) :
    (complexProjectiveChart 1 (Fin.last 1)).symm u = G (u 0) := by
  -- In one complex dimension, every affine vector is exactly `single 0` of its unique coordinate.
  change (complexProjectiveChart 1 (Fin.last 1)).symm u =
    (complexProjectiveChart 1 (Fin.last 1)).symm (EuclideanSpace.single (0 : Fin 1) (u 0))
  have hu : EuclideanSpace.single (0 : Fin 1) (u 0) = u := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp
  simp [hu]

/-- Helper for Problem 2-9: applying the last affine chart to `G z` recovers the affine coordinate
`z`. -/
lemma complex_projective_line_chart_one_apply_G (z : ℂ) :
    complexProjectiveChart 1 (Fin.last 1) (G z) = EuclideanSpace.single (0 : Fin 1) z := by
  -- Rewrite `G z` as the inverse chart at the affine coordinate `single 0 z`.
  calc
    complexProjectiveChart 1 (Fin.last 1) (G z)
      = complexProjectiveChart 1 (Fin.last 1)
          ((complexProjectiveChart 1 (Fin.last 1)).symm
            (EuclideanSpace.single (0 : Fin 1) z)) := by
              rw [complex_projective_line_chart_one_symm_eq_G]
              simp
    _ = EuclideanSpace.single (0 : Fin 1) z := by
          simpa using
            OpenPartialHomeomorph.right_inv (complexProjectiveChart 1 (Fin.last 1))
              (Set.mem_univ (EuclideanSpace.single (0 : Fin 1) z))

/-- Helper for Problem 2-9: the chart-`0` inverse at the origin is the infinity representative
`[1, 0]`. -/
lemma complex_projective_line_chart_zero_invVector_eq_infinity_vector :
    complexProjectiveChartInvVector 1 0 0 = (EuclideanSpace.equiv (Fin 2) ℂ).symm ![1, 0] := by
  -- Inserting `1` into the zeroth slot and `0` elsewhere gives the standard infinity vector.
  ext i
  fin_cases i
  · -- The distinguished zeroth coordinate is the inserted `1`.
    simp [complexProjectiveChartInvVector]
  · -- The remaining coordinate comes from the zero affine vector.
    simp [complexProjectiveChartInvVector]

/-- Helper for Problem 2-9: outside the affine open, a point of `ℂP¹` must be the chart-`0`
point at the origin, i.e. the point at infinity. -/
lemma complex_projective_line_affine_open_compl_eq_infinity (x : ℂP[1])
    (hx : x ∉ complexProjectiveAffineOpen 1) :
    x = (complexProjectiveChart 1 0).symm 0 := by
  -- Route correction: the intended source-faithful proof is to show the last coordinate of
  -- `x.rep` vanishes and then compare `x` with the class of `[1, 0]` using
  -- `Projectivization.mk_eq_mk_iff'`.
  have hrep1 : x.rep 1 = 0 := by
    by_contra h1
    apply hx
    simpa [complexProjectiveAffineOpen, x.mk_rep] using
      (complexProjectiveChartDomain_mk 1 (Fin.last 1) x.rep x.rep_nonzero).2 h1
  -- The remaining homogeneous coordinate must stay nonzero because `x.rep` itself is nonzero.
  have hrep0 : x.rep 0 ≠ 0 := by
    intro h0
    apply x.rep_nonzero
    ext i
    fin_cases i
    · simp [h0]
    · simp [hrep1]
  -- Compare the representative of `x` directly with the chart-`0` inverse vector.
  rw [complexProjectiveChart_symm_apply]
  rw [← x.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ x.rep_nonzero
    (complexProjectiveChartInvVector_ne_zero 1 0 0)).2
  refine ⟨x.rep 0, ?_⟩
  ext i
  fin_cases i
  · simp [complexProjectiveChartInvVector]
  · simp [complexProjectiveChartInvVector, hrep1]

/-- Helper for Problem 2-9: on the affine chart, the lifted projective map is exactly polynomial
evaluation in the unique affine coordinate. -/
lemma complex_projective_line_south_chart_formula (p : Polynomial ℂ)
    (u : EuclideanSpace ℂ (Fin 1)) :
    complexProjectiveChart 1 (Fin.last 1)
      (complex_projective_line_polynomial_map p ((complexProjectiveChart 1 (Fin.last 1)).symm u)) =
        EuclideanSpace.single (0 : Fin 1) (p.eval (u 0)) := by
  -- Follow the affine chart through the already-proved affine compatibility.
  rw [complex_projective_line_chart_one_symm_eq_G, complex_projective_line_polynomial_affine_eq,
    complex_projective_line_chart_one_apply_G]

/-- Helper for Problem 2-9: the north-chart denominator at the origin is the leading coefficient of
`p`. -/
lemma complex_projective_line_north_chart_denominator_zero (p : Polynomial ℂ) :
    MvPolynomial.eval (complexProjectiveChartInvVector 1 0 0) (p.toTupleMvPolynomial 0) =
      p.leadingCoeff := by
  -- The chart-`0` inverse at the origin is the infinity representative `[1, 0]`.
  rw [complex_projective_line_chart_zero_invVector_eq_infinity_vector,
    Polynomial.toTupleMvPolynomial_zero_eq]
  simpa using complex_projective_line_homogenize_eval_at_infinity p (1 : ℂ)

/-- Helper for Problem 2-9: the north-chart denominator is nonzero at the origin for a nonzero
polynomial. -/
lemma complex_projective_line_north_chart_denominator_ne_zero (p : Polynomial ℂ) (hp : p ≠ 0) :
    MvPolynomial.eval (complexProjectiveChartInvVector 1 0 0) (p.toTupleMvPolynomial 0) ≠ 0 := by
  -- At the origin, the denominator is the leading coefficient of `p`.
  rw [complex_projective_line_north_chart_denominator_zero]
  exact Polynomial.leadingCoeff_ne_zero.mpr hp

/-- Helper for Problem 2-9: in the north chart, the projective polynomial map has the expected
homogeneous quotient formula. -/
lemma complex_projective_line_north_chart_formula (p : Polynomial ℂ)
    (u : EuclideanSpace ℂ (Fin 1)) :
    complexProjectiveChart 1 0
      (complex_projective_line_polynomial_map p ((complexProjectiveChart 1 0).symm u)) =
        EuclideanSpace.single (0 : Fin 1)
          ((u 0) ^ p.natDegree / MvPolynomial.eval
            (complexProjectiveChartInvVector 1 0 u) (p.toTupleMvPolynomial 0)) := by
  -- Evaluate the quotient lift on the standard north-chart representative `[1, u]`.
  rw [complex_projective_line_polynomial_map, complexProjectiveChart_symm_apply,
    Projectivization.lift_mk, complexProjectiveChart_mk]
  -- In one complex dimension, the chart has a single coordinate equal to second/first.
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp [complex_projective_line_tuple_second_coord, complex_projective_line_tuple_first_coord,
    complexProjectiveChartInvVector, EuclideanSpace.single]

/-- Helper for Problem 2-9: the zero polynomial induces the constant map with value `G 0`. -/
lemma complex_projective_line_polynomial_map_zero :
    complex_projective_line_polynomial_map (0 : Polynomial ℂ) = fun _ : ℂP[1] ↦ G 0 := by
  -- Evaluate the quotient lift on an arbitrary representative and identify the homogeneous pair
  -- with the fixed affine vector `[0, 1]`.
  funext x
  induction x using Projectivization.ind with
  | h v hv =>
      rw [complex_projective_line_polynomial_map, Projectivization.lift_mk]
      have htuple :
          complex_projective_line_polynomial_tuple (0 : Polynomial ℂ) ⟨v, hv⟩ =
            complex_projective_line_affine_vector 0 := by
        -- For the zero polynomial, the numerator is identically zero and the denominator is `1`.
        ext i
        fin_cases i
        · simp [complex_projective_line_polynomial_tuple, complex_projective_line_affine_vector,
            Polynomial.toTupleMvPolynomial_zero_eq]
        · simp [complex_projective_line_polynomial_tuple, complex_projective_line_affine_vector,
            Polynomial.toTupleMvPolynomial_one_eq]
      simpa [htuple] using (complex_projective_line_affine_mk_eq_G (0 : ℂ))

/-- Helper for Problem 2-9: inserting a complex scalar into the unique affine coordinate of
`EuclideanSpace ℂ (Fin 1)` is Euclidean-smooth. -/
lemma complex_projective_line_single_contDiff :
    ContDiff ℝ ∞
      (fun z : ℂ ↦ (EuclideanSpace.single (0 : Fin 1) z : EuclideanSpace ℂ (Fin 1))) := by
  -- In one complex dimension, inserting the unique affine coordinate is just scalar multiplication
  -- of the fixed basis vector `single 0 1`.
  have hsingle_eq :
      (fun z : ℂ ↦ (EuclideanSpace.single (0 : Fin 1) z : EuclideanSpace ℂ (Fin 1))) =
        fun z : ℂ ↦ z • EuclideanSpace.single (0 : Fin 1) (1 : ℂ) := by
    funext z
    ext i
    simp [PiLp.smul_apply]
  rw [hsingle_eq]
  simpa using
    (contDiff_id.smul
      (contDiff_const : ContDiff ℝ ∞ fun _ : ℂ ↦
        (EuclideanSpace.single (0 : Fin 1) (1 : ℂ) : EuclideanSpace ℂ (Fin 1))))

/-- Helper for Problem 2-9: the affine local model `u ↦ (p(u), 0)` is Euclidean-smooth. -/
lemma complex_projective_line_south_local_model_contDiff (p : Polynomial ℂ) :
    ContDiff ℝ ∞
      (fun u : EuclideanSpace ℂ (Fin 1) ↦
        EuclideanSpace.single (0 : Fin 1) (p.eval (u 0))) := by
  -- Separate the scalar polynomial evaluation from the fixed insertion into the Euclidean model.
  have happly :
      ContDiff ℝ ∞ (fun u : EuclideanSpace ℂ (Fin 1) ↦ u 0) :=
    contDiff_piLp_apply (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 1 ↦ ℂ) (i := 0)
  have hscalar : ContDiff ℝ ∞ (fun u : EuclideanSpace ℂ (Fin 1) ↦ p.eval (u 0)) := by
    -- Polynomial evaluation is complex-smooth, hence also real-smooth after restricting scalars.
    simpa using
      ((Polynomial.contDiff_aeval (R := ℂ) (𝕜 := ℂ) p (∞)).restrict_scalars ℝ).comp happly
  exact complex_projective_line_single_contDiff.comp hscalar

/-- Helper for Problem 2-9: each standard chart of `ℂP¹` already lies in the smooth maximal
atlas. -/
lemma complex_projective_line_chart_mem_maximalAtlas (i : Fin 2) :
    complexProjectiveChart 1 i ∈ IsManifold.maximalAtlas Icp1 ∞ (ℂP[1]) := by
  -- The projective-space atlas is generated by the standard affine charts.
  have hAtlas : complexProjectiveChart 1 i ∈ atlas (EuclideanSpace ℂ (Fin 1)) (ℂP[1]) := by
    change complexProjectiveChart 1 i ∈ { e | ∃ j : Fin (1 + 1), e = complexProjectiveChart 1 j }
    exact ⟨i, rfl⟩
  exact IsManifold.subset_maximalAtlas hAtlas

/-- Helper for Problem 2-9: on the affine open, the polynomial map still lands in the last chart. -/
lemma complex_projective_line_south_image_mem_chart_one (p : Polynomial ℂ) {x : ℂP[1]}
    (hx : x ∈ complexProjectiveAffineOpen 1) :
    complex_projective_line_polynomial_map p x ∈
      (complexProjectiveChart 1 (Fin.last 1)).source := by
  let u : EuclideanSpace ℂ (Fin 1) := complexProjectiveChart 1 (Fin.last 1) x
  have hxsource : x ∈ (complexProjectiveChart 1 (Fin.last 1)).source := by
    simpa [complexProjectiveAffineOpen] using hx
  have hxeq : x = G (u 0) := by
    -- Write `x` through the fixed affine chart and identify the inverse chart with `G`.
    calc
      x = (complexProjectiveChart 1 (Fin.last 1)).symm u := by
        symm
        exact (complexProjectiveChart 1 (Fin.last 1)).left_inv hxsource
      _ = G (u 0) := complex_projective_line_chart_one_symm_eq_G u
  -- After rewriting through `G`, the affine compatibility of the map gives the image.
  rw [hxeq, complex_projective_line_polynomial_affine_eq]
  change G (p.eval (u 0)) ∈ complexProjectiveAffineOpen 1
  simpa [complexProjectiveAffineInclusion, complexProjectiveAffineOpen] using
    complexProjectiveChart_symm_mem_domain 1 (Fin.last 1)
      (EuclideanSpace.single (0 : Fin 1) (p.eval (u 0)))

/-- Helper for Problem 2-9: every affine-open point sees the polynomial map through the last chart
as the Euclidean polynomial `u ↦ p(u)`. -/
lemma complex_projective_line_south_branch_contMDiffAt (p : Polynomial ℂ) {x : ℂP[1]}
    (hx : x ∈ complexProjectiveAffineOpen 1) :
    ContMDiffAt Icp1 Icp1 ∞ (complex_projective_line_polynomial_map p) x := by
  let e := complexProjectiveChart 1 (Fin.last 1)
  let x' : EuclideanSpace ℂ (Fin 1) := (e.extend Icp1) x
  have he : e ∈ IsManifold.maximalAtlas Icp1 ∞ (ℂP[1]) :=
    complex_projective_line_chart_mem_maximalAtlas (Fin.last 1)
  have hxsource : x ∈ e.source := by
    simpa [e, complexProjectiveAffineOpen] using hx
  have hy : complex_projective_line_polynomial_map p x ∈ e.source := by
    simpa [e] using complex_projective_line_south_image_mem_chart_one p hx
  -- Route correction: package the affine branch entirely in the fixed last chart, then replace
  -- the chart expression by the explicit polynomial model on a neighborhood of `x'`.
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas
    (I := Icp1) (I' := Icp1) (e := e) (e' := e) he he hxsource hy,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨(complex_projective_line_polynomial_map_continuous p).continuousAt, ?_⟩
  have hmodel :
      ContDiffWithinAt ℝ ∞
        (fun u : EuclideanSpace ℂ (Fin 1) ↦
          EuclideanSpace.single (0 : Fin 1) (p.eval (u 0)))
        (Set.range Icp1) x' := by
    -- The Euclidean polynomial model is globally smooth, hence smooth within the model range.
    exact (complex_projective_line_south_local_model_contDiff p).contDiffWithinAt
  have htarget_mem : (e.extend Icp1).target ∈ nhdsWithin x' (Set.range Icp1) := by
    -- The extended chart target is the canonical neighborhood used by the manifold smoothness API.
    simpa [e, x'] using (e.extend_target_mem_nhdsWithin (I := Icp1) hxsource)
  have hEq :
      ((e.extend Icp1) ∘ complex_projective_line_polynomial_map p ∘ (e.extend Icp1).symm)
        =ᶠ[nhdsWithin x' (Set.range Icp1)]
          (fun u : EuclideanSpace ℂ (Fin 1) ↦
            EuclideanSpace.single (0 : Fin 1) (p.eval (u 0))) := by
    -- On the extended-chart target, the conjugated map is exactly the affine polynomial formula.
    refine Filter.eventuallyEq_of_mem htarget_mem ?_
    intro z hz
    simpa [e, Function.comp, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.extend_coe] using complex_projective_line_south_chart_formula p z
  have hx'_target : x' ∈ (e.extend Icp1).target :=
    (e.extend Icp1).map_source <| by
      simpa [e, OpenPartialHomeomorph.extend_source] using hxsource
  have hx'_range : x' ∈ Set.range Icp1 := e.extend_target_subset_range hx'_target
  -- Replace the chart expression by the already-proved Euclidean local model.
  exact hmodel.congr_of_eventuallyEq hEq <| hEq.eq_of_nhdsWithin hx'_range

/-- Helper for Problem 2-9: the north-chart inverse vector has first coordinate `1`. -/
lemma complex_projective_line_chart_zero_invVector_zero (u : EuclideanSpace ℂ (Fin 1)) :
    complexProjectiveChartInvVector 1 0 u 0 = 1 := by
  -- The chart inserts the distinguished homogeneous coordinate `1` in the zeroth slot.
  simp [complexProjectiveChartInvVector]

/-- Helper for Problem 2-9: the north-chart inverse vector has second coordinate equal to the
unique affine coordinate. -/
lemma complex_projective_line_chart_zero_invVector_one (u : EuclideanSpace ℂ (Fin 1)) :
    complexProjectiveChartInvVector 1 0 u 1 = u 0 := by
  -- Away from the inserted zeroth coordinate, the chart inverse simply reads off the affine data.
  simp [complexProjectiveChartInvVector]

/-- Helper for Problem 2-9: the denominator in the north-chart formula is the reverse polynomial
evaluated at the affine coordinate. -/
lemma complex_projective_line_north_denominator_eq_reverse_eval (p : Polynomial ℂ)
    (u : EuclideanSpace ℂ (Fin 1)) :
    MvPolynomial.eval (complexProjectiveChartInvVector 1 0 u) (p.toTupleMvPolynomial 0) =
      p.reverse.eval (u 0) := by
  -- Expand the homogenization at the north-chart vector `[1, u]`, then read the resulting finite
  -- sum as the reverse polynomial evaluated at the affine coordinate.
  rw [Polynomial.toTupleMvPolynomial_zero_eq, Polynomial.homogenize, MvPolynomial.eval_sum]
  calc
    ∑ i ∈ Finset.antidiagonal p.natDegree,
        (MvPolynomial.eval (complexProjectiveChartInvVector 1 0 u).ofLp)
          ((MvPolynomial.monomial (fun₀ | 0 => i.1 | 1 => i.2) (p.coeff i.1)))
      =
        ∑ i ∈ Finset.antidiagonal p.natDegree,
          (MvPolynomial.eval (complexProjectiveChartInvVector 1 0 u).ofLp)
            ((MvPolynomial.monomial (fun₀ | 0 => i.2 | 1 => i.1) (p.coeff i.2))) := by
            simpa using
              (Finset.Nat.sum_antidiagonal_swap
                (n := p.natDegree)
                (f := fun ij : ℕ × ℕ ↦
                  (MvPolynomial.eval (complexProjectiveChartInvVector 1 0 u).ofLp)
                    ((MvPolynomial.monomial (fun₀ | 0 => ij.2 | 1 => ij.1)
                      (p.coeff ij.2)))))
    _ = ∑ k ∈ Finset.range p.natDegree.succ,
          (MvPolynomial.eval (complexProjectiveChartInvVector 1 0 u).ofLp)
            ((MvPolynomial.monomial (fun₀ | 0 => p.natDegree - k | 1 => k)
              (p.coeff (p.natDegree - k)))) := by
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j ↦
                (MvPolynomial.eval (complexProjectiveChartInvVector 1 0 u).ofLp)
                  ((MvPolynomial.monomial (fun₀ | 0 => j | 1 => i) (p.coeff j))))
              p.natDegree]
  rw [Polynomial.eval_eq_sum_range' (p := p.reverse)
    (n := p.natDegree + 1) (Nat.lt_succ_iff.mpr p.reverse_natDegree_le)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  -- The north chart fixes the first homogeneous coordinate to `1` and the second to `u 0`.
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le hk_le]
  simp [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single,
    complex_projective_line_chart_zero_invVector_zero,
    complex_projective_line_chart_zero_invVector_one]

/-- Helper for Problem 2-9: the image of the point at infinity lies in the north chart whenever
the polynomial is nonzero. -/
lemma complex_projective_line_north_image_mem_chart_zero (p : Polynomial ℂ) (hp : p ≠ 0) :
    complex_projective_line_polynomial_map p ((complexProjectiveChart 1 0).symm 0) ∈
      (complexProjectiveChart 1 0).source := by
  -- Evaluate the quotient lift on the standard infinity representative and check its first
  -- homogeneous coordinate using the leading coefficient computation.
  rw [complex_projective_line_polynomial_map, complexProjectiveChart_symm_apply,
    Projectivization.lift_mk]
  have hfirst :
      complex_projective_line_polynomial_tuple p
          ⟨complexProjectiveChartInvVector 1 0 0,
            complexProjectiveChartInvVector_ne_zero 1 0 0⟩ 0 ≠ 0 := by
    rw [complex_projective_line_tuple_first_coord]
    exact complex_projective_line_north_chart_denominator_ne_zero p hp
  simpa using
    (complexProjectiveChartDomain_mk 1 0
      (complex_projective_line_polynomial_tuple p
        ⟨complexProjectiveChartInvVector 1 0 0, complexProjectiveChartInvVector_ne_zero 1 0 0⟩)
      (complex_projective_line_polynomial_tuple_ne_zero p
        ⟨complexProjectiveChartInvVector 1 0 0,
          complexProjectiveChartInvVector_ne_zero 1 0 0⟩)).2 hfirst

/-- Helper for Problem 2-9: the north-chart local model is Euclidean-smooth at the origin for a
nonzero polynomial. -/
lemma complex_projective_line_north_local_model_contDiffAt_zero (p : Polynomial ℂ) (hp : p ≠ 0) :
    ContDiffAt ℝ ∞
      (fun u : EuclideanSpace ℂ (Fin 1) ↦
        EuclideanSpace.single (0 : Fin 1)
          ((u 0) ^ p.natDegree / MvPolynomial.eval
            (complexProjectiveChartInvVector 1 0 u) (p.toTupleMvPolynomial 0))) 0 := by
  -- Rewrite the denominator to the one-variable reverse polynomial, prove the scalar quotient is
  -- smooth at `0`, then reinsert it into the Euclidean coordinate.
  have happly :
      ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℂ (Fin 1) ↦ u 0) 0 :=
    (contDiff_piLp_apply (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 1 ↦ ℂ) (i := 0)).contDiffAt
  have hnum :
      ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℂ (Fin 1) ↦ (u 0) ^ p.natDegree) 0 :=
    happly.pow p.natDegree
  have hden :
      ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℂ (Fin 1) ↦ p.reverse.eval (u 0)) 0 := by
    -- The denominator is just the reverse polynomial evaluated in the unique affine coordinate.
    have hreverse : ContDiff ℝ ∞ (fun u : ℂ ↦ p.reverse.eval u) := by
      simpa using
        ((Polynomial.contDiff_aeval (R := ℂ) (𝕜 := ℂ) p.reverse (∞)).restrict_scalars ℝ)
    simpa using hreverse.contDiffAt.comp 0 happly
  have hden_ne :
      p.reverse.eval ((0 : EuclideanSpace ℂ (Fin 1)) 0) ≠ 0 := by
    -- At the chart origin this scalar denominator is the nonzero leading coefficient.
    simpa [complex_projective_line_north_denominator_eq_reverse_eval] using
      complex_projective_line_north_chart_denominator_ne_zero p hp
  have hquot :
      ContDiffAt ℝ ∞
        (fun u : EuclideanSpace ℂ (Fin 1) ↦
          (u 0) ^ p.natDegree / p.reverse.eval (u 0)) 0 :=
    by
      -- Over `ℝ`, division in `ℂ` is handled as multiplication by the inverse denominator.
      simpa [div_eq_mul_inv] using hnum.mul (hden.inv hden_ne)
  -- Reinsert the scalar quotient into the unique Euclidean coordinate.
  simpa [complex_projective_line_north_denominator_eq_reverse_eval] using
    (complex_projective_line_single_contDiff.contDiffAt.comp 0 hquot)

/-- Helper for Problem 2-9: the point at infinity sees the polynomial map through the north chart
as the Euclidean rational local model. -/
lemma complex_projective_line_north_branch_contMDiffAt_infinity (p : Polynomial ℂ) (hp : p ≠ 0) :
    ContMDiffAt Icp1 Icp1 ∞ (complex_projective_line_polynomial_map p)
      ((complexProjectiveChart 1 0).symm 0) := by
  let e := complexProjectiveChart 1 0
  let x : ℂP[1] := (complexProjectiveChart 1 0).symm 0
  let x' : EuclideanSpace ℂ (Fin 1) := (e.extend Icp1) x
  have he : e ∈ IsManifold.maximalAtlas Icp1 ∞ (ℂP[1]) :=
    complex_projective_line_chart_mem_maximalAtlas 0
  have hxsource : x ∈ e.source := by
    -- The north chart inverse is defined at every affine coordinate, in particular at `0`.
    simpa [e, x] using complexProjectiveChart_symm_mem_domain 1 0
      (0 : EuclideanSpace ℂ (Fin 1))
  have hy : complex_projective_line_polynomial_map p x ∈ e.source := by
    simpa [e, x] using complex_projective_line_north_image_mem_chart_zero p hp
  have hx'_eq : x' = 0 := by
    -- The extended north chart sends its own inverse image of `0` back to the chart origin.
    change Icp1 (complexProjectiveChart 1 0 ((complexProjectiveChart 1 0).symm 0)) = 0
    rw [OpenPartialHomeomorph.right_inv (complexProjectiveChart 1 0)
      (Set.mem_univ (0 : EuclideanSpace ℂ (Fin 1)))]
    rfl
  -- Route correction: package the infinity branch in the fixed north chart and replace the chart
  -- expression by the explicit rational local model near the chart origin.
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas
    (I := Icp1) (I' := Icp1) (e := e) (e' := e) he he hxsource hy,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨(complex_projective_line_polynomial_map_continuous p).continuousAt, ?_⟩
  have hmodel :
      ContDiffWithinAt ℝ ∞
        (fun u : EuclideanSpace ℂ (Fin 1) ↦
          EuclideanSpace.single (0 : Fin 1)
            ((u 0) ^ p.natDegree /
              MvPolynomial.eval (complexProjectiveChartInvVector 1 0 u) (p.toTupleMvPolynomial 0)))
        (Set.range Icp1) x' := by
    -- The Euclidean infinity model is smooth at the chart origin and hence within the model range.
    simpa [hx'_eq] using
      (complex_projective_line_north_local_model_contDiffAt_zero p hp).contDiffWithinAt
  have htarget_mem : (e.extend Icp1).target ∈ nhdsWithin x' (Set.range Icp1) := by
    -- The extended north-chart target gives the neighborhood where the chart formula is valid.
    have hxe : (e x : EuclideanSpace ℂ (Fin 1)) = 0 := by
      simpa [e, x, x'] using hx'_eq
    have htarget_mem_zero : (e.extend Icp1).target ∈ nhdsWithin 0 (Set.range Icp1) := by
      simpa [e, hxe] using (e.extend_target_mem_nhdsWithin (I := Icp1) hxsource)
    simpa [hx'_eq] using htarget_mem_zero
  have hEq :
      ((e.extend Icp1) ∘ complex_projective_line_polynomial_map p ∘ (e.extend Icp1).symm)
        =ᶠ[nhdsWithin x' (Set.range Icp1)]
          (fun u : EuclideanSpace ℂ (Fin 1) ↦
            EuclideanSpace.single (0 : Fin 1)
              ((u 0) ^ p.natDegree / MvPolynomial.eval
                (complexProjectiveChartInvVector 1 0 u) (p.toTupleMvPolynomial 0))) := by
    -- On the extended-chart target, the conjugated map is exactly the north-chart formula.
    refine Filter.eventuallyEq_of_mem htarget_mem ?_
    intro z hz
    simpa [e, Function.comp, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.extend_coe] using complex_projective_line_north_chart_formula p z
  have hx'_target : x' ∈ (e.extend Icp1).target :=
    (e.extend Icp1).map_source <| by
      simpa [e, OpenPartialHomeomorph.extend_source] using hxsource
  have hx'_range : x' ∈ Set.range Icp1 := e.extend_target_subset_range hx'_target
  -- Replace the chart expression by the explicit Euclidean local model at the chart origin.
  exact hmodel.congr_of_eventuallyEq hEq <| hEq.eq_of_nhdsWithin hx'_range

/-- Helper for Problem 2-9: the missing step is the chartwise smoothness proof for the lifted
projective polynomial map. -/
lemma complex_projective_line_polynomial_map_contMDiff (p : Polynomial ℂ) :
    ContMDiff Icp1 Icp1 ∞ (complex_projective_line_polynomial_map p) := by
  by_cases hp : p = 0
  · -- The zero polynomial case is the constant map `x ↦ G 0`.
    rw [hp, complex_projective_line_polynomial_map_zero]
    simpa using (contMDiff_const : ContMDiff Icp1 Icp1 ∞ (fun _ : ℂP[1] ↦ G 0))
  · intro x
    by_cases hx : x ∈ complexProjectiveAffineOpen 1
    · -- On the affine open, the south-chart packaging already gives the smoothness.
      exact complex_projective_line_south_branch_contMDiffAt p hx
    · -- Outside the affine open, `x` is the unique point at infinity handled by the north chart.
      have hx_inf : x = (complexProjectiveChart 1 0).symm 0 :=
        complex_projective_line_affine_open_compl_eq_infinity x hx
      simpa [hx_inf] using complex_projective_line_north_branch_contMDiffAt_infinity p hp

/-- Helper for Problem 2-9: a vector in the one-dimensional complex Euclidean space is determined
by its unique coordinate. -/
lemma complex_one_dimensional_vector_eq_single (z : EuclideanSpace ℂ (Fin 1)) :
    EuclideanSpace.single (0 : Fin 1) (z 0) = z := by
  -- In `Fin 1`, every index is the distinguished coordinate `0`.
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp

/-- Helper for Problem 2-9: the affine inclusion `G : ℂ → ℂP¹` has image equal to the standard
affine open subset of `ℂP¹`. -/
lemma range_complexProjectiveLine_affineInclusion :
    Set.range G = complexProjectiveAffineOpen 1 := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    -- Points of the form `[z, 1]` lie in the standard affine chart by construction.
    change complexProjectiveAffineInclusion 1 (EuclideanSpace.single (0 : Fin 1) z) ∈
      complexProjectiveAffineOpen 1
    simpa [complexProjectiveAffineOpen, complexProjectiveAffineInclusion] using
      complexProjectiveChart_symm_mem_domain 1 (Fin.last 1)
        (EuclideanSpace.single (0 : Fin 1) z)
  · intro hx
    let y : complexProjectiveAffineOpen 1 := ⟨x, hx⟩
    let u : EuclideanSpace ℂ (Fin 1) := complexProjectiveAffineChart 1 y
    refine ⟨u 0, ?_⟩
    have hu_open : complexProjectiveAffineInclusionToOpen 1 u = y := by
      -- The affine chart and affine inclusion are inverse on the affine open subset.
      simpa [u, y] using complexProjectiveAffineInclusion_right_inv 1 y
    have hu_val : complexProjectiveAffineInclusion 1 u = x := by
      -- Forgetting the subtype recovers the ambient projective point.
      simpa [u, y, complexProjectiveAffineInclusionToOpen_coe] using congrArg Subtype.val hu_open
    -- In one complex dimension, every affine vector is `single 0` of its unique coordinate.
    change complexProjectiveAffineInclusion 1 (EuclideanSpace.single (0 : Fin 1) (u 0)) = x
    simpa [complex_one_dimensional_vector_eq_single u] using hu_val

/-- Helper for Problem 2-9: a smooth self-map of `ℂP¹` is determined by its restriction to the
dense affine image of `G`. -/
lemma complexProjectiveLine_smoothMap_ext_on_affine
    {f g : C^∞⟮Icp1, ℂP[1]; Icp1, ℂP[1]⟯}
    (hfg : f ∘ G = g ∘ G) :
    f = g := by
  have h_dense : Dense (Set.range G) := by
    -- Problem 2-8 identifies `range G` with the dense standard affine open subset.
    simpa [range_complexProjectiveLine_affineInclusion] using
      complexProjectiveAffineOpen_dense (n := 1)
  have h_eqOn : Set.EqOn f g (Set.range G) := by
    intro x hx
    rcases hx with ⟨z, rfl⟩
    exact congrFun hfg z
  have hfun : (f : ℂP[1] → ℂP[1]) = g := by
    -- Continuous maps into Hausdorff spaces agree globally once they agree on a dense set.
    exact Continuous.ext_on h_dense f.contMDiff.continuous g.contMDiff.continuous h_eqOn
  exact ContMDiffMap.ext fun x ↦ congrFun hfun x

/-- Problem 2-9: every complex polynomial extends uniquely to a bundled smooth self-map of `ℂP¹`
whose restriction along the affine inclusion `G : ℂ → ℂP¹` agrees with polynomial evaluation. -/
theorem exists_unique_smooth_complexProjectiveLine_polynomial_extension
    (p : Polynomial ℂ) :
    ∃! p_tilde : C^∞⟮Icp1, ℂP[1]; Icp1, ℂP[1]⟯,
      p_tilde ∘ G = G ∘ fun z : ℂ ↦ p.eval z := by
  let p_tilde : C^∞⟮Icp1, ℂP[1]; Icp1, ℂP[1]⟯ :=
    ⟨complex_projective_line_polynomial_map p,
      complex_projective_line_polynomial_map_contMDiff p⟩
  have hp_tilde : p_tilde ∘ G = G ∘ fun z : ℂ ↦ p.eval z := by
    -- The lifted projective map agrees with polynomial evaluation on the affine chart.
    funext z
    exact complex_projective_line_polynomial_affine_eq p z
  refine ⟨p_tilde, hp_tilde, ?_⟩
  · intro q hq
    -- Equality on the dense affine image of `G` determines a smooth self-map of `ℂP¹`.
    exact complexProjectiveLine_smoothMap_ext_on_affine (f := q) (g := p_tilde) <|
      calc
        q ∘ G = G ∘ fun z : ℂ ↦ p.eval z := hq
        _ = p_tilde ∘ G := hp_tilde.symm
