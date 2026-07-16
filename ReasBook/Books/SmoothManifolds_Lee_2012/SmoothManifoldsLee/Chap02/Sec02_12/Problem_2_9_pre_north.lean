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
    simpa [hzero]
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
  rw [complex_projective_line_vector_eq_of_second_coord_zero v h1, Polynomial.toTupleMvPolynomial_zero_eq]
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
      exact hsecond (by simpa [hzero])
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
      exact hfirst (by simpa [hzero])
  · -- On the affine chart, the denominator coordinate is the nonzero monomial `v₁ ^ deg p`.
    have hsecond :
        complex_projective_line_polynomial_tuple p v 1 ≠ 0 := by
      rw [complex_projective_line_tuple_second_coord]
      exact pow_ne_zero _ h1
    intro hzero
    exact hsecond (by simpa [hzero])

/-- Helper for Problem 2-9: evaluating a homogeneous bivariate polynomial on a scaled vector
pulls out the expected scalar power. -/
lemma complex_projective_line_homogeneous_eval_smul
    (q : MvPolynomial (Fin 2) ℂ) (n : ℕ) (hq : q.IsHomogeneous n) (x : CVec) (t : ℂ) :
    MvPolynomial.eval (t • x) q = t ^ n * MvPolynomial.eval x q := by
  -- Expand into monomials and use homogeneity to identify the total exponent of `t`.
  rw [q.as_sum, MvPolynomial.eval_sum]
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
                  simp [Finsupp.prod, smul_eq_mul]
            _ = q.coeff d * ∏ i ∈ d.support, (t ^ d i * x i ^ d i) := by
                  simp_rw [mul_pow]
            _ = q.coeff d * ((∏ i ∈ d.support, t ^ d i) * ∏ i ∈ d.support, x i ^ d i) := by
                  rw [Finset.prod_mul_distrib]
            _ = q.coeff d * (t ^ (∑ i ∈ d.support, d i) * ∏ i ∈ d.support, x i ^ d i) := by
                  rw [Finset.prod_pow_eq_pow_sum]
            _ = q.coeff d * (t ^ n * ∏ i ∈ d.support, x i ^ d i) := by
                  rw [← hd_degree]
            _ = t ^ n * (q.coeff d * ∏ i ∈ d.support, x i ^ d i) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
            _ = t ^ n * MvPolynomial.eval x (MvPolynomial.monomial d (q.coeff d)) := by
                  rw [MvPolynomial.eval_monomial, Finsupp.prod]
    _ = t ^ n * ∑ d ∈ q.support, MvPolynomial.eval x (MvPolynomial.monomial d (q.coeff d)) := by
          rw [← Finset.mul_sum]
    _ = t ^ n * MvPolynomial.eval x q := by
          congr 1
          symm
          rw [q.as_sum, MvPolynomial.eval_sum]

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
      simp [Pi.smul_apply, smul_eq_mul, mul_pow]
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
      simpa [complex_projective_line_affine_vector_one]
    change complex_projective_line_polynomial_tuple p
        ⟨complex_projective_line_affine_vector z, complex_projective_line_affine_vector_ne_zero z⟩ 0 =
      complex_projective_line_affine_vector (p.eval z) 0
    rw [complex_projective_line_tuple_first_coord, Polynomial.toTupleMvPolynomial_zero_eq]
    rw [Polynomial.eval_homogenize (p := p) (n := p.natDegree) le_rfl
      (complex_projective_line_affine_vector z) hz1]
    simp [complex_projective_line_affine_vector_zero, complex_projective_line_affine_vector_one,
      complex_projective_line_affine_vector]
  · change complex_projective_line_polynomial_tuple p
        ⟨complex_projective_line_affine_vector z, complex_projective_line_affine_vector_ne_zero z⟩ 1 =
      complex_projective_line_affine_vector (p.eval z) 1
    rw [complex_projective_line_tuple_second_coord]
    simp [complex_projective_line_affine_vector_one, complex_projective_line_affine_vector]

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
    simpa [complexProjectiveChartInvVector, complex_projective_line_affine_vector] using
      (Fin.insertNth_apply_same (α := fun _ : Fin 2 ↦ ℂ) (i := Fin.last 1) (x := (1 : ℂ))
        (p := EuclideanSpace.single (0 : Fin 1) z))

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
  simpa [hu]

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
    simpa [complexProjectiveChartInvVector] using
      (Fin.insertNth_apply_same (α := fun _ : Fin 2 ↦ ℂ) (i := (0 : Fin 2)) (x := (1 : ℂ))
        (p := (0 : Fin 1 → ℂ)))
  · -- The remaining coordinate comes from the zero affine vector.
    simpa [complexProjectiveChartInvVector] using
      (Fin.insertNth_apply_succAbove (α := fun _ : Fin 2 ↦ ℂ) (i := (0 : Fin 2)) (x := (1 : ℂ))
        (p := (0 : Fin 1 → ℂ)) 0)

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
  · simp [complexProjectiveChartInvVector, hrep0]
  · simp [complexProjectiveChartInvVector, hrep1]

/-- Helper for Problem 2-9: on the affine chart, the lifted projective map is exactly polynomial
evaluation in the unique affine coordinate. -/
lemma complex_projective_line_south_chart_formula (p : Polynomial ℂ)
    (u : EuclideanSpace ℂ (Fin 1)) :
    complexProjectiveChart 1 (Fin.last 1)
      (complex_projective_line_polynomial_map p ((complexProjectiveChart 1 (Fin.last 1)).symm u)) =
        EuclideanSpace.single (0 : Fin 1) (p.eval (u 0)) := by
  -- Follow the affine chart through the already-proved affine compatibility.
  calc
    complexProjectiveChart 1 (Fin.last 1)
        (complex_projective_line_polynomial_map p ((complexProjectiveChart 1 (Fin.last 1)).symm u))
      = complexProjectiveChart 1 (Fin.last 1)
          (complex_projective_line_polynomial_map p (G (u 0))) := by
