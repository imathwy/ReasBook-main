import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Separation.CompletelyRegular

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_1 (from Items/Chap15) -/
open BoundedContinuousFunction
open scoped BoundedContinuousFunction

universe u

variable {E : Type u} [TopologicalSpace E]

/- Recall: for `𝕜 = ℝ` or `𝕜 = ℂ`, an algebra of bounded continuous `𝕜`-valued functions on `E`
is canonically a subalgebra of the bounded continuous function algebra `E →ᵇ 𝕜`. -/
#check (Subalgebra ℝ (E →ᵇ ℝ))
#check (Subalgebra ℂ (E →ᵇ ℂ))

/- The canonical bridge from bounded continuous functions to continuous maps is the algebra
homomorphism `toContinuousMapₐ`. -/
#check (toContinuousMapₐ ℝ : (E →ᵇ ℝ) →ₐ[ℝ] C(E, ℝ))
#check (toContinuousMapₐ ℂ : (E →ᵇ ℂ) →ₐ[ℂ] C(E, ℂ))

/- Definition 15.1: for a bounded-continuous-function algebra on `E`, the textbook
point-separation notion is the owner predicate `Subalgebra.SeparatesPoints` on the mapped
subalgebra of `C(E, 𝕜)`. Thus the primitive data is the subalgebra `A`, and the separation clause
is derived after applying `A.map (toContinuousMapₐ 𝕜)`. -/
#check (fun A : Subalgebra ℝ (E →ᵇ ℝ) ↦ (A.map (toContinuousMapₐ ℝ)).SeparatesPoints)
#check (fun A : Subalgebra ℂ (E →ᵇ ℂ) ↦ (A.map (toContinuousMapₐ ℂ)).SeparatesPoints)

/-! ### Exercise_15_1_1 (from Items/Chap15) -/
open BoundedContinuousFunction
open scoped BoundedContinuousFunction Topology

noncomputable section

private def arctanBCF : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup Real.arctan Real.continuous_arctan (Real.pi / 2)
    fun x ↦ by
      rw [Real.norm_eq_abs]
      refine abs_le.2 ?_
      constructor
      · linarith [Real.neg_pi_div_two_lt_arctan x]
      · linarith [Real.arctan_lt_pi_div_two x]

private def sinBCF : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup Real.sin Real.continuous_sin 1 fun x ↦ by
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one x

private theorem eval_aeval_bcf (g : ℝ →ᵇ ℝ) (p : Polynomial ℝ) (x : ℝ) :
    (Polynomial.aeval g p : ℝ →ᵇ ℝ) x = p.eval (g x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [Polynomial.eval_add, hp, hq]
  | monomial n a =>
      simp [Polynomial.eval_monomial]

private theorem arctanBCF_injective : Function.Injective arctanBCF := by
  intro x y hxy
  exact Real.arctan_injective hxy

private theorem arctan_adjoin_separatesPoints :
    ((Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ))).map (toContinuousMapₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  refine ⟨toContinuousMapₐ ℝ arctanBCF, ?_, ?_⟩
  · refine ⟨toContinuousMapₐ ℝ arctanBCF, ?_, rfl⟩
    refine Subalgebra.mem_map.2 ?_
    exact ⟨(arctanBCF : ℝ →ᵇ ℝ), Algebra.self_mem_adjoin_singleton ℝ arctanBCF, rfl⟩
  · simpa using fun h : arctanBCF x = arctanBCF y ↦ hxy (arctanBCF_injective h)

private theorem tendsto_atTop_of_mem_arctanAdjoin {f : ℝ →ᵇ ℝ}
    (hf : f ∈ Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ))) :
    ∃ l : ℝ, Filter.Tendsto (fun x ↦ f x) Filter.atTop (𝓝 l) := by
  rcases Algebra.adjoin_mem_exists_aeval ℝ arctanBCF hf with ⟨p, rfl⟩
  refine ⟨p.eval (Real.pi / 2), ?_⟩
  have harctan : Filter.Tendsto (fun x ↦ arctanBCF x) Filter.atTop (𝓝 (Real.pi / 2)) := by
    simpa [arctanBCF] using
      tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have hpoly :
      Filter.Tendsto (fun x ↦ p.eval (arctanBCF x)) Filter.atTop (𝓝 (p.eval (Real.pi / 2))) :=
    p.continuous.tendsto _ |>.comp harctan
  simpa [eval_aeval_bcf] using hpoly

private theorem sin_far_from_arctanAdjoin {f : ℝ →ᵇ ℝ}
    (hf : f ∈ Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ))) :
    1 / 4 ≤ dist sinBCF f := by
  refine le_of_not_gt ?_
  intro hdist
  rcases tendsto_atTop_of_mem_arctanAdjoin hf with ⟨l, hl⟩
  have hzero : ∀ n : ℕ, |f ((2 * Real.pi) * n)| < 1 / 4 := by
    intro n
    have hpoint :=
      lt_of_le_of_lt
        (dist_coe_le_dist ((2 * Real.pi) * n) : dist (sinBCF ((2 * Real.pi) * n)) (f ((2 * Real.pi) * n)) ≤ _)
        hdist
    have hsin : Real.sin ((2 * Real.pi) * n) = 0 := by
      have h := Real.sin_add_int_mul_two_pi 0 (n : ℤ)
      simpa [Int.cast_natCast, zero_add, zero_mul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using h
    simpa [sinBCF, Real.dist_eq, hsin] using hpoint
  have hone : ∀ n : ℕ, |1 - f (Real.pi / 2 + (2 * Real.pi) * n)| < 1 / 4 := by
    intro n
    have hpoint :=
      lt_of_le_of_lt
        (dist_coe_le_dist (Real.pi / 2 + (2 * Real.pi) * n) :
          dist (sinBCF (Real.pi / 2 + (2 * Real.pi) * n))
            (f (Real.pi / 2 + (2 * Real.pi) * n)) ≤ _)
        hdist
    have hsin : Real.sin (Real.pi / 2 + (2 * Real.pi) * n) = 1 := by
      have h := Real.sin_add_int_mul_two_pi (Real.pi / 2) (n : ℤ)
      simpa [Int.cast_natCast, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
    simpa [sinBCF, Real.dist_eq, hsin, abs_sub_comm] using hpoint
  have hseq0 : Filter.Tendsto (fun n : ℕ ↦ (2 * Real.pi : ℝ) * n) Filter.atTop Filter.atTop := by
    simpa [two_mul, mul_comm] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < (2 * Real.pi : ℝ))
  have hseq1 :
      Filter.Tendsto (fun n : ℕ ↦ Real.pi / 2 + (2 * Real.pi : ℝ) * n) Filter.atTop
        Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    have hb : ∀ᶠ n : ℕ in Filter.atTop, b - Real.pi / 2 ≤ (2 * Real.pi : ℝ) * n :=
      hseq0 <| Filter.Ici_mem_atTop (b - Real.pi / 2)
    filter_upwards [hb] with n hn
    linarith
  have hl0 : Filter.Tendsto (fun n : ℕ ↦ f ((2 * Real.pi : ℝ) * n)) Filter.atTop (𝓝 l) :=
    hl.comp hseq0
  have hl1 :
      Filter.Tendsto (fun n : ℕ ↦ f (Real.pi / 2 + (2 * Real.pi : ℝ) * n)) Filter.atTop
        (𝓝 l) :=
    hl.comp hseq1
  have hlt0 : ∀ᶠ n : ℕ in Filter.atTop, |f ((2 * Real.pi : ℝ) * n) - l| < 1 / 8 := by
    have hball : {y : ℝ | |y - l| < 1 / 8} ∈ 𝓝 l := by
      simpa [Metric.ball, Real.dist_eq] using Metric.ball_mem_nhds l (by positivity)
    simpa using hl0 hball
  have hlt1 :
      ∀ᶠ n : ℕ in Filter.atTop, |f (Real.pi / 2 + (2 * Real.pi : ℝ) * n) - l| < 1 / 8 := by
    have hball : {y : ℝ | |l - y| < 1 / 8} ∈ 𝓝 l := by
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using Metric.ball_mem_nhds l (by positivity)
    simpa [abs_sub_comm] using hl1 hball
  rcases Filter.Eventually.exists (hlt0.and hlt1) with ⟨n, hn0, hn1⟩
  have hclose :
      |f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n)| < 1 / 4 := by
    calc
      |f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n)|
          ≤ |f ((2 * Real.pi : ℝ) * n) - l| + |l - f (Real.pi / 2 + (2 * Real.pi) * n)| := by
            simpa using abs_sub_le (f ((2 * Real.pi : ℝ) * n)) l
              (f (Real.pi / 2 + (2 * Real.pi) * n))
      _ < 1 / 8 + 1 / 8 := add_lt_add hn0 (by simpa [abs_sub_comm] using hn1)
      _ = 1 / 4 := by norm_num
  have hx := abs_lt.mp (hzero n)
  have hy := abs_lt.mp (hone n)
  have hneg :
      f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n) < 0 := by
    linarith
  have hfar :
      1 / 2 < |f ((2 * Real.pi : ℝ) * n) - f (Real.pi / 2 + (2 * Real.pi) * n)| := by
    rw [abs_of_neg hneg]
    linarith
  linarith

-- Proof sketch: take a bounded continuous injective function `ℝ → ℝ`, such as `Real.arctan`,
-- and let `A` be the real subalgebra it generates. A singleton generating family is countable,
-- and polynomial expressions in an injective generator still separate points.
/-- A point-separating real subalgebra of bounded continuous functions on `ℝ` can be generated by
a countable family. -/
theorem exists_countable_generating_set_of_separating_subalgebra_boundedContinuousFunction_real :
    ∃ (A : Subalgebra ℝ (ℝ →ᵇ ℝ)) (s : Set (ℝ →ᵇ ℝ)),
      Set.Countable s ∧
        Algebra.adjoin ℝ s = A ∧
          (A.map (toContinuousMapₐ ℝ)).SeparatesPoints := by
  refine ⟨Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ)), {arctanBCF}, Set.countable_singleton _,
    rfl, ?_⟩
  simpa using arctan_adjoin_separatesPoints

-- Proof sketch: use a countably generated point-separating real subalgebra as above. If it were
-- dense in `C_b(ℝ)`, then the metric space `ℝ →ᵇ ℝ` would be separable because the algebra
-- generated by a countable family is separable, contradicting the standard nonseparability of
-- `C_b(ℝ)`.
/-- Exercise 15.1.1: compactness is essential in Stone--Weierstrass, since there exists a
point-separating real subalgebra of `C_b(ℝ)` that is not dense in the supremum norm topology. -/
theorem stoneWeierstrass_compactness_counterexample_boundedContinuousFunction_real :
    ∃ A : Subalgebra ℝ (ℝ →ᵇ ℝ),
      (A.map (toContinuousMapₐ ℝ)).SeparatesPoints ∧
        ¬ Dense (A : Set (ℝ →ᵇ ℝ)) := by
  refine ⟨Algebra.adjoin ℝ ({arctanBCF} : Set (ℝ →ᵇ ℝ)), ?_, ?_⟩
  · simpa using arctan_adjoin_separatesPoints
  · intro hA
    obtain ⟨f, hf, hdist⟩ :=
      hA.exists_dist_lt sinBCF (show 0 < (1 / 4 : ℝ) by norm_num)
    have hfar := sin_far_from_arctanAdjoin hf
    linarith

/-! ### Exercise_15_1_2 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory

noncomputable section

variable {d : ℕ}
variable {μ ν : Measure (EuclideanSpace ℝ (Fin d))}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

-- Exercise 15.1.2 is a `bridge/view` statement: the textbook Laplace transform on the
-- nonnegative orthant is expressed through the owner `mgf` applied to the linear functional
-- `x ↦ -⟪t, x⟫`, and uniqueness is then reduced to `Measure.ext_of_charFun`.
-- Proof sketch: for each nonnegative `t`, push `μ` and `ν` forward along the linear functional
-- `x ↦ ⟪t, x⟫` and rewrite the hypothesis as equality of the corresponding one-dimensional MGFs.
-- Equality on the nonnegative orthant yields equality of the associated characteristic functions,
-- and `Measure.ext_of_charFun` then identifies the measures.
/-- Exercise 15.1.2: finite measures on `[0, ∞)^d` are determined by their Laplace transforms. If
two finite measures on `ℝ^d` are supported on the nonnegative orthant and have the same Laplace
transform at every nonnegative vector `t`, then the measures are equal. -/
theorem eq_of_laplaceTransform_eq_on_nonnegativeOrthant
    (hμ_nonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i)
    (hν_nonneg : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i)
    (hL :
      ∀ t : EuclideanSpace ℝ (Fin d),
        (∀ i, 0 ≤ t i) → mgf (fun x ↦ -inner ℝ t x) μ 1 = mgf (fun x ↦ -inner ℝ t x) ν 1) :
    μ = ν := sorry

/-! ### Exercise_15_1_3 (from Items/Chap15) -/
open MeasureTheory

open scoped BigOperators

-- Proof sketch: first identify the singleton masses `μ ({x})` with the Fourier coefficients of
-- the `2π`-periodic function induced by `charFun (μ.map latticeEmbedding)` via
-- `discreteFourierInversionFormula`. Then rescale the cube `[-π, π)^d` to the owner Fourier space
-- `UnitAddTorus (Fin d)` and apply mathlib's multivariate Parseval theorem
-- `UnitAddTorus.hasSum_sq_mFourierCoeff`; the present statement keeps the textbook lattice-mass
-- formulation as the source-facing main entry.
/-- Exercise 15.1.3: under the hypotheses of the discrete Fourier inversion formula for a finite
measure `μ` on `ℤ^d`, the sum of the squared singleton masses equals the normalized `L²`-norm of
its characteristic function on the fundamental domain `[-π, π)^d`. -/
theorem lattice_measure_plancherel_formula (d : ℕ) (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    (∑' x : Fin d → ℤ, μ.real ({x} : Set (Fin d → ℤ)) ^ 2) =
      (((2 * Real.pi) ^ d : ℝ)⁻¹ *
        ∫ t in latticeFrequencyCube d, ‖charFun (μ.map latticeEmbedding) t‖ ^ 2 ∂volume) := sorry

/-! ### Exercise_15_1_4 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The Mellin transform of a measure on `[0, ∞)`. -/
abbrev mellinTransform (μ : Measure NNReal) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ^ s ∂μ

-- Proof sketch: unfold `mellinTransform` for the pushforward law `Measure.map X μ` and rewrite the
-- lower integral using `lintegral_map'`, so the Mellin transform becomes the extended expectation
-- of the canonical `ℝ≥0∞` power of `X`.
/-- The Mellin transform of the law of a nonnegative random variable is the lower integral of
`x ↦ x ^ s` along that variable. -/
theorem mellinTransform_map (μ : Measure Ω) (X : Ω → NNReal) (hX : AEMeasurable X μ) (s : ℝ) :
    mellinTransform (μ.map X) s =
      ∫⁻ ω, (X ω : ℝ≥0∞) ^ s ∂μ := by
  have hpow : AEMeasurable (fun x : NNReal ↦ (x : ℝ≥0∞) ^ s) (μ.map X) :=
    by fun_prop
  simpa [mellinTransform] using
    (lintegral_map' hpow hX)

section

variable {μ ν : Measure NNReal} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε ε₀ : ℝ}

-- Proof sketch: first handle laws with continuous densities on `[0, ∞)` by identifying the
-- Mellin transform with a holomorphic Mellin integral and invoking analytic continuation. Then
-- smooth arbitrary laws by multiplying with an independent `U_[1 - δ, 1]` factor, compare the
-- smoothed Mellin transforms on `[0, ε]`, and let `δ ↓ 0` using convergence in distribution of
-- the smoothed laws.
/-- Exercise 15.1.4: among nonnegative probability laws with some positive finite Mellin moment,
the values of the Mellin transform on any interval `[0, ε]` determine the law. -/
theorem measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hμ_moment : mellinTransform μ ε₀ < ∞)
    (h_eq : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      mellinTransform μ s = mellinTransform ν s) :
    μ = ν := sorry

-- Proof sketch: apply the positive-exponent characterization theorem to the pushforwards of `μ`
-- and `ν` under inversion `x ↦ x⁻¹`. The finite negative Mellin moment becomes a positive Mellin
-- moment for the inverted laws, and equality of `m(-s)` on `[0, ε]` becomes equality of the
-- ordinary Mellin transforms of those inverted laws.
/-- The negative-exponent Mellin data `m(-s)` on `[0, ε]` determine a nonnegative probability law
once one negative Mellin moment is finite. -/
theorem measure_eq_of_mellinTransform_neg_eq_on_Icc_of_exists_lt_top
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hμ_moment : mellinTransform μ (-ε₀) < ∞)
    (h_eq : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      mellinTransform μ (-s) = mellinTransform ν (-s)) :
    μ = ν := sorry

end

/-! ### Exercise_15_1_5 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

section

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y Z : Ω → NNReal}

-- Proof sketch: for measurable nonnegative random variables `X`, `Y`, and `Z`, push forward
-- their laws to finite measures on `[0, ∞)`.
-- The assumptions `IndepFun X Z μ` and `IndepFun Y Z μ` identify the laws of `XZ` and `YZ` with
-- the multiplicative convolutions of the laws of `X` and `Y` with the law of `Z`. The Mellin
-- hypothesis is expressed through the canonical owner `mellinTransform`; by
-- `mellinTransform_map` it is the same as a positive finite Mellin moment of `XZ`.
-- The hypothesis `ℙ[Z > 0] > 0` prevents the Mellin transform of `Z` from vanishing identically,
-- so one cancels it and applies
-- `measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top` to the laws of `X` and `Y`
-- (equivalently, uniqueness of Laplace transforms after taking logarithms).
/-- Exercise 15.1.5: if `X`, `Y`, and `Z` are nonnegative measurable random variables, `Z` is
independent of both `X` and `Y`, `XZ =ᵈ YZ`, `Z` is positive with positive probability, and the
law of `XZ` has a finite Mellin transform at some positive exponent, then `X =ᵈ Y`. -/
theorem identDistrib_of_mul_identDistrib_of_indepFun
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXZ_indep : IndepFun X Z μ)
    (hYZ_indep : IndepFun Y Z μ)
    (hZ_pos : 0 < μ (Z ⁻¹' Set.Ioi 0))
    (h_mellin : ∃ s : ℝ, 0 < s ∧
      mellinTransform (μ.map (X * Z)) s < ∞)
    (h_mul : IdentDistrib (X * Z) (Y * Z) μ μ) :
    IdentDistrib X Y μ μ := sorry

end

/-! ### Exercise_15_1_6 (from Items/Chap15) -/
open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

/-- The inverse-Fourier candidate density attached to the characteristic function of a real
probability measure, built from the canonical owners `MeasureTheory.charFun` and `𝓕⁻`. -/
def charFunInversionDensity (μ : Measure ℝ) : ℝ → ℝ :=
  fun x ↦ Complex.re ((𝓕⁻ fun t : ℝ ↦ charFun μ (-2 * Real.pi * t)) x)

section

variable (μ : Measure ℝ)

-- Proof sketch: first compute the inverse-Fourier density for the Gaussian mollifiers
-- `gaussianReal 0 ε`; then identify the densities of `μ ∗ gaussianReal 0 ε` by Fourier inversion
-- and pass to the limit as `ε → 0`.
/-- Exercise 15.1.6: if a probability measure on `ℝ` has integrable characteristic function, then
it is absolutely continuous with respect to Lebesgue measure, with density given by the inverse
Fourier transform of its characteristic function. -/
theorem probabilityMeasure_eq_withDensity_of_integrable_charFun
    [IsProbabilityMeasure μ] (hφ : Integrable (charFun μ) volume) :
    μ = volume.withDensity (ENNReal.ofReal ∘ charFunInversionDensity μ) := sorry

-- Proof sketch: apply dominated convergence to the oscillatory integral defining
-- `charFunInversionDensity μ`, using the `L¹` majorant `t ↦ ‖charFun μ t‖`.
/-- The inverse-Fourier density attached to an integrable characteristic function is continuous. -/
theorem charFunInversionDensity_continuous
    (hφ : Integrable (charFun μ) volume) :
    Continuous (charFunInversionDensity μ) := sorry

-- Proof sketch: bound the oscillatory integral uniformly by the `L¹` norm of the characteristic
-- function.
/-- The inverse-Fourier density is pointwise bounded by the `L¹` norm of the characteristic
function. -/
theorem norm_charFunInversionDensity_le_integral_norm
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    ‖charFunInversionDensity μ x‖ ≤ ∫ t, ‖charFun μ t‖ := sorry

-- Proof sketch: apply `norm_charFunInversionDensity_le_integral_norm` uniformly in `x`.
/-- The inverse-Fourier density attached to an integrable characteristic function is bounded. -/
theorem charFunInversionDensity_bounded
    (hφ : Integrable (charFun μ) volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖charFunInversionDensity μ x‖ ≤ C := by
  refine ⟨∫ t, ‖charFun μ t‖, integral_nonneg fun t ↦ norm_nonneg _, fun x ↦ ?_⟩
  exact norm_charFunInversionDensity_le_integral_norm μ hφ x

end

/-! ### Exercise_15_1_7 (from Items/Chap15) -/
open MeasureTheory TopologicalSpace
open scoped BoundedContinuousFunction

universe u

variable {Ω : Type u} [TopologicalSpace Ω] [CompletelyRegularSpace Ω]
  [SeparableSpace Ω]

-- Proof sketch: the completely regular hypothesis gives bounded continuous functions separating a
-- point from a closed set. Use separability to extract a countable subfamily that still generates
-- the topology, identify the induced embedding into a countable product of copies of `ℝ`, and then
-- conclude that the Borel `σ`-algebra is the supremum of the comaps of `borel ℝ` along all bounded
-- continuous real-valued functions.
/-- Exercise 15.1.7: for a separable completely regular space `Ω`, the Borel `σ`-algebra on `Ω`
is generated by its bounded continuous real-valued functions. -/
theorem borel_eq_iSup_comap_boundedContinuousReal_of_separable_completelyRegular
    : borel Ω = ⨆ f : Ω →ᵇ ℝ, MeasurableSpace.comap f (borel ℝ) := sorry
