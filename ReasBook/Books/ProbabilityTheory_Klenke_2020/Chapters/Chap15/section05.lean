import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_15_5_1 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u

noncomputable section

-- Proof sketch: take a centered real law in the Gaussian domain of attraction with finite second
-- moment but infinite first absolute moment, realize an independent sequence with this law on an
-- infinite product probability space, and then apply the one-dimensional central limit theorem to
-- the raw `√n`-normalized partial sums built from the chapter owner `partialSum`.
/- Exercise 15.5.1 is `source-facing`: it asks for an independent sequence of measurable real
random variables with infinite first absolute moments whose raw `√n`-normalized partial sums
converge in distribution. The project owner for the finite sums themselves is `partialSum`, so the
statement reuses that owner directly instead of introducing a parallel public wrapper for the same
construction. -/
/-- Exercise 15.5.1: there exists an independent sequence `X₁, X₂, ...` of real random variables
such that every absolute first moment is infinite, but the normalized sums
`(X₁ + ⋯ + X_n) / √n` converge in distribution to the standard Gaussian law. In Lean's `0`-based
indexing, these are the maps `ω ↦ (√n)⁻¹ * partialSum X n ω`. -/
theorem exists_heavyTailStandardCLTExample :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      (∀ n, Measurable (X n)) ∧
        iIndepFun X P ∧
        (∀ n, ∫⁻ ω, ENNReal.ofReal |X n ω| ∂P = ⊤) ∧
        TendstoInDistribution
          (fun (n : ℕ) ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum X n ω)
          atTop id (fun _ ↦ P) (gaussianReal 0 1) := sorry

/-! ### Exercise_15_5_2 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

open RealRandomVariableArray

/-- The three-point law of the rare jump variable `Z_{n+1}`: it is `0` with probability
`1 - (n + 1)⁻²` and takes the values `± (n + 1)` with probability `(2 (n + 1)²)⁻¹` each. -/
def rareJumpLaw (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0 +
    ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ) +
      ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (-(n + 1 : ℝ))

/-- The rare-jump law is the sum of the Dirac masses at `0` and `± (n + 1)` with the stated
weights. -/
theorem rareJumpLaw_def (n : ℕ) :
    rareJumpLaw n =
      ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0 +
        ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ) +
          ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) •
            Measure.dirac (-(n + 1 : ℝ)) :=
  rfl

section RareJumpPerturbedArray

variable (Y Z : ℕ → Ω → ℝ)
variable (hY_meas : ∀ n, Measurable (Y n)) (hZ_meas : ∀ n, Measurable (Z n))

/- Exercise 15.5.2 is `source-facing`: it studies the perturbed normalized sums
`n^{-1/2} ∑_{k < n} (Y_k + Z_k)`. The chapter's `core/canonical` owner for rowwise CLT and
Lindeberg data is `RealRandomVariableArray Ω`; the array below is the `bridge/view` packaging of
those source sums as row sums of an owner object. -/
/-- The `n`-th row consists of the first `n` perturbed summands `Y_k + Z_k`, each scaled by
`(√n)⁻¹`, so its row sum is the normalized textbook sum `n^{-1/2} ∑_{k < n} (Y_k + Z_k)`. -/
def rareJumpPerturbedStandardizedArray : RealRandomVariableArray Ω where
  rowLength n := n
  entry n i ω := (Y i.1 ω + Z i.1 ω) / Real.sqrt (n : ℝ)
  measurable_entry n i := by
    simpa using ((hY_meas i.1).add (hZ_meas i.1)).div_const (Real.sqrt (n : ℝ))

/-- The entries of the rare-jump perturbed standardized array are the scaled perturbed summands. -/
theorem rareJumpPerturbedStandardizedArray_apply (n : ℕ) (i : Fin n) (ω : Ω) :
    rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas n i ω =
      (Y i.1 ω + Z i.1 ω) / Real.sqrt (n : ℝ) :=
  rfl

/-- The entries of the rare-jump perturbed standardized array are measurable. -/
theorem measurable_rareJumpPerturbedStandardizedArray_entry (n : ℕ) (i : Fin n) :
    Measurable (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas n i) :=
  (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).measurable_entry n i

end RareJumpPerturbedArray

-- Proof sketch: the source hypotheses require not only that `Y` is i.i.d., but also that the
-- perturbation sequence `Z` is independent and independent of the whole sequence `Y`. The
-- rare-jump law `rareJumpLaw n` gives `∑ n, P[Z n ≠ 0] < ∞`, so Borel--Cantelli yields only
-- finitely many nonzero jumps almost surely. Hence the perturbation is asymptotically negligible
-- after dividing by `√n`, the row sums still converge weakly to the standard Gaussian law by the
-- iid CLT for `Y` and Slutsky, and the exceptional summands still violate the chapter-owner
-- Lindeberg condition.
/-- Exercise 15.5.2: for a `0`-based Lean model of the textbook sequences `Y₁, Y₂, ...` and
`Z₁, Z₂, ...`, the laws of the row sums of
`rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas`, equivalently of the normalized sums
`n^{-1/2} ∑_{k < n} (Y_k + Z_k)`, converge weakly to the standard Gaussian law `𝒩(0, 1)` when
`Y` is i.i.d., the perturbations `Z_k` are independent with laws `rareJumpLaw k`, and `Z` is
independent of the whole sequence `Y`; but the associated standardized array does not satisfy the
chapter-owner Lindeberg condition. -/
theorem rareLargeJumps_clt_but_not_lindeberg
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hZ_indep : iIndepFun Z P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P) :
    Tendsto
      (fun n ↦ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).rowSumLaw P n)
      atTop
      (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) ∧
    ¬ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).SatisfiesLindebergCondition P :=
  sorry

end

/-! ### Exercise_15_5_3 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u v

noncomputable section

/-- A convenient explicit normalization for the inverse-cube-tail central limit theorem. -/
def inverseCubeTailCLTNormingSequence : ℕ → ℝ :=
  fun n ↦ Real.sqrt ((n + 2 : ℝ) * Real.log (n + 2 : ℝ))

-- Proof sketch: rewrite the left-hand side using `hX.map_eq`, then compute the square moment of
-- `symmetricParetoMeasure (1 / 2)` using the density formula from `symmetricParetoDensityReal_eq`;
-- the resulting square moment reduces to `∫_1^∞ x⁻¹ dx`, which diverges.
/-- A random variable with law `symmetricParetoMeasure (1 / 2)`, equivalently with density
`x ↦ |x|⁻³ 1_{ℝ \ [-1,1]}(x)`, has infinite second moment. -/
theorem secondMoment_eq_top_of_hasLaw_inverseCubeTail {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X (symmetricParetoMeasure (1 / 2)) P) :
    ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 : ℕ)) ∂P = ⊤ := sorry

-- Proof sketch: this law is centered and lies in the normal domain of attraction of the standard
-- Gaussian with slowly varying truncated second moment `L(t) ~ 2 log t`; apply the
-- one-dimensional domain-of-attraction CLT with the explicit choice
-- `A_n = √((n + 2) log (n + 2))`, using `hX_indep` and `hX_law` to identify the common law of the
-- summands.
/-- Exercise 15.5.3: one explicit norming sequence for i.i.d. real random variables with density
`x ↦ |x|⁻³ 1_{ℝ \ [-1,1]}(x)` is `A_n = √((n + 2) log (n + 2))`; with this normalization, the
partial sums converge in distribution to the standard Gaussian law. -/
theorem tendstoInDistribution_sum_div_inverseCubeTailCLTNormingSequence
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    TendstoInDistribution
      (fun n ω ↦ (inverseCubeTailCLTNormingSequence n)⁻¹ *
        ∑ k ∈ Finset.range n, X (k + 1) ω)
      atTop Y (fun _ ↦ P) P' := sorry

/-! ### Example_15_5 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- The standard log-normal law on `ℝ`, defined as the image of the standard Gaussian law under
exponentiation. -/
def standardLogNormalMeasure : Measure ℝ :=
  (gaussianReal 0 1).map Real.exp

/-- The density of the standard log-normal law on `ℝ`, extended by `0` on `(-∞, 0]`. -/
def standardLogNormalDensityReal (x : ℝ) : ℝ :=
  if 0 < x then gaussianPDFReal 0 1 (Real.log x) / x else 0

/-- The oscillatory perturbation of the standard log-normal density by the factor
`1 + α sin(2π log x)` for `α ∈ [-1, 1]`. -/
def logNormalPerturbationDensityReal (α : Set.Icc (-1 : ℝ) 1) (x : ℝ) : ℝ :=
  standardLogNormalDensityReal x * (1 + α.1 * Real.sin (2 * Real.pi * Real.log x))

/-- The measure with density `logNormalPerturbationDensityReal α` with respect to Lebesgue
measure. -/
def logNormalPerturbationMeasure (α : Set.Icc (-1 : ℝ) 1) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (logNormalPerturbationDensityReal α x))

-- Proof sketch: apply the one-dimensional change-of-variables formula to the pushforward of the
-- standard Gaussian law under `Real.exp`, which yields the textbook density
-- `x ↦ gaussianPDFReal 0 1 (log x) / x` on `(0, ∞)`.
/-- The standard log-normal law is the image of the standard Gaussian law under exponentiation,
and this image measure has density `standardLogNormalDensityReal` with respect to Lebesgue
measure. -/
theorem standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal :
    standardLogNormalMeasure =
      volume.withDensity (fun x ↦ ENNReal.ofReal (standardLogNormalDensityReal x)) := sorry

-- Proof sketch: rewrite the integral using
-- `standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal`, so the moment becomes
-- `E[exp(nY)]` for a standard Gaussian `Y`, and then evaluate the Gaussian moment-generating
-- function at `n`.
/-- The `n`th moment of the standard log-normal law equals `exp (n^2 / 2)`. -/
theorem standardLogNormalMeasure_moment (n : ℕ) :
    moment id n standardLogNormalMeasure = Real.exp (((n : ℝ) ^ 2) / 2) := sorry

-- Proof sketch: substitute `y = log x - n` in the integral. After simplifying, the remaining
-- Gaussian-weighted integrand is odd because `sin (2π (y + n)) = sin (2π y)`, so the integral
-- vanishes.
/-- The oscillatory correction term used to build the Stieltjes class has vanishing moments. -/
theorem logNormalOscillatoryMoment_eq_zero (n : ℕ) :
    ∫ x, x ^ n * standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x) = 0 := sorry

-- Proof sketch: the bound `|α| ≤ 1` implies that the oscillatory factor
-- `1 + α sin (2π log x)` is nonnegative, so `logNormalPerturbationMeasure α` is a probability
-- measure. The moment identity follows by expanding the perturbed density and using
-- `logNormalOscillatoryMoment_eq_zero` to kill the oscillatory contribution.
/-- Example 15.5: for every `α ∈ [-1, 1]`, the perturbed log-normal density defines a probability
measure whose moments agree with those of the standard log-normal law. -/
theorem logNormalPerturbationMeasure_isProbabilityMeasure_and_sameMoments
    (α : Set.Icc (-1 : ℝ) 1) :
    IsProbabilityMeasure (logNormalPerturbationMeasure α) ∧
      ∀ n : ℕ,
        moment id n (logNormalPerturbationMeasure α) =
          moment id n standardLogNormalMeasure := sorry
