import Mathlib
import AchimKlenkeLean.Items.Chap02.Lemma_2_40
import AchimKlenkeLean.Items.Chap14.Lemma_14_27
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap17.Definition_17_33
import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap15.Theorem_15_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The open cube `(-ε, ε)^d` in the Euclidean frequency space associated with `ℤ^d`. -/
def latticeOpenCube (ε : ℝ) (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {t | ∀ i, |t i| < ε}

-- Proof sketch: unfold `latticeOpenCube`; membership is given coordinatewise by the defining
-- inequalities `|t i| < ε`.
/-- Membership in `latticeOpenCube ε d` means that every coordinate has absolute value `< ε`. -/
theorem mem_latticeOpenCube_iff {ε : ℝ} {d : ℕ} {t : EuclideanSpace ℝ (Fin d)} :
    t ∈ latticeOpenCube ε d ↔ ∀ i, |t i| < ε := sorry

/- Layering for Theorem 17.41:
- source-facing primitive data: `latticeOpenCube`, `symmetricSimpleRandomWalkStepPMF`,
  and `modifiedBesselI0`;
- core/canonical owner: a step law `ν : PMF (LatticePoint d)` together with
  `[IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the increment law;
- source-facing derived API: the recurrence criterion, the dimension-`≤ 2` recurrence statement,
  and the Green-function formulas `(17.24)` and `(17.25)` at the origin for the symmetric simple
  random walk. -/

-- Proof sketch: unfold the owner notions `IsRecurrentMarkovChain` and `IsRecurrentState`, then
-- rewrite the return probability with `returnProbability_eq_measure_exists_pos`.
/-- A lattice chain is recurrent exactly when each state is hit again with probability `1` under
its own start law. -/
theorem isRecurrentMarkovChain_iff {d : ℕ}
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d) :
    IsRecurrentMarkovChain P X ↔
      ∀ x : LatticePoint d, (P x : Measure Ω).real {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 1 := sorry

/-- The one-step law of symmetric simple random walk on `ℤ^d`: choose a coordinate uniformly and
then choose one of the two signs with equal probability. -/
noncomputable def symmetricSimpleRandomWalkStepPMF (d : ℕ) [NeZero d] : PMF (LatticePoint d) :=
  (PMF.uniformOfFintype (Bool × Fin d)).map
    (fun s ↦ if s.1 then Pi.single s.2 (1 : ℤ) else Pi.single s.2 (-1))

/-- The modified Bessel function `I₀`, introduced here through its standard power series because
formula `(17.25)` is part of the public source-facing content of Theorem 17.41. -/
def modifiedBesselI0 (t : ℝ) : ℝ :=
  ∑' k, (t / 2) ^ (2 * k) / ((Nat.factorial k : ℝ) ^ (2 : ℕ))

scoped[ProbabilityTheory] notation "I₀" => modifiedBesselI0

/-- The defining power-series expansion of `I₀`. -/
theorem modifiedBesselI0_eq_tsum (t : ℝ) :
    I₀ t =
      ∑' k, (t / 2) ^ (2 * k) / ((Nat.factorial k : ℝ) ^ (2 : ℕ)) := rfl

-- Proof sketch: expand `symmetricSimpleRandomWalkStepPMF` as the pushforward of the uniform law on
-- `Bool × Fin d`; averaging the exponentials over the two signs turns each coordinate
-- contribution into `cos (t i)`, and averaging over the `d` coordinates gives the displayed mean.
/-- The characteristic function of the symmetric simple random walk step law is
`φ(t) = (1 / d) * ∑ i, cos (t i)`. -/
theorem latticeCharacteristicFunction_symmetricSimpleRandomWalkStepPMF
    (d : ℕ) [NeZero d] (t : EuclideanSpace ℝ (Fin d)) :
    charFun ((symmetricSimpleRandomWalkStepPMF d).toMeasure.map latticeEmbedding) t =
      ((d : ℝ)⁻¹ * ∑ i : Fin d, Real.cos (t i) : ℝ) := sorry

-- Proof sketch: this is the Chung--Fuchs criterion for irreducible random walks on `ℤ^d`,
-- written at the canonical owner layer of the increment law `ν` and its convolution kernel.
/-- Theorem 17.41: an irreducible random walk on `ℤ^d` with increment law `ν` is recurrent exactly
when, for every `ε > 0`, the Chung--Fuchs integral over `(-ε, ε)^d` of the real part of
`(1 - λ φ(t))⁻¹` tends to `∞` as `λ ↑ 1`, where
`φ = charFun (ν.toMeasure.map latticeEmbedding)` is the characteristic function of the step law
pushed forward to `ℝ^d`. The public statement is organized around the canonical owner abstraction
`[IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]`; the
translation-invariant matrix presentation is relegated to a bridge theorem below. -/
theorem irreducible_latticeRandomWalk_isRecurrent_iff_chungFuchs
    {d : ℕ} (ν : PMF (LatticePoint d))
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)] :
    IsRecurrentMarkovChain P X ↔
      ∀ ε > 0,
        Filter.Tendsto
          (fun r : ℝ ↦
            ∫ t in latticeOpenCube ε d,
              Complex.re (((1 : ℂ) - (r : ℂ) * charFun (ν.toMeasure.map latticeEmbedding) t)⁻¹))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) Filter.atTop := sorry

-- Proof sketch: if the transition matrix is translation invariant, the row at the origin encodes
-- the intrinsic increment law and the induced kernel is the translation kernel driven by that
-- law.
/-- Bridge form of Theorem 17.41: for a translation-invariant lattice transition matrix `p`, the
Chung--Fuchs criterion can be read directly from the row at the origin. -/
theorem translationInvariant_latticeRandomWalk_isRecurrent_iff_chungFuchs
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (hp : IsTranslationInvariantStepMatrix p) :
    IsRecurrentMarkovChain P X ↔
      ∀ ε > 0,
        Filter.Tendsto
          (fun r : ℝ ↦
            ∫ t in latticeOpenCube ε d,
              Complex.re
                (((1 : ℂ) - (r : ℂ) * charFun ((discreteMatrixKernel p 0).map latticeEmbedding)
                  t)⁻¹))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) Filter.atTop := sorry

-- Proof sketch: expand the Green function at the origin by the visit-probability series from
-- Definition 17.33, rewrite each `n`-step return probability by lattice Fourier inversion, sum
-- the resulting geometric series on the frequency cube, and recognize the textbook Watson
-- integral `(17.24)`.
/-- Formula `(17.24)` from Theorem 17.41: for the symmetric simple random walk on `ℤ^d`, the
Green function at the origin is the Watson integral over the lattice frequency cube. -/
theorem symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_watsonIntegral
    {d : ℕ} [NeZero d]
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF d).toMeasure ^ n) P X] :
    (G[P, X]) 0 0 =
      ∫⁻ t in latticeFrequencyCube d,
        ENNReal.ofReal
          (((2 * Real.pi) ^ d)⁻¹ *
            (((1 : ℝ) - (d : ℝ)⁻¹ * ∑ i : Fin d, Real.cos (t i))⁻¹)) ∂volume := sorry

-- Proof sketch: if the simple walk is presented by a translation-invariant transition matrix
-- `p`, the row at the origin is the canonical increment law, so the Watson formula is the owner
-- theorem above read through that bridge/view.
/-- Bridge form of formula `(17.24)` for a translation-invariant transition matrix whose row at
the origin is the symmetric simple-random-walk step law. -/
theorem translationInvariant_symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_watsonIntegral
    {d : ℕ} [NeZero d]
    (p : LatticePoint d → LatticePoint d → ENNReal)
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hstep : ∀ y, p 0 y = symmetricSimpleRandomWalkStepPMF d y) :
    (G[P, X]) 0 0 =
      ∫⁻ t in latticeFrequencyCube d,
        ENNReal.ofReal
          (((2 * Real.pi) ^ d)⁻¹ *
            (((1 : ℝ) - (d : ℝ)⁻¹ * ∑ i : Fin d, Real.cos (t i))⁻¹)) ∂volume := sorry

-- Proof sketch: insert the explicit characteristic function from
-- `latticeCharacteristicFunction_symmetricSimpleRandomWalkStepPMF`, use the quadratic expansion of
-- `cos` near `0`, and compare the resulting singularity with the radial integral of `‖t‖⁻²`,
-- which diverges exactly in dimensions `1` and `2`.
/-- A symmetric simple random walk on `ℤ^d` is recurrent exactly in dimensions `d ≤ 2`. The owner
statement is phrased directly for the canonical step law
`symmetricSimpleRandomWalkStepPMF d`. -/
theorem symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two
    {d : ℕ} [NeZero d]
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF d).toMeasure ^ n) P X] :
    IsRecurrentMarkovChain P X ↔ d ≤ 2 := sorry

-- Proof sketch: start from the Green-function series at the origin, insert the multinomial
-- even-return formula for the simple symmetric walk, expand `(I₀ t)^d` by the Cauchy product, and
-- exchange the sum and the integral to recover the modified-Bessel formula `(17.25)`.
/-- Formula `(17.25)` from Theorem 17.41: for the symmetric simple random walk on `ℤ^d`, the
Green function at the origin admits the modified-Bessel integral representation
`G_d(0,0) = d ∫_0^∞ e^{-dt} I₀(t)^d dt`. -/
theorem symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_besselIntegral
    {d : ℕ} [NeZero d]
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF d).toMeasure ^ n) P X] :
    (G[P, X]) 0 0 =
      ∫⁻ t in Set.Ici (0 : ℝ),
        ENNReal.ofReal ((d : ℝ) * Real.exp (-(d : ℝ) * t) * (I₀ t) ^ d) ∂volume := sorry

-- Proof sketch: specialize the owner-level simple-random-walk theorem to the row at the origin of
-- a translation-invariant transition matrix.
/-- Bridge form of the simple-random-walk recurrence criterion for a translation-invariant lattice
transition matrix whose row at the origin is `symmetricSimpleRandomWalkStepPMF d`. -/
theorem translationInvariant_symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two
    {d : ℕ} [NeZero d]
    (p : LatticePoint d → LatticePoint d → ENNReal)
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hstep : ∀ y, p 0 y = symmetricSimpleRandomWalkStepPMF d y) :
    IsRecurrentMarkovChain P X ↔ d ≤ 2 := sorry

-- Proof sketch: if the simple walk is presented by a translation-invariant transition matrix
-- `p`, the row at the origin is `symmetricSimpleRandomWalkStepPMF d`, so the owner theorem above
-- reads directly in this bridge/view presentation.
/-- Bridge form of formula `(17.25)` for a translation-invariant transition matrix whose row at
the origin is `symmetricSimpleRandomWalkStepPMF d`. -/
theorem translationInvariant_symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_besselIntegral
    {d : ℕ} [NeZero d]
    (p : LatticePoint d → LatticePoint d → ENNReal)
    (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hstep : ∀ y, p 0 y = symmetricSimpleRandomWalkStepPMF d y) :
    (G[P, X]) 0 0 =
      ∫⁻ t in Set.Ici (0 : ℝ),
        ENNReal.ofReal ((d : ℝ) * Real.exp (-(d : ℝ) * t) * (I₀ t) ^ d) ∂volume := sorry

end ProbabilityTheory
