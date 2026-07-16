import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_12
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_14
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped CompactlySupported Topology

noncomputable section

/-
Remark 16.18 is a `bridge/view` item for the real-line Lévy--Khinchin owner API in chapter 16.
The owner abstractions are `HasLevyKhinchinRepresentation μ τ` on `ℝ`,
`HasSubordinatorLevyKhinchinRepresentation μ α ν` on `NNReal`, and the chapter-13 vague-limit
predicate `radonMeasureVaguelyConvergesTo`. Accordingly, the auxiliary centering-integrability
fact is kept as a helper, while the public bridge in part (2) is the actual owner-to-owner
comparison recovering the subordinator statement from the real-line one. For part (3), the
source-facing vague-limit statement is kept central and targets the canonical Lévy measure `τ.ν`
itself, matching the textbook recovery statement.
-/
namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: expand both exponents, subtract the two drift terms, and use linearity of the
-- integral to identify the difference with `∫ (f - f̃) dν`.
/-- Remark 16.18 (1): replacing the canonical centering function in the Lévy--Khinchin formula by
another integrable centering changes only the drift coefficient, by
`∫ (f_old - f_new) dν`. -/
theorem levyKhinchinExponent_changeCentering
    (σ2 b : ℝ) (ν : Measure ℝ) (f_old f_new : ℝ → ℝ)
    (hfg : Integrable (fun x ↦ f_old x - f_new x) ν) :
    levyKhinchinExponentWithCentering σ2 (b + ∫ x, (f_old x - f_new x) ∂ ν) ν f_new =
      levyKhinchinExponentWithCentering σ2 b ν f_old := sorry

-- Proof sketch: on a measure concentrated on `(0, ∞)`, the canonical centering
-- `x ↦ x 𝟙_{|x| < 1}` agrees almost everywhere with `x ↦ min 1 x` up to the positive-support
-- truncation, so integrability follows from the assumed integrability of `1 ∧ x`.
/-- Auxiliary bridge lemma for Remark 16.18 (2): on a positive-support Lévy measure with
`∫ (1 ∧ x) dν < ∞`, the canonical real-line centering `x 𝟙_{|x| < 1}` is `ν`-integrable. -/
theorem integrable_levyKhinchinCanonicalCentering_of_positive_support
    (ν : Measure ℝ) (hneg : ν (Set.Iic 0) = 0)
    (hν : Integrable (fun x : ℝ ↦ min 1 x) ν) :
    Integrable levyKhinchinCanonicalCentering ν := sorry

namespace HasLevyKhinchinRepresentation

-- Proof sketch: write the real-line exponent with the centering `x ↦ min 1 x`, use the helper
-- `integrable_levyKhinchinCanonicalCentering_of_positive_support` to justify the change of
-- centering, and read the resulting identity as the Bernstein-formula owner statement on
-- `NNReal`.
/-- Remark 16.18 (2): if a probability law on `[0, ∞)` is viewed on `ℝ` and admits a real-line
Lévy--Khinchin representation with zero Gaussian part, nonnegative drift, positive-support Lévy
measure, and finite truncated first moment, then one recovers the subordinator owner statement of
Theorem 16.14 for the original law on `NNReal`. -/
theorem toSubordinatorLevyKhinchinRepresentation
    {μ : ProbabilityMeasure NNReal} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation
      (ProbabilityMeasure.map μ measurable_coe_nnreal_real.aemeasurable) τ)
    (hσ : τ.sigma2 = 0) (hb : 0 ≤ τ.b) (hpos : τ.ν (Set.Iic 0) = 0)
    (hν : Integrable (fun x : ℝ ↦ min 1 x) τ.ν) :
    HasSubordinatorLevyKhinchinRepresentation
      μ
      ⟨τ.b, hb⟩
      (Measure.map Real.toNNReal τ.ν) := sorry

-- Proof sketch: choose the `n`th convolution roots from Theorem 16.17, reindex the resulting
-- positive integers as an `ℕ`-sequence, and apply the Chapter 13 vague-convergence owner
-- predicate to the scaled positive-part restrictions to recover the canonical Lévy measure.
/-- Remark 16.18 (3): for an infinitely divisible law on `ℝ`, one can choose convolution roots
`μroot n` so that the reindexed scaled positive-part restrictions
`(n + 1) • μroot (n + 1)|_(0,∞)` converge vaguely to the canonical Lévy measure `τ.ν`. -/
theorem canonicalLevyMeasure_vagueLimit
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∃ μroot : ℕ+ → ProbabilityMeasure ℝ,
      (∀ n : ℕ+, μroot n ^ (n : ℕ) = μ) ∧
        radonMeasureVaguelyConvergesTo
          (fun n ↦
            (((n + 1 : ℕ) •
              (((μroot (Nat.succPNat n) : ProbabilityMeasure ℝ) : Measure ℝ).restrict
                (Set.Ioi 0))) : Measure ℝ))
          τ.ν := sorry

end HasLevyKhinchinRepresentation

-- Proof sketch: compare the real-line canonicality condition
-- `∫ min (x^2, 1) dν < ∞` with the stronger subordinator condition
-- `∫ min (1, x) dν < ∞`; the latter is strictly stronger on positive-support measures.
/-- Remark 16.18: the truncated-first-moment condition from Theorem 16.14 is strictly stronger
than the positive-support canonicality condition from Definition 16.16. -/
theorem exists_positiveSupport_canonicalMeasure_not_integrable_min :
    ∃ ν : Measure ℝ,
      IsCanonicalMeasure ν ∧
      ν (Set.Iic 0) = 0 ∧
      ¬ Integrable (fun x : ℝ ↦ min 1 x) ν := sorry

-- Proof sketch: use the preceding strictness statement to choose a positive-support canonical
-- triple `(0, b, ν)` with positive-support Lévy measure satisfying the real-line canonical
-- conditions but not the stronger subordinator hypothesis. Theorem 16.17 still produces the
-- corresponding infinitely divisible law on `ℝ`, and Theorem 16.14 then rules out concentration
-- on `[0, ∞)`.
/-- Consequently, every canonical triple `(0, b, ν)` on `ℝ` with positive-support Lévy measure and
`∫ (1 ∧ x) dν = ∞` corresponds to an infinitely divisible law that is not concentrated on
`[0, ∞)`, regardless of the drift parameter `b`. -/
theorem exists_positiveSupport_canonicalTriple_not_supportedOnNNReal
    (b : ℝ) (ν : Measure ℝ) (hcanon : IsCanonicalMeasure ν)
    (hpos : ν (Set.Iic 0) = 0)
    (hnot_int : ¬ Integrable (fun x : ℝ ↦ min 1 x) ν) :
    ∃ μ : ProbabilityMeasure ℝ,
      HasLevyKhinchinRepresentation μ { sigma2 := 0, b := b, ν := ν } ∧
      (μ : Measure ℝ) (Set.Ici 0) ≠ 1 := sorry

end MeasureTheory.ProbabilityMeasure
