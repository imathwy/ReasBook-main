import ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_32

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- A real random variable satisfies the textbook finite absolute-moment root-growth limsup
hypothesis if it is measurable, all of its absolute moments are finite, and the normalized nth
roots of those absolute moments are bounded above along `atTop`. -/
def HasFiniteAbsoluteMomentRootLimsup (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) : Prop :=
  Measurable X ∧
    (∀ n : ℕ, Integrable (fun ω ↦ |X ω| ^ n) P) ∧
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ)))

/-- Finite absolute-moment root-growth limsup is exactly measurability, finiteness of all absolute
moments, and boundedness of the normalized absolute moments. -/
@[simp] theorem hasFiniteAbsoluteMomentRootLimsup_iff (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) :
    HasFiniteAbsoluteMomentRootLimsup P X ↔
      Measurable X ∧
        (∀ n : ℕ, Integrable (fun ω ↦ |X ω| ^ n) P) ∧
          Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
            (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ))) := by
  rfl

/-- The source-facing finite absolute-moment root-growth limsup hypothesis implies the chapter's
canonical moment-determinacy predicate. -/
-- Proof sketch: a finite limsup bounds the normalized absolute moments along `atTop`, which is
-- the growth input needed in the same moment-problem argument used in Corollary 15.32.
theorem isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimsup P X) :
    IsMomentDeterminate P X := sorry

-- Proof sketch: first pass from the source-facing limsup hypotheses to the canonical owner
-- predicate `IsMomentDeterminate`. For each Borel set `A`, use the factorization of mixed moments
-- together with nonnegativity to form the tilted measures with densities `X^m` and `Y^n`; then
-- moment determinacy shows
-- `E[X^m 1_A(Y)] = E[X^m] P[Y ∈ A]` for all `m`, then apply the same argument to the tilted
-- conditional laws of `X` given `Y ∈ A` to deduce factorization of all rectangle probabilities.
/-- Exercise 15.4.1: if nonnegative real random variables `X` and `Y` both satisfy the textbook
finite absolute-moment root-growth limsup hypothesis and all mixed moments factorize as
`E[X^m Y^n] = E[X^m] E[Y^n]`, with those mixed moments finite, then `X` and `Y` are independent. -/
theorem indepFun_of_mixed_moment_factorization_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_growth : HasFiniteAbsoluteMomentRootLimsup P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P) :
    IndepFun X Y P := by
  have hX_det : IsMomentDeterminate P X :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hX_growth
  have hY_det : IsMomentDeterminate P Y :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hY_growth
  sorry
