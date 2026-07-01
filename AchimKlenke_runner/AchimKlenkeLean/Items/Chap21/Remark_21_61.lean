import AchimKlenkeLean.Items.Chap21.Definition_21_58

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ENNReal Topology

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/- Remark 21.61 is a `bridge/view` item in the Chapter 21 dyadic square-variation API.
Its owner abstractions are the dyadic square-variation and quadratic-covariation predicates from
Definition 21.58 together with mathlib's total-variation owner `eVariationOn`. The primitive data
are chosen square-variation paths `⟨F + G⟩`, `⟨F - G⟩`, `⟨F⟩`, `⟨G⟩`, and a chosen covariation path
`⟨F,G⟩`; the polarization formula and the first-variation bound are derived API for those owner
objects. -/

-- Proof sketch: the mixed dyadic increment sum is the polarization combination of the dyadic
-- square-variation sums for `F + G` and `F - G`, so the limit path is
-- `t ↦ (⟨F + G⟩_t - ⟨F - G⟩_t) / 4`.
/-- Remark 21.61 (1): if `brAdd` and `brSub` are chosen square-variation realizations of
`F + G` and `F - G`, then `((1 / 4) • (brAdd - brSub))` realizes the quadratic covariation of
`F` and `G`; equivalently, `⟨F,G⟩_T = (⟨F + G⟩_T - ⟨F - G⟩_T) / 4`. -/
theorem hasQuadraticCovariationAlong_polarization
    {F G : PathSpace} {brAdd brSub : PathwiseProcess}
    (hAdd : HasSquareVariationAlong (F + G) brAdd)
    (hSub : HasSquareVariationAlong (F - G) brSub) :
    HasQuadraticCovariationAlong F G ((1 / 4 : ℝ) • (brAdd - brSub)) := sorry

-- Proof sketch: apply the pointwise Cauchy--Schwarz bound to the approximating sums and pass to
-- the limit; the dyadic first variations of the approximating mixed sums are bounded by
-- Cauchy--Schwarz. This is the mathlib-owner form of the textbook bound
-- `V_T^1(⟨F,G⟩) ≤ √(⟨F⟩_T * ⟨G⟩_T)`.
/-- Remark 21.61 (2): for a chosen dyadic quadratic-covariation path `covFG` and chosen square
variation paths `brF`, `brG`, the total variation of `covFG` on `[0, T]` is bounded by
`Real.sqrt (brF T * brG T)`. Equivalently, in textbook notation,
`V_T^1(⟨F,G⟩) ≤ Real.sqrt (⟨F⟩_T * ⟨G⟩_T)`. -/
theorem eVariationOn_Icc_le_sqrt_mul_of_hasQuadraticCovariationAlong
    {F G : PathSpace} {brF brG covFG : PathwiseProcess}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG)
    (T : NNReal) :
    eVariationOn covFG (Icc 0 T) ≤ ENNReal.ofReal (Real.sqrt (brF T * brG T)) := sorry
