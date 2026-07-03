import Mathlib
import AchimKlenkeLean.Items.Chap21.Remark_21_59
import AchimKlenkeLean.Items.Chap21.Remark_21_61

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/- Corollary 21.63 is a `source-facing` bridge in the Chapter 21 dyadic square-variation API.
Its core owners are `HasSquareVariationAlong`, `HasQuadraticCovariationAlong`, and mathlib's
variation owner `LocallyBoundedVariationOn`; the relevant derived upstream API is the vanishing
textbook quadratic-variation result of Remark 21.59 and the polarization/covariation API of
Remark 21.61. The primitive data here are only chosen square-variation and covariation paths, and
the corollary records the special zero-right-bracket consequences for those owner objects. -/

variable {F G : PathSpace} {V VF VFG : PathwiseProcess}

-- Proof sketch: this is the preceding vanishing-bracket criterion specialized to a chosen
-- square-variation realization of a path of locally finite variation. Remark 21.59 shows that the
-- textbook quadratic variation is zero, so the dyadic square-variation owner is realized by the
-- zero path.
/-- A continuous path of locally finite variation has zero square variation along the dyadic
partitions. This is the owner-level bridge behind the parenthetical clause in Corollary 21.63. -/
theorem hasSquareVariationAlong_zero_of_locallyFiniteVariation
    (hG : LocallyBoundedVariationOn G univ) :
    HasSquareVariationAlong G 0 := sorry

-- Proof sketch: compare an arbitrary chosen square-variation realization with the canonical zero
-- realization from `hasSquareVariationAlong_zero_of_locallyFiniteVariation`; uniqueness of limits
-- forces the chosen realization to equal `0`.
/-- A continuous path of locally finite variation has identically vanishing square variation along
every chosen square-variation realization. This is the witness-level companion to
`hasSquareVariationAlong_zero_of_locallyFiniteVariation`. -/
theorem squareVariation_eq_zero_of_locallyFiniteVariation
    (hV : HasSquareVariationAlong G V)
    (hG : LocallyBoundedVariationOn G univ) :
    V = 0 := sorry

-- Proof sketch: apply the vanishing-covariation criterion from the square-variation theory to the
-- pair `(F,G)` using that `F` admits a locally finite square-variation realization and that the
-- chosen square variation of `G` is zero.
/-- Corollary 21.63 (1): if `F` has locally finite square variation and `G` has zero square
variation, then the zero path is a quadratic-covariation realization of `F` and `G`. -/
theorem hasQuadraticCovariationAlong_zero_of_right_zeroSquareVariation
    (hVF : HasSquareVariationAlong F VF)
    (hVF_var : LocallyBoundedVariationOn VF univ)
    (hG : HasSquareVariationAlong G 0) :
    HasQuadraticCovariationAlong F G 0 := sorry

-- Proof sketch: from the chosen square-variation paths of `F + G`, `F`, and `G = 0`, the dyadic
-- identity `[F + G] = [F] + 2[F,G] + [G]` yields a quadratic-covariation realization
-- `((1 / 2) • (VFG - VF))` for `(F,G)`. Part (1) forces that covariation path to vanish, and then
-- the bracket identity reduces to `VFG = VF`.
/-- Corollary 21.63 (2): if `F` has locally finite square variation, `G` has zero square
variation, then every chosen square-variation path of `F + G` equals the chosen square-variation
path of `F`. -/
theorem squareVariation_add_eq_left_of_right_zeroSquareVariation
    (hVF : HasSquareVariationAlong F VF)
    (hVF_var : LocallyBoundedVariationOn VF univ)
    (hG : HasSquareVariationAlong G 0)
    (hVFG : HasSquareVariationAlong (F + G) VFG) :
    VFG = VF := sorry
