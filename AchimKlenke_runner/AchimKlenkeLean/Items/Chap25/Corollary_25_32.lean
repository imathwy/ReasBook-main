import Mathlib
import AchimKlenkeLean.Items.Chap25.Theorem_25_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

/- Domain-style sampling for Corollary 25.32:
* primary domain: dyadic pathwise Itô integration with quadratic covariation;
* sampled owner declarations in the same domain:
  `HasQuadraticCovariationAlong`,
  `exists_quadratic_covariation_along_of_hasContinuousSquareVariation`,
  `HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong`, and
  `pathwiseItoIntegralAlong`;
* owner abstraction: the canonical dyadic integral `pathwiseItoIntegralAlong` together with the
  dyadic covariation owner `HasQuadraticCovariationAlong`;
* primitive data: a chosen continuous covariation path `covXY : PathSpace`;
* derived API: the product-rule identity and the polarization corollary below.

Layer triage:
* source-facing: the product-rule identity for `X Y`;
* core/canonical: `HasQuadraticCovariationAlong` and `pathwiseItoIntegralAlong`;
* bridge/view: Corollary 25.32, which rewrites the source formula through those owners. -/

-- Proof sketch: specialize the two-dimensional pathwise Itô formula to `F(x,y) = xy`; the
-- first-order terms are the canonical dyadic Itô integrals of `Y` against `X` and of `X`
-- against `Y`.
/-- For a chosen continuous dyadic quadratic covariation path `⟨X,Y⟩`, the dyadic pathwise
product rule takes the canonical form
`X_T Y_T = X_0 Y_0 + ∫_0^T Y_s dX_s + ∫_0^T X_s dY_s + ⟨X,Y⟩_T`,
where the Itô terms are expressed by `pathwiseItoIntegralAlong`. -/
theorem dyadic_pathwise_product_rule
    {X Y : PathSpace}
    (covXY : PathSpace)
    (hcovXY : HasQuadraticCovariationAlong X Y covXY)
    (hItoYX :
      HasPathwiseItoIntegralAlong
        Y
        X
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong Y X dyadicPartitionSequence))
    (hItoXY :
      HasPathwiseItoIntegralAlong
        X
        Y
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong X Y dyadicPartitionSequence))
    (T : NNReal) :
    X T * Y T =
      X 0 * Y 0 +
        pathwiseItoIntegralAlong Y X dyadicPartitionSequence T +
        pathwiseItoIntegralAlong X Y dyadicPartitionSequence T +
        covXY T := sorry

/-- Corollary 25.32: if `X - Y` and `X + Y` lie in `𝒞_qv`, then the dyadic quadratic covariation
`⟨X,Y⟩` is available by polarization, and whenever the canonical dyadic pathwise Itô integrals of
`Y` against `X` and of `X` against `Y` satisfy their defining convergence, the product rule
`X_T Y_T = X_0 Y_0 + ∫_0^T Y_s dX_s + ∫_0^T X_s dY_s + ⟨X,Y⟩_T`
holds for every `T ≥ 0`, with the Itô terms written via the canonical owner
`pathwiseItoIntegralAlong`. -/
theorem dyadic_pathwise_product_rule_of_continuous_square_variation
    {X Y : PathSpace}
    (hXmY : HasContinuousSquareVariation (X - Y))
    (hXpY : HasContinuousSquareVariation (X + Y))
    (hItoYX :
      HasPathwiseItoIntegralAlong
        Y
        X
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong Y X dyadicPartitionSequence))
    (hItoXY :
      HasPathwiseItoIntegralAlong
        X
        Y
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong X Y dyadicPartitionSequence))
    (T : NNReal) :
    ∃ covXY : PathSpace,
      HasQuadraticCovariationAlong X Y covXY ∧
        X T * Y T =
          X 0 * Y 0 +
            pathwiseItoIntegralAlong Y X dyadicPartitionSequence T +
            pathwiseItoIntegralAlong X Y dyadicPartitionSequence T +
            covXY T := by
  obtain ⟨covXY, hcovXY⟩ :=
    exists_quadratic_covariation_along_of_hasContinuousSquareVariation hXmY hXpY
  exact ⟨covXY, hcovXY,
    dyadic_pathwise_product_rule covXY hcovXY hItoYX hItoXY T⟩
