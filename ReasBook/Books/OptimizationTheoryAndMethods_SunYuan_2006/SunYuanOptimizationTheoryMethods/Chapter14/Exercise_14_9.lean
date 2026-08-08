import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter14.Lemma_14_6_2

-- Source/core/bridge triage:
-- * source-facing item: Exercise 14.9 recalls the Section 14.6 quantities and the seven clauses
--   of Lemma 14.6.2;
-- * core/canonical owner: the existing Section 14.6 declarations in `Lemma_14_6_2`;
-- * bridge/view: none, because this file is a pure recall pointer.
-- The exercise therefore reuses the canonical Chapter 14 API directly and introduces no parallel
-- local wrappers.

/- Chapter14 Exercise 14.9: recall the canonical Section 14.6 owners and the seven clauses of
`SunYuanOptimizationTheoryMethods.Chapter14.Lemma_14_6_2`. -/

#check compositeNonsmoothJacobianTranspose
#check compositeNonsmoothChi
#check compositeNonsmoothPsiValueSet
#check compositeNonsmoothPsi
#check compositeNonsmoothDirectionalValueSet
#check compositeNonsmoothDF

#check compositeNonsmoothDF_isLUB
#check compositeNonsmoothChi_concaveOn
#check compositeNonsmoothChi_hasRightDirectionalDerivAt_zero
#check zero_le_compositeNonsmoothPsi
#check compositeNonsmoothPsi_one_eq_zero_iff_stationaryCondition
#check compositeNonsmoothPsi_concaveOn
#check continuous_compositeNonsmoothPsi
