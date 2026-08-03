import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter01.Definition_1_2_28

-- Domain sampling pass:
-- * mathlib owner abstractions:
--   `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`
--   `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`
-- * chapter source-facing owners:
--   `norm_image_sub_le_of_segment_fderiv_bound`
--   `norm_image_sub_sub_le_of_segment_fderiv_deviation_bound`
--
-- The exercise statements are already formalized canonically in
-- `Definition_1_2_28.lean`, so this file should reuse those owners directly
-- instead of keeping parallel local copies.

/-
Chapter01 Exercise 1.8

Recall-only entry: the two formulas requested here are exactly the source-facing
chapter owners `norm_image_sub_le_of_segment_fderiv_bound` and
`norm_image_sub_sub_le_of_segment_fderiv_deviation_bound`.
-/
#check norm_image_sub_le_of_segment_fderiv_bound
#check norm_image_sub_sub_le_of_segment_fderiv_deviation_bound
