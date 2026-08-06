import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

/- Problem 2.9.4 (1): any category with all coproducts and coequalizers is cocomplete, as
expressed by the canonical theorem constructing all colimits from these two classes of colimits. -/
#check has_colimits_of_hasCoequalizers_and_coproducts

/- Problem 2.9.4 (2): by passage to opposite categories, the dual statement says that products and
equalizers imply completeness, as recorded by the canonical theorem constructing all limits from
these two classes of limits. -/
#check has_limits_of_hasEqualizers_and_products
