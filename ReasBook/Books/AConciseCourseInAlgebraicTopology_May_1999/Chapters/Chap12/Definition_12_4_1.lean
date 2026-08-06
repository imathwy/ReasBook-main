import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

-- `Function.Exact` is the canonical owner for exact pairs of maps. For sequences of modules,
-- `ShortComplex.moduleCat_exact_iff_range_eq_ker` recovers the source condition
-- `LinearMap.range f = LinearMap.ker g`, and
-- `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact` bridges this module-theoretic
-- exactness with the categorical exactness predicate on short complexes in `ModuleCat`.

/- Definition 12.4.1: a sequence of modules is exact when each consecutive pair of module maps is
exact in the canonical mathlib sense `Function.Exact`; for short complexes in `ModuleCat`, this is
equivalent to the source condition that the image of one map equals the kernel of the next. -/
#check Function.Exact
#check ShortComplex.moduleCat_exact_iff_range_eq_ker
#check ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
