import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Theorem_12_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 12.1 is `source-facing`: it isolates the strong-duality equality from the stronger
Chapter 12 owner theorem `dual_based_proximal_gradient_strong_duality_with_dual_attainment`.
The equality companion itself is now owned by `Theorem_12_2`, so this file reuses that canonical
chapter theorem directly rather than keeping a parallel local projection wrapper. -/
recall dual_based_proximal_gradient_problem_strong_duality
