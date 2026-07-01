import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_29_3

-- Declarations for this item will be appended below by the statement pipeline.

set_option linter.style.longLine false

/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, the Chapter 6 content here is the textbook
  differentiability/uniqueness criterion for Kuhn--Tucker objects of a convex bifunction, with
  the Euclidean coordinate formula treated as a downstream bridge.
- `core/canonical`: the owner abstractions already live in the chapter as
  `Bifunction.perturbationFunction` and `Bifunction.IsKuhnTuckerVector`, with the intrinsic
  dual-owner uniqueness theorem and the inner-product gradient bridge supplied upstream in
  `Corollary_6_29_3`, and the interior-domain owner `Bifunction.IsStrictlyConsistent` from
  Definition 6.29.10.
- `bridge/view`: this file adds no new mathematics beyond the canonical source-facing theorem
  family already present in `Items/Chap06/Corollary_6_29_3.lean`, so the correct refinement is
  direct recall of those owner theorems rather than a parallel duplicate.

Primary mathematical domain:
- perturbation functions of convex bifunctions, Kuhn--Tucker vectors/functionals, and the
  differentiability/subgradient bridge.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.IsKuhnTuckerVector` from `Definition_6_29_19`;
- `Function.differentiableAt_iff_existsUnique_mem_subdifferentialAt` from `Theorem_25_2`;
- the intrinsic uniqueness theorem, gradient bridge, and coordinate bridge from
  `Corollary_6_29_3`.

Primitive data vs derived API:
- primitive source data: a convex bifunction `F` and its Chapter 6 owners
  `perturbationFunction F`, `IsStrictlyConsistent F`, and `IsKuhnTuckerVector F`;
- derived API: the uniqueness criterion via strict consistency together with differentiability at
  `0`, the intrinsic gradient formula, and the Euclidean coordinate formula as a bridge.

Layer target: `bridge/view`. The public surface should reuse the canonical Chapter 6 theorem family
already owned upstream, with no second wrapper theorem layer in this file.
-/

/- The strict-consistency plus differentiability uniqueness criterion is already the intrinsic
dual-owner source-facing theorem from `Corollary_6_29_3`. -/
recall Bifunction.existsUnique_kuhnTuckerFunctional_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite

/- The inner-product bridge identifying a Kuhn--Tucker vector with the negative gradient is
already canonical in `Corollary_6_29_3`. -/
recall Bifunction.kuhnTuckerVector_eq_neg_gradient_perturbationFunction_zero

/- The strict-consistency plus differentiability uniqueness criterion is already the canonical
inner-product vector form from `Corollary_6_29_3`. -/
recall Bifunction.existsUnique_kuhnTuckerVector_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite

/- The coordinate formula for a Kuhn--Tucker vector is the Euclidean bridge form and is recalled
as such from `Corollary_6_29_3`. -/
recall Bifunction.kuhnTuckerVector_apply_eq_neg_partialDeriv_perturbationFunction_zero
