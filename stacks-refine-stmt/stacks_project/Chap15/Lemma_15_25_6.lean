import Mathlib
import stacks_project.Chap10.Lemma_10_57_10
import stacks_project.Chap15.Lemma_15_22_10
import stacks_project.Chap15.Lemma_15_25_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open Module

/- Domain-style sampling:
- primary domain: finite-presentation descent for finite type algebras and finite modules over a
  valuation ring;
- sampled owner API:
  `exists_graded_localization_model_of_finite_module`,
  `flat_iff_isTorsionFree_of_valuationRing`,
  `graded_algebra_finitePresentation_of_flat`,
  `graded_module_finitePresentation_of_flat`,
  `primeLocalizationsDetectEquality_of_isDomain`;
- best owner abstraction: the public conclusions are already the canonical owner predicates
  `Algebra.FinitePresentation A B` and `Module.FinitePresentation B M`;
- source/core/bridge triage:
  `source-facing`: the two valuation-ring descent statements in this file;
  `core/canonical`: `Algebra.FinitePresentation` and `Module.FinitePresentation`;
  `bridge/view`: the graded localization model
  `exists_graded_localization_model_of_finite_module`, the valuation-ring flat/torsion-free bridge
  `flat_iff_isTorsionFree_of_valuationRing`, the domain detection bridge
  `primeLocalizationsDetectEquality_of_isDomain`, and the graded descent theorems
  `graded_algebra_finitePresentation_of_flat` and `graded_module_finitePresentation_of_flat`.

The only primitive public data here are the finite type / finite module hypotheses and flatness.
The module theorem should therefore stay at the `AddCommMonoid` owner level of
`Module.Finite`, `Module.Flat`, and `Module.FinitePresentation`; the graded presentation data are
derived bridge data from the sampled owner API and should not be reintroduced as public wrapper
structures or stronger ambient additive assumptions in this file.
-/

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

-- Proof sketch: represent the finite type `A`-algebra `B` as the degree-zero localization of a
-- finite graded algebra over `A` via
-- `exists_graded_localization_model_of_finite_module`, replace the graded algebra by its
-- torsion-free quotient using `flat_iff_isTorsionFree_of_valuationRing`, apply
-- `graded_algebra_finitePresentation_of_flat` together with
-- `primeLocalizationsDetectEquality_of_isDomain`, and then localize the resulting finite
-- presentation.
/-- Lemma 15.25.6 (1): if `A` is a valuation ring, `A → B` is a finite type ring map, and `B` is
flat over `A`, then `B` is a finitely presented `A`-algebra. -/
theorem algebra_finitePresentation_of_finiteType_flat_over_valuationRing [Flat A B] :
    Algebra.FinitePresentation A B := sorry

variable {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M]

-- Proof sketch: choose a graded presentation `M ≅ N_(f)` over a graded finite type algebra `S`
-- using `exists_graded_localization_model_of_finite_module`, replace `N` by its torsion-free
-- quotient using the quotient owner from Lemma `15.22.2` and
-- `flat_iff_isTorsionFree_of_valuationRing`, apply
-- `graded_module_finitePresentation_of_flat` over the graded model using
-- `primeLocalizationsDetectEquality_of_isDomain`, and then localize the resulting finite
-- presentation to `B`.
/-- Lemma 15.25.6 (2): if `A` is a valuation ring, `A → B` is a finite type ring map, `M` is a
finite `B`-module, and `M` is flat as an `A`-module, then `M` is finitely presented as a
`B`-module. -/
theorem module_finitePresentation_of_finite_flat_over_valuationRing [Flat A M] :
    Module.FinitePresentation B M := sorry

end
