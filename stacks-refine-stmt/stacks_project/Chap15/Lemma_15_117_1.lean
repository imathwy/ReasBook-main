import Mathlib
import stacks_project.Chap15.Definition_15_116_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y z

/-
Domain-style sampling for Lemma 15.117.1:
- primary domain: finite tower stability of the Chapter 15 solution predicate for extensions of
  discrete valuation rings, with branchwise formal smoothness on reduced tensor-product integral
  closures;
- sampled owner declarations:
  `IsSolutionFor`,
  `formallySmoothForAdic_localization_baseChange_integralClosure`,
  `Localization.localRingHom`,
  `RingHom.formally_smooth_for_adic`;
- best owner abstraction: the source-facing theorem should remain stated directly with the owner
  predicate `IsSolutionFor`; the localized branch formal-smoothness statement is derived API and
  should be reused from `Lemma_15_115_3` rather than rebuilt through a local branch wrapper;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, and the finite tower `K ⊂ K₁ ⊂ K₂`; the branch localizations and their
  formal-smoothness properties are derived API.

Source/core/bridge triage:
- `source-facing`: `solutionFor_of_finite_extension`;
- `core/canonical`: `IsSolutionFor`, `Localization.localRingHom`,
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: `formallySmoothForAdic_localization_baseChange_integralClosure`.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra K1 K2] [Algebra K K2] [Algebra A K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2]

-- Proof sketch: for each maximal branch of the integral-closure base change over `K1 / K`, the
-- hypothesis gives formal smoothness of the corresponding localized extension. Apply
-- Lemma `15.115.3` to each such localized map after the finite extension `K2 / K1`; this yields
-- formal smoothness for every branch over `K2 / K`, which is exactly the definition of being a
-- solution.
/-- Lemma 15.117.1: if `K₁ / K` is a solution for the extension `A ⊂ B` of discrete valuation
rings, then every finite extension `K₂ / K₁` is again a solution for `A ⊂ B`, viewed as a finite
extension of `K`. -/
theorem solutionFor_of_finite_extension
    (hK1 : IsSolutionFor A B K L K1) :
    IsSolutionFor A B K L K2 := sorry

end
