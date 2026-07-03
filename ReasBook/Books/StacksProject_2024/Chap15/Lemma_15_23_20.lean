import Mathlib
import StacksProject_2024.Chap15.Lemma_15_23_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Module

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
variable [Module.Finite A (integralClosure A L)]
local notation "B" => integralClosure A L

/-
Domain-style sampling:
- primary domain: finite integral closures over Noetherian normal domains, viewed as finite
  modules over the base domain and analyzed via the chapter's reflexivity criterion;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.IsTorsionFree`,
  `IsIntegralClosure.isTorsionFree`,
  `reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection`;
- best owner abstraction:
  `Module.IsReflexive` is the core/canonical owner of the conclusion, and Lemma `15.23.18` is the
  chapter bridge/view that turns the height-one-localization-intersection criterion into that
  owner instance;
- source/core/bridge triage:
  `source-facing`: this lemma asserting that the finite integral closure is reflexive;
  `core/canonical`: `Module.IsReflexive`;
  `bridge/view`: the proof route through torsion-freeness and the height-one localization
    intersection inside the ambient field.

Primitive data are only the normal domain `A`, the finite extension `L / FractionRing A`, and the
finiteness of `integralClosure A L` over `A`. Torsion-freeness of the integral closure and the
final reflexivity claim are derived API from the owner abstractions above, so the public surface
should be a single named owner instance rather than a theorem duplicated by a second wrapper
instance.
-/

-- Proof sketch: by Lemma `15.23.18`, it is enough to show that `integralClosure A L` agrees with
-- the intersection of its height-one localizations inside `L`. For an element of that
-- intersection, Lemma `10.38.6` shows that the coefficients of its minimal polynomial over
-- `FractionRing A` lie in every height-one localization of `A`, and Lemma `10.157.6` then forces
-- those coefficients to lie in `A`, proving integrality over `A`.
/-- Lemma 15.23.20: if `A` is a Noetherian normal domain and `L / FractionRing A` is a finite
extension such that the integral closure of `A` in `L` is finite over `A`, then
`integralClosure A L` is reflexive as an `A`-module. -/
instance integralClosure_isReflexive_of_finite :
    IsReflexive A B := sorry

end
