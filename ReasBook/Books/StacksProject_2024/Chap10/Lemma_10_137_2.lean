import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: smooth commutative algebra maps and their behavior under source and target
  localization;
- sampled owner declarations:
  `Algebra.Smooth.comp`,
  `Algebra.Smooth.of_isLocalization_Away`,
  `RingHom.smooth_algebraMap`,
  `Algebra.TensorProduct.lidOfCompatibleSMul`;
- best owner abstraction: `Algebra.Smooth R S`, with `RingHom.Smooth` as the canonical ring-hom
  view of the induced localization map;
- primitive data: the commutative rings, the algebra structure `R → S`, the localization element,
  and the canonical source localization map `Localization.awayLift`;
- derived API: smoothness after localizing the target, and smoothness of the induced map from the
  source localization when the localized element already becomes a unit in `S`.

Source/core/bridge triage:
- `source-facing`: the two textbook localization lemmas;
- `core/canonical`: `Algebra.Smooth`, `RingHom.Smooth`, and smooth base change;
- `bridge/view`: `RingHom.smooth_algebraMap` and `Algebra.TensorProduct.lidOfCompatibleSMul`
  translate the canonical owner facts to the source-facing ring-hom statement.
-/

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: the localization map `S → S_g` is smooth by
-- `Algebra.Smooth.of_isLocalization_Away`, and smoothness is stable under composition.
/-- Lemma 10.137.2 (1): if `R → S` is smooth, then every localization `S_g` is smooth over `R`. -/
theorem smooth_localization_away_target [Smooth R S] (g : S) :
    Smooth R (Localization.Away g) := by
  letI : Smooth S (Localization.Away g) := Smooth.of_isLocalization_Away g
  exact Smooth.comp R S (Localization.Away g)

-- Proof sketch: the induced map `R_f → S` is the localization map obtained from the fact that the
-- image of `f` is a unit in `S`; use the locality of smoothness with respect to localization on
-- the source.
/-- Lemma 10.137.2 (2): if `f ∈ R` maps to a unit in `S`, then the induced map `R_f → S` is
smooth. -/
theorem smooth_away_lift_of_isUnit [Smooth R S] (f : R) (hf : IsUnit (algebraMap R S f)) :
    RingHom.Smooth (Localization.awayLift (algebraMap R S) f hf) := by
  letI : Algebra (Localization.Away f) S :=
    (Localization.awayLift (algebraMap R S) f hf).toAlgebra
  have hcomp :
      (Localization.awayLift (algebraMap R S) f hf).comp (algebraMap R (Localization.Away f)) =
        algebraMap R S := by
    ext x
    simp [Localization.awayLift]
  letI : IsScalarTower R (Localization.Away f) S := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let e := Algebra.TensorProduct.lidOfCompatibleSMul R (Localization.Away f) S
  have hsmooth : Smooth (Localization.Away f) S := Smooth.of_equiv e
  exact (RingHom.smooth_algebraMap).2 hsmooth

end Algebra
