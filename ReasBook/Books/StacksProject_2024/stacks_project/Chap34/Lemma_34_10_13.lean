import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_124_1
import StacksProject_2024.stacks_project.Chap34.Definition_34_10_7

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owner `UniversallyClosed` together
-- with `universallyClosed_eq_universallySpecializing`, while the local Chapter 34 source-facing
-- owner for the first clause is `IsVCovering`. This item is therefore formalized as the singleton
-- `V`-covering bridge to `UniversallyClosed`, with separate source-facing companions for the
-- valuation-extension and specialization-lifting criteria.

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- Lemma 34.10.13 (1): for a quasi-compact morphism `f : X ⟶ Y`, the singleton family `{X ⟶ Y}`
is a `V` covering if and only if `f` is universally closed. -/
@[stacks 0ETN]
theorem isVCovering_singleton_iff_universallyClosed :
    IsVCovering Y (fun _ : PUnit ↦ X) (fun _ ↦ f) ↔ UniversallyClosed f := sorry

/-- Lemma 34.10.13 (2): for a quasi-compact morphism `f : X ⟶ Y`, universal closedness is
equivalent to the valuation-ring extension lifting criterion from the source. -/
@[stacks 0ETN]
theorem universallyClosed_iff_valuationRingLift :
    UniversallyClosed f ↔
      ∀ ⦃V : Type u⦄ [CommRing V] [IsDomain V] [ValuationRing V]
        (g : Spec (CommRingCat.of V) ⟶ Y),
          ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
            (_ : Algebra V W) (_ : IsExtensionOfValuationRings V W)
            (lift : Spec (CommRingCat.of W) ⟶ X),
            Spec.map (CommRingCat.ofHom (algebraMap V W)) ≫ g = lift ≫ f := sorry

/-- Lemma 34.10.13 (3): for a quasi-compact morphism `f : X ⟶ Y`, universal closedness is
equivalent to lifting every specialization in a base scheme `Z` to a specialization in the
pullback `pullback f g = X ×[Y] Z`, mapping to the given pair under `pullback.snd f g`. -/
@[stacks 0ETN]
theorem universallyClosed_iff_specializationLift :
    UniversallyClosed f ↔
      ∀ ⦃Z : Scheme.{u}⦄ (g : Z ⟶ Y) ⦃z' z : Z⦄, z' ⤳ z →
        ∃ (w' w : pullback f g),
          w' ⤳ w ∧ (pullback.snd f g w', pullback.snd f g w) = (z', z) :=
      sorry

end

end AlgebraicGeometry
