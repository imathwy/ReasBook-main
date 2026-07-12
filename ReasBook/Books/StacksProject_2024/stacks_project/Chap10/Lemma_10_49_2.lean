import Mathlib.AlgebraicGeometry.Properties
import StacksProject_2024.Chap10.Definition_10_43_1
import StacksProject_2024.Chap10.Definition_10_47_4
import StacksProject_2024.Chap10.Definition_10_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

namespace Algebra

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.49.2: a `k`-algebra is geometrically integral exactly when it is geometrically
irreducible over `k` and geometrically reduced over `k`. -/
-- Proof sketch: this is a thin `bridge/view` statement. The owner abstraction is the affine
-- morphism `Spec S ⟶ Spec k`: geometric integrality supplies the owner-side reduced and
-- irreducible instances, and conversely those two owner properties recover geometric integrality.
-- The only non-owner step is the affine bridge
-- `geometricallyReduced_iff_isGeometricallyReduced`.
theorem geometricallyIntegral_iff_geometricallyIrreducible_and_geometricallyReduced :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) ∧
        IsGeometricallyReduced k S := by
  let f : Spec (of S) ⟶ Spec (of k) := Spec.map (ofHom (algebraMap k S))
  change GeometricallyIntegral f ↔ GeometricallyIrreducible f ∧ IsGeometricallyReduced k S
  constructor
  · intro h
    letI : GeometricallyIntegral f := h
    exact ⟨inferInstance, geometricallyReduced_iff_isGeometricallyReduced.mp inferInstance⟩
  · rintro ⟨hIrreducible, hReduced⟩
    letI : GeometricallyIrreducible f := hIrreducible
    have hReduced' : GeometricallyReduced f :=
      geometricallyReduced_iff_isGeometricallyReduced.mpr hReduced
    letI : GeometricallyReduced f := hReduced'
    exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

end

end Algebra
