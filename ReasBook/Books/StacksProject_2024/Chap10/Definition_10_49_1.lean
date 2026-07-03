import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat
open scoped TensorProduct

universe u

/- Definition 10.49.1: the canonical scheme-theoretic notion of a geometrically integral
`k`-algebra `S` is
`AlgebraicGeometry.GeometricallyIntegral (Spec.map (ofHom (algebraMap k S)))`.
-/
recall AlgebraicGeometry.GeometricallyIntegral

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- Companion bridge for Definition 10.49.1: the affine morphism `Spec S ⟶ Spec k` is
geometrically integral if and only if every field extension `K / k` makes `S ⊗[k] K` a domain.
-/
theorem geometricallyIntegral_iff_isDomain_tensorProduct :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (S ⊗[k] K) := by
  let f : Spec (of S) ⟶ Spec (of k) := Spec.map (ofHom (algebraMap k S))
  change GeometricallyIntegral f ↔
    ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (S ⊗[k] K)
  letI : ObjectProperty.IsClosedUnderIsomorphisms (IsIntegral : ObjectProperty Scheme) :=
    ⟨fun e _ ↦ IsIntegral.of_isIso e.hom⟩
  rw [geometricallyIntegral_iff]
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    let _ : IsIntegral (pullback f (Spec.map (ofHom (algebraMap k K)))) := h K
    exact
      (affine_isIntegral_iff (of (S ⊗[k] K))).1 <|
        IsIntegral.of_isIso (pullbackSpecIso k S K).hom
  · intro h K _ _
    let _ : IsIntegral (Spec (of (S ⊗[k] K))) :=
      (affine_isIntegral_iff (of (S ⊗[k] K))).2 (h K)
    exact IsIntegral.of_isIso (pullbackSpecIso k S K).inv

end
