import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open CategoryTheory Limits
open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/- Definition 10.48.3 (Tag 037T): the canonical scheme-theoretic notion of a geometrically
connected `k`-algebra `S` is that the affine morphism `Spec S ⟶ Spec k` is geometrically
connected, namely
`geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S)))`.
-/
#check (geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))))

private theorem connectedSpace_of_iso {X Y : Scheme} (e : X ≅ Y) [ConnectedSpace X] :
    ConnectedSpace Y := by
  let e' := Scheme.homeoOfIso e
  exact e'.surjective.connectedSpace e'.continuous

local instance :
    ObjectProperty.IsClosedUnderIsomorphisms
      (ConnectedSpace · : CategoryTheory.ObjectProperty Scheme) := by
  exact ⟨fun {X Y} e h ↦ by
    letI : ConnectedSpace ↥X := h
    exact connectedSpace_of_iso e⟩

/-- Prime-spectrum form of the base-change criterion from Definition 10.48.3. -/
@[stacks 037T]
theorem geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K], ConnectedSpace (PrimeSpectrum (S ⊗[k] K)) := by
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    letI :
        ConnectedSpace
          ↥(pullback (Spec.map (ofHom (algebraMap k S))) (Spec.map (ofHom (algebraMap k K)))) :=
      h K
    simpa using connectedSpace_of_iso (pullbackSpecIso k S K)
  · intro h K _ _
    letI : ConnectedSpace (Spec (of (S ⊗[k] K))) := by
      simpa using h K
    simpa using connectedSpace_of_iso (pullbackSpecIso k S K).symm

end

section

variable {k : Type u} [Field k]

/-- A field is geometrically connected over itself. -/
instance : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k k))) := by
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
  intro K _ _
  let e : k ⊗[k] K ≃ₐ[k] K := Algebra.TensorProduct.lid k K
  letI : IsDomain (k ⊗[k] K) := MulEquiv.isDomain _ e.toMulEquiv
  infer_instance

end

end Algebra
