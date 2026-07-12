import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Scheme.Hom

universe u

namespace AlgebraicGeometry

-- Source-facing item: the reduced case of the scheme-theoretic image factorization for immersions.
-- The public surface stays at the source layer: the canonical map `h.toImage` is an open
-- immersion, and this yields the usual open-then-closed factorization through the image.

namespace Scheme.Hom

/-- Lemma 29.3.3, canonical bridge: if `h : Z ⟶ X` is an immersion and `Z` is reduced, then the
map from `Z` to the scheme-theoretic image of `h` is an open immersion. -/
@[stacks 03DQ]
theorem isOpenImmersion_toImage_of_isImmersion_of_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) (hh : IsImmersion h) [IsReduced Z] :
    IsOpenImmersion h.toImage := by
  sorry

end Scheme.Hom

/-- Lemma 29.3.3: if `h : Z ⟶ X` is an immersion and `Z` is reduced, then `h` factors as an open
immersion followed by a closed immersion. -/
@[stacks 03DQ]
theorem immersion_factors_open_then_closed_of_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) (hh : IsImmersion h) [IsReduced Z] :
    ∃ (Zbar : Scheme.{u}) (j : Z ⟶ Zbar) (hj : IsOpenImmersion j)
      (i : Zbar ⟶ X) (hi : IsClosedImmersion i), j ≫ i = h := by
  refine ⟨Scheme.Hom.image h, h.toImage,
    isOpenImmersion_toImage_of_isImmersion_of_isReduced h hh,
    Scheme.Hom.imageι h, inferInstance, ?_⟩
  simpa using Scheme.Hom.toImage_imageι h

end AlgebraicGeometry
