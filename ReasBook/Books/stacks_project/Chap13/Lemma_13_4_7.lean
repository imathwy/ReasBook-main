import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

/- Domain-style sampling:
- primary domain: pretriangulated categories, organized around distinguished triangles and the
  TR1/TR3 comparison data attached to a fixed morphism;
- sampled owner declarations:
  `Pretriangulated.distinguished_cocone_triangle`,
  `Pretriangulated.isoTriangleOfIso₁₂`,
  `Pretriangulated.exists_iso_of_arrow_iso`,
  `distTriang`;
- best owner abstraction: the existence part of Lemma 13.4.7 is exactly the canonical owner
  `distinguished_cocone_triangle`, while the comparison between two distinguished cones on the
  same morphism is derived directly from the canonical owner theorem
  `exists_iso_of_arrow_iso` by specializing to the identity arrow isomorphism on `f`;
- primitive data: a morphism `f : X ⟶ Y`, and for the comparison statement two distinguished
  triangles of the form `Triangle.mk f _ _`;
- derived API: the source-facing uniqueness statement, whose witness is obtained from
  `exists_iso_of_arrow_iso` and has identity first two components.

Source/core/bridge triage:
- `source-facing`: existence of a distinguished triangle on `f`, and the comparison between two
  such distinguished triangles;
- `core/canonical`: `distinguished_cocone_triangle`, `exists_iso_of_arrow_iso`, and `distTriang`;
- `bridge/view`: the identity-arrow specialization of `exists_iso_of_arrow_iso` for
  `Triangle.mk f g h` and `Triangle.mk f g' h'`.

The file should therefore recall the canonical owner for the existence statement and keep only the
source-facing uniqueness theorem as derived API.
-/

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Lemma 13.4.7 (existence): this is exactly the canonical owner theorem
`Pretriangulated.distinguished_cocone_triangle`. -/
recall distinguished_cocone_triangle

/-- Lemma 13.4.7: any two distinguished triangles with the same first morphism are isomorphic by
a triangle isomorphism whose first two components are identities. -/
theorem exists_distinguished_triangle_unique_up_to_iso {X Y Z Z' : D} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧} {g' : Y ⟶ Z'} {h' : Z' ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang D) (hT' : Triangle.mk f g' h' ∈ distTriang D) :
    ∃ e : Triangle.mk f g h ≅ Triangle.mk f g' h', e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y := by
  simpa using
    (exists_iso_of_arrow_iso _ _ hT hT' (Arrow.isoMk (Iso.refl X) (Iso.refl Y) (by simp)))

end CategoryTheory
