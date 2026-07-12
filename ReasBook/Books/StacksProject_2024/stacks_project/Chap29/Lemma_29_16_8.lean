import Mathlib
import StacksProject_2024.Chap29.Definition_29_16_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced `Scheme.Hom.closePoints_subset_preimage_closedPoints` and
  `LocallyOfFiniteType.jacobsonSpace` as the canonical Jacobson/locally finite type API;
- local Chapter 29 precedent fixes finite type points as `finiteTypePoints S`;
- residue-field finiteness follows the local Chapter 29 surface using `f.residueFieldMap t` and
  `Module.Finite`.
-/

/-- Lemma 29.16.8: for a scheme `S`, the following are equivalent: `S` is Jacobson; the finite
type points of `S` are exactly its closed points; every locally finite type morphism to `S` sends
closed points to closed points; and, in that situation, the induced residue-field extension at a
closed point is finite. -/
@[stacks 01TB]
theorem jacobsonSpace_tfae_finiteTypePoints_closedPoints_locallyOfFiniteType
    (S : Scheme.{u}) :
    List.TFAE
      [ JacobsonSpace S
      , finiteTypePoints S = closedPoints S
      , ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f],
          f '' closedPoints T ⊆ closedPoints S
      , ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f], ∀ t : T,
          t ∈ closedPoints T →
            f t ∈ closedPoints S ∧
              let _ : Algebra (S.residueField (f t)) (T.residueField t) :=
                (f.residueFieldMap t).hom.toAlgebra
              Module.Finite (S.residueField (f t)) (T.residueField t)
      ] := sorry

end AlgebraicGeometry
