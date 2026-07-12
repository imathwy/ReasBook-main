import Mathlib.AlgebraicGeometry.Morphisms.Flat

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.affineOpenCover`, `Flat`, and
-- `IsAffineOpen`; the owner here stays the explicit fixed-target family `ι → Over T`, matching the
-- source's indexed family of morphisms without introducing an extra wrapper object.

section

variable {T : Scheme.{u}} {ι : Type v} (X : ι → Over T)

/-- The finite affine-refinement condition for an indexed family of morphisms to `T`: every affine
open of `T` is the union of the images of finitely many affine opens drawn from members of the
family. -/
def HasAffineRefinement : Prop :=
  ∀ U : T.Opens, IsAffineOpen U →
    ∃ n : ℕ,
      ∃ a : Fin n → ι,
        ∃ V : (j : Fin n) → ((X (a j)).left).Opens,
          (∀ j : Fin n, IsAffineOpen (V j)) ∧
            (⋃ j : Fin n, (X (a j)).hom.base '' (V j : Set (X (a j)).left.carrier)) =
              (U : Set T.carrier)

/-- Definition 34.9.1: an fpqc covering of a scheme `T` is a family of morphisms to `T` whose
members are flat and whose images admit finite affine refinements over every affine open of `T`. -/
@[stacks 022B]
class IsFpqcCovering : Prop where
  /-- Each member of an fpqc covering is a flat morphism of schemes. -/
  flat (i : ι) : Flat (X i).hom
  /-- Over every affine open of the target, finitely many affine opens in members of the family
  cover that affine open by images. -/
  affine_refinement : HasAffineRefinement X

/-- Every member of an fpqc covering is flat. -/
instance instFlatHomOfIsFpqcCovering [hX : IsFpqcCovering X] (i : ι) :
    Flat (X i).hom :=
  hX.flat i

/-- Source-facing specification for Definition 34.9.1: an fpqc covering consists of flat morphisms
and the finite affine refinement condition over each affine open of the target. -/
theorem IsFpqcCovering.source_spec [hX : IsFpqcCovering X] :
    (∀ i : ι, Flat (X i).hom) ∧
      HasAffineRefinement X := by
  exact ⟨hX.flat, hX.affine_refinement⟩

/-- An fpqc covering admits the finite affine refinement required by the definition over each
affine open of the target. -/
theorem IsFpqcCovering.exists_affine_refinement [hX : IsFpqcCovering X]
    (U : T.Opens) (hU : IsAffineOpen U) :
    ∃ n : ℕ,
      ∃ a : Fin n → ι,
        ∃ V : (j : Fin n) → ((X (a j)).left).Opens,
          (∀ j : Fin n, IsAffineOpen (V j)) ∧
            (⋃ j : Fin n, (X (a j)).hom.base '' (V j : Set (X (a j)).left.carrier)) =
              (U : Set T.carrier) :=
  hX.affine_refinement U hU

end

end AlgebraicGeometry
