import StacksProject_2024.stacks_project.Chap34.Definition_34_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical fixed-target family owner
-- `SemiRepresentableFamily.Over` and its refinement relation, while local Chapter 34 precedent
-- fixes the fpqc owner at `IsFpqcCovering` on indexed families `ι → Over T`.
--
-- Source/core/bridge triage:
-- * `source-facing`: the Stacks lemma that a flat family is fpqc once some fpqc covering refines
--   it;
-- * `core/canonical`: the Chapter 7 refinement relation `Refines` on
--   `SemiRepresentableFamily.Over T`;
-- * `bridge/view`: the raw indexed family `X : ι → Over T`, viewed canonically via `ofArrows`.
--
-- The refine-stage API repair here keeps the main Stacks-tagged lemma at the source-facing
-- indexed-family layer, while using the canonical fixed-target family owner internally.

variable {T : Scheme.{u}} {ι : Type v}

/-- Canonical fixed-target-family form of Lemma 34.9.5: if the indexed family `X` is pointwise
flat and some fpqc covering family in `SemiRepresentableFamily.Over T` refines the family induced
by `X`, then `X` is an fpqc covering of `T`. -/
theorem isFpqcCovering_of_flat_of_exists_fpqcRefiningOverFamily
    (X : ι → Over T) (hflat : ∀ i : ι, Flat (X i).hom)
    (hrefines :
      ∃ 𝒴 : SemiRepresentableFamily.Over T,
        IsFpqcCovering 𝒴.obj ∧
          Refines 𝒴 (ofArrows (fun i ↦ (X i).left) fun i ↦ (X i).hom)) :
    IsFpqcCovering X := sorry

/-- Lemma 34.9.5: if each member of a family of morphisms to `T` is flat and the family admits a
refinement by an fpqc covering of `T`, then the original family is an fpqc covering of `T`. -/
@[stacks 03L8]
theorem isFpqcCovering_of_flat_of_exists_fpqcRefinement
    (X : ι → Over T) (hflat : ∀ i : ι, Flat (X i).hom)
    (hrefines :
      ∃ (κ : Type w) (Y : κ → Over T),
        IsFpqcCovering Y ∧
          Refines
            (ofArrows (fun j ↦ (Y j).left) fun j ↦ (Y j).hom)
            (ofArrows (fun i ↦ (X i).left) fun i ↦ (X i).hom)) :
    IsFpqcCovering X := by
  rcases hrefines with ⟨κ, Y, hY, hrefinesY⟩
  exact
    isFpqcCovering_of_flat_of_exists_fpqcRefiningOverFamily X hflat
      ⟨ofArrows (fun j ↦ (Y j).left) fun j ↦ (Y j).hom, hY, hrefinesY⟩

end AlgebraicGeometry
