import Mathlib
import StacksProject_2024.stacks_project.Chap34.Definition_34_9_10
import StacksProject_2024.stacks_project.Chap34.Lemma_34_9_5
import StacksProject_2024.stacks_project.Chap34.Lemma_34_9_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the general scheme-cover API, but local Chapter 34
-- precedent fixes the fpqc owner at `IsFpqcCovering` on indexed families `ι → Over T`. The
-- source's affine test condition is therefore expressed by `StandardFpqcCover Z` together with a
-- refinement into the pullback family over `Z`.

variable {T : Scheme.{u}} {ι : Type v}

/-- Lemma 34.9.12: let `T` be a scheme and let `X : ι → Over T` be a family of morphisms to `T`.
Assume each member of `X` is flat, and for every affine scheme `Z` and morphism `h : Z ⟶ T` there
exists a standard fpqc covering of `Z` refining the pullback family `X ×[T] Z`. Then `X` is an
fpqc covering of `T`. -/
@[stacks 03LB]
theorem isFpqcCovering_of_flat_of_affine_pullback_standardFpqcRefinements
    (X : ι → Over T) (hflat : ∀ i : ι, Flat (X i).hom)
    (hrefines :
      ∀ ⦃Z : Scheme.{u}⦄ (hZ : IsAffine Z) (h : Z ⟶ T),
        ∃ 𝒰 : StandardFpqcCover Z,
          let 𝒰' : SemiRepresentableFamily.Over Z :=
            ofArrows
              (fun j : ULift.{v} (Fin 𝒰.n) ↦ 𝒰.U j.down)
              (fun j : ULift.{v} (Fin 𝒰.n) ↦ 𝒰.map j.down)
          let 𝒳h : SemiRepresentableFamily.Over Z :=
            ofArrows
              (fun i : ι ↦ pullback h (X i).hom)
              (fun i : ι ↦ pullback.fst h (X i).hom)
          Refines 𝒰' 𝒳h) :
    IsFpqcCovering X := sorry

end AlgebraicGeometry
