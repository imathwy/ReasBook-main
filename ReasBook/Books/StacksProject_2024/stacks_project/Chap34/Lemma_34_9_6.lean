import StacksProject_2024.Chap34.Definition_34_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the scheme pullback-cover API, but the local Chapter
-- 34 owner remains `IsFpqcCovering` on indexed families `ι → Over T`; the source's base-changed
-- family over `Y j` is therefore expressed directly by `pullback.fst (Y j).hom (X i).hom`.

variable {T : Scheme.{u}} {ι : Type v}

/-- Lemma 34.9.6: let `T` be a scheme and let `X : ι → Over T` be a family of morphisms to `T`.
Assume each member of `X` is flat, and there exists an fpqc covering `Y` of `T` such that for
every member `Y j`, the base-changed family `Y j ×[T] X i ⟶ Y j` is an fpqc covering of `Y j`.
Then `X` is an fpqc covering of `T`. -/
@[stacks 03L9]
theorem isFpqcCovering_of_flat_of_exists_fpqcCovering_pullbacks
    (X : ι → Over T) (hflat : ∀ i : ι, Flat (X i).hom)
    (hpullback :
      ∃ (κ : Type w) (Y : κ → Over T),
        IsFpqcCovering Y ∧
          ∀ j : κ,
            IsFpqcCovering
              (fun i : ι ↦ Over.mk (pullback.fst (Y j).hom (X i).hom))) :
    IsFpqcCovering X := sorry

end AlgebraicGeometry
