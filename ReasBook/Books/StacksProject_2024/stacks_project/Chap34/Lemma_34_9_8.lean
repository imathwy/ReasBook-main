import Mathlib
import StacksProject_2024.stacks_project.Chap34.Definition_34_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the general scheme-cover and isomorphism-cover
-- API; local Chapter 34 precedent fixes the fpqc owner at `IsFpqcCovering` on indexed families
-- `ι → Over T`, so the three source clauses are stated directly on that owner.

variable {T T' : Scheme.{u}} {ι : Type v} {κ : ι → Type w}

/-- Lemma 34.9.8 (1): if `f : T' ⟶ T` is an isomorphism, then the singleton family `{T' ⟶ T}` is
an fpqc covering of `T`. -/
@[stacks 022D]
theorem isFpqcCovering_singleton_of_isIso (f : T' ⟶ T) [IsIso f] :
    IsFpqcCovering (fun _ : Unit ↦ Over.mk f) := sorry

/-- Lemma 34.9.8 (2): if `X : ι → Over T` is an fpqc covering of `T` and for each `i` the family
`Y i : κ i → Over (X i).left` is an fpqc covering of `X i`, then the composite family
`{Y i j ⟶ X i ⟶ T}` is an fpqc covering of `T`. -/
@[stacks 022D]
theorem IsFpqcCovering.comp (X : ι → Over T) (Y : (i : ι) → κ i → Over (X i).left)
    (hX : IsFpqcCovering X) (hY : ∀ i : ι, IsFpqcCovering (Y i)) :
    IsFpqcCovering (fun p : Sigma κ ↦ Over.mk ((Y p.1 p.2).hom ≫ (X p.1).hom)) := sorry

/-- Lemma 34.9.8 (3): if `X : ι → Over T` is an fpqc covering of `T` and `f : T' ⟶ T` is a
morphism of schemes, then the pullback family `{T' ×[T] X i ⟶ T'}` is an fpqc covering of `T'`. -/
@[stacks 022D]
theorem IsFpqcCovering.pullback (X : ι → Over T) (hX : IsFpqcCovering X) (f : T' ⟶ T) :
    IsFpqcCovering (fun i : ι ↦ Over.mk (pullback.snd (X i).hom f)) := sorry

end AlgebraicGeometry
