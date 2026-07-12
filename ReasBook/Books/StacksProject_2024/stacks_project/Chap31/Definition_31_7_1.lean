import Mathlib.AlgebraicGeometry.Fiber
import StacksProject_2024.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

-- Semantic recall: the relative assassin is built from the scheme-theoretic fibers
-- `Scheme.Hom.fiber f s`, their canonical inclusions `Scheme.Hom.fiberι f s`, and the stalkwise
-- associated-point owner on the pulled-back module over each fiber.

-- Semantic recall: the source only uses quasi-coherent modules, but the fiberwise associated-point
-- construction makes sense for every `\mathcal O_X`-module, so the source-facing quasi-coherent
-- case is exposed through the more reusable owner below.

/-- Definition 31.7.1: for a morphism of schemes `f : X ⟶ S` and a quasi-coherent
`\mathcal O_X`-module `ℱ`, the relative assassin `Ass_{X/S}(ℱ)` is the union over all `s ∈ S` of
the assassins of the fiber restrictions `ℱ_s` on the scheme-theoretic fibers `X_s`, viewed as
subsets of `X` via the canonical fiber inclusions. -/
@[stacks 05AT]
def relativeAssassin (f : X ⟶ S) (ℱ : X.Modules) : Set X :=
  {x : X | ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
    y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).associatedPoints ∧
      CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x}

/-- The relative assassin is the union of the associated-point loci on the scheme-theoretic
fibers, viewed inside `X` via the canonical fiber inclusions. -/
theorem relativeAssassin_eq_iUnion_image (f : X ⟶ S) (ℱ : X.Modules) :
    relativeAssassin f ℱ =
      ⋃ s : S,
        Set.image
          (CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base)
          (((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).associatedPoints) := by
  ext x
  constructor
  · rintro ⟨s, y, hy, rfl⟩
    exact Set.mem_iUnion.2 ⟨s, y, hy, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hs⟩
    rcases hs with ⟨y, hy, rfl⟩
    exact ⟨s, y, hy, rfl⟩

/-- A point of `X` lies in the relative assassin exactly when it comes from an associated point of
the restriction of `ℱ` to some scheme-theoretic fiber of `f`. -/
theorem mem_relativeAssassin_iff (f : X ⟶ S) (ℱ : X.Modules) (x : X) :
    x ∈ relativeAssassin f ℱ ↔
      ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
        y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).associatedPoints ∧
          CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x := by
  rfl

end AlgebraicGeometry.Scheme.Modules
