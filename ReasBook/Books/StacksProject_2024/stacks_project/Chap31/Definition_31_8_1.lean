import Mathlib.AlgebraicGeometry.Fiber
import StacksProject_2024.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

-- Semantic recall: the relative weak assassin is built from the canonical scheme-theoretic fiber
-- `Scheme.Hom.fiber f s`, its inclusion `Scheme.Hom.fiberι f s`, pullback of modules along that
-- inclusion, and the Chapter 31 owner `Scheme.Modules.weakAss` for weakly associated points.

/-- Definition 31.8.1: for a morphism of schemes `f : X ⟶ S` and a quasi-coherent
`\mathcal O_X`-module `\mathcal F`, the relative weak assassin `WeakAss_{X/S}(\mathcal F)`
consists of those points of `X` coming from a weakly associated point of the restriction of
`\mathcal F` to some scheme-theoretic fiber `X_s`; equivalently, it is the union over all
`s ∈ S` of the weak assassins of the fiber restrictions `\mathcal F_s`, viewed in `X` via the
canonical fiber inclusions. -/
@[stacks 05AV]
def relativeWeakAss (f : X ⟶ S) (ℱ : X.Modules) : Set X :=
  {x : X | ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
    y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).weakAss ∧
      CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x}

/-- The relative weak assassin is the union of the weak assassins on the scheme-theoretic fibers,
viewed inside `X` via the canonical fiber inclusions. -/
theorem relativeWeakAss_eq_iUnion_image (f : X ⟶ S) (ℱ : X.Modules) :
    relativeWeakAss f ℱ =
      ⋃ s : S,
        Set.image
          (CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base)
          (((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).weakAss) := by
  ext x
  constructor
  · rintro ⟨s, y, hy, rfl⟩
    exact Set.mem_iUnion.2 ⟨s, y, hy, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hs⟩
    rcases hs with ⟨y, hy, rfl⟩
    exact ⟨s, y, hy, rfl⟩

/-- A point of `X` lies in the relative weak assassin exactly when it comes from a weakly
associated point of the restriction of `\mathcal F` to some scheme-theoretic fiber of `f`. -/
theorem mem_relativeWeakAss_iff (f : X ⟶ S) (ℱ : X.Modules) (x : X) :
    x ∈ relativeWeakAss f ℱ ↔
      ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
        y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).weakAss ∧
          CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x := by
  rfl

end AlgebraicGeometry.Scheme.Modules
