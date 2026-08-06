import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_1

open CategoryTheory

universe u

-- Semantic recall via `lean_leansearch` and repository precedent: the later Adams-operation file
-- uses the same source-facing pullback-on-bundle-classes witness, but this item keeps the
-- witness local rather than importing later Chapter 24 material only to reuse that helper.

section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A function `K(X) → K(Y)` is the canonical pullback on `complexKTheory` induced by
`f : Y ⟶ X` when it agrees with pullback on honest bundle classes. -/
def IsComplexKTheoryPresentationPullback
    (f : TopCat.of Y ⟶ TopCat.of X)
    (fStar : complexKTheory X → complexKTheory Y) : Prop :=
  ∃ pullbackBundle : ComplexVectorBundle.Presentation X → ComplexVectorBundle.Presentation Y,
    (∀ V : ComplexVectorBundle.Presentation X,
      (pullbackBundle V).bundle = f *ᵖ V.bundle) ∧
    ∀ V : ComplexVectorBundle.Presentation X,
      fStar (ComplexVectorBundle.toVirtualPresentation V) =
        ComplexVectorBundle.toVirtualPresentation (pullbackBundle V)

namespace IsComplexKTheoryPresentationPullback

theorem spec
    {f : TopCat.of Y ⟶ TopCat.of X}
    {fStar : complexKTheory X → complexKTheory Y}
    (hfStar : IsComplexKTheoryPresentationPullback f fStar) :
    ∃ pullbackBundle : ComplexVectorBundle.Presentation X → ComplexVectorBundle.Presentation Y,
      (∀ V : ComplexVectorBundle.Presentation X,
        (pullbackBundle V).bundle = f *ᵖ V.bundle) ∧
      ∀ V : ComplexVectorBundle.Presentation X,
        fStar (ComplexVectorBundle.toVirtualPresentation V) =
          ComplexVectorBundle.toVirtualPresentation (pullbackBundle V) :=
  hfStar

/-- A presentation-level pullback sends each honest bundle class on `X` to the class of a bundle
over `Y` whose underlying family is the actual pullback along `f`. -/
theorem toVirtualPresentation
    {f : TopCat.of Y ⟶ TopCat.of X}
    {fStar : complexKTheory X → complexKTheory Y}
    (hfStar : IsComplexKTheoryPresentationPullback f fStar)
    (V : ComplexVectorBundle.Presentation X) :
    ∃ W : ComplexVectorBundle.Presentation Y,
      W.bundle = f *ᵖ V.bundle ∧
      fStar (ComplexVectorBundle.toVirtualPresentation V) =
        ComplexVectorBundle.toVirtualPresentation W := by
  rcases hfStar with ⟨pullbackBundle, hpullbackBundle, hmap⟩
  exact ⟨pullbackBundle V, hpullbackBundle V, hmap V⟩

end IsComplexKTheoryPresentationPullback

/-- Proposition 24.1.8 (1): the canonical addition on `complexKTheory X` from Definition 24.1.1
is natural with respect to pullback on `K`-theory. -/
theorem complexKTheoryPullback_map_add
    (f : TopCat.of Y ⟶ TopCat.of X)
    (fStar : complexKTheory X → complexKTheory Y)
    (hfStar : IsComplexKTheoryPresentationPullback f fStar)
    (x y : complexKTheory X) :
    fStar (x + y) = fStar x + fStar y := sorry

/-- Proposition 24.1.8 (2): the canonical multiplication on `complexKTheory X` from Definition
24.1.1 is natural with respect to pullback on `K`-theory. -/
theorem complexKTheoryPullback_map_mul
    (f : TopCat.of Y ⟶ TopCat.of X)
    (fStar : complexKTheory X → complexKTheory Y)
    (hfStar : IsComplexKTheoryPresentationPullback f fStar)
    (x y : complexKTheory X) :
    fStar (x * y) = fStar x * fStar y := sorry

end
