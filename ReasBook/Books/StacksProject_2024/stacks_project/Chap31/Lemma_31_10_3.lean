import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_29_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical smoothness owner `IsSmooth` and
-- `IsSmoothOfRelativeDimension`; local Chapter 29/31 precedent fixes the pointwise smooth locus as
-- `f.smoothLocus`, fixed fibre dimension as `Scheme.Hom.RelativeDimension`, and the closed
-- Fitting locus as `(Scheme.fittingIdealSheaf (Ω[f.toShHom]) d).support`.

/-- Lemma 31.10.3: let `f : X ⟶ S` be flat and locally of finite presentation, and suppose every
nonempty fibre of `f` is equidimensional of dimension `d`, formalized by
`Scheme.Hom.RelativeDimension f d`. Then the closed subscheme cut out by the `d`th Fitting ideal
of `Ω_{X/S}` has underlying set exactly the points where `f` is not smooth. -/
@[stacks 0C3K]
theorem fittingIdealSheaf_differentials_support_eq_nonsmoothLocus
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) [Flat f] [LocallyOfFinitePresentation f]
    [Scheme.Hom.RelativeDimension f d] :
    ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) d).support : Set X) =
      {x : X | x ∉ f.smoothLocus} := sorry

end AlgebraicGeometry
