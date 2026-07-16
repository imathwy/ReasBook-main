import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `QuasiCompact`, `IsClosedImmersion`, and local search found the project owners
-- `Scheme.Hom.FinitePresentation` and `Scheme.Hom.fiberDimensionAt`. Local Chapter 32 precedent
-- states fibre-dimension bounds pointwise by `fiberDimensionAt`, which avoids adding a finite-type
-- hypothesis to the original closed subscheme `Z`.

/-- Lemma 32.18.5: let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be a morphism of finite presentation, and let `d ≥ 0`. If `Z ⊆ X` is a closed
subscheme whose fibres over `S` have dimension at most `d`, then there exists a closed subscheme
`Z' ⊆ X` containing `Z`, such that `Z' ⟶ X` is of finite presentation and all fibres of `Z'`
over `S` have dimension at most `d`. The containment `Z ⊆ Z'` is encoded by the ideal-sheaf
inequality `Z' ≤ Z`. -/
@[stacks 05M6]
theorem exists_finitePresentation_closedSubscheme_containing_of_fiberDimensionLE
    {X S : Scheme.{u}} [CompactSpace S.carrier] [QuasiSeparatedSpace S.carrier]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] (d : ℕ) (Z : X.IdealSheafData)
    (hZdim : ∀ z : Z.subscheme, (Z.subschemeι ≫ f).fiberDimensionAt z ≤ (d : WithBot ℕ∞)) :
    ∃ Z' : X.IdealSheafData,
      ∃ _ : Z' ≤ Z, Scheme.Hom.FinitePresentation Z'.subschemeι ∧
        ∀ z : Z'.subscheme, (Z'.subschemeι ≫ f).fiberDimensionAt z ≤ (d : WithBot ℕ∞) := sorry

end AlgebraicGeometry
