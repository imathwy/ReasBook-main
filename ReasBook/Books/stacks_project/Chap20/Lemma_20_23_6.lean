import Mathlib
import stacks_project.Chap20.Lemma_20_23_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/-- The morphism from the ordinary Čech complex to the alternating Čech complex obtained by first
projecting to ordered cochains and then extending by the signed comparison map. -/
abbrev cechProjectionToAlternating (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (cechComplexFunctor 𝒰).obj F ⟶ alternatingCechComplex 𝒰 F :=
  cechProjectionToOrderedCech 𝒰 F ≫ orderedCechComparison 𝒰 F

-- Proof sketch: use the explicit first homotopy from 20.23.6.1 to pass from the identity of the
-- ordinary Čech complex to the semi-alternating projector, identify the semi-alternating complex
-- with the semi-ordered complex, and then apply the second explicit homotopy 20.23.6.2 to deform
-- further to the ordered projector. Transporting along the comparison map from ordered to
-- alternating cochains yields the displayed composite with the alternating inclusion.
/-- Lemma 20.23.6 (1): the composite of the projection from ordinary to ordered Čech cochains with
the comparison to alternating cochains, followed by the inclusion of the alternating Čech complex
into the ordinary Čech complex, is homotopic to the identity on the ordinary Čech complex. -/
theorem cechProjectionToAlternating_comp_alternatingCechInclusion_homotopic_id
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    Nonempty
      (Homotopy
        (cechProjectionToAlternating 𝒰 F ≫ alternatingCechInclusion 𝒰 F)
        (𝟙 ((cechComplexFunctor 𝒰).obj F))) := sorry

-- Proof sketch: use `cechProjectionToAlternating` as the candidate homotopy inverse to the
-- inclusion. The previous theorem provides a homotopy from the composite on the ordinary Čech
-- complex to the identity, while Lemma 20.23.4 identifies the alternating complex with the ordered
-- complex and gives the identity on the alternating side after projecting back to ordered
-- cochains.
/-- Lemma 20.23.6 (2): the inclusion
`\check{\mathcal C}_{alt}^\bullet(\mathcal U,\mathcal F) \to
\check{\mathcal C}^\bullet(\mathcal U,\mathcal F)` is a homotopy equivalence of cochain
complexes. -/
theorem alternatingCechInclusion_isHomotopyEquivalence
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ))
      (alternatingCechInclusion 𝒰 F) := sorry
