import Mathlib.Algebra.Homology.HomotopyCategory
import StacksProject_2024.Chap20.«20_23_6_2»
import StacksProject_2024.Chap20.Lemma_20_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

/- Domain-style sampling for Lemma 20.23.6:
- primary domain: homotopy comparison between the ordinary and alternating Čech complexes of a
  linearly ordered cover;
- sampled owner declarations:
  `cechProjectionToOrderedCech`,
  `orderedCechComparison`,
  `alternatingCechInclusion`,
  `HomotopyEquiv`,
  `HomologicalComplex.homotopyEquivalences`,
  `homotopic`;
- best owner abstraction: the core data already live on the chapter owners
  `cechProjectionToOrderedCech`, `orderedCechComparison`, and `alternatingCechInclusion`; this file
  should state the source-facing homotopy and homotopy-equivalence consequences directly on those
  owners, using `HomotopyEquiv` only inside the proof of the morphism-property theorem rather than
  exporting a separate chosen witness datum.

Source/core/bridge triage:
- `source-facing`: the two statements of Lemma 20.23.6;
- `core/canonical`: the Chapter 20 Čech comparison maps and the homological-complex owners
  `homotopic` and `HomologicalComplex.homotopyEquivalences`;
- `bridge/view`: the ordinary-to-alternating composite
  `cechProjectionToOrderedCech 𝒰 F ≫ orderedCechComparison 𝒰 F`. -/

-- Proof sketch: use the explicit first homotopy from `20.23.6.1` to pass from the identity of
-- the ordinary Čech complex to the semi-alternating projector, identify the semi-alternating
-- complex with the semi-ordered complex, and then apply the second explicit homotopy `20.23.6.2`
-- to deform further to the ordered projector. Transporting that homotopy across the canonical
-- comparison `orderedCechComparison 𝒰 F` yields the displayed composite with
-- `alternatingCechInclusion 𝒰 F`.
/-- Lemma 20.23.6 (1): the composite of the projection from ordinary to ordered Čech cochains with
the comparison to alternating cochains, followed by the inclusion of the alternating Čech complex
into the ordinary Čech complex, is homotopic to the identity on the ordinary Čech complex. -/
@[stacks 01FM]
theorem cechProjectionToOrderedCech_comp_orderedCechComparison_comp_alternatingCechInclusion_homotopic_id
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    homotopic AddCommGrpCat.{max u v} (ComplexShape.up ℕ)
      (cechProjectionToOrderedCech 𝒰 F ≫
        orderedCechComparison 𝒰 F ≫ alternatingCechInclusion 𝒰 F)
      (𝟙 ((cechComplexFunctor 𝒰).obj F)) := sorry

-- Proof sketch: use the composite `π ≫ c` as the candidate homotopy inverse to the inclusion.
-- The previous theorem provides the homotopy from the composite on the ordinary Čech complex to
-- the identity, while Lemma `20.23.3` gives the canonical isomorphism
-- `orderedCechComparison 𝒰 F : orderedCechComplex 𝒰 F ⟶ alternatingCechComplex 𝒰 F`, so the
-- ordered-side inverse can be taken to be `alternatingCechProjection 𝒰 F`.
/-- Lemma 20.23.6 (2): the inclusion
`alternatingCechInclusion 𝒰 F : alternatingCechComplex 𝒰 F ⟶ (cechComplexFunctor 𝒰).obj F`
is a homotopy equivalence of cochain complexes. -/
@[stacks 01FM]
theorem alternatingCechInclusion_isHomotopyEquivalence
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ)
      (alternatingCechInclusion 𝒰 F) := by
  refine ⟨{
    hom := alternatingCechInclusion 𝒰 F
    inv := cechProjectionToOrderedCech 𝒰 F ≫ orderedCechComparison 𝒰 F
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_
  }, rfl⟩
  · simpa [alternatingCechProjection, Category.assoc] using
      Homotopy.ofEq (alternatingCechProjection_comp_orderedCechComparison 𝒰 F)
  · simpa [Category.assoc] using
      Classical.choice
        (cechProjectionToOrderedCech_comp_orderedCechComparison_comp_alternatingCechInclusion_homotopic_id 𝒰 F)
