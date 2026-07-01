import Mathlib
import stacks_project.Chap20.Lemma_20_23_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u v

/- Domain-style sampling for Lemma 20.23.3:
- primary domain: ordered and alternating Čech cochain complexes for a linearly ordered cover.
- sampled owner declarations:
  `orderedCechComplex`,
  `alternatingCechComplex`,
  `orderedCechComparison`,
  `alternatingCechProjection`.
- best owner abstraction: the complex morphism `orderedCechComparison : orderedCechComplex 𝒰 F ⟶
  alternatingCechComplex 𝒰 F` from `Lemma_20_23_4`; the isomorphism statement here is derived API,
  not a second owner.
- primitive data: the cover `𝒰` and presheaf `F`.
- derived API: the projection `alternatingCechProjection`, its isomorphism
  `alternatingCechProjection_isIso`, and the left-inverse identity
  `orderedCechComparison_comp_alternatingCechProjection`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.23.3, asserting that the ordered-to-alternating comparison is an
  isomorphism.
- `core/canonical`: `orderedCechComparison` and `alternatingCechProjection` from
  `Lemma_20_23_4`.
- `bridge/view`: this file only derives the `IsIso` statement from that owner-level comparison and
  its canonical inverse. -/

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

-- Proof sketch: `Lemma 20.23.4` constructs the projection from alternating to ordered Čech
-- cochains and proves it is an isomorphism; the comparison `c` is its inverse because their
-- composite is the identity on the ordered complex.
/-- Lemma 20.23.3: for a linearly ordered index set, the canonical comparison from the ordered
Čech complex of a cover to the alternating Čech complex is an isomorphism of cochain complexes. -/
theorem orderedCechComparison_isIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    IsIso (orderedCechComparison 𝒰 F) := by
  exact CategoryTheory.isIso_of_comp_hom_eq_id (alternatingCechProjection 𝒰 F)
    (orderedCechComparison_comp_alternatingCechProjection 𝒰 F)
