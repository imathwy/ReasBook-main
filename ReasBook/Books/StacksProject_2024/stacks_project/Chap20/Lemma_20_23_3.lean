import StacksProject_2024.stacks_project.Chap20.Lemma_20_23_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

/- Domain-style sampling for Lemma 20.23.3:
- primary domain: ordered and alternating Čech cochain complexes for a linearly ordered cover.
- sampled owner declarations:
  `orderedCechComplex`,
  `alternatingCechComplex`,
  `orderedCechComparison`,
  `alternatingCechProjection`,
  `alternatingCechProjection_comp_orderedCechComparison`.
- best owner abstraction: the complex morphism `orderedCechComparison : orderedCechComplex 𝒰 F ⟶
  alternatingCechComplex 𝒰 F` from `Lemma_20_23_4`; the isomorphism statement here is derived API,
  not a second owner.
- primitive data: the cover `𝒰` and presheaf `F`.
- derived API: the source-facing `IsIso` theorem for the ordered-to-alternating comparison.

Source/core/bridge triage:
- `source-facing`: Lemma 20.23.3, asserting that the ordered-to-alternating comparison is an
  isomorphism.
- `core/canonical`: `orderedCechComparison` and `alternatingCechProjection` from
  `Lemma_20_23_4`.
- `bridge/view`: this file only derives the `IsIso` statement from that owner-level comparison and
  its canonical inverse. -/

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

/-- Lemma 20.23.3: for a linearly ordered index set, the canonical comparison from the ordered
Čech complex of a cover to the alternating Čech complex is an isomorphism of cochain complexes. -/
@[stacks 01FJ]
instance orderedCechComparison_isIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    IsIso (orderedCechComparison 𝒰 F) := by
  exact ⟨⟨alternatingCechProjection 𝒰 F,
    orderedCechComparison_comp_alternatingCechProjection 𝒰 F,
    alternatingCechProjection_comp_orderedCechComparison 𝒰 F⟩⟩

/-- The inverse of the canonical isomorphism attached to `orderedCechComparison 𝒰 F` is the
projection back to the ordered Čech complex. -/
@[simp] theorem asIso_orderedCechComparison_inv (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (asIso (orderedCechComparison 𝒰 F)).inv = alternatingCechProjection 𝒰 F := by
  apply IsIso.inv_eq_of_hom_inv_id
  simpa using orderedCechComparison_comp_alternatingCechProjection 𝒰 F
