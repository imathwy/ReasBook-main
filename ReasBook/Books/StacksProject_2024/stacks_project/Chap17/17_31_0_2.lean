import Mathlib
import StacksProject_2024.Chap17.«17_31_0_1»

open CategoryTheory Limits TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (X.Sheaf CommRingCat.{u})]
variable (𝒜 : X.Sheaf CommRingCat.{u}) (𝒝 : Under 𝒜)

/- Domain-style sampling:
- primary domain: the conormal exact sequence for the canonical presentation of a sheaf of
  `\mathcal A`-algebras `\mathcal B`;
- sampled owner declarations:
  `presentationSheaf`,
  `presentationBase`,
  `presentationMap`,
  `Under.costarAdjForget`,
  `SheafOfModules.RingedSite.conormalSource`,
  `SheafOfModules.RingedSite.conormalTensorTerm`,
  `SheafOfModules.RingedSite.conormalMap`,
  `SheafOfModules.RingedSite.conormalToDifferentials`,
  `conormalSequence_exact_of_sectionwiseSurjective`;
- best owner abstraction: the owner is the general sheaf-level conormal sequence of
  `SheafOfModules.RingedSite`, specialized here through Lemma `17.28.9` to the canonical
  polynomial presentation
  `\mathcal A[\mathcal B] \to \mathcal B`;
- primitive data: the canonical presentation sheaf `\mathcal A[\mathcal B]`, its structure map
  `\mathcal A → \mathcal A[\mathcal B]`, and the evaluation map
  `\mathcal A[\mathcal B] \to \mathcal B`;
- derived API: sectionwise surjectivity of the counit and the specialized exactness statement.
  The exactness owner itself remains the site-level theorem
  `SheafOfModules.RingedSite.conormalSequence_exact_of_sectionwiseSurjective`.

Source/core/bridge triage:
- `source-facing`: Equation `17.31.0.2`, namely the conormal sequence of the canonical
  presentation of `\mathcal B` over `\mathcal A`;
- `core/canonical`: the generic-site owner
  `SheafOfModules.RingedSite.conormalSource`,
  `SheafOfModules.RingedSite.conormalTensorTerm`,
  `SheafOfModules.RingedSite.conormalMap`,
  `SheafOfModules.RingedSite.conormalToDifferentials`,
  specialized to the opens site of `X`;
- `bridge/view`: this file is only the specialization of that owner to the canonical presentation,
  so it should not maintain a parallel presentation-level module-sheaf API. -/

-- Proof sketch: a local section `b ∈ \mathcal B(U)` is already one of the generators of the
-- polynomial presentation `\mathcal A[\mathcal B](U)`, and the evaluation map sends `[b]` to `b`.
omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The canonical presentation morphism `\mathcal A[\mathcal B] \to \mathcal B` is sectionwise
surjective. -/
theorem presentationMap_isSectionwiseSurjective
    (U : (Opens X)ᵒᵖ) :
    Function.Surjective (((presentationMap 𝒜 𝒝).hom.app U).hom) := by
  intro b
  refine ⟨
    ((((Under.costarAdjForget 𝒜).unit.app
        (presentationFreeSheaf (presentationVariables 𝒝))).hom.app U).hom
      (((CategoryTheory.Sheaf.adjunction
          (Opens.grothendieckTopology X) CommRingCat.adj).unit.app
          (presentationVariables 𝒝)).hom.app U b)),
    ?_⟩
  simpa using congrFun
    (congrArg
      (fun η : presentationVariables 𝒝 ⟶ presentationVariables 𝒝 ↦
        η.hom.app U)
      (SheafOfModules.RingedSite.presentationMap_on_brackets
        (J := Opens.grothendieckTopology X) 𝒜 𝒝))
    b

-- Proof sketch: specialize the sheaf-level conormal exact sequence of Lemma `17.28.9` to the
-- canonical presentation map `presentationMap 𝒜 𝒝`, using its sectionwise surjectivity.
omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/- Equation 17.31.0.2: the conormal sequence of the canonical presentation
`\mathcal A[\mathcal B] \to \mathcal B` is exactly the Chapter 18 owner theorem
`SheafOfModules.RingedSite.conormalSequence_exact_of_sectionwiseSurjective`, specialized to
`presentationBase 𝒜 𝒝` and `presentationMap 𝒜 𝒝`. -/
#check SheafOfModules.RingedSite.conormalSequence_exact_of_sectionwiseSurjective
  (presentationBase 𝒜 𝒝)
  (presentationMap 𝒜 𝒝)
  (presentationMap_isSectionwiseSurjective 𝒜 𝒝)

end TopCat.Sheaf
