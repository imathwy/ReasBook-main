import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_11
import StacksProject_2024.stacks_project.Chap13.Definition_13_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
variable [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
variable [Abelian 𝒜] [Abelian ℬ] [Abelian 𝒞]
variable [HasDerivedCategory.{w} 𝒜]
variable [HasDerivedCategory.{w} ℬ] [HasDerivedCategory.{w} 𝒞]
variable [HasInjectiveResolutions ℬ]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable [LocallySmall 𝒞] [WellPowered 𝒞] [HasWidePullbacks 𝒞] [HasCoproducts 𝒞]
variable [InitialMonoClass 𝒞]
variable (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞)
variable [F.Additive] [G.Additive]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow (F ⋙ G))
  (boundedBelowHomotopyQuasiIso 𝒜)]

/- Domain-style sampling:
- primary domain: Grothendieck spectral sequences arising from compositions of bounded-below
  right derived functors between abelian categories;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `Functor.rightDerived`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.cohomologyFiltrationIsFinite`,
  `FilteredComplex.convergesToCohomology`,
  `CohomologicalSpectralSequence.IsBounded`;
- best owner abstraction: the canonical bounded-below total right derived functors on `D⁺`
  together with the Chapter 13 bounded-below right-acyclicity owner on injective images and the
  Chapter 12 owners for associated filtered complexes and convergence;
- primitive data: the additive functors `F`, `G`, the bounded-below derived object `X`, and the
  owner-level acyclicity hypothesis that injective images under `F` are bounded-below right
  `G`-acyclic;
- derived API: the source-facing Grothendieck spectral sequence, its `E₂`-page identification,
  its abutment comparison, boundedness, the finite abutment-filtration owner, and the remaining
  convergence package;
- source/core/bridge triage:
  `source-facing`: `exists_grothendieckSpectralSequence`;
  `core/canonical`: `Functor.totalRightDerived`, `Functor.rightDerived`,
    `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
    `IsAssociatedToFilteredComplex`, `FilteredComplex.cohomologyFiltrationIsFinite`,
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the page-two and abutment isomorphisms expressing the canonical owners in the
    textbook `R^p G(H^q(RF(X)))` and `H^n(R(G ∘ F)(X))` forms, plus the higher-derived-vanishing
    characterization of bounded-below right acyclicity from Lemma `13.16.4`.

The local bounded-below derived-functor wrappers are therefore duplicate wheels: the theorem
should use `Functor.totalRightDerived` directly, keeping only notation-level shortening. -/

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "plusιB" => ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
local notation "plusιC" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒞)))
local notation "HB" => DerivedCategory.homologyFunctor ℬ
local notation "HC" => DerivedCategory.homologyFunctor 𝒞
local notation "RF" => Functor.totalRightDerived
  (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Qplus
  (boundedBelowHomotopyQuasiIso 𝒜)
local notation "RGF" => Functor.totalRightDerived
  (mapBoundedBelowHomotopyCategoryToDerivedBelow (F ⋙ G)) Qplus
  (boundedBelowHomotopyQuasiIso 𝒜)

-- Proof sketch: choose a bounded-below representative of `X`, replace it by an injective
-- resolution, and apply `F` termwise. The hypothesis that injective objects of `𝒜` are sent to
-- `G`-acyclic objects makes the second Cartan-Eilenberg spectral sequence for `G(F(I^{\bullet}))`
-- identify its `E₂`-page with `R^pG(H^q(RF(X)))`. The Cartan-Eilenberg construction gives
-- boundedness and convergence, and the comparison of derived functors identifies the abutment
-- with `H^*(R(G \circ F)(X))`.
/-- Lemma 13.22.2 (Grothendieck spectral sequence): assume that every injective object of
`\mathcal A` is sent by `F` to an object that is right acyclic for `G`. Then for every object `X`
of `D^+(\mathcal A)` there is a cohomological spectral sequence
whose `E_2`-page is `R^pG(H^q(RF(X)))`, which is bounded, converges to
`H^*(R(G \circ F)(X))`, and whose convergence package records the finite filtration on each
abutment cohomology object through the separate owner
`FilteredComplex.cohomologyFiltrationIsFinite`. -/
theorem exists_grothendieckSpectralSequence
    (hAcyclic :
      ∀ (I : 𝒜) [Injective I],
        IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I))
    (X : D⁺(𝒜)) :
    ∃ (filteredComplex : FilteredComplex 𝒞)
      (spectralSequence : CohomologicalSpectralSequence 𝒞 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso : ∀ p : ℕ, ∀ q : ℤ,
        (spectralSequence.page 2).X (Int.ofNat p, q) ≅
          (G.rightDerived p).obj
            ((plusιB ⋙ HB q).obj ((RF).obj X)))
      (abutmentIso : ∀ n : ℤ,
        filteredComplex.underlying.homology n ≅
          ((plusιC ⋙ HC n).obj ((RGF).obj X))),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

end

end CategoryTheory
