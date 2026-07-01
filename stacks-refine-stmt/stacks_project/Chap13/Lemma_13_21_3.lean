import Mathlib
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap12.Lemma_12_25_1
import stacks_project.Chap12.Lemma_12_25_3
import stacks_project.Chap12.Lemma_12_25_4
import stacks_project.Chap13.Definition_13_15_3
import stacks_project.Chap13.Definition_13_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex₂
open CochainComplex
open DerivedCategory.TStructure
open scoped CategoryTheory HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

/- Domain-style sampling:
- primary domain: Cartan-Eilenberg double complexes, their two canonical filtered totals, and the
  associated cohomological spectral sequences together with the bounded-below right-derived
  abutment;
- sampled owner declarations:
  `Functor.mapHomologicalComplex`,
  `firstDoubleComplexFilteredComplex`,
  `secondDoubleComplexFilteredComplex`,
  `Functor.totalRightDerived`;
- best owner abstraction: the functorial image of a double complex is the iterated canonical owner
  `((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj I`, while the two spectral
  sequences are owned by the canonical filtered complexes attached to that double complex, and the
  abutment is owned by the bounded-below right derived functor of
  `mapBoundedBelowHomotopyCategoryToDerivedBelow F`;
- primitive data here: the bounded-below source complex `K`, a Cartan-Eilenberg resolution `CE`
  of `K`, and the resulting mapped double complex;
- derived API here: the two associated spectral sequences, their page identifications,
  boundedness, the two finite abutment-filtration owners, the two convergence packages, together
  with the canonical comparison from `H^*(Tot(F(I^{•,•})))` to the right-derived cohomology of
  `K^•`;
- source/core/bridge triage:
  `source-facing`: the existence statement for the two Cartan-Eilenberg spectral sequences;
  `core/canonical`: the mapped double complex owner from `Functor.mapHomologicalComplex`, the two
    filtered-complex owners, `Functor.totalRightDerived`, and
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the page-one and page-two identifications with the right-derived functors and
    the abutment isomorphism to the bounded-below derived value.

The one-off name for the mapped double complex is therefore a duplicate wheel: the theorem should
use the canonical owner directly, derive the two filtered-complex views from it, and expose the
abutment through the canonical bounded-below right-derived owner rather than an existential
`HasTotal` witness.
-/

section

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
variable [Category.{v₁} 𝒜] [Category.{v₂} 𝒝] [Abelian 𝒜] [Abelian 𝒝]
variable [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒝]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable [LocallySmall 𝒝] [WellPowered 𝒝] [HasWidePullbacks 𝒝] [HasCoproducts 𝒝]
variable [InitialMonoClass 𝒝]

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒝)))

section

variable (F : 𝒜 ⥤ 𝒝) [F.Additive] [PreservesFiniteLimits F] [HasInjectiveResolutions 𝒜]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (K : CochainComplex.Plus 𝒜) (CE : CartanEilenbergResolution K)

local notation "Qhplus" => HomotopyCategory.Plus.quotient 𝒜

-- Proof sketch: let `I` be the canonical functorial image of the Cartan-Eilenberg double complex
-- under `((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ))`. Use the column
-- resolutions and horizontal-homology resolutions in `CE` to identify the first `E₁`-page with
-- the objectwise right derived functors `R^qF(K^p)` and the second `E₂`-page with
-- `R^pF(H^q(K^•))`. Apply the two spectral-sequence constructions for `I`; this directly
-- produces the two associated spectral sequences together with the page identifications,
-- boundedness, the finite filtrations on the abutment cohomology owned by the two canonical
-- filtered complexes, convergence to the cohomology of the total complex, and the canonical
-- comparison of that abutment with `H^*(RF(K^•))`.
/-- Lemma 13.21.3: let `F : 𝒜 ⥤ 𝒝` be a left exact functor of abelian categories, let `K^•` be
a bounded-below cochain complex of `𝒜`, and let `CE` be a Cartan-Eilenberg resolution of `K^•`.
Then the two spectral sequences associated to the double complex `F(I^{•,•})` can be packaged so
that `{}'E_1^{p,q} = R^qF(K^p)` and `{}''E_2^{p,q} = R^pF(H^q(K^•))`; both are bounded and both
converge to the cohomology of `Tot(F(I^{•,•}))`, together with canonical abutment isomorphisms
`H^n(Tot(F(I^{•,•}))) ≅ H^n(RF(K^•))`. The induced filtrations on the abutment cohomology are
finite, recorded separately by the canonical owner
`FilteredComplex.cohomologyFiltrationIsFinite`, while convergence itself is recorded by
`FilteredComplex.convergesToCohomology`. -/
theorem exists_cartanEilenberg_rightDerived_spectralSequences
    :
    let I :=
      ((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
    let FI₁ := firstDoubleComplexFilteredComplex I
    let FI₂ := secondDoubleComplexFilteredComplex I
    ∃ (firstSpectralSequence secondSpectralSequence : CohomologicalSpectralSequence 𝒝 0)
      (_ : IsAssociatedToFilteredComplex FI₁ firstSpectralSequence)
      (_ : IsAssociatedToFilteredComplex FI₂ secondSpectralSequence)
      (firstPageOneIso :
        ∀ (p : ℤ) (q : ℕ),
          (firstSpectralSequence.page 1).X (p, Int.ofNat q) ≅
            (F.rightDerived q).obj (K.obj.X p))
      (secondPageTwoIso :
        ∀ (p : ℕ) (q : ℤ),
          (secondSpectralSequence.page 2).X (Int.ofNat p, q) ≅
            (F.rightDerived p).obj (K.obj.homology q))
      (targetIso :
        ∀ n : ℤ,
          FI₁.underlying.homology n ≅
            ((plusι ⋙ DerivedCategory.homologyFunctor 𝒝 n).obj
              ((Functor.totalRightDerived
                  (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
                  Qplus
                  (boundedBelowHomotopyQuasiIso 𝒜)).obj
                ((Qhplus ⋙ Qplus).obj K)))),
      CohomologicalSpectralSequence.IsBounded firstSpectralSequence ∧
        FI₁.cohomologyFiltrationIsFinite ∧
        FI₁.convergesToCohomology firstSpectralSequence ∧
        CohomologicalSpectralSequence.IsBounded secondSpectralSequence ∧
        FI₂.cohomologyFiltrationIsFinite ∧
        FI₂.convergesToCohomology secondSpectralSequence := sorry

end

end
