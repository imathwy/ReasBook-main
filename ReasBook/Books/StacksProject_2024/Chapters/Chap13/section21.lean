import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_21_1 (from Chap13) -/
open CategoryTheory Limits HomologicalComplex₂

noncomputable section

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: cohomological double complexes and their columnwise injective resolutions;
- sampled owner declarations:
  `CochainComplex.Plus`,
  `CochainComplex.plus_iff`,
  `CategoryTheory.InjectiveResolution`,
  `CategoryTheory.InjectiveResolution.cochainComplex`,
  `CategoryTheory.InjectiveResolution.ι'`,
  `CochainComplex.Plus (CochainComplex 𝒜 ℤ)`;
- best owner abstraction: the source-facing object is a Cartan-Eilenberg resolution, but the
  bounded-below source complex and the horizontal boundedness of the double complex should be
  owned by the canonical `CochainComplex.Plus` owners, while the row/image-column constructions
  live on the ambient double complex `HomologicalComplex₂`, the kernel/image/homology columns are
  owned by the canonical `HomologicalComplex.cycles` / `image` / `.homology` APIs, and the
  chosen resolution of each single object should be owned by `CategoryTheory.InjectiveResolution`;
  horizontally bounded-below double complex, its augmentation from `K.obj`, and the chosen
  column/cycles/image/homology objectwise injective resolutions with comparison isos;
- derived API here: the bottom row, the horizontal image columns, and the induced augmentations.

This file is therefore `source-facing`, but its repeated row/column views should live on
the ambient `HomologicalComplex₂`/`HomologicalComplex` owners rather than through exact-interface
local aliases; the single-object resolutions should be read through the canonical owner
`CategoryTheory.InjectiveResolution`, and the vertical bounded-below property should be derived
from those canonical resolutions rather than stored as parallel primitive data.
-/

/-- Definition 13.21.1: a Cartan-Eilenberg resolution of a bounded-below cochain complex
`K : CochainComplex.Plus 𝒜` in
an abelian category consists of a double complex `I^{\bullet,\bullet}` and an augmentation
`ε : K^• ⟶ I^{\bullet,0}` such that the double complex is horizontally bounded below, each column
resolves the corresponding term of `K^•`, and likewise the cycles, image, and
horizontal-homology columns resolve the corresponding kernel, image, and cohomology objects of
`K^•`. -/
structure CartanEilenbergResolution (K : CochainComplex.Plus 𝒜) where
  /-- The horizontally bounded-below double complex `I^{\bullet,\bullet}` underlying the
  Cartan-Eilenberg resolution. -/
  doubleComplex : CochainComplex.Plus (CochainComplex 𝒜 ℤ)
  /-- The augmentation `ε : K^• ⟶ I^{\bullet,0}` into the bottom row. -/
  ε : K.obj ⟶ (flip doubleComplex.obj).X 0
  /-- A chosen injective resolution of the object `K^p`, owned by
  `CategoryTheory.InjectiveResolution`. -/
  columnResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.X p)
  /-- The chosen `p`-th injective resolution is identified with the actual column
  `I^{p,\bullet}`. -/
  columnIso (p : ℤ) : (columnResolution p).cochainComplex ≅ doubleComplex.obj.X p
  /-- The degree-zero component of the column augmentation agrees with the bottom-row
  augmentation. -/
  columnAugmentation_f_zero (p : ℤ) :
    ((columnResolution p).ι' ≫ (columnIso p).hom).f 0 = ε.f p
  /-- A chosen injective resolution of the object `ker(d_K^p)`, owned by
  `K.obj.cycles p`. -/
  cyclesResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.cycles p)
  /-- The chosen cycles-column injective resolution is identified with the actual cycles complex,
  i.e. the kernel of `d_1^{p,\bullet}`. -/
  cyclesIso (p : ℤ) :
    (cyclesResolution p).cochainComplex ≅ doubleComplex.obj.cycles p
  /-- A chosen injective resolution of the object `im(d_K^p)`. -/
  imageResolution (p : ℤ) :
    CategoryTheory.InjectiveResolution (image (K.obj.d p (p + 1)))
  /-- The chosen image-column injective resolution is identified with the actual image complex
  of `d_1^{p,\bullet}`. -/
  imageIso (p : ℤ) :
    (imageResolution p).cochainComplex ≅ image (doubleComplex.obj.d p (p + 1))
  /-- A chosen injective resolution of the object `H^p(K^•)`. -/
  homologyResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.homology p)
  /-- The chosen horizontal-homology injective resolution is identified with the actual complex
  `H_I^p(I^{\bullet,\bullet})`. -/
  homologyIso (p : ℤ) :
    (homologyResolution p).cochainComplex ≅ doubleComplex.obj.homology p

variable {K : CochainComplex.Plus 𝒜}

namespace CartanEilenbergResolution

/-- Every column of a Cartan-Eilenberg resolution is zero in negative vertical degrees. -/
theorem vertical_isStrictlyGE (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsStrictlyGE (I.doubleComplex.obj.X p) 0 := by
  let _ : CochainComplex.IsStrictlyGE ((I.columnResolution p).cochainComplex) 0 := inferInstance
  simpa using CochainComplex.isStrictlyGE_of_iso (I.columnIso p) 0

end CartanEilenbergResolution

end

/-! ### Lemma_13_21_2 (from Chap13) -/
open CategoryTheory

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

/-
Domain-style sampling:
- primary domain: Cartan-Eilenberg resolutions of bounded-below cochain complexes in an abelian
  category with enough injectives;
- sampled owner declarations:
  `CartanEilenbergResolution`,
  `CochainComplex.InjectiveResolution`,
  `CategoryTheory.ShortComplex`,
  `CategoryTheory.InjectiveResolution`;
- best owner abstraction: the source-facing owner for the present lemma is
  `CartanEilenbergResolution`, while the columnwise and successive short-exact-sequence inputs used
  to build it are already canonically owned by `CochainComplex.InjectiveResolution`,
  `CategoryTheory.ShortComplex`, and `CategoryTheory.InjectiveResolution`;
- primitive data here: only the bounded-below source complex `K`;
- derived API here: the genuine existence statement that `K` admits a Cartan-Eilenberg
  resolution.

Source/core/bridge triage:
- `source-facing`: the existence statement below;
- `core/canonical`: the existing injective-resolution owners from Chapter 13 and mathlib;
- `bridge/view`: none in this file, since the target statement is already directly about the
  source-facing owner `CartanEilenbergResolution`.
-/

-- Proof sketch: choose a lower bound for `K`, then for each short exact sequence
-- `0 ⟶ Z^p ⟶ K^p ⟶ B^{p + 1} ⟶ 0` and `0 ⟶ B^{p + 1} ⟶ Z^{p + 1} ⟶ H^{p + 1}(K^•) ⟶ 0`
-- use the canonical owner `CochainComplex.InjectiveResolution` from Lemma 13.18.3 together with
-- the short-complex comparison data supplied directly by Lemma 13.18.9 to fit consecutive choices
-- into short exact sequences of complexes. Iterating this construction produces the
-- double complex and augmentation data required by the source-facing owner
-- `CartanEilenbergResolution`.
/-- Lemma 13.21.2: every bounded-below cochain complex in an abelian category with enough
injectives admits a Cartan-Eilenberg resolution. -/
theorem exists_cartanEilenbergResolution (K : CochainComplex.Plus 𝒜) :
    Nonempty (CartanEilenbergResolution K) := sorry

end

/-! ### Lemma_13_21_3 (from Chap13) -/
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

/-! ### Remark_13_21_4 (from Chap13) -/
universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: filtered complexes in an abelian category and the associated cohomological
  spectral sequence construction;
- sampled owner declarations:
  `FilteredComplex`,
  `exists_filteredComplexAssociatedSpectralSequence`,
  `IsAssociatedToFilteredComplex`;
- best owner abstraction: the source object is a filtered complex, already canonically owned in
  the project by `FilteredComplex 𝒜`; Chapter `12` already supplies the owner-level existence
  theorem for associated spectral sequences, while the spectral-sequence side itself is owned by
  `CohomologicalSpectralSequence 𝒜 0`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜`;
- derived API: an associated spectral sequence together with its comparison maps/pages, recorded
  through `IsAssociatedToFilteredComplex`.

Source/core/bridge triage:
- `source-facing`: this remark only points back to the general filtered-complex construction
  underlying Lemma `13.21.3`;
- `core/canonical`: `FilteredComplex 𝒜` and `exists_filteredComplexAssociatedSpectralSequence`;
- `bridge/view`: `IsAssociatedToFilteredComplex`.

This remark is therefore recall-only: the correct surface is to reuse the Chapter `12` owner
declarations directly, not to introduce a parallel local wrapper or a fake local functor owner. -/
/- Remark 13.21.4: the two spectral sequences attached in Lemma 13.21.3 should be regarded as
instances of the general construction sending a filtered complex of `𝒜` to an associated
cohomological spectral sequence, so the correct owner-level reference here is the Chapter `12`
existence theorem for associated spectral sequences. -/
#check exists_filteredComplexAssociatedSpectralSequence

end CategoryTheory
