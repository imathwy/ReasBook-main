import StacksProject_2024.Chap13.Lemma_13_22_2_Grothendieck_spectral_sequence
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Lemma_21_20_5_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open DerivedCategory.TStructure
open CategoryTheory.Limits
open scoped RingedSite.Hom RingedSiteDerivedSections

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace RingedSite.Hom

/- Domain-style sampling for Lemma `21.14.5`.
- primary domain: bounded-below Leray spectral sequences for global sections of sheaves of
  modules on ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.modulePushforwardDerived`,
  `RingedSite.Hom.moduleGlobalSectionsAdditiveFunctor`,
  `exists_grothendieckSpectralSequence`,
  `Functor.totalRightDerived`,
  `CohomologicalSpectralSequence`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the Chapter `13` Grothendieck spectral-sequence existence theorem,
  specialized to `f_*` and the chapter additive global-sections bridge
  `moduleGlobalSectionsAdditiveFunctor` on the target ringed site;
- primitive data: the module categories on `X` and `Y`, the additive functors `f_*` and
  `Γ(Y, -)`, and the bounded-below derived object `K`;
- derived API in this file: the bounded-below derived direct-image owner
  `modulePushforwardDerivedPlus`, exposed on the theorem surface through the source-facing
  notation `Rf_[f] K`, its cohomology-sheaf bridge `H^q(Rf_[f] K)`, and the Leray page-two and
  abutment identifications written directly through the canonical module-cohomology and
  global-sections owners.

Source/core/bridge triage:
- `source-facing`: the existence theorem below;
- `core/canonical`: `exists_grothendieckSpectralSequence`, `Functor.totalRightDerived`,
  `moduleGlobalSectionsAdditiveFunctor`, `CohomologicalSpectralSequence`,
  `IsAssociatedToFilteredComplex`, and the filtered-complex convergence owners from Chapter `12`;
- `bridge/view`: the bounded-below derived direct-image owner `Rf_[f] K`, its cohomology-sheaf
  bridge `H^q(Rf_[f] K)`, and the page-two and abutment isomorphisms expressing the Chapter `13`
  owners in the textbook `H^p(𝒟, R^q f_* K)` and `H^n(𝒞, K)` forms.

The bounded-below direct-image owner belongs already at this stage of the chapter and is shared by
the relative Leray file below. The global-sections layer should therefore reuse the chapter
additive bridge `moduleGlobalSectionsAdditiveFunctor`, not a fresh local composite wrapper.
-/

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

local notation "DModX" => D⁺(ModX)
local notation "DModY" => D⁺(ModY)
local notation "QplusX" =>
  (mapBoundedBelowHomotopyToDerivedBelow : HomotopyCategory.Plus ModX ⥤ DModX)
local notation "plusX" => ObjectProperty.ι (t.plus : ObjectProperty (D(ModX)))

/-- The bounded-below derived direct-image functor on `𝒪_X`-modules. -/
abbrev modulePushforwardDerivedPlus
    (f : RingedSite.Hom X Y)
    [Functor.Additive f.modulePushforward]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
      (boundedBelowHomotopyQuasiIso ModX)] :
    DModX ⥤ DModY :=
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
    QplusX
    (boundedBelowHomotopyQuasiIso ModX)

/- Textbook surface notation for the bounded-below derived direct image object `Rf_* K` and its
cohomology sheaves `H^q(Rf_[f] K)`. The cohomology notation inserts the canonical inclusion
`D⁺(𝒪_Y) ⥤ D(𝒪_Y)` before applying the Chapter `13` owner `H^q`. -/
scoped syntax:100 "Rf_[" term "] " term:max : term
scoped macro_rules
  | `(Rf_[ $f ] $K) => `((RingedSite.Hom.modulePushforwardDerivedPlus $f).obj $K)
scoped notation3:max "H^" q:max "(" "Rf_[" f "] " K ")" =>
  ((H^q).obj (((Rf_[f] K)).1))

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: apply the Grothendieck spectral sequence to the composite
-- `Γ(𝒞, -) = Γ(𝒟, -) ∘ f_*` on sheaves of `𝒪`-modules. Lemma
-- `21.14.1` shows that the pushforward of an injective module sheaf is totally acyclic on the
-- target, and Lemma `21.14.3` upgrades total acyclicity to right acyclicity for global sections.
-- Therefore the hypotheses of Lemma `13.22.2` hold for the pair
-- `f_* : Mod(𝒪_𝒞) ⥤ Mod(𝒪_𝒟)` and `Γ(𝒟, -)`, yielding the stated `E₂`-page. The latter is
-- written through the canonical Chapter `21` module-cohomology owner
-- `Ext (SheafOfModules.unit Y.structureSheaf) (H^q(Rf_[f] K)) p` via
-- `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`. The abutment is then read
-- through the canonical Chapter `21` owner `RΓ[X]` after the standard inclusion
-- `D⁺(𝒪_X) ⥤ D(𝒪_X)`.
/-- Lemma 21.14.5 (Leray spectral sequence): for a morphism of ringed topoi, formalized here by a
morphism of ringed sites `f`, and a bounded-below complex `K` of `𝒪_𝒞`-modules,
there is a cohomological spectral sequence whose `E_2^{p,q}`-term is
`H^p(𝒟, R^q f_*(K))` and whose abutment is `H^{p+q}(𝒞, K)`. -/
@[stacks 0732]
theorem exists_leraySpectralSequence
    [HasInjectiveResolutions ModY]
    [HasExt ModY]
    [Functor.Additive f.modulePushforward]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
      (boundedBelowHomotopyQuasiIso ModX)]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
    (K : DModX) :
    ∃ (filteredComplex : FilteredComplex AddCommGrpCat.{max u v})
      (spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{max u v} 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso : ∀ p : ℕ, ∀ q : ℤ,
        (spectralSequence.page 2).X (Int.ofNat p, q) ≅
          AddCommGrpCat.of
            (Ext (SheafOfModules.unit Y.structureSheaf) (H^q(Rf_[f] K)) p))
      (targetIso : ∀ n : ℤ,
        filteredComplex.underlying.homology n ≅
          (H^n).obj ((RΓ[X]).obj ((plusX).obj K))),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := by
  sorry

end

end RingedSite.Hom
