import StacksProject_2024.stacks_project.Chap17.Definition_17_28_3
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_13_4_Leray_spectral_sequence

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open DerivedCategory.TStructure
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceOpenHypercohomology

variable {X Y : RingedSpace.{u}}

namespace Hom

/-- The ringed space `(Y, f_*𝒪_X)` attached to a morphism `f : X ⟶ Y`. -/
abbrev pushforwardStructure (f : X ⟶ Y) : RingedSpace.{u} :=
  TopCat.Sheaf.toRingedSpace ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf)

/-- The canonical morphism of ringed spaces `f' : (X, 𝒪_X) ⟶ (Y, f_*𝒪_X)` induced by `f`. -/
abbrev toPushforwardStructure (f : X ⟶ Y) :
    X ⟶ pushforwardStructure f :=
  InducedCategory.homMk
    { base := f.hom.base
      c := 𝟙 _ }

end Hom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => D⁺(ModX)
local notation "ModΓX" => ModuleCat (globalSectionsRing X)
local notation "ModΓY" => ModuleCat (globalSectionsRing Y)
local notation "TopOpenX" => (⊤ : Opens X.carrier)
local notation "TopOpenY" => (⊤ : Opens Y.carrier)
local notation "RΓX" => moduleDerivedGlobalSections X
local notation "HΓX" n => DerivedCategory.homologyFunctor ModΓX n

/- Domain-style sampling for Remark `20.13.5`.
- primary domain: Leray spectral sequences for bounded-below derived `𝒪_X`-modules on ringed
  spaces, together with the induced `Γ(X, 𝒪_X)`-module structures on their
  higher pages;
- sampled owner declarations:
  `globalSectionsRing`,
  `moduleDerivedGlobalSections`,
  `exists_leraySpectralSequence_boundedBelow`,
  `CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) 0`,
  `DerivedCategory.homologyFunctor`,
  `TopCat.Sheaf.toRingedSpace`;
- best owner abstraction: a module-valued cohomological spectral sequence over
  `ModuleCat (globalSectionsRing X)` attached to the existing bounded-below Leray owner of
  Lemma `20.13.4`, together with the canonical pushed-forward-structure target `(Y, f_*𝒪_X)`
  whose top-open global sections are definitionally `Γ(X, 𝒪_X)`;
- primitive data: the source-facing Leray package of Lemma `20.13.4` for `f`, together with a
  module-valued spectral sequence over `Γ(X, 𝒪_X)` coming from the canonical morphism
  `f' : (X, 𝒪_X) ⟶ (Y, f_*𝒪_X)`;
- derived API: the module-valued `E₂`-page identification for `f'`, its module-valued abutment in
  `moduleDerivedGlobalSections X`, and the pagewise additive comparison with the same Leray
  spectral sequence for `f` on every page `r ≥ 2`, recorded through explicit isomorphisms;
- source/core/bridge triage:
  `source-facing`: the `Γ(X, 𝒪_X)`-module structure on the Leray terms `E_r^{p,q}` for `r ≥ 2`
    of the spectral sequence from Lemma `20.13.4`;
  `core/canonical`: `CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) 0`;
  `bridge/view`: the canonical target `(Y, f_*𝒪_X)` and
    `forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat` applied pagewise. -/

-- Proof sketch: replace `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` by the morphism of ringed spaces
-- `f' : (X, 𝒪_X) ⟶ (Y, f_*𝒪_X)`. Since `Γ(Y, f_*𝒪_X) = Γ(X, 𝒪_X)`, the Leray spectral sequence
-- for `f'` is naturally valued in `Γ(X, 𝒪_X)`-modules. Lemma `20.13.3` then identifies the
-- underlying additive pages of this module-valued spectral sequence with those of the usual
-- Leray spectral sequence for `f` from page `2` onward.
section

variable (f : X ⟶ Y)

local notation "YPush" => Hom.pushforwardStructure f
local notation "fPush" => Hom.toPushforwardStructure f

/-- Remark 20.13.5: in the bounded-below-derived Leray spectral sequence of
Lemma `20.13.4` for `f : X ⟶ Y`, every page entry `E_r^{p,q}` with `r ≥ 2` carries a
`Γ(X, 𝒪_X)`-module structure. Equivalently, the same Leray spectral sequence can be realized as a
cohomological spectral sequence valued in `ModuleCat (globalSectionsRing X)` for the canonical
morphism of ringed spaces `f' : (X, 𝒪_X) ⟶ (Y, f_*𝒪_X)`, with the usual `E₂`-page
`H^p(Y, R^q f'_∗ K)` and converging to the module-valued derived global sections of `K`. The
additive comparison with Lemma `20.13.4` is recorded separately below. -/
@[stacks 01F3]
theorem exists_leraySpectralSequence_globalSectionsModulePages
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (fPush _*))
      (boundedBelowHomotopyQuasiIso ModX)]
    (K : DModX) :
    ∃ (filteredComplex : FilteredComplex ModΓX)
      (spectralSequence : CohomologicalSpectralSequence ModΓX 0)
      (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso :
        ∀ p : ℕ, ∀ q : ℤ,
          (spectralSequence.page 2).X (Int.ofNat p, q) ≅
            moduleCohomologyAtOpen (⊤ : Opens (Hom.pushforwardStructure f).carrier)
              (H^q(Rf_[fPush] K)) p)
      (targetIso :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            (HΓX n).obj ((RΓX).obj K.toDerived)),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := by
  sorry

/-- Companion bridge for Remark `20.13.5`: every additive Leray realization in the canonical
shape of Lemma `20.13.4` is compared, from page `2` onward, with a
`ModuleCat (globalSectionsRing X)`-valued Leray realization for
`f' : (X, 𝒪_X) ⟶ (Y, f_*𝒪_X)`. The comparison is recorded by explicit pagewise
isomorphisms after forgetting the `Γ(X, 𝒪_X)`-module structure. -/
theorem exists_leraySpectralSequence_globalSectionsModulePages_compareTo_boundedBelow
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
      (boundedBelowHomotopyQuasiIso ModX)]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (fPush _*))
      (boundedBelowHomotopyQuasiIso ModX)]
    (K : DModX)
    {filteredComplex : FilteredComplex AddCommGrpCat.{u}}
    {spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{u} 0}
    (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
    (pageTwoIso :
      ∀ p : ℕ, ∀ q : ℤ,
        (spectralSequence.page 2).X (Int.ofNat p, q) ≅
          ((forget₂ ModΓY AddCommGrpCat.{u}).obj
            (moduleCohomologyAtOpen TopOpenY (H^q(Rf_[f] K)) p)))
    (targetIso :
      ∀ n : ℤ,
        filteredComplex.underlying.homology n ≅ H^n(TopOpenX, K.toDerived))
    (hconvergent :
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence) :
    ∃ (filteredComplex' : FilteredComplex ModΓX)
      (spectralSequence' : CohomologicalSpectralSequence ModΓX 0)
      (associated' : IsAssociatedToFilteredComplex filteredComplex' spectralSequence')
      (pageTwoIso' :
        ∀ p : ℕ, ∀ q : ℤ,
          (spectralSequence'.page 2).X (Int.ofNat p, q) ≅
            moduleCohomologyAtOpen (⊤ : Opens (Hom.pushforwardStructure f).carrier)
              (H^q(Rf_[fPush] K)) p)
      (targetIso' :
        ∀ n : ℤ,
          filteredComplex'.underlying.homology n ≅
            (HΓX n).obj ((RΓX).obj K.toDerived))
      (pageComparison :
        ∀ {r : ℕ} (hr : 2 ≤ r) (p : ℕ) (q : ℤ),
          ((forget₂ ModΓX AddCommGrpCat.{u}).obj
            ((spectralSequence'.page r).X (Int.ofNat p, q))) ≅
            (spectralSequence.page r).X (Int.ofNat p, q)),
      CohomologicalSpectralSequence.IsBounded spectralSequence' ∧
        filteredComplex'.cohomologyFiltrationIsFinite ∧
        filteredComplex'.convergesToCohomology spectralSequence' := by
  sorry

end

end AlgebraicGeometry.RingedSpace
