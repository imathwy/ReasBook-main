import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Localization.BaseChange
import StacksProject_2024.Chap15.Lemma_15_91_6
import StacksProject_2024.Chap15.Theorem_15_90_18

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule (equivTensorProduct mkLinearMap)
open scoped CategoricalPullback TensorProduct

noncomputable section

universe u

section

/- 
Domain-style sampling:
* primary domain: Beauville-Laszlo glueing data for a single localization, together with the
  resulting short exact sequence in `ModuleCat`;
* inspected owner declarations:
  `formalGlueingSingleFunctor`,
  `beauvilleLaszloCechSequence`,
  `LocalizedModule.mkLinearMap`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `LinearMap.shortComplexKer`,
  `LinearMap.shortExact_shortComplexKer`;
* best owner abstraction: the primitive datum is an object `X` of the single-element categorical
  pullback `Mod_{R'} ×_{Mod_{R'_f}} Mod_{R_f}` from `Theorem_15_90_18`, rather than a separate
  coordinate triple `(M', M₁, α₁)`;
* primitive data: the pullback object `X`, with first component `X.fst`, second component `X.snd`,
  overlap isomorphism `X.iso`, and the canonical localization map
  `LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst`;
* derived API: the canonical localized-side map, the differential `d`, its kernel `H⁰`, and the
  canonical kernel short complex `d.shortComplexKer`, together with its short exactness under the
  glueing-pair hypothesis;
* source/core/bridge triage:
  `source-facing`: `beauvilleLaszloGlueingDifferential`, `beauvilleLaszloGlueingH0`;
  `core/canonical`: the pullback owner `X : CategoricalPullback ...` and
    `(beauvilleLaszloGlueingDifferential f X).shortComplexKer`;
  `bridge/view`: `beauvilleLaszloGlueingLocalizedSideMap` and
    `beauvilleLaszloGlueingH0_shortExact`.
-/

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (f : R)

local notation "Away" => LocalizedModule.Away
local notation "Rf" => Localization.Away f
local notation "R'f" => Localization.Away (algebraMap R R' f)
local notation "extendToOverlap" => ModuleCat.extendScalars (algebraMap R' R'f)

private abbrev awayMapToOverlap : Rf →+* R'f :=
  Localization.awayMap (algebraMap R R') f

section

variable
  (X :
    CategoricalPullback
      (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
      (ModuleCat.extendScalars (awayMapToOverlap f)))

local instance : Module R ↑X.fst := Module.compHom _ (algebraMap R R')
local instance : Module R ↑X.snd := Module.compHom _ (algebraMap R Rf)
local instance : IsScalarTower R R' ↑X.fst := IsScalarTower.of_compHom R R' ↑X.fst
local instance : IsScalarTower R Rf ↑X.snd := IsScalarTower.of_compHom R Rf ↑X.snd
local instance : Algebra Rf R'f := (awayMapToOverlap f).toAlgebra
local instance : IsScalarTower R R' (Away (algebraMap R R' f) ↑X.fst) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simpa

private noncomputable def restrictScalarsOverlapSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R' R'f)).obj (ModuleCat.of R'f R'f)) ≃ₗ[R'f] R'f :=
  { __ := AddEquiv.refl R'f
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsOverlapSelfIsScalarTower :
    IsScalarTower R' R'f
      ↑((ModuleCat.restrictScalars (algebraMap R' R'f)).obj (ModuleCat.of R'f R'f)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendToOverlapIso :
    (extendToOverlap).obj X.fst ≅ ModuleCat.of R'f (R'f ⊗[R'] ↑X.fst) := by
  change
    ModuleCat.of R'f
        (↑((ModuleCat.restrictScalars (algebraMap R' R'f)).obj (ModuleCat.of R'f R'f)) ⊗[R']
          ↑X.fst) ≅
      ModuleCat.of R'f (R'f ⊗[R'] ↑X.fst)
  exact
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsOverlapSelfEquiv f)
      (LinearEquiv.refl R' ↑X.fst)).toModuleIso

/-- The canonical map from the localized-side component `X.snd` of a Beauville-Laszlo pullback
datum to the overlap module `(X.fst)_f`. -/
noncomputable def beauvilleLaszloGlueingLocalizedSideMap :
    ↑X.snd →ₗ[R] Away (algebraMap R R' f) ↑X.fst :=
  let overlap : ModuleCat R'f :=
    ModuleCat.of R'f (Away (algebraMap R R' f) ↑X.fst)
  let tensorToAway :
      (extendToOverlap).obj X.fst ⟶ overlap :=
    (extendToOverlapIso f X).hom ≫
      ModuleCat.ofHom
        (show R'f ⊗[R'] ↑X.fst →ₗ[R'f] Away (algebraMap R R' f) ↑X.fst from
          (equivTensorProduct (Submonoid.powers (algebraMap R R' f)) ↑X.fst).symm)
  let localizedSideMap :
      X.snd ⟶ (ModuleCat.restrictScalars (awayMapToOverlap f)).obj overlap :=
    ((ModuleCat.extendRestrictScalarsAdj (awayMapToOverlap f)).homEquiv X.snd
      overlap) (X.iso.inv ≫ tensorToAway)
  let overlapMapR :
      (ModuleCat.restrictScalars (algebraMap R Rf)).obj X.snd ⟶
        (ModuleCat.restrictScalars (algebraMap R R'f)).obj overlap :=
    (ModuleCat.restrictScalars (algebraMap R Rf)).map localizedSideMap ≫
      ((ModuleCat.restrictScalarsComp'
        (algebraMap R Rf)
        (awayMapToOverlap f)
        (algebraMap R R'f)
        (formalGlueingSingleAwaySquare_commutes f)).symm.app overlap).hom
  let overlapMapLin :
      ↑((ModuleCat.restrictScalars (algebraMap R Rf)).obj X.snd) →ₗ[R]
        ↑((ModuleCat.restrictScalars (algebraMap R R'f)).obj overlap) :=
    ModuleCat.Hom.hom overlapMapR
  let overlapForget :
      ↑((ModuleCat.restrictScalars (algebraMap R R'f)).obj overlap) →ₗ[R]
        Away (algebraMap R R' f) ↑X.fst :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        simpa using
          (show (algebraMap R R'f r) • x = (algebraMap R R'f r) • x from rfl) }
  show ↑((ModuleCat.restrictScalars (algebraMap R Rf)).obj X.snd) →ₗ[R]
      Away (algebraMap R R' f) ↑X.fst from
    overlapForget.comp overlapMapLin

/-- The differential `d : X.fst × X.snd → (X.fst)_f` attached to a single Beauville-Laszlo
pullback object `X`. -/
def beauvilleLaszloGlueingDifferential :
    ↑X.fst × ↑X.snd →ₗ[R] Away (algebraMap R R' f) ↑X.fst :=
  ((mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst).restrictScalars R).coprod
    (-(beauvilleLaszloGlueingLocalizedSideMap f X))

/-- The module `H⁰` defined as the kernel of the Beauville-Laszlo differential attached to `X`. -/
abbrev beauvilleLaszloGlueingH0 : Submodule R (↑X.fst × ↑X.snd) :=
  (beauvilleLaszloGlueingDifferential f X).ker

-- Proof sketch: the left map is the subtype inclusion of `ker d`, hence exact with `d`; it is
-- injective by construction; `LinearMap.shortExact_shortComplexKer` packages those canonical
-- facts, so only surjectivity of `d` remains under the standing glueing-pair hypothesis.
/-- 15.91.16.1: if `(R → R', f)` is a Beauville-Laszlo glueing pair and `X` is a single
Beauville-Laszlo pullback datum, then the sequence
`0 → H⁰ → X.fst ⊕ X.snd → (X.fst)_f → 0` is short exact. In Lean, the binary direct sum is
written as `X.fst × X.snd`, and the canonical owner is the kernel short complex
`(beauvilleLaszloGlueingDifferential f X).shortComplexKer`. -/
local notation "GlueingPair" => IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f

theorem beauvilleLaszloGlueingH0_shortExact
    (hpair : GlueingPair) :
    (beauvilleLaszloGlueingDifferential f X).shortComplexKer.ShortExact := by
  letI := hpair
  refine LinearMap.shortExact_shortComplexKer ?_
  change Function.Surjective (beauvilleLaszloGlueingDifferential f X)
  sorry

end

end
