import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Localization.BaseChange
import StacksProject_2024.Chap15.PrincipalIdeal
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

/-- Helper for 15.91.16.1: the left Beauville-Laszlo Cech map
`R → R' × R_f` attached to `algebraMap R R'` and `f`. -/
private abbrev beauvilleLaszloCechLeftMapLocal :
    R →ₗ[R] R' × Rf :=
  LinearMap.prod
    (Algebra.linearMap R R')
    (Algebra.linearMap R Rf)

/-- Helper for 15.91.16.1: the right Beauville-Laszlo Cech map
`R' × R_f → R'_f` attached to `algebraMap R R'` and `f`. -/
private abbrev beauvilleLaszloCechRightMapLocal :
    R' × Rf →ₗ[R] R'f :=
  let left : R' × Rf →ₗ[R] R'f :=
    ((Algebra.linearMap R' R'f).restrictScalars R).comp
      (LinearMap.fst R R' Rf)
  let right : R' × Rf →ₗ[R] R'f :=
    ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap).comp
      (LinearMap.snd R R' Rf)
  left - right

/-- Helper for 15.91.16.1: the local Beauville-Laszlo Cech maps form a complex. -/
private theorem beauvilleLaszloCech_comp_eq_zero_local :
    (beauvilleLaszloCechRightMapLocal (R := R) (R' := R') f).comp
        (beauvilleLaszloCechLeftMapLocal (R := R) (R' := R') f) =
      (0 : R →ₗ[R] R'f) := by
  -- Evaluate the two Cech components on a base element and compare the two canonical maps
  -- `R → R'_f`.
  apply LinearMap.ext
  intro x
  change
    (algebraMap R' R'f (algebraMap R R' x) -
        (Localization.awayMap (algebraMap R R') f) (algebraMap R Rf x)) =
      0
  rw [sub_eq_zero]
  exact congrArg (fun g ↦ g x) (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)

/-- Helper for 15.91.16.1: the local Cech maps package into the canonical short complex in
`ModuleCat R`. -/
private noncomputable abbrev beauvilleLaszloCechSequenceLocal :
    ShortComplex (ModuleCat R) :=
  let α : R →ₗ[R] R' × Rf := beauvilleLaszloCechLeftMapLocal (R := R) (R' := R') f
  let β : R' × Rf →ₗ[R] R'f := beauvilleLaszloCechRightMapLocal (R := R) (R' := R') f
  let h : β.comp α = 0 := by
    simpa using beauvilleLaszloCech_comp_eq_zero_local (R := R) (R' := R') (f := f)
  ModuleCat.shortComplexOfCompEqZero α β h

/-- Helper for 15.91.16.1: a local witness encoding the Beauville-Laszlo glueing-pair hypotheses
used by this proof. -/
private class BeauvilleLaszloGlueingPairLocal : Prop where
  quotientMapBijective :
    ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)
  shortExact :
    (beauvilleLaszloCechSequenceLocal (R := R) (R' := R') f).ShortExact

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

/-- Helper for 15.91.16.1: after restricting scalars along `R_f → R'_f`, the overlap scalar ring
is still canonically `R'_f`. -/
private noncomputable def restrictScalarsSideOverlapSelfEquiv :
    ↑((ModuleCat.restrictScalars (awayMapToOverlap f)).obj (ModuleCat.of R'f R'f)) ≃ₗ[R'f] R'f :=
  { __ := AddEquiv.refl R'f
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for 15.91.16.1: the restricted overlap scalar tower over `R_f` is the evident one. -/
private instance restrictScalarsSideOverlapSelfIsScalarTower :
    IsScalarTower Rf R'f
      ↑((ModuleCat.restrictScalars (awayMapToOverlap f)).obj (ModuleCat.of R'f R'f)) :=
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

/-- Helper for 15.91.16.1: extending scalars on `X.snd` from `R_f` to the overlap ring `R'_f`
is canonically the tensor product `R'_f ⊗[R_f] X.snd`. -/
private noncomputable abbrev sideExtendToOverlapIso :
    (ModuleCat.extendScalars (awayMapToOverlap f)).obj X.snd ≅
      ModuleCat.of R'f (R'f ⊗[Rf] ↑X.snd) := by
  change
    ModuleCat.of R'f
        (↑((ModuleCat.restrictScalars (awayMapToOverlap f)).obj (ModuleCat.of R'f R'f)) ⊗[Rf]
          ↑X.snd) ≅
      ModuleCat.of R'f (R'f ⊗[Rf] ↑X.snd)
  exact
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSideOverlapSelfEquiv f)
      (LinearEquiv.refl Rf ↑X.snd)).toModuleIso

/-- Helper for 15.91.16.1: the canonical comparison from the overlap tensor product
`R'_f ⊗[R'] X.fst` to the localized module `(X.fst)_f`. -/
private noncomputable abbrev overlapTensorToAway :
    R'f ⊗[R'] ↑X.fst →ₗ[R'f] Away (algebraMap R R' f) ↑X.fst :=
  (equivTensorProduct (Submonoid.powers (algebraMap R R' f)) ↑X.fst).symm

/-- Helper for 15.91.16.1: the overlap tensor comparison sends a pure tensor to the corresponding
localized generator. -/
private theorem overlapTensorToAway_apply_tmul
    (r : R') (s : Submonoid.powers (algebraMap R R' f)) (m : ↑X.fst) :
    overlapTensorToAway f X ((Localization.mk r s) ⊗ₜ[R'] m) =
      r • LocalizedModule.mk m s := by
  -- This is the standard tensor/localization comparison from mathlib.
  simpa [overlapTensorToAway] using
    (LocalizedModule.equivTensorProduct_symm_apply_tmul
      (S := Submonoid.powers (algebraMap R R' f))
      (M := ↑X.fst)
      (x := m)
      (r := r)
      (s := s))

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

local notation "GlueingPair" => BeauvilleLaszloGlueingPairLocal (R := R) (R' := R') f

-- Proof sketch: the left map is the subtype inclusion of `ker d`, hence exact with `d`; it is
-- injective by construction; `LinearMap.shortExact_shortComplexKer` packages those canonical
-- facts, so only surjectivity of `d` remains under the standing glueing-pair hypothesis.
/-- Helper for 15.91.16.1: the Beauville-Laszlo glueing-pair hypothesis already gives
surjectivity of the ring-level Cech right map. -/
private theorem beauvilleLaszloCechRightMap_surjective
    (hpair : GlueingPair) :
    Function.Surjective (beauvilleLaszloCechRightMapLocal (R := R) (R' := R') f) := by
  -- The short exactness recorded in `hpair` packages right-surjectivity as `epi_g`.
  exact (ModuleCat.epi_iff_surjective _).mp hpair.shortExact.epi_g

/-- Helper for 15.91.16.1: the localized-side map is the adjunction transpose of the overlap
comparison, evaluated on the standard generator `1 ⊗ x`. -/
private theorem beauvilleLaszloGlueingLocalizedSideMap_apply_eq
    (x : ↑X.snd) :
    beauvilleLaszloGlueingLocalizedSideMap f X x =
      overlapTensorToAway f X
        ((extendToOverlapIso f X).hom (X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x))) := by
  -- Unfold the adjunction transpose and evaluate it on the standard tensor generator `1 ⊗ x`.
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
    ((ModuleCat.extendRestrictScalarsAdj (awayMapToOverlap f)).homEquiv X.snd overlap)
      (X.iso.inv ≫ tensorToAway)
  have hlocalized :
      localizedSideMap x = (X.iso.inv ≫ tensorToAway) ((1 : R'f) ⊗ₜ[Rf] x) := by
    simpa [localizedSideMap] using
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (f := awayMapToOverlap f)
        (M := X.snd)
        (N := overlap)
        (φ := X.iso.inv ≫ tensorToAway)
        x)
  simpa [beauvilleLaszloGlueingLocalizedSideMap, overlap, tensorToAway, localizedSideMap]
    using hlocalized

/-- Helper for 15.91.16.1: scalar multiples of the localized-side map are obtained by evaluating
the same overlap comparison on the pure tensor `a ⊗ x`. -/
private theorem beauvilleLaszloGlueingLocalizedSideMap_smul_eq
    (a : R'f) (x : ↑X.snd) :
    a • beauvilleLaszloGlueingLocalizedSideMap f X x =
      overlapTensorToAway f X
        ((extendToOverlapIso f X).hom (X.iso.inv (a ⊗ₜ[Rf] x))) := by
  -- Push the scalar through the comparison maps until it reaches the tensor generator.
  rw [beauvilleLaszloGlueingLocalizedSideMap_apply_eq]
  calc
    a •
        overlapTensorToAway f X
          ((extendToOverlapIso f X).hom (X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x))) =
      overlapTensorToAway f X
        (a • ((extendToOverlapIso f X).hom (X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x)))) := by
          simpa using
            ((overlapTensorToAway f X).map_smul a
              ((extendToOverlapIso f X).hom (X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x)))
            ).symm
    _ = overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (a • X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x))) := by
          rw [← map_smul]
    _ = overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv (a • ((1 : R'f) ⊗ₜ[Rf] x)))) := by
          rw [← map_smul]
          rfl
    _ = overlapTensorToAway f X
          ((extendToOverlapIso f X).hom (X.iso.inv (a ⊗ₜ[Rf] x))) := by
          have htensor : a • ((1 : R'f) ⊗ₜ[Rf] x) = a ⊗ₜ[Rf] x := by
            simpa [TensorProduct.smul_tmul', one_smul]
          rw [htensor]
          rfl

/-- Helper for 15.91.16.1: the differential is the overlap comparison applied to the difference
between the base generator `1 ⊗ m` and the overlap tensor attached to the side component. -/
private theorem beauvilleLaszloGlueingDifferential_apply_eq
    (m : ↑X.fst) (x : ↑X.snd) :
    beauvilleLaszloGlueingDifferential f X (m, x) =
      overlapTensorToAway f X
        (((1 : R'f) ⊗ₜ[R'] m) -
          (extendToOverlapIso f X).hom (X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x))) := by
  -- Rewrite the coprod differential as the difference of the two canonical overlap maps.
  change
    mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst m -
        beauvilleLaszloGlueingLocalizedSideMap f X x =
      _
  rw [beauvilleLaszloGlueingLocalizedSideMap_apply_eq]
  rw [show mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst m =
      overlapTensorToAway f X ((1 : R'f) ⊗ₜ[R'] m) by
        simpa [LocalizedModule.mkLinearMap]]
  rw [LinearMap.map_sub]

/-- Helper for 15.91.16.1: every localized generator can be rewritten by clearing its denominator
against the denominator-one generator. -/
private theorem localizedModule_mk_eq_scalar_smul_mk_one
    (m : ↑X.fst) (s : Submonoid.powers (algebraMap R R' f)) :
    LocalizedModule.mk m s =
      (Localization.mk 1 s : R'f) •
        LocalizedModule.mk m (1 : Submonoid.powers (algebraMap R R' f)) := by
  -- Move the denominator into the localization scalar and evaluate the standard scalar action.
  simpa [one_smul] using
    (LocalizedModule.mk_smul_mk (R := R')
      (S := Submonoid.powers (algebraMap R R' f))
      (r := 1) (m := m) (s := s) (t := (1 : Submonoid.powers (algebraMap R R' f)))).symm

/-- Helper for 15.91.16.1: an `R'`-scalar acting on the denominator-one localized generator is the
ordinary localized image of the scaled base element. -/
private theorem base_scalar_smul_mk_one_eq
    (r : R') (m : ↑X.fst) :
    ((algebraMap R' R'f r) : R'f) •
        LocalizedModule.mk m (1 : Submonoid.powers (algebraMap R R' f)) =
      mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst (r • m) := by
  simpa [LocalizedModule.mkLinearMap, one_smul] using
    (overlapTensorToAway_apply_tmul (f := f) (X := X) r 1 m)

/-- Helper for 15.91.16.1: an overlap scalar coming from `R_f` can be absorbed into the side
component of the localized-side map. -/
private theorem away_scalar_smul_localizedSideMap_eq
    (y : Rf) (x : ↑X.snd) :
    ((awayMapToOverlap f) y : R'f) • beauvilleLaszloGlueingLocalizedSideMap f X x =
      beauvilleLaszloGlueingLocalizedSideMap f X (y • x) := by
  -- Route correction: use exact `R_f`-linearity on the tensor side instead of searching for an
  -- existential replacement of the side generator.
  rw [beauvilleLaszloGlueingLocalizedSideMap_smul_eq,
    beauvilleLaszloGlueingLocalizedSideMap_apply_eq]
  have htensor :
      (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x) = (1 : R'f) ⊗ₜ[Rf] (y • x) := by
    calc
      (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x) =
          ((algebraMap Rf R'f y) ⊗ₜ[Rf] x) := by
        rfl
      _ = ((y : Rf) • (1 : R'f)) ⊗ₜ[Rf] x := by
        simp [Algebra.smul_def]
      _ = (1 : R'f) ⊗ₜ[Rf] (y • x) := by
        simpa using (TensorProduct.smul_tmul (R := Rf) (R' := Rf) y (1 : R'f) x)
  exact congrArg
    (fun z ↦ overlapTensorToAway f X ((extendToOverlapIso f X).hom (X.iso.inv z)))
    htensor

/-- Helper for 15.91.16.1: every localized-side value already lies in the differential range. -/
private theorem beauvilleLaszloGlueingDifferential_range_contains_side_map
    (x : ↑X.snd) :
    beauvilleLaszloGlueingLocalizedSideMap f X x ∈
      LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
  -- Use the explicit witness `(0, -x)` so the two minus signs in the differential cancel.
  refine LinearMap.mem_range.mpr ⟨(0, -x), ?_⟩
  change
    mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst 0 -
        beauvilleLaszloGlueingLocalizedSideMap f X (-x) =
      beauvilleLaszloGlueingLocalizedSideMap f X x
  simp

/-- Helper for 15.91.16.1: the denominator-one localized generator coming from the left component
is visibly in the differential range. -/
private theorem beauvilleLaszloGlueingDifferential_range_contains_base_generator
    (m : ↑X.fst) :
    LocalizedModule.mk m (1 : Submonoid.powers (algebraMap R R' f)) ∈
      LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
  -- The witness `(m, 0)` kills the side term and leaves the standard localized generator.
  refine LinearMap.mem_range.mpr ⟨(m, 0), ?_⟩
  change
    mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst m -
        beauvilleLaszloGlueingLocalizedSideMap f X 0 =
      LocalizedModule.mk m (1 : Submonoid.powers (algebraMap R R' f))
  simp [LocalizedModule.mkLinearMap]

/-- Helper for 15.91.16.1: the chosen power `(algebraMap R R' f)^n` belongs to the powers
submonoid. -/
private theorem algebraMap_f_pow_mem_powers (n : ℕ) :
    (algebraMap R R' f) ^ n ∈ Submonoid.powers (algebraMap R R' f) := by
  exact ⟨n, rfl⟩

/-- Helper for 15.91.16.1: every localized-side value can be written with a denominator equal to
one power of `algebraMap R R' f`. -/
private theorem beauvilleLaszloGlueingLocalizedSideMap_exists_power_denominator
    (x : ↑X.snd) :
    ∃ n : ℕ, ∃ m : ↑X.fst,
      beauvilleLaszloGlueingLocalizedSideMap f X x =
        LocalizedModule.mk m
          ⟨(algebraMap R R' f) ^ n, algebraMap_f_pow_mem_powers (R := R) (R' := R') (f := f) n⟩ := by
  -- Choose one localization representative for `α₁(x)` and rewrite its denominator as a power.
  obtain ⟨⟨m, s⟩, hs⟩ :=
    IsLocalizedModule.surj
      (Submonoid.powers (algebraMap R R' f))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst)
      (beauvilleLaszloGlueingLocalizedSideMap f X x)
  rcases s with ⟨s, ⟨n, rfl⟩⟩
  let t : Submonoid.powers (algebraMap R R' f) :=
    ⟨(algebraMap R R' f) ^ n, algebraMap_f_pow_mem_powers (R := R) (R' := R') (f := f) n⟩
  refine ⟨n, m, ?_⟩
  have ht :
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst)
          m t =
        beauvilleLaszloGlueingLocalizedSideMap f X x := by
    rw [IsLocalizedModule.mk'_eq_iff]
    simpa [t, LocalizedModule.mkLinearMap_apply] using hs.symm
  simpa [eq_comm, t, IsLocalizedModule.mk_eq_mk'] using ht

/-- Helper for 15.91.16.1: quotient-bijectivity lets us split an `R'`-coefficient into a lifted
base part plus a remainder divisible by a chosen power of `f`. -/
private theorem rprime_eq_base_add_fpow_mul
    (hpair : GlueingPair) (g : R') (n : ℕ) :
    ∃ a : R, ∃ b : R', g = algebraMap R R' a + (algebraMap R R' f) ^ n * b := by
  -- Route correction: split the coefficient modulo the same power of `f` that appears in the
  -- chosen denominator for `α₁(x)`, rather than trying to normalize an arbitrary `R'_f`-scalar.
  cases n with
  | zero =>
      refine ⟨0, g, ?_⟩
      simp
  | succ n =>
      let npos : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩
      obtain ⟨xbar, hxbar⟩ :=
        (hpair.quotientMapBijective npos).2
          ((Ideal.Quotient.mk (principalPowerIdeal (algebraMap R R' f) (n + 1))) g)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective xbar
      have hquot :
          (Ideal.Quotient.mk (principalPowerIdeal (algebraMap R R' f) (n + 1)))
              (algebraMap R R' a) =
            (Ideal.Quotient.mk (principalPowerIdeal (algebraMap R R' f) (n + 1))) g := by
        simpa [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap] using hxbar
      have hmem :
          g - algebraMap R R' a ∈ principalPowerIdeal (algebraMap R R' f) (n + 1) := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [map_sub] using
          (sub_eq_zero.mpr hquot.symm :
            (Ideal.Quotient.mk (principalPowerIdeal (algebraMap R R' f) (n + 1))) g -
                (Ideal.Quotient.mk (principalPowerIdeal (algebraMap R R' f) (n + 1)))
                  (algebraMap R R' a) =
              0)
      rcases
          (Ideal.mem_span_singleton.mp
            (by
              simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using
                hmem)) with
        ⟨b, hb⟩
      refine ⟨a, b, ?_⟩
      exact sub_eq_iff_eq_add'.1 <| by simpa [mul_comm] using hb

/-- Helper for 15.91.16.1: if `α₁(x)` is represented with denominator `(f^n)`, then the scalar
branch divisible by `(f^n)` collapses to a denominator-one base generator. -/
private theorem fpow_mul_localized_side_eq_base_generator
    (x : ↑X.snd) (m : ↑X.fst) (b : R') (n : ℕ)
    (hx : beauvilleLaszloGlueingLocalizedSideMap f X x =
      LocalizedModule.mk m
        ⟨(algebraMap R R' f) ^ n, algebraMap_f_pow_mem_powers (R := R) (R' := R') (f := f) n⟩) :
    ((algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) •
        beauvilleLaszloGlueingLocalizedSideMap f X x) =
      mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst (b • m) := by
  -- Clear the chosen denominator first, then identify the remaining denominator-one term with the
  -- standard localized generator from the base component.
  rw [hx, localizedModule_mk_eq_scalar_smul_mk_one]
  let s : Submonoid.powers (algebraMap R R' f) :=
    ⟨(algebraMap R R' f) ^ n, algebraMap_f_pow_mem_powers (R := R) (R' := R') (f := f) n⟩
  have hs :
      (Localization.mk 1 s : R'f) * (algebraMap R' R'f ((algebraMap R R' f) ^ n) : R'f) = 1 := by
    simpa [Localization.mk_eq_mk'_apply, Localization.mk_one_eq_algebraMap, Algebra.smul_def,
      mul_comm, s] using
      (IsLocalization.smul_mk'_self (S := R'f) (m := s) (r := (1 : R')))
  have hcoeff :
      (algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) *
          (Localization.mk 1 s : R'f) =
        algebraMap R' R'f b := by
    calc
      (algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) *
          (Localization.mk 1 s : R'f) =
        (algebraMap R' R'f b : R'f) *
          ((Localization.mk 1 s : R'f) *
            (algebraMap R' R'f ((algebraMap R R' f) ^ n) : R'f)) := by
              simp [map_mul, mul_comm, mul_left_comm]
      _ = (algebraMap R' R'f b : R'f) * 1 := by rw [hs]
      _ = algebraMap R' R'f b := by simp
  calc
    (algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) •
        ((Localization.mk 1 s : R'f) •
          LocalizedModule.mk m (1 : Submonoid.powers (algebraMap R R' f))) =
      (((algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) *
          (Localization.mk 1 s : R'f)) •
        LocalizedModule.mk m (1 : Submonoid.powers (algebraMap R R' f))) := by
          rw [smul_smul]
    _ = ((algebraMap R' R'f b : R'f) •
          LocalizedModule.mk m (1 : Submonoid.powers (algebraMap R R' f))) := by
          rw [hcoeff]
    _ = mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst (b • m) := by
          simpa using base_scalar_smul_mk_one_eq (f := f) (X := X) b m

/-- Helper for 15.91.16.1: the remaining pure `R'`-scalar transport branch of the overlap
argument is the only unresolved range-membership step. -/
private theorem beauvilleLaszloGlueingDifferential_range_contains_rscalar_transport
    (hpair : GlueingPair) (r : R') (x : ↑X.snd) :
    overlapTensorToAway f X
        ((extendToOverlapIso f X).hom
          (X.iso.inv (((algebraMap R' R'f r : R'f) • ((1 : R'f) ⊗ₜ[Rf] x))))) ∈
      LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
  -- Route correction: normalize the `R'`-scalar branch by choosing one denominator for `α₁(x)`,
  -- split `r` modulo that power of `f`, and send the two summands to the side and base witnesses.
  have hscalar :
      overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv (((algebraMap R' R'f r : R'f) • ((1 : R'f) ⊗ₜ[Rf] x))))) =
        (algebraMap R' R'f r : R'f) • beauvilleLaszloGlueingLocalizedSideMap f X x := by
    rw [beauvilleLaszloGlueingLocalizedSideMap_apply_eq]
    calc
      overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv (((algebraMap R' R'f r : R'f) • ((1 : R'f) ⊗ₜ[Rf] x))))) =
        overlapTensorToAway f X
          ((algebraMap R' R'f r : R'f) •
            ((extendToOverlapIso f X).hom (X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x)))) := by
              rw [← map_smul, ← map_smul]
              rfl
      _ = (algebraMap R' R'f r : R'f) •
            overlapTensorToAway f X
              ((extendToOverlapIso f X).hom (X.iso.inv ((1 : R'f) ⊗ₜ[Rf] x))) := by
              exact (overlapTensorToAway f X).map_smul _ _
  rw [hscalar]
  rcases
      beauvilleLaszloGlueingLocalizedSideMap_exists_power_denominator (f := f) (X := X) x with
    ⟨n, m, hx⟩
  rcases rprime_eq_base_add_fpow_mul (f := f) hpair r n with ⟨a, b, hab⟩
  have ha_comm :
      (algebraMap R' R'f (algebraMap R R' a) : R'f) =
        ((awayMapToOverlap f) (algebraMap R Rf a) : R'f) := by
    exact congrArg (fun g : R →+* R'f ↦ g a)
      (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)
  have ha :
      (algebraMap R' R'f (algebraMap R R' a) : R'f) •
          beauvilleLaszloGlueingLocalizedSideMap f X x ∈
        LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
    rw [ha_comm, away_scalar_smul_localizedSideMap_eq]
    exact beauvilleLaszloGlueingDifferential_range_contains_side_map
      (f := f) (X := X) ((algebraMap R Rf a) • x)
  have hb_eq :
      (algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) •
          beauvilleLaszloGlueingLocalizedSideMap f X x =
        mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst (b • m) :=
    fpow_mul_localized_side_eq_base_generator
      (f := f) (X := X) (x := x) (m := m) (b := b) (n := n) hx
  have hb :
      (algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) •
          beauvilleLaszloGlueingLocalizedSideMap f X x ∈
        LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
    rw [hb_eq]
    exact beauvilleLaszloGlueingDifferential_range_contains_base_generator
      (f := f) (X := X) (b • m)
  have hsplit :
      (algebraMap R' R'f r : R'f) • beauvilleLaszloGlueingLocalizedSideMap f X x =
        (algebraMap R' R'f (algebraMap R R' a) : R'f) •
            beauvilleLaszloGlueingLocalizedSideMap f X x +
          (algebraMap R' R'f (((algebraMap R R' f) ^ n) * b) : R'f) •
            beauvilleLaszloGlueingLocalizedSideMap f X x := by
    rw [hab, map_add, add_smul]
  rw [hsplit]
  exact Submodule.add_mem _ ha hb

/-- Helper for 15.91.16.1: once the overlap coefficient is split as an `R'` part minus an `R_f`
part, each branch can be sent to the differential range separately. -/
private theorem beauvilleLaszloGlueingDifferential_range_contains_split_coefficient
    (hpair : GlueingPair) (r : R') (y : Rf) (x : ↑X.snd) :
    overlapTensorToAway f X
        ((extendToOverlapIso f X).hom
          (X.iso.inv
            ((((algebraMap R' R'f r : R'f) - ((awayMapToOverlap f) y : R'f)) ⊗ₜ[Rf] x)))) ∈
      LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
  -- Handle the `R'` contribution by the isolated scalar-transport lemma.
  have hr :
      overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv (((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x)))) ∈
        LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
    have hr_scalar :
        overlapTensorToAway f X
            ((extendToOverlapIso f X).hom
              (X.iso.inv (((algebraMap R' R'f r : R'f) • ((1 : R'f) ⊗ₜ[Rf] x))))) ∈
          LinearMap.range (beauvilleLaszloGlueingDifferential f X) :=
      beauvilleLaszloGlueingDifferential_range_contains_rscalar_transport
        (f := f) (X := X) hpair r x
    simpa [TensorProduct.smul_tmul', Algebra.smul_def, one_mul] using
      hr_scalar
  -- Rewrite the `R_f` contribution back into the side component and use its explicit witness.
  have hy :
      overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv ((((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x)))) ∈
        LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
    have hy_side_base :
        beauvilleLaszloGlueingLocalizedSideMap f X (y • x) ∈
          LinearMap.range (beauvilleLaszloGlueingDifferential f X) :=
      beauvilleLaszloGlueingDifferential_range_contains_side_map
        (f := f) (X := X) (y • x)
    have hy_side :
        ((awayMapToOverlap f) y : R'f) • beauvilleLaszloGlueingLocalizedSideMap f X x ∈
          LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
      rw [away_scalar_smul_localizedSideMap_eq]
      exact hy_side_base
    simpa [beauvilleLaszloGlueingLocalizedSideMap_smul_eq] using hy_side
  -- Expand the split coefficient additively and use range closure under subtraction.
  have htensor :
      (((algebraMap R' R'f r : R'f) - ((awayMapToOverlap f) y : R'f)) ⊗ₜ[Rf] x) =
        ((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x) -
          (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x) := by
    calc
      (((algebraMap R' R'f r : R'f) - ((awayMapToOverlap f) y : R'f)) ⊗ₜ[Rf] x) =
          (((algebraMap R' R'f r : R'f) + -((awayMapToOverlap f) y : R'f)) ⊗ₜ[Rf] x) := by
        rfl
      _ = ((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x) +
            ((-((awayMapToOverlap f) y : R'f)) ⊗ₜ[Rf] x) := by
        rw [TensorProduct.add_tmul]
      _ = ((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x) -
            (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x) := by
        rw [sub_eq_add_neg]
        congr 1
  have himage :
      overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv
              ((((algebraMap R' R'f r : R'f) - ((awayMapToOverlap f) y : R'f)) ⊗ₜ[Rf] x)))) =
        overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv
              (((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x) -
                (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x)))) := by
    exact congrArg
      (fun z ↦
        overlapTensorToAway f X ((extendToOverlapIso f X).hom (X.iso.inv z)))
      htensor
  let A : R'f ⊗[Rf] ↑X.snd := (algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x
  let B : R'f ⊗[Rf] ↑X.snd := ((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x
  have hsub₁ :
      X.iso.inv (A - B) = X.iso.inv A - X.iso.inv B := by
    exact (ModuleCat.Hom.hom X.iso.inv).map_sub A B
  have hsub₂ :
      (extendToOverlapIso f X).hom (X.iso.inv (A - B)) =
        (extendToOverlapIso f X).hom (X.iso.inv A) -
          (extendToOverlapIso f X).hom (X.iso.inv B) := by
    rw [hsub₁]
    simpa using
      (map_sub
        ((extendToOverlapIso f X).hom :
          (extendToOverlap).obj X.fst →ₗ[R'f] ModuleCat.of R'f (R'f ⊗[R'] ↑X.fst))
        (X.iso.inv A) (X.iso.inv B))
  have hsub :
      overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv
              (((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x) -
                (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x)))) =
        overlapTensorToAway f X
          ((extendToOverlapIso f X).hom
            (X.iso.inv ((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x))) -
          overlapTensorToAway f X
            ((extendToOverlapIso f X).hom
              (X.iso.inv (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x))) := by
    rw [show
        (((algebraMap R' R'f r : R'f) ⊗ₜ[Rf] x) -
            (((awayMapToOverlap f) y : R'f) ⊗ₜ[Rf] x)) = A - B by rfl]
    rw [hsub₂, LinearMap.map_sub]
    rfl
  rw [himage, hsub]
  exact Submodule.sub_mem _ hr hy

/-- Helper for 15.91.16.1: transporting a side-overlap tensor across the pullback isomorphism
produces an element of the differential range. -/
private theorem beauvilleLaszloGlueingDifferential_range_contains_transport
    (hpair : GlueingPair) (w : R'f ⊗[Rf] ↑X.snd) :
    overlapTensorToAway f X ((extendToOverlapIso f X).hom (X.iso.inv w)) ∈
      LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
  -- Route correction: the outer argument is now a clean tensor induction, with the stubborn
  -- `R'`-scalar branch delegated to a dedicated helper lemma.
  induction w using TensorProduct.induction_on with
  | zero =>
      -- The transported zero tensor is hit by the zero vector in the source.
      refine LinearMap.mem_range.mpr ⟨0, ?_⟩
      symm
      have hzero₁ :
          X.iso.inv (0 : R'f ⊗[Rf] ↑X.snd) = 0 := by
        exact (ModuleCat.Hom.hom X.iso.inv).map_zero
      have hzero₂ :
          (extendToOverlapIso f X).hom (X.iso.inv (0 : R'f ⊗[Rf] ↑X.snd)) = 0 := by
        rw [hzero₁]
        simpa using
          (map_zero
            ((extendToOverlapIso f X).hom :
              (extendToOverlap).obj X.fst →ₗ[R'f] ModuleCat.of R'f (R'f ⊗[R'] ↑X.fst)))
      rw [hzero₂]
      simpa using (LinearMap.map_zero (overlapTensorToAway f X))
  | tmul a x =>
      -- Split the overlap coefficient by surjectivity of the ring-level Cech map, then invoke the
      -- adapter lemma for an already-split coefficient.
      rcases (beauvilleLaszloCechRightMap_surjective (R := R) (R' := R') (f := f) hpair a) with
        ⟨⟨r, y⟩, hsplit⟩
      have hcoeff :
          a = (algebraMap R' R'f r : R'f) - ((awayMapToOverlap f) y : R'f) := by
        simpa [beauvilleLaszloCechRightMapLocal, awayMapToOverlap, LinearMap.comp_apply] using
          hsplit.symm
      have hsplit_range :
          overlapTensorToAway f X
              ((extendToOverlapIso f X).hom
                (X.iso.inv
                  ((((algebraMap R' R'f r : R'f) - ((awayMapToOverlap f) y : R'f)) ⊗ₜ[Rf] x)))) ∈
            LinearMap.range (beauvilleLaszloGlueingDifferential f X) :=
        beauvilleLaszloGlueingDifferential_range_contains_split_coefficient
          (f := f) (X := X) hpair r y x
      simpa [hcoeff] using
        hsplit_range
  | add w₁ w₂ hw₁ hw₂ =>
      -- Add witnesses for the two summands to obtain a witness for the transported sum.
      rcases LinearMap.mem_range.mp hw₁ with ⟨z₁, hz₁⟩
      rcases LinearMap.mem_range.mp hw₂ with ⟨z₂, hz₂⟩
      refine LinearMap.mem_range.mpr ⟨z₁ + z₂, ?_⟩
      rw [LinearMap.map_add, hz₁, hz₂]
      have hXadd :
          X.iso.inv (w₁ + w₂) = X.iso.inv w₁ + X.iso.inv w₂ := by
        exact (ModuleCat.Hom.hom X.iso.inv).map_add w₁ w₂
      have hextadd :
          (extendToOverlapIso f X).hom (X.iso.inv (w₁ + w₂)) =
            (extendToOverlapIso f X).hom (X.iso.inv w₁) +
              (extendToOverlapIso f X).hom (X.iso.inv w₂) := by
        rw [hXadd]
        exact (ModuleCat.Hom.hom ((extendToOverlapIso f X).hom)).map_add _ _
      calc
        overlapTensorToAway f X
            ((extendToOverlapIso f X).hom (X.iso.inv w₁)) +
            overlapTensorToAway f X
              ((extendToOverlapIso f X).hom (X.iso.inv w₂)) =
          overlapTensorToAway f X
            ((extendToOverlapIso f X).hom (X.iso.inv w₁) +
              (extendToOverlapIso f X).hom (X.iso.inv w₂)) := by
              rw [← LinearMap.map_add]
        _ = overlapTensorToAway f X
              ((extendToOverlapIso f X).hom (X.iso.inv (w₁ + w₂))) := by
              rw [← hextadd]

/-- Helper for 15.91.16.1: every localized generator of `(X.fst)_f` has a preimage under the
Beauville-Laszlo differential once the ring-level Cech map is surjective. -/
private theorem beauvilleLaszloGlueingDifferential_preimage_of_generator
    (hpair : GlueingPair) (m : ↑X.fst) (s : Submonoid.powers (algebraMap R R' f)) :
    ∃ z : ↑X.fst × ↑X.snd,
      beauvilleLaszloGlueingDifferential f X z = LocalizedModule.mk m s := by
  -- Transport the target localized generator to the side-overlap tensor, then extract a witness
  -- from the differential-range statement for transported side tensors.
  let w : R'f ⊗[Rf] ↑X.snd :=
    X.iso.hom
      ((extendToOverlapIso f X).inv (((Localization.mk (1 : R') s : R'f) ⊗ₜ[R'] m)))
  have hw :
      overlapTensorToAway f X ((extendToOverlapIso f X).hom (X.iso.inv w)) ∈
        LinearMap.range (beauvilleLaszloGlueingDifferential f X) :=
    beauvilleLaszloGlueingDifferential_range_contains_transport
      (f := f) (X := X) hpair w
  have hmk :
      LocalizedModule.mk m s ∈ LinearMap.range (beauvilleLaszloGlueingDifferential f X) := by
    -- The chosen transport collapses back to the pure tensor representing `LocalizedModule.mk m s`.
    simpa [w, overlapTensorToAway_apply_tmul, one_smul] using hw
  rcases LinearMap.mem_range.mp hmk with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- 15.91.16.1: if `(R → R', f)` is a Beauville-Laszlo glueing pair and `X` is a single
Beauville-Laszlo pullback datum, then the sequence
`0 → H⁰ → X.fst ⊕ X.snd → (X.fst)_f → 0` is short exact. In Lean, the binary direct sum is
written as `X.fst × X.snd`, and the canonical owner is the kernel short complex
`(beauvilleLaszloGlueingDifferential f X).shortComplexKer`. -/
theorem beauvilleLaszloGlueingH0_shortExact
    (hpair : GlueingPair) :
    (beauvilleLaszloGlueingDifferential f X).shortComplexKer.ShortExact := by
  -- Reduce short exactness to surjectivity of the differential and build preimages on the
  -- localization generators.
  apply LinearMap.shortExact_shortComplexKer
  intro z
  induction z using LocalizedModule.induction_on with
  | h m s =>
      exact beauvilleLaszloGlueingDifferential_preimage_of_generator
        (f := f) (X := X) hpair m s

end

end
