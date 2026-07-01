import stacks_project.Chap15.«15_91_16_2»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule (Away mkLinearMap)
open scoped IdealPowerTorsion
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (f : R)

private abbrev awayMapToOverlap :
    Localization.Away f →+* Localization.Away (algebraMap R R' f) :=
  Localization.awayMap (algebraMap R R') f

/- 
Domain-style sampling for 15.91.16.3:
* primary domain: the Beauville-Laszlo mod-torsion exact sequence after base change;
* inspected owner declarations:
  `beauvilleLaszloModTorsionSequence`,
  `beauvilleLaszloGlueingLocalizedSideMap`,
  `(beauvilleLaszloModTorsionSequence f X).f.hom`,
  `LinearMap.baseChange`,
  `LinearMap.liftBaseChange`;
* best owner abstraction: the primitive datum is again the single pullback object `X`; the
  base-changed sequence is a source-facing bridge/view built from the canonical base-changed left
  map `R' ⊗[R] (H⁰ / H⁰[f^∞]) → (X.fst)_f` and the canonical localization quotient map with
  target `(X.fst)_f / X.fst`;
* primitive data: `X`, the glueing-pair hypothesis `hpair`, and the canonical maps from
  `15.91.16.1`-`15.91.16.2`;
* derived API: the canonical comparison map
  `R' ⊗[R] (beauvilleLaszloGlueingH0 f X ⧸ (beauvilleLaszloGlueingH0 f X)[f^∞]) → (X.fst)_f`,
  built from the owner declaration `beauvilleLaszloGlueingLocalizedSideMap`, the induced left
  base-change map from `(beauvilleLaszloModTorsionSequence f X).f.hom`, and the source-facing
  displayed `ShortComplex (ModuleCat R')`;
* source/core/bridge triage:
  `source-facing`: the base-changed short exact sequence itself;
  `core/canonical`: `beauvilleLaszloModTorsionSequence`,
    `mkLinearMap`, and the direct quotient `(X.fst)_f / X.fst`;
  `bridge/view`: the canonical comparison map from
    `R' ⊗[R] (beauvilleLaszloGlueingH0 f X ⧸ (beauvilleLaszloGlueingH0 f X)[f^∞])` to
    `(X.fst)_f` and the resulting displayed `ShortComplex (ModuleCat R')`.
-/

section

variable
  (X :
    CategoricalPullback
      (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
      (ModuleCat.extendScalars (awayMapToOverlap f)))

local instance : Module R ↑X.fst := Module.compHom (↑X.fst) (algebraMap R R')
local instance : Module R ↑X.snd := Module.compHom (↑X.snd) (algebraMap R (Localization.Away f))
local instance : IsScalarTower R R' ↑X.fst := IsScalarTower.of_compHom R R' ↑X.fst
local instance : IsScalarTower R (Localization.Away f) ↑X.snd :=
  IsScalarTower.of_compHom R (Localization.Away f) ↑X.snd
local instance : Algebra (Localization.Away f) (Localization.Away (algebraMap R R' f)) :=
  (awayMapToOverlap f).toAlgebra
local instance : IsScalarTower R R' (Away (algebraMap R R' f) ↑X.fst) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simpa
local notation "Sf" => Submonoid.powers (algebraMap R R' f)
local instance : Module R (Away (algebraMap R R' f) ↑X.fst) :=
  inferInstance

/-- The image of the base Beauville-Laszlo left map in the localized overlap lies in the canonical
localized-base range. This is extracted from the owner equation
`(beauvilleLaszloModTorsionSequence f X).zero`, whose quotient is taken over the same underlying
subset after restricting scalars from `R'` to `R`. -/
private theorem beauvilleLaszloModTorsion_left_mem_range
    (x : ↑((beauvilleLaszloModTorsionSequence f X).X₁)) :
    beauvilleLaszloGlueingLocalizedSideMap f X
        ((beauvilleLaszloModTorsionSequence f X).f.hom x) ∈
      beauvilleLaszloGlueingLocalizedBaseRange f X := by
  sorry

-- Proof sketch: evaluate on pure tensors. The preceding range lemma turns the quotient term into
-- zero, and additivity then gives the result on all tensors.
private theorem beauvilleLaszloModTorsionBaseChange_comp_eq_zero :
    (beauvilleLaszloGlueingLocalizedBaseRange f X).mkQ.comp
        (((beauvilleLaszloGlueingLocalizedSideMap f X).liftBaseChange R').comp
          ((beauvilleLaszloModTorsionSequence f X).f.hom.baseChange R')) =
      (0 :
        R' ⊗[R] ↑((beauvilleLaszloModTorsionSequence f X).X₁) →ₗ[R']
          LocalizedModule Sf ↑X.fst ⧸ beauvilleLaszloGlueingLocalizedBaseRange f X) := by
  sorry

/- The source-facing owner is the short complex whose middle term is already the canonical
localized module `(X.fst)_f`; the tensorized complex from `15.91.16.2` is only a bridge/view
used in the proof of short exactness, and the component maps should be read directly from the
owner as `.f.hom` and `.g.hom`. -/
/-- The base-changed Beauville-Laszlo mod-torsion sequence attached to `X`, viewed in the
canonical owner `ShortComplex (ModuleCat R')`. -/
noncomputable def beauvilleLaszloModTorsionBaseChangeSequence :
    ShortComplex (ModuleCat R') :=
  ModuleCat.shortComplexOfCompEqZero
    (((beauvilleLaszloGlueingLocalizedSideMap f X).liftBaseChange R').comp
      ((beauvilleLaszloModTorsionSequence f X).f.hom.baseChange R'))
    (beauvilleLaszloGlueingLocalizedBaseRange f X).mkQ
    (beauvilleLaszloModTorsionBaseChange_comp_eq_zero f X)

-- Proof sketch: tensor the short exact sequence from `15.91.16.2` with `R'`; the Tor-vanishing
-- and torsion comparison results rewrite the tensorized sequence canonically as
-- `0 → R' ⊗[R] (H⁰ / H⁰[f^∞]) → (X.fst)_f → (X.fst)_f / X.fst → 0`.
/-- 15.91.16.3: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the tensor of the
sequence from `15.91.16.2` is canonically the short exact sequence
`0 → R' ⊗[R] (H⁰ / H⁰[f^∞]) → (X.fst)_f → (X.fst)_f / X.fst → 0`. -/
theorem beauvilleLaszloModTorsionBaseChange_shortExact
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModTorsionBaseChangeSequence f X).ShortExact := by
  letI := hpair
  sorry

end

end
