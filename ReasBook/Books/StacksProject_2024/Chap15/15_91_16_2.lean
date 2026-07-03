import StacksProject_2024.Chap15.«15_91_16_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule (Away mkLinearMap)
open scoped IdealPowerTorsion

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (f : R)
local notation "Rf" => Localization.Away f
local notation "R'f" => Localization.Away (algebraMap R R' f)

private abbrev awayMapToOverlap : Rf →+* R'f :=
  Localization.awayMap (algebraMap R R') f

/- 
Domain-style sampling:
* primary domain: the Beauville-Laszlo mod-torsion quotient sequence attached to a single
  Beauville-Laszlo pullback datum `X`;
* sampled owner declarations:
  `beauvilleLaszloGlueingLocalizedSideMap`,
  `mkLinearMap`,
  `Submodule.liftQ`,
  `Submodule.mkQ`,
  `beauvilleLaszloGlueingH0`,
  `ModuleCat.shortComplexOfCompEqZero`;
* best owner abstraction: the primitive datum is the single pullback object
  `X : Mod_{R'} ×_{Mod_{R'_f}} Mod_{R_f}`; the quotient sequence is derived from the kernel owner
  `beauvilleLaszloGlueingH0 f X`, its canonical principal-power torsion submodule
  `(beauvilleLaszloGlueingH0 f X)[f^∞]`, and the canonical quotient-map owners
  `Submodule.liftQ` and `Submodule.mkQ` applied to the two canonical maps out of `X`;
* primitive data: `X` and the canonical maps already exposed by `15.91.16.1`;
* derived API: the quotient terms as direct canonical quotient expressions, the induced short
  complex, and its short exactness;
* source/core/bridge triage:
  `source-facing`: `beauvilleLaszloModTorsionSequence`,
    `beauvilleLaszloModTorsion_shortExact`;
  `core/canonical`: the pullback owner `X`, `beauvilleLaszloGlueingH0`,
    `LocalizedModule.mkLinearMap`, `beauvilleLaszloGlueingLocalizedSideMap`;
  `bridge/view`: the direct component projections
    `(beauvilleLaszloModTorsionSequence f X).f.hom` and
    `(beauvilleLaszloModTorsionSequence f X).g.hom`, exposing the canonical arrows from the short
    complex owner.
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
local instance : IsScalarTower R Rf ↑X.snd := IsScalarTower.of_compHom R Rf ↑X.snd
local instance : Algebra Rf R'f := (awayMapToOverlap f).toAlgebra
local instance : IsScalarTower R R' (Away (algebraMap R R' f) ↑X.fst) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simpa
local notation "Sf" => Submonoid.powers (algebraMap R R' f)
local instance : Module R (Away (algebraMap R R' f) ↑X.fst) :=
  inferInstance

private abbrev h0
    (f : R)
    (X :
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
        (ModuleCat.extendScalars (awayMapToOverlap f))) :
    Submodule R (↑X.fst × ↑X.snd) :=
  beauvilleLaszloGlueingH0 f X

private abbrev h0Tors
    (f : R)
    (X :
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
        (ModuleCat.extendScalars (awayMapToOverlap f))) :
    Submodule R (h0 f X) :=
  (Submodule.torsion' R (h0 f X) (Submonoid.powers f) : Submodule R (h0 f X))

/-- The canonical image of `X.fst` inside the localized overlap module `(X.fst)_f`. This is the
submodule by which the Beauville-Laszlo mod-torsion sequence quotients on the right, and later
base-change statements should reuse this owner rather than rebuilding the same range locally. -/
abbrev beauvilleLaszloGlueingLocalizedBaseRange
    (f : R)
    (X :
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
        (ModuleCat.extendScalars (awayMapToOverlap f))) :
    Submodule R' (Away (algebraMap R R' f) ↑X.fst) :=
  LinearMap.range (mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst)

-- Proof sketch: if an element of `H⁰` is killed by a power of `f`, then its image in `X.snd` is
-- also killed by a power of `f`. Since `X.snd` is an `R_f`-module, multiplication by `f` is
-- invertible there, so the image must vanish.
/-- The projection `H⁰ → X.snd` kills the `f^∞`-torsion of `H⁰`. -/
private theorem beauvilleLaszloGlueingH0_fPowerTorsion_le_ker_snd :
    h0Tors f X ≤
      LinearMap.ker
        ((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype) := by
  sorry

-- Proof sketch: for `x ∈ H⁰`, the defining relation `d(x) = 0` says exactly that the image of
-- the `X.snd`-component in `(X.fst)_f` lies in the image of `X.fst`. Hence its class in the
-- quotient is zero, and passing to `H⁰ / H⁰[f^∞]` preserves that vanishing.
/-- The canonical Beauville-Laszlo mod-torsion maps form a complex. -/
private theorem beauvilleLaszloModTorsion_comp_eq_zero :
    (((beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R).mkQ.comp
        (beauvilleLaszloGlueingLocalizedSideMap f X)).comp
        ((h0Tors f X).liftQ
          ((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype)
          (beauvilleLaszloGlueingH0_fPowerTorsion_le_ker_snd f X)) =
      (0 :
        h0 f X ⧸ h0Tors f X →ₗ[R]
          Away (algebraMap R R' f) ↑X.fst ⧸
            (beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R) := by
  sorry

/- The Beauville-Laszlo mod-torsion sequence is source-facing, but its canonical owner is the
short complex built from the quotient map `H⁰ / H⁰[f^∞] → X.snd` and the localization quotient map
`X.snd → (X.fst)_f / X.fst`. -/
/-- The Beauville-Laszlo mod-torsion sequence attached to `X`, viewed in the canonical owner
`ShortComplex (ModuleCat R)`. -/
noncomputable def beauvilleLaszloModTorsionSequence :
    ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero
    ((h0Tors f X).liftQ
      ((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype)
      (beauvilleLaszloGlueingH0_fPowerTorsion_le_ker_snd f X))
    (((beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R).mkQ.comp
      (beauvilleLaszloGlueingLocalizedSideMap f X))
    (beauvilleLaszloModTorsion_comp_eq_zero f X)

-- Proof sketch: the left map is induced from the projection `H⁰ → X.snd` after quotienting by the
-- maximal `f`-power-torsion submodule of `H⁰`. Its kernel is trivial, its image is the kernel of
-- the right map, and the right map is surjective onto `(X.fst)_f / X.fst`.
/-- 15.91.16.2: the canonical Beauville-Laszlo mod-torsion maps form a short exact sequence
`0 → H⁰ / H⁰[f^∞] → X.snd → (X.fst)_f / X.fst → 0`. -/
theorem beauvilleLaszloModTorsion_shortExact
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModTorsionSequence f X).ShortExact := by
  letI := hpair
  refine ModuleCat.shortComplex_shortExact (beauvilleLaszloModTorsionSequence f X) ?_ ?_ ?_
  · change Function.Exact
      (beauvilleLaszloModTorsionSequence f X).f.hom
      (beauvilleLaszloModTorsionSequence f X).g.hom
    sorry
  · change Function.Injective (beauvilleLaszloModTorsionSequence f X).f.hom
    sorry
  · change Function.Surjective (beauvilleLaszloModTorsionSequence f X).g.hom
    sorry

end

end
