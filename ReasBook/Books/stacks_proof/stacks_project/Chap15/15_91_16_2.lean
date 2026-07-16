import stacks_proof.stacks_project.Chap15.«15_91_16_1»
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule (Away mkLinearMap)

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

/-- Helper for 15.91.16.2: the domain type of a dependent function. -/
private abbrev pi_domain
    {α : Sort _} {β : α → Sort _} (_ : ∀ a, β a) : Sort _ :=
  α

/-- Helper for 15.91.16.2: the imported glueing-pair hypothesis required to apply
`beauvilleLaszloGlueingH0_shortExact` to the datum `X`. -/
private abbrev beauvilleLaszloGlueingH0ShortExactHypothesis
    (f : R)
    (X :
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
        (ModuleCat.extendScalars (awayMapToOverlap f))) :
    Sort _ :=
  pi_domain (@beauvilleLaszloGlueingH0_shortExact R _ R' _ _ f X)

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

/-- Helper for 15.91.16.2: an element of the localized-side module comes from the base range
exactly when it extends to an `H⁰` pair. -/
private theorem beauvilleLaszloGlueingLocalizedSideMap_mem_baseRange_iff
    {x : ↑X.snd} :
    beauvilleLaszloGlueingLocalizedSideMap f X x ∈
        (beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R ↔
      ∃ x' : ↑X.fst, ((x', x) : ↑X.fst × ↑X.snd) ∈ h0 f X := by
  constructor
  · rintro ⟨x', hx'⟩
    refine ⟨x', ?_⟩
    -- Membership in `H⁰` is exactly the vanishing of the Beauville-Laszlo differential.
    change beauvilleLaszloGlueingDifferential f X (x', x) = 0
    simp [beauvilleLaszloGlueingDifferential, LinearMap.coprod_apply, hx']
  · rintro ⟨x', hx'⟩
    refine ⟨x', ?_⟩
    -- Unfold the kernel condition and solve for the localized-side component.
    have hx'' : mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst x' -
        beauvilleLaszloGlueingLocalizedSideMap f X x = 0 := by
      change beauvilleLaszloGlueingDifferential f X (x', x) = 0 at hx'
      simpa [beauvilleLaszloGlueingDifferential, LinearMap.coprod_apply, sub_eq_add_neg] using hx'
    exact sub_eq_zero.mp hx''

-- Proof sketch: if an element of `H⁰` is killed by a power of `f`, then its image in `X.snd` is
-- also killed by a power of `f`. Since `X.snd` is an `R_f`-module, multiplication by `f` is
-- invertible there, so the image must vanish.
/-- The projection `H⁰ → X.snd` kills the `f^∞`-torsion of `H⁰`. -/
private theorem beauvilleLaszloGlueingH0_fPowerTorsion_le_ker_snd :
    h0Tors f X ≤
      LinearMap.ker
        ((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype) := by
  intro z hz
  rw [LinearMap.mem_ker]
  rw [Submodule.mem_torsion'_iff] at hz
  rcases hz with ⟨a, ha⟩
  have hsnd :
      (a : R) • (((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype) z) = 0 := by
    -- Apply the second projection to the torsion relation in `H⁰`.
    simpa [LinearMap.comp_apply] using
      congrArg (((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype)) ha
  have hsnd' :
      (algebraMap R Rf (a : R)) •
          (((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype) z) =
        0 := by
    simpa [Algebra.smul_def] using hsnd
  have hsnd0 :
      (algebraMap R Rf (a : R)) •
          (((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype) z) =
        (algebraMap R Rf (a : R)) • (0 : ↑X.snd) := by
    simpa using hsnd'
  -- The scalar corresponding to a power of `f` is a unit in `R_f`, so it cancels.
  exact (IsUnit.smul_left_cancel (IsLocalization.map_units Rf a)).mp hsnd0

/-- Helper for 15.91.16.2: the projection from `H⁰` to the localized-side module `X.snd`. -/
private abbrev beauvilleLaszloGlueingH0Snd :
    h0 f X →ₗ[R] ↑X.snd :=
  (LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype

/-- Helper for 15.91.16.2: if the second component of an `H⁰` pair vanishes, then that pair is
`f^∞`-torsion. -/
private theorem beauvilleLaszloGlueingH0_ker_snd_le_fPowerTorsion :
    LinearMap.ker (beauvilleLaszloGlueingH0Snd f X) ≤ h0Tors f X := by
  intro z hz
  rw [Submodule.mem_torsion'_iff]
  have hz_snd : z.1.2 = 0 := by
    simpa [LinearMap.comp_apply] using hz
  have hz_fst :
      mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst z.1.1 = 0 := by
    -- With zero second component, the defining `H⁰` relation says the first component localizes
    -- to zero.
    have hz_h0 : beauvilleLaszloGlueingDifferential f X z.1 = 0 := z.2
    have hz_h0' :
        mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst z.1.1 +
          -(beauvilleLaszloGlueingLocalizedSideMap f X z.1.2) =
        0 := by
      exact hz_h0
    have hz_fst_zero :
        mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst z.1.1 = 0 := by
      simpa [hz_snd] using hz_h0'
    exact hz_fst_zero
  have hz_mem_ker :
      z.1.1 ∈ LinearMap.ker (mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst) := by
    simpa [LinearMap.mem_ker] using hz_fst
  rcases (LocalizedModule.mem_ker_mkLinearMap_iff
      (S := Submonoid.powers (algebraMap R R' f)) (m := z.1.1)).mp hz_mem_ker with
    ⟨r, hr, hrz⟩
  rcases hr with ⟨n, rfl⟩
  refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  -- The same power kills the first component, while the second component is already zero.
  change (f ^ n : R) • z.1 = 0
  ext
  · change (algebraMap R R' (f ^ n)) • z.1.1 = 0
    simpa [map_pow] using hrz
  · simp [hz_snd]

/-- Helper for 15.91.16.2: the left quotient map `H⁰ / H⁰[f^∞] → X.snd`. -/
private abbrev beauvilleLaszloModTorsionLeftMap :
    h0 f X ⧸ h0Tors f X →ₗ[R] ↑X.snd :=
  (h0Tors f X).liftQ
    (beauvilleLaszloGlueingH0Snd f X)
    (beauvilleLaszloGlueingH0_fPowerTorsion_le_ker_snd f X)

/-- Helper for 15.91.16.2: the right quotient map `X.snd → (X.fst)_f / X.fst`. -/
private abbrev beauvilleLaszloLocalizedBaseMkQ :
    Away (algebraMap R R' f) ↑X.fst →ₗ[R]
      Away (algebraMap R R' f) ↑X.fst ⧸
        (beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R :=
  ((beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R).mkQ

/-- Helper for 15.91.16.2: the right quotient map `X.snd → (X.fst)_f / X.fst`. -/
private abbrev beauvilleLaszloModTorsionRightMap :
    ↑X.snd →ₗ[R]
      Away (algebraMap R R' f) ↑X.fst ⧸
        (beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R :=
  (beauvilleLaszloLocalizedBaseMkQ f X).comp
    (beauvilleLaszloGlueingLocalizedSideMap f X)

-- Proof sketch: for `x ∈ H⁰`, the defining relation `d(x) = 0` says exactly that the image of
-- the `X.snd`-component in `(X.fst)_f` lies in the image of `X.fst`. Hence its class in the
-- quotient is zero, and passing to `H⁰ / H⁰[f^∞]` preserves that vanishing.
/-- The canonical Beauville-Laszlo mod-torsion maps form a complex. -/
private theorem beauvilleLaszloModTorsion_comp_eq_zero :
    (beauvilleLaszloModTorsionRightMap f X).comp
        (beauvilleLaszloModTorsionLeftMap f X) =
      (0 :
        h0 f X ⧸ h0Tors f X →ₗ[R]
          Away (algebraMap R R' f) ↑X.fst ⧸
            (beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R) := by
  apply (LinearMap.cancel_right (g := (h0Tors f X).mkQ)
    (f := (beauvilleLaszloModTorsionRightMap f X).comp (beauvilleLaszloModTorsionLeftMap f X))
    (f' := 0) (Submodule.mkQ_surjective (h0Tors f X))).mp
  rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ]
  ext z
  -- Reduce the quotient statement to the representative in `H⁰`.
  change beauvilleLaszloLocalizedBaseMkQ f X
      (beauvilleLaszloGlueingLocalizedSideMap f X z.1.2) = 0
  simpa [beauvilleLaszloLocalizedBaseMkQ] using
    (Submodule.Quotient.mk_eq_zero
      ((beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R)).2 <|
      (beauvilleLaszloGlueingLocalizedSideMap_mem_baseRange_iff (f := f) (X := X)).2
        ⟨z.1.1, z.2⟩

/- The Beauville-Laszlo mod-torsion sequence is source-facing, but its canonical owner is the
short complex built from the quotient map `H⁰ / H⁰[f^∞] → X.snd` and the localization quotient map
`X.snd → (X.fst)_f / X.fst`. -/
/-- The Beauville-Laszlo mod-torsion sequence attached to `X`, viewed in the canonical owner
`ShortComplex (ModuleCat R)`. -/
noncomputable def beauvilleLaszloModTorsionSequence :
    ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero
    (beauvilleLaszloModTorsionLeftMap f X)
    (beauvilleLaszloModTorsionRightMap f X)
    (beauvilleLaszloModTorsion_comp_eq_zero f X)

/-- Helper for 15.91.16.2: the quotient Beauville-Laszlo maps are exact in the middle term. -/
private theorem beauvilleLaszloModTorsion_middle_exact :
    Function.Exact
      (beauvilleLaszloModTorsionLeftMap f X)
      (beauvilleLaszloModTorsionRightMap f X) := by
  -- Route correction: after the earlier `H⁰` short exact sequence is available, the source proof
  -- identifies the kernel of the quotient-right map by lifting a representative back to `H⁰`.
  refine LinearMap.exact_of_comp_of_mem_range
    (beauvilleLaszloModTorsion_comp_eq_zero f X) ?_
  intro x hx
  have hx_mem :
      beauvilleLaszloGlueingLocalizedSideMap f X x ∈
        (beauvilleLaszloGlueingLocalizedBaseRange f X).restrictScalars R := by
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  rcases (beauvilleLaszloGlueingLocalizedSideMap_mem_baseRange_iff
      (f := f) (X := X) (x := x)).1 hx_mem with ⟨x', hx'⟩
  refine ⟨Submodule.Quotient.mk ⟨(x', x), hx'⟩, ?_⟩
  -- The constructed `H⁰` class maps back to the chosen middle-term element.
  change ((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype) ⟨(x', x), hx'⟩ = x
  simp [LinearMap.comp_apply]

/-- Helper for 15.91.16.2: quotienting `H⁰` by its `f^∞`-torsion kills exactly the kernel of the
projection to `X.snd`, so the induced left map is injective. -/
private theorem beauvilleLaszloModTorsion_left_injective :
    Function.Injective (beauvilleLaszloModTorsionLeftMap f X) := by
  -- The quotient is by the full kernel of `H⁰ → X.snd`, hence the induced map has trivial kernel.
  exact LinearMap.ker_eq_bot.mp <|
    Submodule.ker_liftQ_eq_bot _ _ _
      (beauvilleLaszloGlueingH0_ker_snd_le_fPowerTorsion f X)

/-- Helper for 15.91.16.2: the right quotient map is surjective once the preceding `H⁰`
short exact sequence is available. -/
private theorem beauvilleLaszloModTorsion_right_surjective
    (hpair : beauvilleLaszloGlueingH0ShortExactHypothesis f X) :
    Function.Surjective (beauvilleLaszloModTorsionRightMap f X) := by
  sorry

-- Proof sketch: the left map is induced from the projection `H⁰ → X.snd` after quotienting by the
-- maximal `f`-power-torsion submodule of `H⁰`. Its kernel is trivial, its image is the kernel of
-- the right map, and the right map is surjective onto `(X.fst)_f / X.fst`.
/-- 15.91.16.2: the canonical Beauville-Laszlo mod-torsion maps form a short exact sequence
`0 → H⁰ / H⁰[f^∞] → X.snd → (X.fst)_f / X.fst → 0`. -/
@[stacks 0BP4]
theorem beauvilleLaszloModTorsion_shortExact
    (hpair : beauvilleLaszloGlueingH0ShortExactHypothesis f X) :
    (beauvilleLaszloModTorsionSequence f X).ShortExact := by
  letI := hpair
  refine ModuleCat.shortComplex_shortExact (beauvilleLaszloModTorsionSequence f X) ?_ ?_ ?_
  · change Function.Exact
      (beauvilleLaszloModTorsionLeftMap f X)
      (beauvilleLaszloModTorsionRightMap f X)
    exact beauvilleLaszloModTorsion_middle_exact (f := f) (X := X)
  · change Function.Injective
      (beauvilleLaszloModTorsionLeftMap f X)
    exact beauvilleLaszloModTorsion_left_injective (f := f) (X := X)
  · change Function.Surjective (beauvilleLaszloModTorsionRightMap f X)
    exact beauvilleLaszloModTorsion_right_surjective (f := f) (X := X) hpair

end

end
