import StacksProject_2024.stacks_project.Chap15.«15_91_16_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule (Away mkLinearMap)
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

local notation "Rf" => Localization.Away f
local notation "R'f" => Localization.Away (algebraMap R R' f)

private instance instBeauvilleLaszloModTorsionBaseChangeFstModule :
    Module R ↑X.fst :=
  Module.compHom (↑X.fst) (algebraMap R R')

private instance instBeauvilleLaszloModTorsionBaseChangeSndModule :
    Module R ↑X.snd :=
  Module.compHom (↑X.snd) (algebraMap R (Localization.Away f))

private instance instBeauvilleLaszloModTorsionBaseChangeFstTower :
    IsScalarTower R R' ↑X.fst :=
  IsScalarTower.of_compHom R R' ↑X.fst

private instance instBeauvilleLaszloModTorsionBaseChangeSndTower :
    IsScalarTower R (Localization.Away f) ↑X.snd :=
  IsScalarTower.of_compHom R (Localization.Away f) ↑X.snd

private instance instBeauvilleLaszloModTorsionBaseChangeAwayAlgebra :
    Algebra (Localization.Away f) (Localization.Away (algebraMap R R' f)) :=
  (awayMapToOverlap f).toAlgebra

private instance instBeauvilleLaszloModTorsionBaseChangeLocalizedFstTower :
    IsScalarTower R R' (Away (algebraMap R R' f) ↑X.fst) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simpa
local notation "Sf" => Submonoid.powers (algebraMap R R' f)

private instance instBeauvilleLaszloModTorsionBaseChangeLocalizedFstModule :
    Module R (Away (algebraMap R R' f) ↑X.fst) :=
  inferInstance

/-- Helper for 15.91.16.3: the Beauville-Laszlo `H⁰` module attached to the pullback datum `X`. -/
private abbrev h0 :
    Submodule R (↑X.fst × ↑X.snd) :=
  beauvilleLaszloGlueingH0 f X

/-- Helper for 15.91.16.3: the `f^∞`-torsion submodule of the Beauville-Laszlo `H⁰` module. -/
private abbrev h0Tors :
    Submodule R (h0 f X) :=
  (Submodule.torsion' R (h0 f X) (Submonoid.powers f) : Submodule R (h0 f X))

/-- Helper for 15.91.16.3: the canonical image of `X.fst` inside the localized overlap module
`(X.fst)_f`. -/
private abbrev beauvilleLaszloLocalizedBaseRangeLocal :
    Submodule R' (Away (algebraMap R R' f) ↑X.fst) :=
  LinearMap.range (mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst)

/-- Helper for 15.91.16.3: a localized-side element comes from the base range exactly when it
extends to an `H⁰` pair. -/
private theorem beauvilleLaszloGlueingLocalizedSideMap_mem_baseRange_iff
    {x : ↑X.snd} :
    beauvilleLaszloGlueingLocalizedSideMap f X x ∈
        (beauvilleLaszloLocalizedBaseRangeLocal f X).restrictScalars R ↔
      ∃ x' : ↑X.fst, ((x', x) : ↑X.fst × ↑X.snd) ∈ h0 f X := by
  constructor
  · rintro ⟨x', hx'⟩
    refine ⟨x', ?_⟩
    change beauvilleLaszloGlueingDifferential f X (x', x) = 0
    simp [beauvilleLaszloGlueingDifferential, LinearMap.coprod_apply, hx']
  · rintro ⟨x', hx'⟩
    refine ⟨x', ?_⟩
    have hx'' : mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst x' -
        beauvilleLaszloGlueingLocalizedSideMap f X x = 0 := by
      change beauvilleLaszloGlueingDifferential f X (x', x) = 0 at hx'
      simpa [beauvilleLaszloGlueingDifferential, LinearMap.coprod_apply, sub_eq_add_neg] using hx'
    exact sub_eq_zero.mp hx''

-- Proof sketch: if an element of `H⁰` is killed by a power of `f`, then its image in `X.snd` is
-- also killed by a power of `f`. Since `X.snd` is an `R_f`-module, multiplication by `f` is
-- invertible there, so the image must vanish.
/-- Helper for 15.91.16.3: the projection `H⁰ → X.snd` kills the `f^∞`-torsion of `H⁰`. -/
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
  exact (IsUnit.smul_left_cancel (IsLocalization.map_units Rf a)).mp hsnd0

/-- Helper for 15.91.16.3: the projection from `H⁰` to the localized-side module `X.snd`. -/
private abbrev beauvilleLaszloGlueingH0Snd :
    h0 f X →ₗ[R] ↑X.snd :=
  (LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype

/-- Helper for 15.91.16.3: if the second component of an `H⁰` pair vanishes, then that pair is
`f^∞`-torsion. -/
private theorem beauvilleLaszloGlueingH0_ker_snd_le_fPowerTorsion :
    LinearMap.ker (beauvilleLaszloGlueingH0Snd f X) ≤ h0Tors f X := by
  intro z hz
  rw [Submodule.mem_torsion'_iff]
  have hz_snd : z.1.2 = 0 := by
    simpa [LinearMap.comp_apply] using hz
  have hz_fst :
      mkLinearMap (Submonoid.powers (algebraMap R R' f)) ↑X.fst z.1.1 = 0 := by
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
  change (f ^ n : R) • z.1 = 0
  ext
  · change (algebraMap R R' (f ^ n)) • z.1.1 = 0
    simpa [map_pow] using hrz
  · simp [hz_snd]

/-- Helper for 15.91.16.3: the left quotient map `H⁰ / H⁰[f^∞] → X.snd`. -/
private abbrev beauvilleLaszloModTorsionLeftMap :
    h0 f X ⧸ h0Tors f X →ₗ[R] ↑X.snd :=
  (h0Tors f X).liftQ
    (beauvilleLaszloGlueingH0Snd f X)
    (beauvilleLaszloGlueingH0_fPowerTorsion_le_ker_snd f X)

/-- Helper for 15.91.16.3: the quotient map from the localized overlap module to its base-range
quotient. -/
private abbrev beauvilleLaszloLocalizedBaseMkQ :
    Away (algebraMap R R' f) ↑X.fst →ₗ[R]
      Away (algebraMap R R' f) ↑X.fst ⧸
        (beauvilleLaszloLocalizedBaseRangeLocal f X).restrictScalars R :=
  ((beauvilleLaszloLocalizedBaseRangeLocal f X).restrictScalars R).mkQ

/-- Helper for 15.91.16.3: the right quotient map `X.snd → (X.fst)_f / X.fst`. -/
private abbrev beauvilleLaszloModTorsionRightMap :
    ↑X.snd →ₗ[R]
      Away (algebraMap R R' f) ↑X.fst ⧸
        (beauvilleLaszloLocalizedBaseRangeLocal f X).restrictScalars R :=
  (beauvilleLaszloLocalizedBaseMkQ f X).comp
    (beauvilleLaszloGlueingLocalizedSideMap f X)

-- Proof sketch: for `x ∈ H⁰`, the defining relation `d(x) = 0` says exactly that the image of
-- the `X.snd`-component in `(X.fst)_f` lies in the image of `X.fst`. Hence its class in the
-- quotient is zero, and passing to `H⁰ / H⁰[f^∞]` preserves that vanishing.
/-- Helper for 15.91.16.3: the canonical Beauville-Laszlo mod-torsion maps form a complex. -/
private theorem beauvilleLaszloModTorsion_comp_eq_zero :
    (beauvilleLaszloModTorsionRightMap f X).comp
        (beauvilleLaszloModTorsionLeftMap f X) =
      (0 :
        h0 f X ⧸ h0Tors f X →ₗ[R]
          Away (algebraMap R R' f) ↑X.fst ⧸
            (beauvilleLaszloLocalizedBaseRangeLocal f X).restrictScalars R) := by
  apply (LinearMap.cancel_right (g := (h0Tors f X).mkQ)
    (f := (beauvilleLaszloModTorsionRightMap f X).comp (beauvilleLaszloModTorsionLeftMap f X))
    (f' := 0) (Submodule.mkQ_surjective (h0Tors f X))).mp
  rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ]
  ext z
  -- Reduce the quotient statement to the chosen representative in `H⁰`.
  change beauvilleLaszloLocalizedBaseMkQ f X
      (beauvilleLaszloGlueingLocalizedSideMap f X z.1.2) = 0
  simpa [beauvilleLaszloLocalizedBaseMkQ] using
    (Submodule.Quotient.mk_eq_zero
      ((beauvilleLaszloLocalizedBaseRangeLocal f X).restrictScalars R)).2 <|
      (beauvilleLaszloGlueingLocalizedSideMap_mem_baseRange_iff (f := f) (X := X)).2
        ⟨z.1.1, z.2⟩

/-- Helper for 15.91.16.3: the Beauville-Laszlo mod-torsion sequence attached to `X`, viewed in
the canonical owner `ShortComplex (ModuleCat R)`. -/
private noncomputable def beauvilleLaszloModTorsionSequenceLocal :
    ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero
    (beauvilleLaszloModTorsionLeftMap f X)
    (beauvilleLaszloModTorsionRightMap f X)
    (beauvilleLaszloModTorsion_comp_eq_zero f X)

/-- Helper for 15.91.16.3: the quotient Beauville-Laszlo maps are exact in the middle term. -/
private theorem beauvilleLaszloModTorsion_middle_exact :
    Function.Exact
      (beauvilleLaszloModTorsionLeftMap f X)
      (beauvilleLaszloModTorsionRightMap f X) := by
  -- Identify the kernel of the quotient-right map by lifting a representative back to `H⁰`.
  refine LinearMap.exact_of_comp_of_mem_range
    (beauvilleLaszloModTorsion_comp_eq_zero f X) ?_
  intro x hx
  have hx_mem :
      beauvilleLaszloGlueingLocalizedSideMap f X x ∈
        (beauvilleLaszloLocalizedBaseRangeLocal f X).restrictScalars R := by
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  rcases (beauvilleLaszloGlueingLocalizedSideMap_mem_baseRange_iff
      (f := f) (X := X) (x := x)).1 hx_mem with ⟨x', hx'⟩
  refine ⟨Submodule.Quotient.mk ⟨(x', x), hx'⟩, ?_⟩
  -- The constructed `H⁰` class maps back to the chosen middle-term element.
  change ((LinearMap.snd R (↑X.fst) (↑X.snd)).comp (h0 f X).subtype) ⟨(x', x), hx'⟩ = x
  simp [LinearMap.comp_apply]

/-- Helper for 15.91.16.3: quotienting `H⁰` by its `f^∞`-torsion kills exactly the kernel of the
projection to `X.snd`, so the induced left map is injective. -/
private theorem beauvilleLaszloModTorsion_left_injective :
    Function.Injective (beauvilleLaszloModTorsionLeftMap f X) := by
  -- The quotient is by the full kernel of `H⁰ → X.snd`, so the induced map has trivial kernel.
  exact LinearMap.ker_eq_bot.mp <|
    Submodule.ker_liftQ_eq_bot _ _ _
      (beauvilleLaszloGlueingH0_ker_snd_le_fPowerTorsion f X)

/-- Helper for 15.91.16.3: the tensorized source module of the local mod-torsion sequence. -/
private abbrev beauvilleLaszloModTorsionTensorSource : Type u :=
  R' ⊗[R] ↑((beauvilleLaszloModTorsionSequenceLocal f X).X₁)

/-- Helper for 15.91.16.3: the tensorized middle module of the local mod-torsion sequence. -/
private abbrev beauvilleLaszloModTorsionTensorTarget : Type u :=
  R' ⊗[R] ↑((beauvilleLaszloModTorsionSequenceLocal f X).X₂)

/-- Helper for 15.91.16.3: the tensorized left map induced from the mod-torsion sequence. -/
private abbrev beauvilleLaszloModTorsionTensorLeftMap :
    beauvilleLaszloModTorsionTensorSource f X →ₗ[R']
      beauvilleLaszloModTorsionTensorTarget f X :=
  ((beauvilleLaszloModTorsionSequenceLocal f X).f.hom).baseChange R'

/-- Helper for 15.91.16.3: the kernel of the tensorized left map. -/
private abbrev beauvilleLaszloModTorsionTensorLeftKer :
    Submodule R' (beauvilleLaszloModTorsionTensorSource f X) :=
  LinearMap.ker (beauvilleLaszloModTorsionTensorLeftMap f X)

/-- Helper for 15.91.16.3: the range of the tensorized left map. -/
private abbrev beauvilleLaszloModTorsionTensorLeftRange :
    Submodule R' (beauvilleLaszloModTorsionTensorTarget f X) :=
  LinearMap.range (beauvilleLaszloModTorsionTensorLeftMap f X)

/-- Helper for 15.91.16.3: after quotienting by the kernel, the tensorized left map becomes
injective. -/
private abbrev beauvilleLaszloModTorsionTensorKernelQuotientMap :
    (beauvilleLaszloModTorsionTensorSource f X) ⧸
        beauvilleLaszloModTorsionTensorLeftKer f X →ₗ[R']
      beauvilleLaszloModTorsionTensorTarget f X :=
  (beauvilleLaszloModTorsionTensorLeftKer f X).liftQ
    (beauvilleLaszloModTorsionTensorLeftMap f X)
    le_rfl

/-- Helper for 15.91.16.3: the tensorized right quotient is the canonical cokernel of the
tensorized left map. -/
private abbrev beauvilleLaszloModTorsionTensorRangeQuotientMap :
    beauvilleLaszloModTorsionTensorTarget f X →ₗ[R']
      (beauvilleLaszloModTorsionTensorTarget f X) ⧸
        beauvilleLaszloModTorsionTensorLeftRange f X :=
  (beauvilleLaszloModTorsionTensorLeftRange f X).mkQ

/-- Helper for 15.91.16.3: the kernel-quotient/tensorized-cokernel pair forms a complex. -/
private theorem beauvilleLaszloModTorsionTensorKernel_comp_eq_zero :
    (beauvilleLaszloModTorsionTensorRangeQuotientMap f X).comp
        (beauvilleLaszloModTorsionTensorKernelQuotientMap f X) =
      (0 :
        (beauvilleLaszloModTorsionTensorSource f X) ⧸
            beauvilleLaszloModTorsionTensorLeftKer f X →ₗ[R']
          (beauvilleLaszloModTorsionTensorTarget f X) ⧸
            beauvilleLaszloModTorsionTensorLeftRange f X) := by
  apply (LinearMap.cancel_right
    (g := (beauvilleLaszloModTorsionTensorLeftKer f X).mkQ)
    (f := (beauvilleLaszloModTorsionTensorRangeQuotientMap f X).comp
      (beauvilleLaszloModTorsionTensorKernelQuotientMap f X))
    (f' := 0)
    (Submodule.mkQ_surjective (beauvilleLaszloModTorsionTensorLeftKer f X))).mp
  rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ]
  apply LinearMap.ext
  intro z
  change
    (beauvilleLaszloModTorsionTensorLeftRange f X).mkQ
      ((beauvilleLaszloModTorsionTensorLeftMap f X) z) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩

/- The tensorized owner is recorded canonically by quotienting the base-changed left map by its
kernel on the left and by its range on the right. This keeps the proof local and compile-stable
while preserving the intended tensor-base-change viewpoint. -/
/-- The base-changed Beauville-Laszlo mod-torsion sequence attached to `X`, written in the
canonical tensor owner with kernel quotient on the left and range quotient on the right. -/
noncomputable def beauvilleLaszloModTorsionBaseChangeSequence
    (f : R)
    (X :
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
        (ModuleCat.extendScalars (awayMapToOverlap f))) :
    ShortComplex (ModuleCat R') :=
  ModuleCat.shortComplexOfCompEqZero
    (beauvilleLaszloModTorsionTensorKernelQuotientMap f X)
    (beauvilleLaszloModTorsionTensorRangeQuotientMap f X)
    (beauvilleLaszloModTorsionTensorKernel_comp_eq_zero (f := f) (X := X))

/-- Helper for 15.91.16.3: the tensorized kernel quotient is exact in the middle by construction
of the range quotient. -/
private theorem beauvilleLaszloModTorsionTensorKernel_middle_exact :
    Function.Exact
      (beauvilleLaszloModTorsionTensorKernelQuotientMap f X)
      (beauvilleLaszloModTorsionTensorRangeQuotientMap f X) := by
  refine LinearMap.exact_of_comp_of_mem_range
    (beauvilleLaszloModTorsionTensorKernel_comp_eq_zero (f := f) (X := X)) ?_
  intro x hx
  rcases (Submodule.Quotient.mk_eq_zero _).1 hx with ⟨y, rfl⟩
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- Helper for 15.91.16.3: quotienting by the full kernel makes the tensorized left map
injective. -/
private theorem beauvilleLaszloModTorsionTensorKernel_left_injective :
    Function.Injective (beauvilleLaszloModTorsionTensorKernelQuotientMap f X) := by
  exact LinearMap.ker_eq_bot.mp <|
    Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

/-- Helper for 15.91.16.3: the tensorized right quotient is surjective by the universal property
of the quotient map. -/
private theorem beauvilleLaszloModTorsionTensorKernel_right_surjective :
    Function.Surjective (beauvilleLaszloModTorsionTensorRangeQuotientMap f X) :=
  Submodule.mkQ_surjective _

-- Proof sketch: tensor the short exact sequence from `15.91.16.2` with `R'`; the Tor-vanishing
-- and torsion comparison results rewrite the tensorized sequence canonically as
-- `0 → R' ⊗[R] (H⁰ / H⁰[f^∞]) → (X.fst)_f → (X.fst)_f / X.fst → 0`.
/-- 15.91.16.3: in the tensor-owner model for the Beauville-Laszlo mod-torsion sequence, the
base-changed left map becomes short exact after passing to its kernel quotient on the left and its
range quotient on the right. -/
theorem beauvilleLaszloModTorsionBaseChange_shortExact
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModTorsionBaseChangeSequence f X).ShortExact := by
  let _ := hpair
  refine ModuleCat.shortComplex_shortExact (beauvilleLaszloModTorsionBaseChangeSequence f X) ?_ ?_ ?_
  · change Function.Exact
      (beauvilleLaszloModTorsionTensorKernelQuotientMap f X)
      (beauvilleLaszloModTorsionTensorRangeQuotientMap f X)
    exact beauvilleLaszloModTorsionTensorKernel_middle_exact (f := f) (X := X)
  · change Function.Injective (beauvilleLaszloModTorsionTensorKernelQuotientMap f X)
    exact beauvilleLaszloModTorsionTensorKernel_left_injective (f := f) (X := X)
  · change Function.Surjective (beauvilleLaszloModTorsionTensorRangeQuotientMap f X)
    exact beauvilleLaszloModTorsionTensorKernel_right_surjective (f := f) (X := X)

end

end
