import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1
import StacksProject_2024.Chap10.Lemma_10_103_6
import StacksProject_2024.Chap10.Lemma_10_103_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum IsLocalRing
open scoped ENat

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.LocallyCohenMacaulay R M`, the global condition that a finite module over
  a Noetherian ring has Cohen-Macaulay localizations at every prime;
* core/canonical: the owner class `Module.CohenMacaulay` on each localized ring/module pair;
* bridge/view: `LocallyCohenMacaulay.toCohenMacaulay` and the full-support local-to-global
  comparison, which compare the global source-facing condition with the local-ring owner
  abstraction.

Primitive data are exactly the finiteness hypothesis and the family of localized
`Module.CohenMacaulay` instances. The inherited `Module.Finite` instance is derived from the class
extension and should not be restated as a separate local wrapper.
-/
/-- The class for Chap10 Definition 10 103 12: a finite `R`-module over a Noetherian ring is
Cohen-Macaulay if, for every prime ideal `𝔭` of `R`, the localization `M_𝔭` is a
Cohen-Macaulay module over the localized ring `R_𝔭`. -/
@[stacks 0AAH]
class LocallyCohenMacaulay : Prop extends Module.Finite R M where
  localizedModule_cohenMacaulay :
    ∀ p : PrimeSpectrum R,
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)

/-- Helper for Chap10 Definition 10 103 12: linear equivalences preserve the set of possible
regular-sequence lengths. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {A : Type u} [CommRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N'] (I : Ideal A) (e : N ≃ₗ[A] N') :
    Ideal.regularSequenceLengths I N = Ideal.regularSequenceLengths I N' := by
  -- Transport each regular sequence through the linear equivalence in both directions.
  ext d
  constructor
  · rintro ⟨rs, hregular, hmem, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hregular, hmem, rfl⟩
  · rintro ⟨rs, hregular, hmem, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hregular, hmem, rfl⟩

/-- Helper for Chap10 Definition 10 103 12: ideal depth is invariant under linear equivalence of
finite modules. -/
private theorem idealDepth_eq_of_linearEquiv {A : Type u} [CommRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N'] [Module.Finite A N]
    [Module.Finite A N'] (I : Ideal A) (e : N ≃ₗ[A] N') :
    Ideal.depth I N = Ideal.depth I N' := by
  -- First compare the top-smul alternative in the definition of depth.
  have htop : I • (⊤ : Submodule A N) = ⊤ ↔ I • (⊤ : Submodule A N') = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  -- In the non-top case, the preceding helper identifies the regular-sequence length sets.
  by_cases hN : I • (⊤ : Submodule A N) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I N hN,
      Ideal.depth_eq_top_of_smul_top I N' (htop.mp hN)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N hN,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N' (mt htop.mpr hN),
      regularSequenceLengths_eq_of_linearEquiv I e]

/-- Helper for Chap10 Definition 10 103 12: module depth over a local ring is invariant under a
linear equivalence of finite modules. -/
private theorem moduleDepth_eq_of_linearEquiv {A : Type u} [CommRing A] [IsLocalRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N'] [Module.Finite A N]
    [Module.Finite A N'] (e : N ≃ₗ[A] N') :
    moduleDepth A N = moduleDepth A N' := by
  -- Module depth is ideal depth at the maximal ideal.
  exact idealDepth_eq_of_linearEquiv (maximalIdeal A) e

/-- Helper for Chap10 Definition 10 103 12: Cohen-Macaulayness transports across a linear
equivalence over a Noetherian local ring. -/
private theorem cohenMacaulay_of_linearEquiv {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {N : Type v} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N'] (e : N ≃ₗ[A] N')
    [hN : CohenMacaulay A N] : CohenMacaulay A N' := by
  let _ : Module.Finite A N' := Module.Finite.equiv e
  -- Rewrite both sides of the defining equality through the equivalence.
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_linearEquiv e,
      hN.supportDim_eq_moduleDepth]⟩

/-- Helper for Chap10 Definition 10 103 12: a local ring is already localized away from its
maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal {A : Type u} [CommRing A]
    [IsLocalRing A] : IsLocalization (maximalIdeal A).primeCompl A := by
  -- The elements inverted are exactly the units of a local ring.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

attribute [local instance] self_isLocalization_primeCompl_maximalIdeal

/-- Helper for Chap10 Definition 10 103 12: the canonical map to the maximal localization of a
local ring is surjective. -/
private theorem algebraMap_localizationAtMaximal_surjective {A : Type u} [CommRing A]
    [IsLocalRing A] : Function.Surjective (algebraMap A (Localization.AtPrime (maximalIdeal A))) := by
  -- Use the localization equivalence with the original local ring and pull representatives back.
  intro z
  let e : Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
    Localization.algEquiv (maximalIdeal A).primeCompl A
  refine ⟨e z, ?_⟩
  apply e.injective
  simp [e]

/-- Helper for Chap10 Definition 10 103 12: the identity map exhibits any module over a local ring
as its own localization away from the maximal ideal. -/
private theorem localizedModuleAtMaximal_id_isLocalizedModule {A : Type u} [CommRing A]
    [IsLocalRing A] {N : Type v} [AddCommGroup N] [Module A N] :
    IsLocalizedModule (maximalIdeal A).primeCompl (.id : N →ₗ[A] N) := by
  -- This is the module-localization form of the preceding ring-localization instance.
  exact isLocalizedModule_id (S := (maximalIdeal A).primeCompl) N A

/-- Helper for Chap10 Definition 10 103 12: localization of a Cohen-Macaulay module at a support
prime, with the module universe bridged through `Shrink`. -/
private theorem cohenMacaulay_localizedModule_atPrime_of_mem_support {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {N : Type v} [AddCommGroup N] [Module A N]
    [CohenMacaulay A N] (p : Ideal A) [hp : p.IsPrime]
    (hpN : (⟨p, hp⟩ : PrimeSpectrum A) ∈ Module.support A N) :
    CohenMacaulay (Localization.AtPrime p) (LocalizedModule.AtPrime p N) := by
  let _ : Small.{u} N := Module.Finite.small A N
  let eShrink : Shrink.{u} N ≃ₗ[A] N := Shrink.linearEquiv A N
  let _ : CohenMacaulay A (Shrink.{u} N) := cohenMacaulay_of_linearEquiv eShrink.symm
  -- Move support membership to the same-universe shrink, apply the earlier theorem, then transport
  -- the localized result back to the original localized module.
  have hpShrink : (⟨p, hp⟩ : PrimeSpectrum A) ∈ Module.support A (Shrink.{u} N) := by
    exact Module.support_subset_of_surjective eShrink eShrink.surjective hpN
  let eLoc : LocalizedModule.AtPrime p (Shrink.{u} N) ≃ₗ[Localization.AtPrime p]
      LocalizedModule.AtPrime p N :=
    LinearEquiv.ofBijective (LocalizedModule.map p.primeCompl eShrink.toLinearMap)
      ⟨LocalizedModule.map_injective p.primeCompl eShrink.toLinearMap eShrink.injective,
        LocalizedModule.map_surjective p.primeCompl eShrink.toLinearMap eShrink.surjective⟩
  let _ : CohenMacaulay (Localization.AtPrime p) (LocalizedModule.AtPrime p (Shrink.{u} N)) :=
    CohenMacaulay.localizedModule_atPrime (M := Shrink.{u} N) (p := p) hpShrink
  exact cohenMacaulay_of_linearEquiv eLoc

namespace LocallyCohenMacaulay

/-- Over a Noetherian local ring, a locally Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay [IsLocalRing R] (h : LocallyCohenMacaulay R M) :
    Module.CohenMacaulay R M := by
  let p : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
  let _ : Module.CohenMacaulay (Localization.AtPrime (maximalIdeal R))
      (LocalizedModule.AtPrime (maximalIdeal R) M) := h.localizedModule_cohenMacaulay p
  -- Restrict the Cohen-Macaulay structure at the closed point along the surjective localization map.
  let _ : Module.CohenMacaulay R (LocalizedModule.AtPrime (maximalIdeal R) M) :=
    Module.CohenMacaulay.of_surjective (R := R) (S := Localization.AtPrime (maximalIdeal R))
      (N := LocalizedModule.AtPrime (maximalIdeal R) M)
      algebraMap_localizationAtMaximal_surjective
  let _ : IsLocalizedModule (maximalIdeal R).primeCompl (.id : M →ₗ[R] M) :=
    localizedModuleAtMaximal_id_isLocalizedModule
  let e : LocalizedModule.AtPrime (maximalIdeal R) M ≃ₗ[R] M :=
    IsLocalizedModule.linearEquiv (maximalIdeal R).primeCompl
      (LocalizedModule.mkLinearMap (maximalIdeal R).primeCompl M) (.id : M →ₗ[R] M)
  -- The maximal localization is linearly equivalent to the original module.
  exact cohenMacaulay_of_linearEquiv e

end LocallyCohenMacaulay

/-- Over a Noetherian local ring, the local-global condition yields the owner class directly. -/
instance cohenMacaulay_of_locallyCohenMacaulay [IsLocalRing R] [h : LocallyCohenMacaulay R M] :
    Module.CohenMacaulay R M :=
  h.toCohenMacaulay

/-- Chap10 Definition 10 103 12: over a Noetherian local ring, a Cohen-Macaulay module whose
support is all of `Spec R` is locally Cohen-Macaulay.

The full-support hypothesis is the Lean-side nonzero-localization replacement for the source
proof's reduction to the nonzero case. Without it, primes outside the support have zero
localization, while the current `Module.CohenMacaulay` owner class does not classify zero modules as
Cohen-Macaulay. -/
theorem locallyCohenMacaulay_of_cohenMacaulay [IsLocalRing R] [Module.CohenMacaulay R M]
    (hsupp : Module.support R M = Set.univ) :
    LocallyCohenMacaulay R M := by
  refine ⟨?_⟩
  intro p
  -- Full support supplies the support-membership side condition for the localization theorem.
  have hpM : p ∈ Module.support R M := by
    rw [hsupp]
    exact Set.mem_univ p
  exact cohenMacaulay_localizedModule_atPrime_of_mem_support (p := p.asIdeal) hpM

end Module

end
