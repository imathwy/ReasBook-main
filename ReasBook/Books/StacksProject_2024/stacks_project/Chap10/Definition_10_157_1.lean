import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.RegularLocalRing.Defs
import StacksProject_2024.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped ENat

section

variable {R : Type u} [CommRing R]

private theorem regularSequenceLengths_eq_of_equiv {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

private theorem idealDepth_eq_of_equiv {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_equiv I e]

/-- Linear equivalences preserve module depth over a local ring. -/
theorem moduleDepth_eq_of_equiv {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] [IsLocalRing R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N :=
  idealDepth_eq_of_equiv (IsLocalRing.maximalIdeal R) e

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.SerreConditionS R M k`, the module-theoretic Serre condition `(S_k)`;
* core/canonical: the localized owner data `moduleDepth` and `Module.supportDim` on
  `LocalizedModule.AtPrime p.asIdeal M`;
* bridge/view: the ring self-module specialization `SerreConditionS R k` below.

Primitive data are exactly the finiteness hypothesis and the primewise depth inequality for the
localized modules. The ring version is derived from this owner by specializing to `M = R`.
-/
/-- Definition 10.157.1 (3): a finite `R`-module satisfies Serre's condition `(S_k)` if, for every
prime ideal `𝔭`, the depth of `M_𝔭` is at least `min(k, dim(Supp(M_𝔭)))`. -/
class SerreConditionS (k : outParam ℕ) : Prop extends Module.Finite R M where
  moduleDepth_localizationAtPrime_ge_min_supportDim :
    ∀ p : PrimeSpectrum R,
      WithBot.some
          (moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :
            ℕ∞) ≥
        min (k : WithBot ℕ∞)
          (_root_.Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M))

namespace SerreConditionS

/-- Serre's condition `(S_k)` is invariant under linear equivalence. -/
theorem of_linearEquiv {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ} (e : M ≃ₗ[R] N)
    [hM : Module.SerreConditionS R M k] : Module.SerreConditionS R N k where
  toFinite := Module.Finite.equiv e
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    intro p
    let _ : Module.Finite R N := Module.Finite.equiv e
    let ep : LocalizedModule.AtPrime p.asIdeal M ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime p.asIdeal N :=
      LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
        ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
          LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
    have hsupport :
        Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
          Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) :=
      Module.supportDim_eq_of_equiv ep
    have hdepth :
        moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
          moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) :=
      moduleDepth_eq_of_equiv ep
    simpa [hdepth, hsupport] using hM.moduleDepth_localizationAtPrime_ge_min_supportDim p

end SerreConditionS

end Module

end

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-
Source/core/bridge triage:
* source-facing: `SerreConditionR R k` and `SerreConditionS R k`, the textbook ring conditions;
* core/canonical: `IsRegularLocalRing (Localization.AtPrime p.asIdeal)` for `(R_k)` and the
  module owner `Module.SerreConditionS R R k` for `(S_k)`;
* bridge/view: `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`, recovering the ringwise
  depth bound from the self-module owner.

For `(S_k)`, the old ring-specific primewise depth field was duplicate derived API for the
self-module. The primitive owner data are Noetherianity together with `Module.SerreConditionS R R`.
-/
/-- Definition 10.157.1 (1): a Noetherian ring satisfies Serre's condition `(R_k)` if every
localization at a prime ideal of height at most `k` is a regular local ring; equivalently, `R` is
regular in codimension at most `k`. -/
class SerreConditionR (k : outParam ℕ) : Prop extends IsNoetherianRing R where
  isRegularLocalRing_localizationAtPrime :
    ∀ p : PrimeSpectrum R,
      Ideal.primeHeight p.asIdeal ≤ k →
        IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-- Definition 10.157.1 (2): a Noetherian ring satisfies Serre's condition `(S_k)` if, for every
prime ideal `𝔭`, the depth of `R_𝔭` is at least `min(k, dim(R_𝔭))`. -/
class SerreConditionS (k : outParam ℕ) : Prop extends IsNoetherianRing R, Module.SerreConditionS R R k

namespace SerreConditionS

/-- The self-module owner `Module.SerreConditionS R R k` recovers the usual ring-theoretic depth
bound in each localization. -/
theorem moduleDepth_localizationAtPrime_ge_min {k : ℕ} (h : SerreConditionS R k)
    (p : PrimeSpectrum R) :
    WithBot.some
        (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) : ℕ∞) ≥
      min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p.asIdeal)) := by
  rw [← _root_.Module.supportDim_self_eq_ringKrullDim]
  simpa using h.toSerreConditionS.moduleDepth_localizationAtPrime_ge_min_supportDim p

end SerreConditionS

end

notation:max R:max " ⊧ " "(" "R₁" ")" => SerreConditionR R 1
notation:max R:max " ⊧ " "(" "S₂" ")" => SerreConditionS R 2
