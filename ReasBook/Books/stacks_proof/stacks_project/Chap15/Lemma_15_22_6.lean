import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: torsion-free modules and localization at maximal ideals;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Module.IsTorsionFree.of_smul_eq_zero`,
  `IsLocalizedModule.isTorsionFree`,
  `Module.eq_zero_of_localization_maximal`,
  `smul_eq_zero_iff_right`;
- best owner abstraction: `Module.IsTorsionFree`;
- source-facing layer: the Stacks lemma detecting torsion-freeness from maximal localizations;
- core/canonical layer: scalar-regularity packaged by `Module.IsTorsionFree`;
- bridge/view layer: the canonical localization maps `LocalizedModule.mkLinearMap`.

Primitive data are only the domain `R`, the module `M`, and the canonical family of localizations
at maximal ideals. Local torsion-freeness is already owner-level derived data, so this file should
reuse the canonical localization and local-detection API directly.
-/

section

open Module
open LocalizedModule (AtPrime mkLinearMap)

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: the forward implication is the canonical localized-module torsion-free instance.
-- Conversely, use the owner constructor `Module.IsTorsionFree.of_smul_eq_zero`. If `r ≠ 0` and
-- `r • x = 0`, then in every maximal localization the image of `x` is killed by the nonzero
-- scalar `algebraMap R (Localization.AtPrime m) r`, hence is zero by local torsion-freeness. The
-- mathlib local-to-global theorem `Module.eq_zero_of_localization_maximal` then gives `x = 0`.
/-- Lemma 15.22.6: an `R`-module over a domain is torsion free if and only if its localization at
every maximal ideal is torsion free. -/
@[stacks 0AUT]
theorem isTorsionFree_iff_localizedModule_atPrime_maximal :
    IsTorsionFree R M ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        IsTorsionFree (Localization.AtPrime m) (AtPrime m M) := by
  constructor
  · intro hM m _
    letI := hM
    simpa using
      (IsLocalizedModule.isTorsionFree (mkLinearMap m.primeCompl M) m.primeCompl :
        IsTorsionFree (Localization.AtPrime m) (AtPrime m M))
  · intro hlocal
    have hzero : ∀ (r : R) (x : M), r • x = 0 → r = 0 ∨ x = 0 := fun r x hx ↦ by
      by_cases hr : r = 0
      · exact Or.inl hr
      · let Mₘ : ∀ (m : Ideal R) [m.IsMaximal], Type (max u v) := fun m _ ↦ AtPrime m M
        let fₘ : ∀ (m : Ideal R) [m.IsMaximal], M →ₗ[R] Mₘ m :=
          fun m _ ↦ mkLinearMap m.primeCompl M
        have hx_zero : x = 0 := eq_zero_of_localization_maximal Mₘ fₘ x fun m _ ↦ by
          letI := hlocal m
          have hmap :
              (algebraMap R (Localization.AtPrime m)) r • mkLinearMap m.primeCompl M x = 0 := by
            simpa using congrArg (mkLinearMap m.primeCompl M) hx
          have hmap_ne_zero : (algebraMap R (Localization.AtPrime m)) r ≠ 0 :=
            IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors
              (Localization.AtPrime m)
              (Ideal.primeCompl_le_nonZeroDivisors m)
              (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
          exact (smul_eq_zero_iff_right hmap_ne_zero).mp hmap
        exact Or.inr hx_zero
    exact Module.IsTorsionFree.of_smul_eq_zero hzero

end
