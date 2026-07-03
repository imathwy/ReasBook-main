import StacksProject_2024.Chap10.Lemma_10_96_4
import StacksProject_2024.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Module
open scoped nonZeroDivisors
open AdicCompletion

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of the Beauville-Laszlo Cech sequence for the principal-adic
  completion map `R → principalAdicCompletion f`;
- sampled owner declarations:
  `principalAdicCompletion`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`,
  `primaryComponent_principalIdeal_eq_fPowerTorsion`,
  `powerTorsionSubmodule_eq_bot_of_injective_awayLocalizationFamilyMap`,
  `Ideal.primaryComponent`;
- best owner abstraction: the chapter owner `IsBeauvilleLaszloGlueingPairAlong`, specialized to
  the completion owner `principalAdicCompletion`; the source-facing `f^∞`-torsion notation is a
  bridge to the canonical torsion owner `(principalIdeal f).primaryComponent`;
- primitive data: a commutative ring `R` and an element `f : R`;
- derived API: the completion-side nonzerodivisor statement and the source theorem that a
  nonzerodivisor yields this exact completion-localization glueing pair;
- triage: `core/canonical` = `principalAdicCompletion` together with
  `IsBeauvilleLaszloGlueingPairAlong` and `Ideal.primaryComponent`,
  `bridge/view` = the completion specialization below,
  `source-facing` =
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_of_mem_nonZeroDivisors`,
  `bridge/view` also includes the torsion-vanishing and completion-side nonzerodivisor comparison
  theorems below.
-/

private theorem fPowerTorsion_eq_bot_of_algebraMap_mem_nonZeroDivisors
    {S : Type u} [CommRing S] [Algebra R S] (f : R)
    (hf : algebraMap R S f ∈ nonZeroDivisors S) :
    Submodule.torsion' R S (Submonoid.powers f) = ⊥ := by
  sorry

-- Proof sketch: apply Algebra Lemma `10.96.4` to the exact sequence
-- `0 → R --f--> R → R / (f) → 0`. The induced completion map on the first arrow is
-- multiplication by the image of `f`, so its injectivity shows that image is a nonzerodivisor.
private theorem principalAdicCompletion_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    algebraMap R (principalAdicCompletion f) f ∈
      nonZeroDivisors (principalAdicCompletion f) := by
  sorry

-- Proof sketch: after the previous theorem, both `R[f^∞]` and `R^∧[f^∞]` vanish, so Lemma
-- `15.91.6` gives the exact Beauville-Laszlo Cech condition for the completion pair.
/-- Remark 15.91.7: if `f` is a nonzerodivisor in `R`, then `(R, f)` is a Beauville-Laszlo
glueing pair for the completion map. -/
theorem principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_of_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  sorry

end
