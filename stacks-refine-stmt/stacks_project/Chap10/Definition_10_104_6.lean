import Mathlib
import stacks_project.Chap10.Definition_10_103_12
import stacks_project.Chap10.Definition_10_110_7
import stacks_project.Chap10.Definition_10_157_1
import stacks_project.Chap10.Lemma_10_106_3
import stacks_project.Chap10.Lemma_10_72_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open scoped ENat

section

variable (R : Type u) [CommRing R]

/-
Source/core/bridge triage:
* source-facing: `CohenMacaulayRing R`, the textbook global ring notion;
* core/canonical: `Module.LocallyCohenMacaulay R R`, the chapter owner saying the self-module is
  Cohen-Macaulay after localization at every prime;
* bridge/view: the self-module specialization of `Module.CohenMacaulay` on each localized ring.

Primitive data are exactly the Noetherian hypothesis together with the owner class
`Module.LocallyCohenMacaulay R R`. The old primewise depth-equals-dimension field was duplicate
derived API for the self-module, so it should be recovered from the owner abstraction rather than
stored as primitive public data.
-/
/-- Definition 10.104.6: a ring is Cohen-Macaulay if it is Noetherian and every localization at a
prime ideal is a Cohen-Macaulay local ring. -/
class CohenMacaulayRing : Prop extends IsNoetherianRing R, Module.LocallyCohenMacaulay R R

/-- A Cohen-Macaulay ring is Noetherian. -/
instance isNoetherianRing_of_cohenMacaulayRing [h : CohenMacaulayRing R] : IsNoetherianRing R :=
  h.toIsNoetherian

/-- Every localization of a Cohen-Macaulay ring is a Cohen-Macaulay self-module. -/
theorem localizedRing_cohenMacaulay (p : PrimeSpectrum R) [h : CohenMacaulayRing R] :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  simpa using h.toLocallyCohenMacaulay.localizedModule_cohenMacaulay p

/-- Every localization of a Cohen-Macaulay ring satisfies the depth-equals-dimension condition. -/
theorem localizedRing_moduleDepth_eq_ringKrullDim (p : PrimeSpectrum R) [h : CohenMacaulayRing R] :
    WithBot.some (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) =
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  rw [← Module.supportDim_self_eq_ringKrullDim]
  exact (localizedRing_cohenMacaulay R p).supportDim_eq_moduleDepth.symm

namespace CohenMacaulayRing

/-- A Cohen-Macaulay ring satisfies Serre's condition `(S_k)` for every `k`. -/
theorem serreConditionS (k : ℕ) [h : CohenMacaulayRing R] : SerreConditionS R k := by
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro p
  rw [Module.supportDim_self_eq_ringKrullDim, localizedRing_moduleDepth_eq_ringKrullDim R p]
  exact min_le_right _ _

/-- A Noetherian ring is Cohen-Macaulay if it satisfies Serre's condition `(S_k)` for every
`k`. -/
theorem of_serreConditionS [IsNoetherianRing R] (hS : ∀ k : ℕ, SerreConditionS R k) :
    CohenMacaulayRing R := by
  refine
    { toIsNoetherian := inferInstance
      toLocallyCohenMacaulay := ?_ }
  refine
    { toFinite := inferInstance
      localizedModule_cohenMacaulay := ?_ }
  intro p
  let h := p.asIdeal.height
  have hp : h ≠ ⊤ := by
    simpa [h] using Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  let k := h.toNat
  let _ : SerreConditionS R k := hS k
  refine Module.CohenMacaulay.mk ?_
  have hdepth_ge :
      WithBot.some
          (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) : ℕ∞) ≥
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    have hserre :=
      SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R) (k := k)
        (h := inferInstance) p
    have hdim :
        ringKrullDim (Localization.AtPrime p.asIdeal) = (k : WithBot ℕ∞) := by
      calc
        ringKrullDim (Localization.AtPrime p.asIdeal) = ↑p.asIdeal.height := by
          simpa using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
              (Localization.AtPrime p.asIdeal))
        _ = k := by
          simpa [h, k] using
            congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hp).symm
    simpa [hdim] using hserre
  have hdepth_le :
      WithBot.some
          (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) : ℕ∞) ≤
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact depth_le_supportDim
  rw [Module.supportDim_self_eq_ringKrullDim]
  exact (le_antisymm hdepth_le hdepth_ge).symm

end CohenMacaulayRing

/-- A regular ring is Cohen-Macaulay. -/
instance [IsRegularRing R] : CohenMacaulayRing R where
  toIsNoetherian := inferInstance
  toLocallyCohenMacaulay := by
    refine
      { toFinite := inferInstance
        localizedModule_cohenMacaulay := ?_ }
    intro p
    let _ : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
      IsRegularRing.isRegularLocalRing_atPrime p
    infer_instance

end
