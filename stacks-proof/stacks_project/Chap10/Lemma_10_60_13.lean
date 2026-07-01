import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open Pointwise
open scoped nonZeroDivisors

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain triage:
* source-facing: the textbook statements are about the quotient `R / (x)`, written in Lean as
  `R ⧸ Ideal.span {x}`;
* core/canonical: the owner abstractions are the root theorem
  `ringKrullDim_le_ringKrullDim_quotSMulTop_succ` and the module theorem
  `Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal`;
* bridge/view: the only extra work in this file is to identify `Ideal.span {x}` with the owner
  ideal `x • ⊤` and specialize the module theorem to `M = R`.
-/

-- Proof sketch: identify `Ideal.span {x}` with the owner ideal `x • ⊤` and apply the canonical
-- one-step dimension bound `ringKrullDim_le_ringKrullDim_quotSMulTop_succ`.
/-- Lemma 10.60.13: if `R` is a Noetherian local ring and `x` lies in the maximal ideal, then
`dim R ≤ dim (R / (x)) + 1`, written canonically as
`ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1`. -/
theorem ringKrullDim_le_ringKrullDim_quotient_span_singleton_add_one (x : R)
    (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
  have hspan : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv]
  exact ringKrullDim_le_ringKrullDim_quotSMulTop_succ hx

-- Proof sketch: identify `dim R` with `supportDim R R`, note that `annihilator R R = ⊥`, and
-- apply the equality case `supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal`
-- for the module `R`.
/-- If `x` is in the maximal ideal and avoids every minimal prime of `R`, then quotienting by the
principal ideal `(x)` lowers the Krull dimension by exactly one. -/
theorem ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
    (x : R) (hx : x ∈ maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim R = ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
  have hspan : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.mpr inferInstance
  have hmin' : ∀ p ∈ (Module.annihilator R R).minimalPrimes, x ∉ p := by
    simpa [hann, minimalPrimes] using hmin
  symm
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  exact Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    hmin' hx

/- Companion recall: the nonzerodivisor case is already the canonical mathlib theorem
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`, stated with
the standard submonoid notation `x ∈ R⁰`. -/
recall ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors

end
