import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/- 
Source/core/bridge triage:
* source-facing: Lemma `10.103.3` extracts the regularity and quotient consequences of the support
  dimension equality for `QuotSMulTop g M`;
* core/canonical: `CohenMacaulay R M`, `IsSMulRegular M g`, and the local-depth bridge
  `moduleDepth R M`;
* bridge/view: the quotient module `QuotSMulTop g M` together with the hypothesis
  `supportDim R (QuotSMulTop g M) + 1 = supportDim R M`.

Primitive data are only the owner assumption `[CohenMacaulay R M]` and the support-dimension
equality. In a local ring, `g ∈ maximalIdeal R` is recovered internally from that equality, since
the Cohen-Macaulay hypothesis gives `supportDim R M ≠ ⊥` while a unit `g` would force
`QuotSMulTop g M = 0` and hence `supportDim R (QuotSMulTop g M) = ⊥`. The quotient
Cohen-Macaulayness and depth drop are derived consequences and should be stated through the owner
APIs rather than by repeating a longer `Ideal.depth (maximalIdeal R)` surface.
-/

-- Proof sketch: the Cohen-Macaulay hypothesis gives `supportDim R M = .some (moduleDepth R M)`,
-- so `supportDim R M ≠ ⊥`. If `g` were a unit, then `QuotSMulTop g M = 0`, forcing
-- `supportDim R (QuotSMulTop g M) = ⊥`, contradicting `hdim`; hence `g ∈ maximalIdeal R`
-- internally. Choose a maximal `M`-regular sequence in the maximal ideal from the Cohen-Macaulay
-- hypothesis. The support-dimension equality for `QuotSMulTop g M` shows that `g` is good with
-- respect to that sequence, so Lemma `10.103.2 (1)` yields injectivity of multiplication by `g`.
/-- Lemma 10.103.3 (1): if `R` is a Noetherian local ring, `M` is a Cohen-Macaulay `R`-module,
and `g` cuts the support dimension down by one, written as
`supportDim R (QuotSMulTop g M) + 1 = supportDim R M`, then `g` is a nonzerodivisor on `M`. -/
theorem isSMulRegular_of_cohenMacaulay_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    IsSMulRegular M g := sorry

-- Proof sketch: first recover `g ∈ maximalIdeal R` internally from `hdim` as in part (1), and
-- then apply part (1) to obtain that `g` is a nonzerodivisor on `M`. Use the quotient criterion
-- for Cohen-Macaulay modules together with the support-dimension equality to identify the depth of
-- `QuotSMulTop g M` as one less than the depth of `M`.
/-- Lemma 10.103.3 (2): under the same hypotheses, the quotient `M / gM`, written canonically as
`QuotSMulTop g M`, is Cohen-Macaulay, and its depth is one less than the depth of `M`. -/
theorem cohenMacaulay_quotSMulTop_and_depth_eq_sub_one_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    CohenMacaulay R (QuotSMulTop g M) ∧
      moduleDepth R (QuotSMulTop g M) = moduleDepth R M - 1 := sorry

end Module

end
