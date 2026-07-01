import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_15
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_16
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_31
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_33
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_35

noncomputable section

open scoped Rockafellar

universe u v u' v' z

namespace Bifunction

section ZeroDualityGap

variable {𝕜 : Type z} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

variable (F : U → X → WithTopBot 𝕜) (u : U) (xStar : XStar)

local notation "H" => H[F | u, xStar]
local notation "p" => perturbationFunction H
local notation "H⋆" => adjoint XStar UStar H
local notation "q" => upperPerturbationFunction H⋆
local notation "PairEq" => PairingEquationAt (UStar := UStar) F u xStar

/-!
Source/core/bridge triage for the companion bridge in this section.

- `source-facing`: the Chapter 33 pairing equation `PairingEquationAt F u xStar`.
- `core/canonical`: `translatedSubPairing`, `perturbationFunction`, `upperPerturbationFunction`,
  and `adjoint`.
- `bridge/view`: the theorem below identifies the pairing equation only with zero duality gap for
  the translated pair. This is a value-equality companion, not the chapter's normality notion.

Primary mathematical domain:
- perturbation duality for translated bifunctions on paired modules.

Domain-style sampling used before refinement:
- `Bifunction.PairingEquationAt` from `Definition33_0_31`;
- `Bifunction.translatedSubPairing` from `Definition33_0_33`;
- `Bifunction.perturbationFunction` / `Bifunction.upperPerturbationFunction` from Chapter 6;
- the translated-value identities from `Lemma33_0_35`.

Primitive data vs derived API:
- primitive data: `F`, `u`, and `xStar`;
- primitive owner reused from Chapter 33: `PairingEquationAt F u xStar`;
- derived API here: the zero-duality-gap equality for the translated pair.
-/

/-- Companion bridge for Lemma33.0.36: the Chapter 33 pairing equation at `(u, xStar)` is
equivalent to zero duality gap for the translated pair attached to
`H = translatedSubPairing F u xStar`, rendered on the canonical Chapter 6 owner expressions
`perturbationFunction H 0` and `upperPerturbationFunction H⋆ 0`. This is not, by itself, the
Chapter 6 normality notion. -/
theorem pairingEquationAt_iff_zeroDualityGap_translatedSubPairing
    :
    PairEq ↔ p 0 = q 0 := by
  rw [← optimalValue_eq_perturbationFunction_zero H]
  rw [optimalValue_translatedSubPairing_eq_neg_convex_slice_pairing F u xStar]
  rw [upperPerturbationFunction_adjoint_translatedSubPairing_zero_eq_neg_adjoint_slice_pairing
      F u xStar]
  constructor
  · intro hEq
    simpa [PairingEquationAt] using congrArg Neg.neg hEq
  · intro hGap
    simpa [PairingEquationAt] using congrArg Neg.neg hGap

end ZeroDualityGap

section Normality

variable {𝕜 : Type z} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜]

variable (F : U → X → WithTopBot 𝕜) (u : U) (xStar : XStar)

local notation "H" => H[F | u, xStar]
local notation "p" => perturbationFunction H
local notation "H⋆" => adjoint XStar UStar H
local notation "q" => upperPerturbationFunction H⋆
local notation "PairEq" => PairingEquationAt (UStar := UStar) F u xStar

/-!
Source/core/bridge triage for the main theorem in this section.

- `source-facing`: Lemma33.0.36 identifies the Chapter 33 pairing equation with normality of the
  translated primal-dual pair `(Q), (Q*)`.
- `core/canonical`: the Chapter 6 owners for that normality statement are the primal and dual
  closure identities `p 0 = cl(p) 0` and `q 0 = (-cl(-q)) 0`.
- `bridge/view`: this file reads Lemma33.0.36 directly in the pairing-parametric Chapter 6 ambient
  layer where `primalNormal_dualNormal_zeroDualityGap_tfae` already lives.

Primary mathematical domain:
- Chapter 6 normality for closed convex primal-dual bifunction pairs on scalar-parametric paired
  spaces.

Domain-style sampling used before refinement:
- `Bifunction.PairingEquationAt` from `Definition33_0_31`;
- `Bifunction.primalNormal_dualNormal_zeroDualityGap_tfae` from `Theorem_6_30_16`;
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11`;
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.translatedSubPairing` from `Definition33_0_33`.

Primitive data vs derived API:
- primitive data: the translated kernel `H = translatedSubPairing F u xStar`;
- primitive normality owners: the two Chapter 6 closure identities for `p` and `q`;
- derived bridge: the equivalence with `PairingEquationAt F u xStar`.
-/

/-- Lemma33.0.36: for the translated closed-convex pair `(Q), (Q*)`, the Chapter 33 pairing
equation at `(u, xStar)` is equivalent to normality of the translated pair, rendered canonically
as the conjunction of primal and dual normality for `H = translatedSubPairing F u xStar`, in the
pairing-parametric Chapter 6 ambient layer. -/
theorem pairingEquationAt_iff_normality_translatedSubPairing
    (hH_convex : (Function.uncurry H).IsConvex 𝕜)
    (hH_closed : LowerSemicontinuous (Function.uncurry H)) :
    PairEq ↔
      p 0 = cl(p) 0 ∧
        q 0 = (- cl(-q)) 0 := by
  have hGap :
      PairEq ↔
        p 0 = q 0 := by
    simpa using
      (pairingEquationAt_iff_zeroDualityGap_translatedSubPairing F u xStar)
  have hTFAE :
      List.TFAE
        [p 0 = cl(p) 0,
          q 0 = (- cl(-q)) 0,
          p 0 = q 0] :=
    primalNormal_dualNormal_zeroDualityGap_tfae H hH_convex hH_closed
  constructor
  · intro hEq
    have hGapEq : p 0 = q 0 := by
      simpa using hGap.mp hEq
    exact ⟨(hTFAE.out 0 2).mpr hGapEq, (hTFAE.out 1 2).mpr hGapEq⟩
  · rintro ⟨hp, hq⟩
    have hGapEq_fromPrimal : p 0 = q 0 := (hTFAE.out 0 2).mp hp
    have hGapEq_fromDual : p 0 = q 0 := (hTFAE.out 1 2).mp hq
    have hGapEq : p 0 = q 0 := by
      calc
        p 0 = q 0 := hGapEq_fromPrimal
        _ = p 0 := hGapEq_fromDual.symm
        _ = q 0 := hGapEq_fromDual
    exact hGap.mpr (by simpa using hGapEq)

end Normality

end Bifunction
