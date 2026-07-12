import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.ERealSMul
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_5

noncomputable section

universe u v

open scoped Rockafellar
open SaddleFunction

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: view `lowerPairing F` as the canonical Chapter 34 lower saddle representative
-- attached to `F`. The Chapter 33 slice-conjugate results give the required concave-convex and
-- slice-closed properties of that kernel, and the Chapter 34 simplicity criterion then applies
-- to this canonical representative.
/-- Text 34.4.2: convex-side clause of the source statement. If `F` is a convex bifunction, then
the saddle-function `K(u, x^*) = ⟪F u, x^*⟫ᶠ`, i.e. `lowerPairing F`, is simple. -/
theorem lowerPairing_isSimple_of_uncurry_isConvex
    {F : U → X → EReal}
    (hF_convex : (Function.uncurry F).IsConvex ℝ) :
    IsSimple ℝ (lowerPairing F) := sorry

end

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: apply the convex-side statement to the sign-dual/swapped kernel corresponding to
-- `G`, then rewrite the resulting lower-pairing representative as the concave slice-conjugate
-- kernel `fun u xStar ↦ concaveConjugate (G xStar) u`.
/-- Concave-side companion: if `G` is a concave bifunction, then the saddle kernel
`(u, x^*) ↦ concaveConjugate (G x^*) u` is simple. -/
theorem concaveConjugateKernel_isSimple_of_uncurry_isConcave
    {G : X → U → EReal}
    (hG_concave : (Function.uncurry G).IsConcave ℝ) :
    IsSimple ℝ (fun (u : U) (xStar : X) ↦ concaveConjugate (G xStar) u) := sorry

end

end Bifunction
