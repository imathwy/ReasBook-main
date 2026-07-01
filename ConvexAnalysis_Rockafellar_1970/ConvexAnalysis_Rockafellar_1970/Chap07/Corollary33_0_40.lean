import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_29
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_31

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v u' v'

open scoped Rockafellar

namespace Bifunction

section FullPrimalDomain

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup X] [Module ℝ X]
variable [Neg UStar]
variable [HasPairing U UStar ℝ] [HasPairing X XStar ℝ]
variable {F : U → X → EReal}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary33.0.40 gives sufficient hypotheses for the Chapter 33 pairing
  equation to hold globally for a convex bifunction.
- `core/canonical`: the owner surface is `PairingEquationAt F u xStar`, together with the
  domain owners `dom F` and `dom (-F⋆)`.
- `bridge/view`: the global quantification over `(u, xStar)` is derived API; the mathematically
  primary statement is the pointwise owner `PairingEquationAt`.

Domain-style sampling inspected before refinement:

- `Bifunction.dom`;
- `Bifunction.PairingEquationAt`;
- `Bifunction.pairingEquationAt_iff_normality_translatedSubPairing`;
- `Bifunction.not_forall_pairingEquationAt_of_dom_ne_univ_and_dom_neg_adjoint_ne_univ`.

Primitive data vs derived API:

- primitive data: the bifunction `F`;
- primitive owner hypotheses: graph convexity, primal full-domain `dom F = Set.univ`, and
  adjoint-side full-domain `dom (-F⋆) = Set.univ` together with closedness when needed;
- derived API: the source-global reading “for all `u` and `x⋆`”, now presented through the
  pointwise owner theorem surface instead of a separate `∀`-valued wrapper.

Layer target: `source-facing`, stated directly on the canonical Chapter 33 owner
`PairingEquationAt`.
-/

-- Proof sketch: under the full-domain hypothesis `dom F = Set.univ`, every primal parameter lies
-- in the source domain, so the Chapter 33 normality criterion from the preceding results applies
-- at each `(u, xStar)` and yields the pairing equation pointwise.
/-- If a convex bifunction has full primal source domain, then the Chapter 33 pairing equation
holds at every parameter pair `(u, x⋆)`. -/
theorem pairingEquationAt_of_dom_eq_univ
    (hF_convex : (Function.uncurry F).IsConvex ℝ)
    (hDom : dom F = Set.univ)
    (u : U) (xStar : XStar) :
    PairingEquationAt F u xStar := sorry

end FullPrimalDomain

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable [Neg UStar]
variable [HasPairing U UStar ℝ] [HasPairing X XStar ℝ]
variable {F : U → X → EReal}

local notation "F⋆" => adjoint XStar UStar F

-- Proof sketch: closedness of `F` and the full adjoint-side domain hypothesis
-- `dom (-F⋆) = Set.univ` give normality for every translated primal-dual pair, so the Chapter 33
-- pairing equation follows pointwise at each `(u, xStar)`.
/-- If a convex bifunction is closed and its adjoint-side source domain is all of `XStar`, then
the Chapter 33 pairing equation holds at every parameter pair `(u, x⋆)`. -/
theorem pairingEquationAt_of_closed_and_dom_neg_adjoint_eq_univ
    (hF_convex : (Function.uncurry F).IsConvex ℝ)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hAdjDom : dom (-F⋆) = Set.univ)
    (u : U) (xStar : XStar) :
    PairingEquationAt F u xStar := sorry

-- Proof sketch: split into the two source cases. The first branch applies
-- `pairingEquationAt_of_dom_eq_univ`; the second applies
-- `pairingEquationAt_of_closed_and_dom_neg_adjoint_eq_univ`.
/-- Corollary33.0.40, owner form: a convex bifunction satisfies the Chapter 33 pairing identity
at each parameter pair `(u, x⋆)` if either `dom F = Set.univ`, or `F` is closed and
`dom (-F⋆) = Set.univ`. -/
theorem pairingEquationAt_of_dom_eq_univ_or_closed_and_dom_neg_adjoint_eq_univ
    (hF_convex : (Function.uncurry F).IsConvex ℝ)
    (h : dom F = Set.univ ∨
      LowerSemicontinuous (Function.uncurry F) ∧ dom (-F⋆) = Set.univ)
    (u : U) (xStar : XStar) :
    PairingEquationAt F u xStar := sorry

end

end Bifunction
