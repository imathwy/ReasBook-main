import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open Function
open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.15 identifies the primal perturbation function `inf F`, the dual
  upper perturbation function `sup F*`, the zero-slice objectives `F₀` and `F*₀`, and the two
  conjugacy correspondences between them.
  `perturbationFunction`, `upperPerturbationFunction`, `(·)₀`, `adjoint`,
  `concaveConjugate`, the Fenchel conjugate `(·)⋆`, the convex closure `cl(·)`, and the concave
  closure `concaveClosure`.
- `bridge/view`: this file contributes only theorem-level identities between those existing
  owners; it introduces no new wrapper around primal or dual programs.

Primary mathematical domain:
- convex/concave duality for bifunctions. The first conjugacy identity is a
  formal owner bridge on a generic pairing codomain layer `L`; the remaining biconjugacy and
  closure identities use the chapter `WithBotTop 𝕜` closure owners. The second identity uses the
  finite-dimensional scalar-parametric biconjugacy layer on `U`, while the final objective-side
  identities stay on the intrinsic scalar-parametric paired `X`/`XStar` owner layer provided by
  `adjoint` and `f⋆` under `HasPairing.swap`.

Domain-style sampling used here:
- `perturbationFunction` and `(·)₀` from Definitions 6.29.1 and 6.29.12;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` and `objective_adjoint_apply` from Definition 6.30.14;
- `concaveConjugate`, `(·)⋆`, `cl(·)`, and `concaveClosure`;
- `Function.IsConcave.biconjugate_eq_concaveClosure` from Theorem 6.30.3.

Primitive data vs derived API:
- primitive input: a bifunction `F`, at the generic codomain layer for the first identity and at
  the `WithBotTop 𝕜` layer for the closure identities (specializing to `EReal` at `𝕜 = ℝ`);
- primitive owners already upstream: `perturbationFunction F`, `(F)₀`,
  `upperPerturbationFunction (F⋆)`, and the dual zero-slice objective `(F⋆)₀`;
- derived API added here: the four source conjugacy identities relating those owners.

Layer target: `bridge/view`. The public statements stay on the chapter's canonical owner
declarations and use the Chapter 6 source notation `(·)₀` and `⋆` on the theorem surface,
avoiding any auxiliary package for the primal or dual programs.
-/

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Add L] [Sub L] [Neg L] [InfSet L] [SupSet L]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable (F : U → X → L)

local notation "F⋆" => adjoint XStar UStar F

-- Proof sketch: evaluate `(F⋆)₀` using `objective_adjoint_apply`, then rewrite the
-- right-hand side as the defining `iInf` formula for the concave conjugate of
-- `- perturbationFunction F`. The slice infimum in the perturbation variable is exactly
-- `perturbationFunction F`.
/-- Theorem 6.30.15, first conjugacy identity: on the canonical pairing-based codomain layer,
the dual zero-slice objective `(F⋆)₀` is the concave conjugate `(- perturbationFunction F)∗`
of the primal perturbation function. -/
theorem concaveConjugate_neg_perturbationFunction_eq_objective_adjointFunction
    :
    (- perturbationFunction F)∗ = (F⋆)₀ := sorry

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [Zero XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: combine the previous conjugacy identity with the Chapter 6 concave biconjugacy
-- theorem applied to `- perturbationFunction F`. The only owner-level input is concavity of
-- `- perturbationFunction F`, equivalently convexity of `perturbationFunction F` on `U`.
-- Unfolding `concaveClosure` gives the displayed right-hand side `- cl(perturbationFunction F)`.
/-- The concave conjugate of the dual zero-slice objective is the negative closure of the primal
perturbation function. This is stated on the finite-dimensional scalar-parametric pairing layer on
`U` together with convexity of the primal perturbation function on `U`; the `X`-side assumptions
are only the primitive paired owner data needed to form `adjoint XStar U F`. -/
theorem concaveConjugate_objective_adjointFunction_eq_neg_cl_perturbationFunction
    (hp_convex : (perturbationFunction F).IsConvex 𝕜) :
    ((F⋆)₀)∗ = - cl(perturbationFunction F) := sorry

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

local instance : HasPairing XStar X (WithBotTop 𝕜) :=
  HasPairing.swap (X := X) (Y := XStar) (L := WithBotTop 𝕜)

/- Theorem 6.30.15 is recorded above as the generic owner-bridge identity, then the
`U`-side closed-value identity on the scalar-parametric `WithBotTop 𝕜` layer, and finally the two
closed-proper companion identities for the reverse direction. -/

-- Proof sketch: use the closed-proper-convex fixed-point theorem for the double adjoint
-- bifunction to identify `F` with the convex conjugate picture coming from the dual upper
-- perturbation function. The resulting equality is exactly the source formula
-- `(- sup F*)* = F₀`.
/-- For a closed proper convex bifunction, the primal zero-slice objective is the swapped-pairing
Fenchel conjugate of the convex function `- sup F*`, written directly as
`((- supᵇ(F⋆))⋆ : X → WithBotTop 𝕜)`. -/
theorem convexConjugateSwap_neg_upperPerturbationFunction_adjoint_eq_objective
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    ((- supᵇ(F⋆))⋆ : X → WithBotTop 𝕜) = (F)₀ := sorry

-- Proof sketch: apply convex biconjugacy to the closed proper convex function
-- `- upperPerturbationFunction (F⋆)` and combine it with the previous equality.
-- Rewriting the closure of a negated concave function through `concaveClosure` yields the
-- displayed right-hand side.
/-- For a closed proper convex bifunction, the Fenchel conjugate of the primal zero-slice
objective is the negative concave closure of the dual upper perturbation function. -/
theorem convexConjugate_objective_eq_neg_concaveClosure_upperPerturbationFunction_adjoint
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    (((F)₀)⋆ : XStar → WithBotTop 𝕜) =
      - concaveClosure (supᵇ(F⋆)) := sorry

end

end Bifunction
