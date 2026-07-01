import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped BigOperators Pointwise Rockafellar

universe u v w

namespace OrdinaryConvexProgram

attribute [local instance] Classical.propDecidable

section

variable {m : ℕ}
variable {𝕜 : Type w}
variable {X : Type u} {XStar : Type v}
variable {ι : Type}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [HasPairing X XStar 𝕜]
variable [Fintype ι] [Fact (Fintype.card ι = m)]

variable (P : OrdinaryConvexProgram 𝕜 X (WithBotTop 𝕜) m 0 ι)

local notation "F" => (P.pureInequalityPerturbedProblem : (ι → 𝕜) → X → WithBotTop 𝕜)
local notation "weighted" => (fun u : ι → 𝕜 ↦ P.weightedObjective u 0)

/-- The source multiplier space `𝕜^m`, represented intrinsically as `ι → 𝕜`, carries the canonical
pairing used by the Chapter 6 adjoint owner and by the pure-inequality specialization of
`P.perturbedProblem`. -/
local instance : HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 :=
  instHasPairingOfHasLinearPairing

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.20 computes the adjoint of the bifunction attached to a
  pure-inequality ordinary convex program.
- `core/canonical`: Chapter 6 already owns the perturbed-problem bifunction as
  `P.perturbedProblem`, its pure-inequality bridge owner `P.pureInequalityPerturbedProblem`, and
  the multiplier-weighted primal objective `P.weightedObjective`.
- `bridge/view`: in the case `s = 0`, the source bifunction is exactly the canonical chapter
  bridge owner `P.pureInequalityPerturbedProblem`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.pureInequalityPerturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.weightedObjective` from `Definition_6_28_3`, specialized to the
  pure-inequality case by setting the equality block to `0`;
- `Bifunction.adjoint` and the scoped adjoint notation `(·)⋆` from
  `Definition_6_30_14`;
- the canonical function-space pairing supplied by `instHasPairingOfHasLinearPairing`.

Primitive data vs derived API:
- primitive source data: the ordinary convex program `P` and the multiplier vector
  `uStar : ι → 𝕜`;
- primitive owner objects: `P.pureInequalityPerturbedProblem` and
  `P.weightedObjective uStar 0`;
- main derived API: the explicit adjoint-value formula for that pure-inequality bridge, with the
  admissible-multiplier condition expressed through the canonical order owner `0 ≤ uStar`.

Layer target: `bridge/view`, with the theorem centered on the existing ordinary-program owners and
only the canonical `s = 0` bridge owner `P.pureInequalityPerturbedProblem` exposed on the
bifunction side.
-/

-- Proof sketch: start from the owner identity
-- `(P.pureInequalityPerturbedProblem)⋆ xStar uStar =
--  -((Function.uncurry P.pureInequalityPerturbedProblem)⋆ (-uStar, xStar))`.
-- A non-admissible multiplier vector forces the value `⊥`, while for an admissible multiplier
-- `uStar` satisfying `0 ≤ uStar` the perturbation infimum occurs at the boundary values of the
-- inequality block, leaving the negative Fenchel conjugate of
-- `P.weightedObjective uStar 0`.
/-- Theorem 6.30.20: the adjoint of the perturbed-problem bifunction of a pure-inequality
ordinary convex program is the negative Fenchel conjugate of the weighted primal objective when
the multiplier vector is admissible in the canonical order interval `Set.Ici (0 : ι → 𝕜)`,
equivalently when `0 ≤ uStar`, and it is `-∞` otherwise. -/
theorem adjointFunction_pureInequalityPerturbedProblem_apply
    (xStar : XStar) (uStar : ι → 𝕜) :
    F⋆ xStar uStar =
      if 0 ≤ uStar then
        -((weighted uStar)⋆ xStar)
      else
        (⊥ : WithBotTop 𝕜) := sorry

end

end OrdinaryConvexProgram
