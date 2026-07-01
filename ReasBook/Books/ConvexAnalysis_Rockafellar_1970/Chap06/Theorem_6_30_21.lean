import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_28_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_20
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_16

noncomputable section

open scoped BigOperators Pointwise Rockafellar Function

universe u v w

attribute [local instance] Classical.propDecidable

section

variable {m : ℕ}
variable {𝕜 : Type w}
variable {X : Type u} {XStar : Type v}
variable {ι : Type}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [HasPairing X XStar 𝕜] [Zero XStar]
variable [Fintype ι] [Fact (Fintype.card ι = m)]

variable (P : OrdinaryConvexProgram 𝕜 X (WithBotTop 𝕜) m 0 ι)

local notation "F" => (P.pureInequalityPerturbedProblem : (ι → 𝕜) → X → WithBotTop 𝕜)
local notation "F⋆₀" =>
  (((F⋆ : XStar → (ι → 𝕜) → WithBotTop 𝕜)₀) : (ι → 𝕜) → WithBotTop 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.21 identifies the dual zero-slice objective of the pure-inequality
  ordinary convex program `P`, then characterizes its feasible multiplier vectors.
- `core/canonical`: the relevant Chapter 6 owners already exist upstream as
  the adjoint and zero-slice owners `(·)⋆`, `(·)₀`, the pure-inequality bridge owner `F`, and
  `P.weightedObjective`.
- `bridge/view`: in the case `s = 0`, the source bifunction is exactly the canonical chapter
  bridge owner `F = P.pureInequalityPerturbedProblem`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.adjointFunction_pureInequalityPerturbedProblem_apply` from
  `Theorem_6_30_20`;
- `Bifunction.objective` / `(·)₀` from `Definition_6_30_16`;
- `OrdinaryConvexProgram.pureInequalityPerturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.weightedObjective` from `Definition_6_28_3`, specialized to the
  pure-inequality case by setting the equality block to `0`;
- `effectiveDomain` / `dom(·)` from `Chap01.Definition_4_4`.

Primitive data vs derived API:
- primitive source data: the program `P` and the multiplier vector `uStar : ι → 𝕜`;
- primitive owner-side objects: `F` and `P.weightedObjective uStar 0`;
- derived API: the explicit dual-objective formula and the dual-feasibility criterion, both using
  the canonical admissibility condition `0 ≤ uStar`.

Layer target: `bridge/view`, with the theorem centered on the existing ordinary-program owners and
only the canonical `s = 0` bridge owner `F` exposed on the bifunction side.
-/

-- Proof sketch: specialize Theorem 6.30.20 at `xStar = 0`, then rewrite the zero slice through
-- the zero slice of the canonical pure-inequality bridge owner `F`.
-- For any function `g`, `-(g⋆ 0)` is the indexed infimum of `g`, so the surviving
-- admissible-multiplier branch becomes the infimum of the canonical weighted
-- objective `P.weightedObjective uStar 0`.
/-- Theorem 6.30.21: the zero-slice objective of the dual concave program attached to the
perturbed problem of a pure-inequality ordinary convex program equals the infimum of the weighted
primal objective when the multiplier vector satisfies the canonical admissibility condition
`0 ≤ uStar`, and it is `-∞`
otherwise. -/
theorem OrdinaryConvexProgram.dualObjective_pureInequalityPerturbedProblem_apply
    (uStar : ι → 𝕜) :
    F⋆₀ uStar =
      if 0 ≤ uStar then
        ⨅ x : X, P.weightedObjective uStar 0 x
      else
        (⊥ : WithBotTop 𝕜) := sorry

-- Proof sketch: rewrite feasibility of the dual objective as membership in
-- `dom (-((F⋆)₀))`, then
-- substitute the owner formula
-- above. The admissible branch is exactly the source condition that the weighted-objective
-- infimum be strictly above `-∞`.
/-- A multiplier vector is dual feasible for the pure-inequality ordinary convex program exactly
when it satisfies the canonical admissibility condition `0 ≤ uStar` and the infimum of the
weighted primal objective is strictly above `-∞`. -/
theorem OrdinaryConvexProgram.dualFeasible_iff_nonnegative_and_weightedObjective_boundedBelow
    (uStar : ι → 𝕜) :
    uStar ∈ dom(-F⋆₀) ↔
      0 ≤ uStar ∧
        (⊥ : WithBotTop 𝕜) < ⨅ x : X, P.weightedObjective uStar 0 x := sorry

end

namespace Function

section ConjugateDomain

variable {m : ℕ}
variable {𝕜 : Type w} {X : Type u} {XStar : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar] [HasPairing X XStar 𝕜]

local notation "U" => Fin m → 𝕜

-- Proof sketch: apply the bounded-below criterion at the origin to
-- `g := L[Finset.univ](f₀, f, uStar)`, which rewrites the source
-- condition `⊥ < ⨅ x, g x` as `0 ∈ dom(g⋆)`. Then use the hypothesis `hdom` identifying `dom(g⋆)`
-- with the Minkowski sum of the conjugate domains of `f₀` and the weighted constraint functions.
/-- Under the source conjugate-domain formula for the weighted objective, the condition that
`f₀ + v₁* f₁ + ⋯ + v_m* f_m` be bounded below is equivalent to the origin lying in the Minkowski
sum `dom(f₀⋆) + v₁* dom(f₁⋆) + ⋯ + v_m* dom(f_m⋆)`. -/
theorem lagrangeCombination_boundedBelow_iff_zero_mem_sum_conjugateDomains_of_conjugateDomain_eq
    (f₀ : X → WithBotTop 𝕜) (f : Fin m → X → WithBotTop 𝕜) (uStar : U)
    (hdom :
      dom(((L[Finset.univ](f₀, f, uStar))⋆ : XStar → WithBotTop 𝕜)) =
        dom((f₀⋆ : XStar → WithBotTop 𝕜)) +
          ∑ i : Fin m, uStar i • dom(((f i)⋆ : XStar → WithBotTop 𝕜))) :
    (⊥ : WithBotTop 𝕜) < ⨅ x : X, L[Finset.univ](f₀, f, uStar) x ↔
      (0 : XStar) ∈
        dom((f₀⋆ : XStar → WithBotTop 𝕜)) +
          ∑ i : Fin m, uStar i • dom(((f i)⋆ : XStar → WithBotTop 𝕜)) := sorry

end ConjugateDomain

end Function
