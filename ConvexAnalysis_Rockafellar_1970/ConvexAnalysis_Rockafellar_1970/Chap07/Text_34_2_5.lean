import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_7
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v

namespace Bifunction

section

open Function

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.2.5 records the endpoint-valued behavior of a closed convex bifunction
  that is not proper.
- `core/canonical`: the chapter already exposes the closed-convex owner as
  `Bifunction.IsClosedConvex`;
  graph improperness remains `¬ (uncurry F).IsProper`.
- `bridge/view`: this item should therefore consume `IsClosedConvex` directly and reuse Chapter 2's
  endpoint dichotomy theorem on the uncurried graph function.

Domain-style sampling used here:
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `Function.IsProper` from `Chap01.Definition_4_6`, imported through `Chap02.Text_7_0_7`;
- `Function.IsConvex.eq_bot_or_eq_top_of_lowerSemicontinuous_of_not_isProper` from
  `Chap02.Text_7_0_7`.

Primitive data vs derived API:
- primitive source data: the bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner hypotheses: `IsClosedConvex F` and graph improperness
  `¬ (uncurry F).IsProper`;
- derived source-facing output: the pointwise endpoint dichotomy
  `F u x = ⊥ ∨ F u x = ⊤`.

Layer target: `source-facing`, stated directly on the primitive graph-function owners.
-/

namespace IsClosedConvex

-- Proof sketch: apply Chapter 2's endpoint dichotomy theorem to the uncurried graph function at
-- the point `(u, x)`.
/-- Text 34.2.5 (owner form): if a bifunction is closed convex in the Chapter 34 owner sense and
improper in graph-function form, then each value is an endpoint `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_not_uncurry_isProper
    {F : U → X → WithBotTop 𝕜}
    (hF : IsClosedConvex F)
    (hF_improper : ¬ (uncurry F).IsProper)
    (u : U) (x : X) :
    F u x = ⊥ ∨ F u x = ⊤ := by
  simpa using
    hF.convex.eq_bot_or_eq_top_of_lowerSemicontinuous_of_not_isProper hF.closed hF_improper (u, x)

end IsClosedConvex

end

end Bifunction
