import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Definition_12_17
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Definition_12_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric
open scoped BigOperators

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 12.18 is `source-facing`: it adds the bounded-distance hypothesis for positive
superlevel sets of the block dual objective from Definition 12.17.

Domain sampling against the surrounding project points to:
- `IsDualBlockProximalGradientProblem` from Definition 12.15 as the ambient standing-assumptions
  owner;
- `dual_block_proximal_gradient_dual_objective` from Definition 12.17 as the source-facing block
  dual objective owner; and
- `dual_block_proximal_gradient_dual_optimal_set` from Definition 12.17 as the canonical owner
  for the optimal dual set `Λ*`.

The right public API is therefore the canonical optimal-set owner together with the source-facing
bounded-superlevel assumption class extending the existing Chapter 12 problem data. -/

/-- Definition 12.18 is `source-facing`: under Assumption 12.14, the block dual optimal set `Λ*`
is nonempty and, for every `α > 0`, every dual point `y` with `q(y) ≥ α` lies within a uniformly
bounded distance of every optimal dual solution `y* ∈ Λ*`, where
`q(y) = -f*(∑ i, y_i) - ∑ i, g_i*(-y_i)`.

The stronger pairwise bound is primitive source data. The weaker canonical
`infDist y Λ* ≤ Rα` reformulation is derived API below. -/
class IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (σ : PosReal) : Prop
    extends IsDualBlockProximalGradientProblem f g σ where
  dual_optimal_set_nonempty :
    (Λ*(f, g)).Nonempty
  bounded_dual_superlevel_distance_to_each_optimal_point (α : PosReal) :
    ∃ Rα : PosReal,
      ∀ (y yStar : Fin p → E)
        (_ : ((α : ℝ) : EReal) ≤ q(f, g) y)
        (_ : yStar ∈ Λ*(f, g)),
        ‖y - yStar‖ ≤ (Rα : ℝ)

namespace IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem

variable {p : ℕ} {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}

/-- The source-facing pairwise superlevel bound from Definition 12.18 implies the weaker canonical
distance-to-optimal-set estimate used downstream. -/
theorem bounded_dual_superlevel_distance_to_optimal_set
    (h : IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem f g σ) (α : PosReal) :
    ∃ Rα : PosReal,
      ∀ (y : Fin p → E) (_ : ((α : ℝ) : EReal) ≤ q(f, g) y),
        infDist y (Λ*(f, g)) ≤ Rα := by
  rcases h.bounded_dual_superlevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro y hy
  rcases h.dual_optimal_set_nonempty with ⟨yStar, hyStar⟩
  refine (Metric.infDist_le_dist_of_mem hyStar).trans ?_
  simpa [dist_eq_norm] using hRα y yStar hy hyStar

end IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem

end
