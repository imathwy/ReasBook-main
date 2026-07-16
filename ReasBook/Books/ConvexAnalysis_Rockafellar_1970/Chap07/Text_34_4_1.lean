import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_5

noncomputable section

universe u v

namespace SaddleFunction

section

variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: apply the Chapter 34 closed-slice characterization from Theorem 34.3 to the
-- closed proper concave-convex saddle-function `K`. Clause `(a)` gives
-- `dom (K u) = dom₂ K` for every `u ∈ ri[ℝ](dom₁ K)`, and clause `(d)` gives
-- `dom (fun u ↦ -K u v) = dom₁ K` for every `v ∈ ri[ℝ](dom₂ K)`. Each equality implies the
-- corresponding inclusion into the relevant closure, which is exactly the pair of fields of
-- `IsSimple ℝ K`.
/-- Text 34.4.1: every closed proper saddle-function is simple. In the Chapter 34 owner layer,
this is formalized for a closed proper concave-convex saddle-function `K` as the implication
from `IsConcaveConvex ℝ K`, `IsClosed K`, and `IsProper K` to `IsSimple ℝ K`. -/
theorem isSimple_of_isClosed_of_isProper
    {K : U → V → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_closed : IsClosed K)
    (hK_proper : IsProper K) :
    IsSimple ℝ K := sorry

end

end SaddleFunction
