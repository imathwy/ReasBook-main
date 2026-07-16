import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
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

-- Proof sketch: the nonempty-interior hypothesis on `dom K = dom₁ K ×ˢ dom₂ K`
-- forces both coordinate domains to have nonempty interior. For a concave-convex saddle-function,
-- those coordinate domains are convex, so their relative interiors agree with their ordinary
-- interiors. The Chapter 34 slice-domain behavior over interior points then gives exactly the two
-- containment fields required by `IsSimple ℝ K`.
/-- Text 34.4.3: if the effective domain of a saddle-function `K` has nonempty interior, then `K`
is simple. In the chapter owner language, a concave-convex saddle-function whose effective domain
`dom K` has nonempty interior satisfies `IsSimple ℝ K`. -/
theorem isSimple_of_interior_nonempty_dom
    {K : U → V → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hdom_int : (interior (dom K)).Nonempty) :
    IsSimple ℝ K := sorry

end

end SaddleFunction
