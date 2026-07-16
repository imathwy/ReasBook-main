import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4

noncomputable section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section SameKernel

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 34.4 compares the Chapter 34 equivalence relation with having the same
  kernel.
- `core/canonical`: the owner layer is the existing Chapter 34 equivalence relation `K ∼ L`
  together with the Chapter 34 product domain `dom K` and its relative interior `ri[ℝ](dom K)`.
- `bridge/view`: literal equality of the restricted kernels is ill-typed because the restriction
  domains depend on the bifunction, so the canonical source-facing formulation is equality of the
  product domains together with equality of values on their common relative interior.

Primary mathematical domain:
- closed proper concave-convex saddle-functions and their Chapter 34 equivalence classes.

Domain-style sampling used here:
- `Bifunction.equivalence` and `Bifunction.equivalent_iff` from `Defn_34_4`;
- `SaddleFunction.IsClosed` from `Defn_34_2`;
- the Chapter 34 notation `dom K` from `Defn_34_3`;
- `ri[ℝ](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive source data: two saddle-functions `K, L : U → X → EReal`;
- primitive owner data already present upstream: `K ∼ L`, `SaddleFunction.IsClosed`,
  `dom ·`, and `ri[ℝ](·)`;
- derived bridge API introduced here: the predicate `SameKernel K L`.

Layer target: `bridge/view`.
-/

/-- Two saddle-functions have the same Chapter 34 kernel when they have the same effective domain
and their uncurried graph functions agree on the relative interior of that domain. -/
def SameKernel (K L : U → X → EReal) : Prop :=
  dom K = dom L ∧
    Set.EqOn (Function.uncurry K) (Function.uncurry L) (ri[ℝ](dom K))

-- Proof sketch: unfold `SameKernel`; the relation is definitionally the conjunction of common
-- effective domain and equality of the two uncurried graph functions on the common relative
-- interior.
/-- Unfolded criterion for two saddle-functions to have the same Chapter 34 kernel. -/
theorem sameKernel_iff (K L : U → X → EReal) :
    SameKernel K L ↔
      dom K = dom L ∧
        Set.EqOn (Function.uncurry K) (Function.uncurry L) (ri[ℝ](dom K)) :=
  Iff.rfl

end SameKernel

section

open Bifunction

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: for `→`, use Corollary 34.2.1 to transport the effective domain and the
-- relative-interior values across the Chapter 34 equivalence relation. For `←`, Theorem 34.3
-- identifies a closed proper concave-convex saddle-function by its closed slices on the relative
-- interiors of the coordinate domains, so common kernel data forces equivalence.
/-- Theorem 34.4: two closed proper concave-convex saddle-functions are equivalent if and only if
they have the same kernel, i.e. the same effective domain and the same values on its relative
interior. -/
theorem equivalent_iff_sameKernel_of_isConcaveConvex_of_isClosed_of_isProper
    {K L : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hL_shape : IsConcaveConvex ℝ L)
    (hK_closed : IsClosed K)
    (hL_closed : IsClosed L)
    (hK_proper : IsProper K)
    (hL_proper : IsProper L) :
    K ∼ L ↔ SameKernel K L := sorry

end

end SaddleFunction
