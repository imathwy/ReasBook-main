import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_5
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_34_4

noncomputable section

universe u v

open scoped Rockafellar
open SaddleFunction

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 34.5 compares the iterated closures `lowerClosure K` and
  `upperClosure K` of a proper simple concave-convex saddle-function `K`, then characterizes the
  concave-convex saddle-functions lying between them.
- `core/canonical`: the owner layer is already present in Chapter 34: `lowerClosure`,
  `upperClosure`, the equivalence relation `∼`, the closedness and properness owners
  `SaddleFunction.IsClosed` and `SaddleFunction.IsProper`, the simplicity owner
  `SaddleFunction.IsSimple`, and the kernel-comparison owner `SaddleFunction.SameKernel`.
- `bridge/view`: the final source sentence is best expressed as a sandwich characterization among
  concave-convex saddle-functions, rather than by introducing a new packaged equivalence-class
  object.

Domain-style sampling used here:
- `Bifunction.lowerClosure` and `Bifunction.upperClosure` from `Defn_34_1`;
- `Bifunction.equivalence` and `Bifunction.equivalent_iff` from `Defn_34_4`;
- `SaddleFunction.IsSimple` from `Chap07.Defn_34_5`;
- `SaddleFunction.SameKernel` from `Theorem_34_4`.

Primitive data vs derived API:
- primitive source data: a saddle-function `K : U → X → EReal`;
- primitive owner hypotheses: `IsConcaveConvex ℝ K`, `IsProper K`, and `IsSimple ℝ K`;
- derived API: equivalence of the two closure representatives, their order relation, and the
  sandwich characterization of the whole equivalence class determined by `K`.

Layer target: `source-facing`, split into atomic clauses: equivalence of the two closure
representatives, their order relation, the three forward consequences of the sandwich condition,
and the reverse implication from closedness, properness, and common kernel back to the sandwich.
-/

-- Proof sketch: use Theorem 34.1 to make `lowerClosure K` lower closed and `upperClosure K`
-- upper closed. Corollary 34.2.2 upgrades both to closed saddle-functions. Simplicity preserves
-- the kernel under each partial closure, so Theorem 34.4 identifies the two closed proper
-- representatives as equivalent.
/-- Theorem 34.5 (1): if `K` is a proper simple concave-convex saddle-function, then its lower
closure `cl₂ (cl₁ K)` and upper closure `cl₁ (cl₂ K)` are equivalent. -/
theorem lowerClosure_equivalent_upperClosure_of_isSimple
    {K : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_proper : IsProper K)
    (hK_simple : IsSimple ℝ K) :
    lowerClosure K ∼ upperClosure K := sorry

-- Proof sketch: once the two closures are known to belong to the same closed equivalence class by
-- the previous clause, Corollary 34.2.2 identifies the lower-closed representative as the least
-- element and the upper-closed representative as the greatest element of that class, yielding the
-- pointwise inequality.
/-- Theorem 34.5 (2): for a proper simple concave-convex saddle-function `K`, the lower closure is
pointwise below the upper closure. -/
theorem lowerClosure_le_upperClosure_of_isSimple
    {K : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_proper : IsProper K)
    (hK_simple : IsSimple ℝ K) :
    lowerClosure K ≤ upperClosure K := sorry

-- Proof sketch: use the order interval between the two closure representatives together with
-- Theorem 34.1 and Corollary 34.2.2 to place any intermediate concave-convex representative in
-- the same closed equivalence class, yielding closedness.
/-- Theorem 34.5 (3): among concave-convex saddle-functions, any function lying between the lower
and upper closures of a proper simple saddle-function `K` is closed. -/
theorem isClosed_of_between_closures_of_isSimple
    {K L : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_proper : IsProper K)
    (hK_simple : IsSimple ℝ K)
    (hL_shape : IsConcaveConvex ℝ L) :
    lowerClosure K ≤ L ∧ L ≤ upperClosure K →
      SaddleFunction.IsClosed L := sorry

-- Proof sketch: the same sandwich argument identifies any intermediate concave-convex
-- representative with members of the proper closed equivalence class determined by the two
-- closure representatives, so properness transports to `L`.
/-- Theorem 34.5 (4): among concave-convex saddle-functions, any function lying between the lower
and upper closures of a proper simple saddle-function `K` is proper. -/
theorem isProper_of_between_closures_of_isSimple
    {K L : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_proper : IsProper K)
    (hK_simple : IsSimple ℝ K)
    (hL_shape : IsConcaveConvex ℝ L) :
    lowerClosure K ≤ L ∧ L ≤ upperClosure K →
      IsProper L := sorry

-- Proof sketch: use the simplicity hypothesis to transport the kernel from `K` to the two
-- closure representatives, then apply the same closed-equivalence-class argument to any
-- intermediate `L` to identify its kernel with that of `K`.
/-- Theorem 34.5 (5): among concave-convex saddle-functions, any function lying between the lower
and upper closures of a proper simple saddle-function `K` has the same kernel as `K`. -/
theorem sameKernel_of_between_closures_of_isSimple
    {K L : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_proper : IsProper K)
    (hK_simple : IsSimple ℝ K)
    (hL_shape : IsConcaveConvex ℝ L) :
    lowerClosure K ≤ L ∧ L ≤ upperClosure K →
      SameKernel L K := sorry

-- Proof sketch: apply Theorem 34.4 to a closed proper concave-convex `L` with `SameKernel L K`
-- to place `L` in the same equivalence class as the two closure representatives of `K`, then use
-- the lower-closed and upper-closed extremality statements from Corollary 34.2.2 to recover the
-- two sandwich inequalities.
/-- Theorem 34.5 (6): among concave-convex saddle-functions, a closed proper function with the
same kernel as a proper simple saddle-function `K` lies between the lower and upper closures of
`K`. -/
theorem between_closures_of_isClosed_of_isProper_of_sameKernel_of_isSimple
    {K L : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_proper : IsProper K)
    (hK_simple : IsSimple ℝ K)
    (hL_shape : IsConcaveConvex ℝ L)
    (hL_closed : SaddleFunction.IsClosed L)
    (hL_proper : IsProper L)
    (hLK_kernel : SameKernel L K) :
    lowerClosure K ≤ L ∧ L ≤ upperClosure K := sorry

end

end Bifunction
