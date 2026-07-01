import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_2_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_0_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_26_4

noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 26.3 says that for a closed proper convex function, essential strict
  convexity is equivalent to essential smoothness of the Fenchel conjugate.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Function.IsEssentiallyStrictlyConvex`, `Function.IsEssentiallySmooth`, and Fenchel conjugation
  `f⋆`.
- `bridge/view`: the proof route stays on the intrinsic subdifferential-graph owner
  `_root_.subdifferentialGraph`, together with
  `_root_.subdifferentialGraph_convexConjugate_eq_inv` from `Text_26_0_1` and the Chapter 26
  graph-uniqueness owner theorems
  `_root_.rightUnique_subdifferentialGraph_primalCodomain_iff_isEssentiallySmooth` from
  `Theorem_26_1` and
  `_root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`
  from `Theorem_26_4`.

Domain-style sampling used here:
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- Fenchel conjugation `f⋆` from `Text_26_0_1`;
- `_root_.subdifferentialGraph_convexConjugate_eq_inv` from `Text_26_0_1`;
- `_root_.rightUnique_subdifferentialGraph_primalCodomain_iff_isEssentiallySmooth` from
  `Theorem_26_1`;
- `_root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex` from
  `Theorem_26_4`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f` and its conjugate `f⋆`;
- primitive owner predicates: `f.IsEssentiallyStrictlyConvex` and `f⋆.IsEssentiallySmooth`;
- derived API here: none.

Layer target: `source-facing`, stated directly with the intrinsic Chapter 26 owners from
Definitions 26.1.1 and 26.2.1.
-/

namespace Function.IsClosedProperConvex

variable {f : E → WithBotTop ℝ}
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)
local notation "f⋆ₛ" => ((f⋆ : StrongDual ℝ E → WithBotTop ℝ))

-- Proof sketch: rewrite essential strict convexity of `f` as left-uniqueness of the intrinsic
-- graph owner `_root_.subdifferentialGraph f`, identify that owner with right-uniqueness of the
-- conjugate graph through `_root_.subdifferentialGraph_convexConjugate_eq_inv`, and apply
-- Theorem 26.1 to `f⋆`.
/-- Theorem 26.3: for a closed proper convex function on the ambient finite-dimensional real
normed space used in Chapter 26, essential strict convexity is equivalent to essential
smoothness of the Fenchel conjugate.

Scalar-layer note: this declaration remains over `ℝ` because, in this dependency closure, the
owner predicates `Function.IsEssentiallyStrictlyConvex` and `Function.IsEssentiallySmooth`
and the subdifferential-owner bridges in Theorems 26.1/26.4 are themselves real-specific. -/
theorem isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth
    (hf : IsClosedProperConvex[ℝ] f) :
    Function.IsEssentiallyStrictlyConvex f ↔
      f⋆ₛ.IsEssentiallySmooth := by
  sorry

end Function.IsClosedProperConvex

end
