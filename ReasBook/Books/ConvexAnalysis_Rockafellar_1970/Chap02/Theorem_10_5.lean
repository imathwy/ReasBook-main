import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.5 characterizes global uniform continuity of a finite convex
  function on a finite-dimensional normed space over an ordered normed field, by global finiteness
  of its recession function, and then records the stronger global Lipschitz conclusion.
- `core/canonical`: the convexity owner on theorem surfaces is `ConvexOn 𝕜 Set.univ f`; the
  recession object is computed on the canonical codomain lift `f.toWithBotTop`. The other owners
  are mathlib's global continuity/Lipschitz predicates
  `UniformContinuous f` and `LipschitzWith α f`, together with the chapter effective-domain owner
  `dom(·)` applied to the recession function.
- `bridge/view`: the source's finite-valued convex function is viewed through the canonical
  codomain lift `Function.toWithBotTop`.

Domain-style sampling used here:
- `ConvexOn 𝕜 Set.univ f`;
- the project bridge `Function.toWithBotTop`;
- `Function.recessionFunction`;
- `Function.IsConvex.continuous_of_finite`;
- `LipschitzWith.uniformContinuous`.

Primitive data vs derived API:
- primitive input: global convexity `ConvexOn 𝕜 Set.univ f` of the finite-valued map;
- source-facing comparison object: the recession function of the canonical `WithBotTop` lift
  `f.toWithBotTop`;
- derived API: the global uniform continuity criterion, whose finite-value side is expressed by the
  intrinsic effective-domain owner condition `dom((f.toWithBotTop)₀⁺) = univ`; for a proper
  recession function, the alternative value `⊥` is already excluded. The stronger Lipschitz
  consequence uses the same owner-level finiteness hypothesis.

Layer target: `source-facing`, expressed with the canonical global continuity/Lipschitz owners and
the existing chapter recession-function owner, without introducing a parallel wrapper for finite
convex functions.

Scalar/ambient minimality note:
- this owner is kept at the finite-dimensional ordered normed-field layer needed by the
  convex-order and recession-function owners; no real-specific specialization is exposed on the
  theorem surfaces below.
-/

/- The canonical owner theorem used to pass from the Lipschitz conclusion in Theorem 10.5 to
uniform continuity. -/
recall LipschitzWith.uniformContinuous

variable (f : E → 𝕜)

-- Proof sketch: for the forward implication, use uniform continuity to bound each increment
-- `f (x + z) - f x` uniformly for small `z`, then apply the recession-function supremum formula to
-- deduce that `(f.toWithBotTop)₀⁺` takes finite scalar values on a neighborhood of `0`, hence
-- everywhere by positive homogeneity and properness of the recession function.
-- For the reverse implication, the owner bridge
-- `Function.IsConvex.continuous_of_finite` gives continuity of the recession function of the
-- `WithBotTop` lift `f.toWithBotTop`, so its restriction to the unit sphere has finite supremum
-- `α`.
-- Corollary 8.5.1
-- then yields `f y - f x ≤ f0⁺ (y - x) ≤ α ‖y - x‖`, and the same bound with `x` and `y`
-- exchanged gives a global Lipschitz estimate, hence uniform continuity.
/-- Theorem 10.5: for a finite-valued map `f : E → 𝕜` with intrinsically convex canonical lift
`ConvexOn 𝕜 Set.univ f`, global uniform continuity is equivalent to finiteness everywhere of
the recession function of that lift, rendered by `dom((f.toWithBotTop)₀⁺) = univ`. -/
theorem uniformContinuous_iff_recessionFunction_finite_everywhere
    [FiniteDimensional 𝕜 E]
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f) :
    UniformContinuous f ↔
      dom((f.toWithBotTop)₀⁺) = (Set.univ : Set E) := sorry

-- Proof sketch: by Theorem 10.5, finiteness of the recession function is equivalent to uniform
-- continuity. The second half of the same argument bounds the recession function on the unit
-- sphere by some `α`, and Corollary 8.5.1 converts that bound into the global estimate
-- `|f y - f x| ≤ α ‖y - x‖`, which is exactly `LipschitzWith α f`.
/-- If the recession function of the canonical `WithBotTop` lift of a globally convex finite-valued
function is finite everywhere, then the function is globally Lipschitz. -/
theorem exists_lipschitzWith_of_recessionFunction_finite_everywhere
    [FiniteDimensional 𝕜 E]
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hf_recession_finite : dom((f.toWithBotTop)₀⁺) = (Set.univ : Set E)) :
    ∃ α : NNReal, LipschitzWith α f := sorry

end
