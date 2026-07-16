import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_17_0_3

open Convexity

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {E : Type u} {R : Type v}
variable [Field R] [ConditionallyCompleteLinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup E] [Module R E]

local instance : ConvexSpace R E := ConvexSpace.ofModule
local instance : IsModuleConvexSpace R E := IsModuleConvexSpace.ofModule

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.1.5 states the Carathéodory refinement of Rockafellar's value
  formula for `conv(f)`, reducing the infimum from arbitrary finite convex combinations to ones
  using at most `n + 1` points in ambient dimension `n`, and then to ones with affinely
  independent support, where the same `n + 1` bound is then theorem-level data rather than
  primitive witness data.
- `core/canonical`: the owner abstractions already fixed in the project are `conv(f)` for the
  convex hull of a function, `Function.convexCombinationValues` for the unrestricted admissible
  value set, together with the chapter's finite-support simplex surface `StdSimplex R s`,
  `(w.map z).convexCombination`, and the canonical simplex sum surface `w.sum`.
- `bridge/view`: Theorem 17.0.3 supplies the finite-dimensional Carathéodory restriction from the
  unrestricted owner `Function.convexCombinationValues` to bounded-cardinality witnesses, while
  mathlib's `eq_pos_convex_span_of_mem_convexHull` is the affine-independent pruning owner for the
  unrestricted convex-hull side. In finite dimension,
  `AffineIndependent.card_le_finrank_succ` together with `Submodule.finrank_le` then recovers the
  cardinality bound automatically from the affine-independent support.

Domain-style sampling used here:
- `Function.convexHull_eq_sInf_convexCombination_values`;
- `Function.convexCombinationValues`;
- `StdSimplex.map_convexCombination_eq_sum`;
- `StdSimplex.sum`;
- `exists_convex_combination_card_le_of_mem_conv`;
- `eq_pos_convex_span_of_mem_convexHull`.
- `AffineIndependent`.

Primitive data vs derived API:
- primitive input: an arbitrary extended-real-valued function `f`;
- derived output: the Carathéodory-refined `sInf` formulas for `conv(f) x`, expressed directly as
  restrictions of the canonical owner surface `Function.convexCombinationValues`; the first uses a
  finite-dimensional cardinality bound, while in the second formula affine independence is
  primitive and the `finrank + 1` bound is only a derived finite-dimensional corollary of that
  affine-independent support.
  The represented point is written on the canonical owner surface
  `(w.map ((↑) : s → E)).convexCombination` rather than through its weighted-sum bridge.

Ambient minimization:
- the unrestricted owner `Function.convexHull_eq_sInf_convexCombination_values` already lives over
  an ordered field with conditionally complete order;
- Theorem 17.0.3 has the same ordered-field scalar layer, so the bounded-cardinality clause does
  not need to be specialized to `ℝ`;
- the affine-independent clause is only a finite-support pruning refinement, so it also does not
  need a finite-dimensional ambient hypothesis.

Layer target: `source-facing`, stated directly on the existing owners without introducing a local
package for admissible witness data.
-/

namespace Function

-- Proof sketch: start from `Function.convexHull_eq_sInf_convexCombination_values`, which writes
-- `conv(f) x` as the infimum over arbitrary finite convex combinations of epigraph points of `f`.
-- Apply Theorem 17.0.3 to the relevant epigraph convex-hull witness to replace each such witness
-- by one with at most `Module.finrank R E + 1` support points while preserving the same
-- represented base point `x` and the same height. State the represented point through the
-- canonical simplex surface `(w.map ((↑) : s → E)).convexCombination`, leaving the
-- weighted-sum equation only as an upstream bridge theorem. This yields the bounded-cardinality
-- formula.
/-- Corollary 17.1.5 (1): for an arbitrary function `f` on a finite-dimensional vector space over
an ordered field `R`, `conv(f) x` is the infimum of the weighted sums `∑ λᵢ f(xᵢ)` over
convex-combination representations of `x` using at most `Module.finrank R E + 1` points.
Specializing to `R = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n`
statement with `n + 1` points. -/
theorem convexHull_eq_sInf_convexCombination_values_card_le_finrank_succ
    [FiniteDimensional R E]
    (f : E → WithBotTop R) (x : E) :
    Function.convexHull (𝕜 := R) f x =
      sInf
        {r : WithBotTop R |
          ∃ s : Finset E, s.card ≤ Module.finrank R E + 1 ∧
            ∃ w : StdSimplex R s,
              x = (w.map ((↑) : s → E)).convexCombination ∧
                r = w.sum (fun i a ↦ (a : WithBotTop R) * f i)} := sorry

-- Proof sketch: refine the bounded-cardinality representation above by the usual Carathéodory
-- pruning argument inside the supporting simplex: discard affine dependencies among the support
-- points while keeping the represented point `x` and the same height on the epigraph side. This
-- affine-independent pruning is a finite-support phenomenon and does not use finite-dimensionality.
-- In finite dimension the surviving affine-independent support automatically has cardinality at
-- most `Module.finrank R E + 1` by `AffineIndependent.card_le_finrank_succ`.
/-- Corollary 17.1.5 (2): the same value formula remains valid when the support points are
required to be affinely independent; in finite dimension the `Module.finrank R E + 1` bound is a
derived consequence of affine independence, not extra primitive witness data. -/
theorem convexHull_eq_sInf_affineIndependent_convexCombination_values
    (f : E → WithBotTop R) (x : E) :
    Function.convexHull (𝕜 := R) f x =
      sInf
        {r : WithBotTop R |
          ∃ s : Finset E, AffineIndependent R ((↑) : s → E) ∧
            ∃ w : StdSimplex R s,
              x = (w.map ((↑) : s → E)).convexCombination ∧
                r = w.sum (fun i a ↦ (a : WithBotTop R) * f i)} := sorry

end Function

end
