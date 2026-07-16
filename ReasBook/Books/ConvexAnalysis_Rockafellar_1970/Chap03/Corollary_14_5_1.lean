import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_4_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_13_2_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_5

-- Declarations for this item will be appended below by the statement pipeline.

section

open Bornology
open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:
- `source-facing`: Corollary 14.5.1 identifies boundedness of a set or of its polar with the
  origin lying in the interior of the dual set.
- `core/canonical`: the owner abstractions already present in the project are the set polar
  `Set.polar`, the canonical boundedness predicate `Bornology.IsBounded`, the structural owner
  theorems `Set.convex_polar` and `Set.polar_polar_eq`, and the interior owner theorem
  `Convex.mem_interior_iff_forall_exists_pos_add_smul_mem`.
- `bridge/view`: Rockafellar's notation `Cᵒ` is rendered directly by `Set.polar C`, and the two
  source clauses are exposed as separate atomic theorems on the `Convex` and `Set` owner surfaces.

Domain-style sampling used here:
- `Set.polar` and `Set.polar_closure` from `Text_14_0_5`;
- `Set.convex_polar` and `Set.polar_polar_eq` from `Theorem_14_5`;
- `Convex.mem_interior_iff_forall_exists_pos_add_smul_mem` from `Corollary_6_4_1`.
- mathlib's nearby dual-space polar owners `WeakDual.polar` and `LinearMap.polar`, inspected as
  neighbors but not reused because they formalize dual-valued or bilinear-form polars rather than
  the chapter's support-function sublevel set `Set.polar`.

Primitive data vs derived API:
- clause (1) primitive input: a convex set `C : Set E`;
- clause (1) derived output: boundedness of `Set.polar C` versus `0 ∈ interior C`;
- clause (2) primitive input: an arbitrary set `C : Set E`;
- clause (2) derived output: boundedness of `C` versus `0 ∈ interior (Set.polar C)`.

Layer target:
- clause (1) stays `source-facing`, but it belongs on the `Convex` owner abstraction rather than
  as a parallel global theorem carrying convexity as loose data;
- clause (2) stays `source-facing` on the `Set` owner surface, with no extra closedness or
  convexity packaging because those are mathematically redundant in the polar-interior criterion.

Ambient refinement:
- the supporting owner theorems already live on arbitrary finite-dimensional real inner-product
  spaces, so this file is stated at that intrinsic layer rather than in the coordinate model
  `EuclideanSpace ℝ (Fin n)`;
- the proof route for clause (1) should pass through `closure C`, but the public API should use the
  existing owner theorem `Set.polar_closure` instead of restating closure invariance through the
  support-function presentation;
- clause (1) needs the ambient space to be nontrivial. In the zero-dimensional case `E = PUnit`,
  the empty set has polar `univ`, which is bounded, while `0 ∉ interior ∅`, so the textbook
  bounded-polar/interior criterion is not valid without that ambient hypothesis.
-/

namespace Convex

variable [Nontrivial E]
variable {C : Set E}

-- Proof sketch: replace `C` by `closure C`. The owner identity `Set.polar_closure` gives
-- `(closure C)ᵒ[ℝ] = Cᵒ[ℝ]`, so Theorem 14.5 applies to `closure C`. Corollary 13.2.2 identifies
-- boundedness of `Set.polar C` with finiteness of its support function in every direction, and
-- Corollary 6.4.1 transports the resulting interior statement back from `closure C` to `C` using
-- convexity.
/-- Corollary 14.5.1 (1): on a nontrivial finite-dimensional real inner-product space, the polar
set `Cᵒ[ℝ]` of a convex set `C` is bounded if and only if the origin lies in `interior C`.
Specializing to `EuclideanSpace ℝ (Fin n)` with `n ≠ 0` recovers the textbook `R^n` statement. -/
theorem isBounded_polar_iff_zero_mem_interior (hC : Convex ℝ C) :
    IsBounded ((Cᵒ[ℝ] : Set E)) ↔ (0 : E) ∈ interior C := sorry

end Convex

namespace Set

-- Proof sketch: if `C` is bounded, choose `R > 0` with `‖x‖ ≤ R` for all `x ∈ C`. Then every
-- `xStar` with `‖xStar‖ < R⁻¹` satisfies `⟪x, xStar⟫ ≤ 1` on `C` by Cauchy-Schwarz, so a ball
-- around `0` lies in `Cᵒ[ℝ]`. Conversely, if a ball of radius `ε > 0` around `0` lies in
-- `Cᵒ[ℝ]`, then
-- for each `x ∈ C`, testing the polar inequality at `ε • ‖x‖⁻¹ • x` (or `0` when `x = 0`)
-- yields `‖x‖ ≤ ε⁻¹`, hence `C` is bounded.
/-- Corollary 14.5.1 (2): on a finite-dimensional real inner-product space, a set `C` is bounded
if and only if the origin lies in the interior of its polar set `Cᵒ[ℝ]`. Specializing to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
theorem isBounded_iff_zero_mem_interior_polar
    (C : Set E) :
    IsBounded C ↔ (0 : E) ∈ interior ((Cᵒ[ℝ] : Set E)) := sorry

end Set

end
