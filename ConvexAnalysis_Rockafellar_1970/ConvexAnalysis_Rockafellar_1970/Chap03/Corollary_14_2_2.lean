import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_7_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open Bornology
open scoped Rockafellar

variable {E Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace Y] [AddCommMonoid Y] [Module ℝ Y]
variable [HasLinearPairing E Y ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 14.2.2 characterizes when every real sublevel set
  `{x | f x ≤ α}` of a closed proper convex function is bounded.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.IsClosedProperConvex`, `Function.recessionFunction`,
  `Function.recessionCone`, `convexConjugate`, the interior operator on subsets of `Y`, and
  mathlib's boundedness predicate `Bornology.IsBounded`, together with the chapter owner
  `dom(f⋆)` for `dom f*`.
- `bridge/view`: this file is stated on the pairing-level dual ambient owner `Y`, so the dual
  effective-domain side is `dom(f⋆)` without fixing the concrete model `StrongDual ℝ E`.

Domain-style sampling used here:
- `Function.IsClosedProperConvex`;
- `Function.IsConvex.isBounded_sublevel_of_nonempty_bounded_sublevel`;
- `recessionCone_sublevelSet_eq_functionRecessionCone`;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero`;
- `mem_interior_iff_forall_ne_zero_dual_lt_supportFunction`;
- the Chapter 13 effective-domain/support-function recession bridge for Fenchel conjugates.

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot ℝ`;
- owner hypothesis: `f.IsClosedProperConvex`;
- owner invariant: `Function.recessionCone (Function.recessionFunction f)`;
- derived API: boundedness of every real sublevel set and the interior criterion at the origin for
  `dom(f⋆)` on the dual ambient owner `Y`.

Layer target: `source-facing`, stated directly in the bounded-sublevel-set language of the source
and the canonical dual effective-domain owner for `dom f*`.

Ambient refinement: the source-facing owner statement only needs the finite-dimensional real
normed-space layer on the primal side and a pairing-level real topological module ambient `Y`, so
the surface avoids fixing a concrete dual realization (for example `StrongDual ℝ E`) or an
`InnerProductSpace` identification.

Scalar/codomain/topology checks for this item:
- codomain: the statement is kept at `WithTopBot ℝ`, matching the reused Chapter 8/13 recession
  and support-function bridge owners;
- scalar: this corollary remains genuinely `ℝ`-scalar in this dependency closure, since the
  boundedness/recession owner route it uses is currently developed on the real layer;
- topology: ambient `interior` is the source-facing primary clause and is the direct output owner
  of this Chapter 14 criterion, while the intrinsic/relative surface is exposed immediately below
  as a canonical consequence via `interior_subset_intrinsicInterior`.
-/

-- Proof sketch: choose one finite point of `f` from properness, hence one canonical nonempty real
-- sublevel set `S α0`. Corollary 8.7.1 packages the source fact that boundedness of this one
-- nonempty sublevel set is equivalent to boundedness of every real sublevel set, so it remains to
-- compare `IsBounded (S α0)` with `0 ∈ interior dom(f⋆)`. Theorem 8.4 makes boundedness of
-- `S α0` equivalent to triviality of its recession cone, and Theorem 8.7 identifies that cone
-- with the common owner `Function.recessionCone (f0⁺)`. This triviality is equivalent to strict
-- positivity of `f0⁺` on every nonzero direction, and the Chapter 13 interior/support and
-- effective-domain/recession bridges identify that positivity criterion with
-- `0 ∈ interior dom(f⋆)` on the paired dual side.
/- Corollary 14.2.2: for a closed proper convex function `f` on a finite-dimensional real normed
space with a real pairing into a dual topological module `Y`, every real sublevel set
`{x | f x ≤ α}` is bounded if and only if the dual-side origin lies in the interior of the
effective domain `dom(f⋆)`. -/
namespace Function.IsClosedProperConvex

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-- Primitive owner form for Corollary 14.2.2: boundedness of one nonempty real sublevel set is
equivalent to interior membership of `0` in `dom(f⋆)`. -/
theorem exists_nonempty_bounded_sublevelSet_iff_zero_mem_interior_effectiveDomain_convexConjugate
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (∃ α : ℝ, ({x : E | f x ≤ α}).Nonempty ∧ IsBounded {x : E | f x ≤ α}) ↔
      0 ∈ interior dom(f⋆) := by
  sorry

theorem all_sublevelSets_bounded_iff_zero_mem_interior_effectiveDomain_convexConjugate
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (∀ α : ℝ, IsBounded {x : E | f x ≤ α}) ↔
      0 ∈ interior dom(f⋆) := by
  constructor
  · intro hall
    rcases (Function.isProper_iff.mp hf.proper) with ⟨⟨x0, hx0_dom⟩, hnot_bot⟩
    lift (f x0) to ℝ using ⟨hx0_dom.ne, hnot_bot x0⟩ with α0 hα0
    have hnonempty : ({x : E | f x ≤ α0}).Nonempty := by
      refine ⟨x0, ?_⟩
      change f x0 ≤ (α0 : WithTopBot ℝ)
      simpa [hα0]
    have hexists :
        ∃ α : ℝ, ({x : E | f x ≤ α}).Nonempty ∧ IsBounded {x : E | f x ≤ α} :=
      ⟨α0, hnonempty, hall α0⟩
    exact
      (hf.exists_nonempty_bounded_sublevelSet_iff_zero_mem_interior_effectiveDomain_convexConjugate).1
        hexists
  · intro h0
    rcases
        (hf.exists_nonempty_bounded_sublevelSet_iff_zero_mem_interior_effectiveDomain_convexConjugate).2
          h0 with
      ⟨α0, hnonempty, hbounded⟩
    exact
      hf.convex.isBounded_sublevel_of_nonempty_bounded_sublevel
        hf.closed α0 hnonempty hbounded

/-- Intrinsic/relative consequence of Corollary 14.2.2: boundedness of every real sublevel set
forces `0` to lie in `ri(dom(f⋆))`. -/
theorem all_sublevelSets_bounded_imp_zero_mem_riDom_convexConjugate
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (∀ α : ℝ, IsBounded {x : E | f x ≤ α}) →
      0 ∈ riDom(f⋆) := by
  intro hbounded
  exact interior_subset_intrinsicInterior
    ((hf.all_sublevelSets_bounded_iff_zero_mem_interior_effectiveDomain_convexConjugate).1
      hbounded)

end Function.IsClosedProperConvex

end
