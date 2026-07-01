import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped Rockafellar

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜]
variable {E : Type v} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {Y : Type w} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
  [HasLinearPairing.Nondegenerate E Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 20.2 characterizes when a nonempty convex set can be properly separated
  from a nonempty polyhedral convex set by a hyperplane that does not contain the right-hand set.
- `core/canonical`: the owner abstractions are `AffineSubspace.SeparatesProperly`, the subset
  predicates `Convex 𝕜` and `Set.IsPolyhedral` in the same pairing codomain `Y`, and the
  relative interior owner notation `ri[𝕜](·)`.
- `bridge/view`: Rockafellar's `ri C₂` is represented by `ri[𝕜](C2)`, and the source's
  separator is recorded by the Chapter 11 owner `H.SeparatesProperly Y C1 C2` together with the
  source-asymmetric clause `¬ C2 ⊆ H`.
- Primitive data vs derived API: the primitive inputs are the sets `C1`, `C2` and the hypotheses
  that `C1` is polyhedral and nonempty while `C2` is convex and nonempty; the separation criterion
  and the relative-interior disjointness condition are the derived theorem-level content.
- Domain-style sampling used here: the project declarations `AffineSubspace.SeparatesProperly`,
  `Set.IsPolyhedral`, and `Set.IsPolyhedral.convex`, together with the chapter owner notation
  `ri[𝕜](·)` and `Disjoint`.
- Layer target: `source-facing`, but attached to the left owner `Set.IsPolyhedral` rather
  than kept as a parallel free-standing theorem, with proper separation carried by the existing
  owner `AffineSubspace.SeparatesProperly` and the right-side noncontainment clause kept explicit.
- Ambient refinement: no coordinate-level data are used, and the separator owner is pairing-based
  with an explicit pairing codomain `Y`, so the theorem lives canonically on finite-dimensional
  topological pairing modules over an ordered-compatible topological scalar layer, rather than on
  any concrete inner-product coordinate model.
- Nondegeneracy boundary: `HasLinearPairing E Y 𝕜` by itself allows degenerate pairings, which can
  invalidate the source equivalence. The theorem therefore uses the canonical pairing owner
  class `HasLinearPairing.Nondegenerate E Y 𝕜`.
-/

namespace Set.IsPolyhedral

/-- Theorem 20.2: for a nonempty polyhedral convex set `C1` and a nonempty convex set `C2` in a
finite-dimensional topological nondegenerate pairing module over `𝕜`, there exists a hyperplane
that separates `C1` from `C2` properly and does not contain `C2` if and only if
`C1 ∩ ri[𝕜](C2) = ∅`, represented canonically as `Disjoint C1 (ri[𝕜](C2))`.
This keeps proper separation on the canonical owner surface while retaining the source's
asymmetric right-side noncontainment clause explicitly. -/
-- Proof sketch: for necessity, if `H.SeparatesProperly C1 C2` and `C2` is not contained in `H`,
-- then `ri[𝕜](C2)` lies in the open half-space on the `C2` side of `H`,
-- hence it is disjoint
-- from `C1`. For sufficiency, intersect `C1` with `affineSpan 𝕜 C2`; if this intersection is
-- empty, use the strong separation theorem for a polyhedral set and an affine subspace. Otherwise
-- first separate inside `affineSpan 𝕜 C2`, enlarge `C2` to a polyhedral half-space of that affine
-- span, and reduce to the polyhedral-polyhedral separation argument from Corollary 19.3.3.
theorem exists_separator_not_subset_right_iff_disjoint_ri
    {C1 C2 : Set E} (hC1 : C1.IsPolyhedral 𝕜 Y) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_ne : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H C1 C2 ∧ ¬ C2 ⊆ H) ↔
      Disjoint C1 (ri[𝕜](C2)) := sorry

end Set.IsPolyhedral

end
