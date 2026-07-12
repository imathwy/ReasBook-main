import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_5_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_6_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [IsTopologicalAddGroup V]
  [Module 𝕜 V] [ContinuousSMul 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]
variable {C1 C2 : Set V}

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 11.3 characterizes when two nonempty convex sets admit a proper
  separating hyperplane.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, the chapter relation
  `AffineSubspace.SeparatesProperly`, and the relative interior operator `intrinsicInterior 𝕜`.
- `bridge/view`: Rockafellar's `ri C₁` and `ri C₂` are represented by `ri[𝕜](C1)` and
  `ri[𝕜](C2)` as a thin notation bridge over `intrinsicInterior 𝕜`, while proper separation is
  represented at raw owner level by `AffineSubspace.SeparatesProperly Y H C1 C2`.
- Best owner abstraction: there is no exact upstream theorem with the target interface, so the
  public owner layer here remains the Chapter 11 relation `AffineSubspace.SeparatesProperly`
  together with the canonical owner `intrinsicInterior 𝕜`; the `ri[𝕜](·)` surface is a
  source-facing bridge theorem, not the primitive owner statement.
- Primitive data vs derived API: the primitive inputs are the two sets together with convexity
  and nonemptiness. The proper-separation criterion and the relative-interior disjointness
  condition are theorem-level content.
- Domain-style sampling used here: the Chapter 11 owner predicate
  `AffineSubspace.SeparatesProperly` from `Text_11_0_2`, the separation theorem
  `exists_separating_hyperplane_containing_of_disjoint_relativelyOpen_convex` from
  `Theorem_11_2`, the owner-side Minkowski-sum relative-interior formula
  `Convex.intrinsicInterior_add` from `Corollary_6_6_2`, and the relative-interior inclusion
  theorem from `Corollary_6_5_2`.
- Layer target: `source-facing`, with the theorem stated directly in the existing Chapter 11
  owner relation and the canonical intrinsic-interior API, rather than through a new separation
  wrapper.
- Ambient refinement: although Rockafellar states the theorem in coordinate form, the owner
  abstractions for proper separation and relative interior already live on finite-dimensional
  topological pairing modules, so the public statement is kept at that canonical ambient level
  rather than a concrete coordinate model.
-/

/-- Theorem 11.3 at the primitive owner layer: for nonempty convex sets `C1` and `C2` in a
finite-dimensional topological pairing module over `𝕜`, there exists a hyperplane separating `C1`
and `C2` properly if and only if their intrinsic interiors are disjoint. -/
-- Proof sketch: apply Theorem 11.2 to the pointwise difference set `C1 - C2` and the affine set
-- `{0}`. Rewriting `C1 - C2` as `C1 + (-C2)` and using Corollary 6.6.2 identifies its relative
-- interior with `ri[𝕜](C1) + (-ri[𝕜](C2))`, so the origin lies outside that relative interior
-- exactly when `ri[𝕜](C1)` and `ri[𝕜](C2)` are disjoint. The resulting separating hyperplane for
-- `C1 - C2` is equivalent to a proper separating hyperplane for `C1` and `C2`, and the converse
-- uses Corollary 6.5.2 to push the relative interior of `C1 - C2` into the open half-space
-- determined by the separator.
theorem exists_separatesProperly_iff_disjoint_intrinsicInterior
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 V, AffineSubspace.SeparatesProperly Y H C1 C2) ↔
      Disjoint (intrinsicInterior 𝕜 C1) (intrinsicInterior 𝕜 C2) := sorry

/-- Source-facing `ri` bridge form of Theorem 11.3. -/
theorem exists_separatesProperly_iff_disjoint_ri
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 V, AffineSubspace.SeparatesProperly Y H C1 C2) ↔
      Disjoint (ri[𝕜](C1)) (ri[𝕜](C2)) := by
  simpa using exists_separatesProperly_iff_disjoint_intrinsicInterior
    (Y := Y) hC1_conv hC1_nonempty hC2_conv hC2_nonempty

end
