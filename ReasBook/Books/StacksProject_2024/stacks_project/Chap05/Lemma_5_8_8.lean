import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Sober
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap05.Lemma_5_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Topology TopologicalSpace

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.8.8:
- primary domain: local behavior of `T₀`, quasi-sobriety, and sobriety under covers of a
  topological space;
- sampled owner declarations:
  `T0Space.of_cover`,
  `T0Space.of_open_cover`,
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`,
  `IsLocallyClosed.sober`;
- best owner abstractions: `T0Space` for the separation axiom, `QuasiSober` for generic-point
  existence, and `TopologicalSpace.IsOpenCover` for the canonical open-cover descent API, with
  `IsLocallyClosed.sober` as the chapter bridge for open pieces;
- primitive-vs-derived split: the primitive input is only a cover together with local-closed/open
  hypotheses on its pieces. The local `T₀`, quasi-sober, and sober conclusions are derived from
  the owner abstractions above, so this file should expose only the minimal bridge statements and
  direct recalls.

Source/core/bridge triage:
- `source-facing`: Lemma 5.8.8, asserting that `T₀`, quasi-sobriety, and sobriety are local on the
  covers described in the source;
- `core/canonical`: `T0Space.of_cover`, `T0Space.of_open_cover`, and
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`;
- `bridge/view`: the locally closed cover statement for `T₀`, and the owner-level open-cover
  sobriety theorem obtained from `T0Space.of_open_cover`, `TopologicalSpace.IsOpenCover.quasiSober`,
  and the earlier locally closed bridge `IsLocallyClosed.sober`.
-/

/-- Lemma 5.8.8 (1): for a cover of `X` by locally closed subsets, `X` is Kolmogorov if and only
if every member of the cover is Kolmogorov. -/
-- Proof sketch: for the forward implication, each subtype inherits `T0Space`. For the reverse
-- implication, use the canonical descent theorem `T0Space.of_cover` and the locally closed
-- decomposition to show any pair of topologically indistinguishable points lies in a common
-- `T₀` cover piece.
theorem t0Space_iff_forall_of_locallyClosed_cover
    (S : ι → Set X) (hcover : ⋃ i, S i = univ) (hloc : ∀ i, IsLocallyClosed (S i)) :
    T0Space X ↔ ∀ i, T0Space (S i) := sorry

/- Open-cover quasi-sobriety descent is provided canonically by
`TopologicalSpace.IsOpenCover.quasiSober_iff_forall`. -/
recall IsOpenCover.quasiSober_iff_forall

namespace TopologicalSpace.IsOpenCover

/- The `T₀` half of sober descent along an open cover is the canonical theorem
`T0Space.of_open_cover` together with the subtype instance on each `U i`. -/
/-- Lemma 5.8.8 (2): for an open cover `U` of `X`, sobriety is local on the cover, expressed via
the canonical `T0Space` and `QuasiSober` components. -/
-- Proof sketch: the `T₀` component descends by `T0Space.of_open_cover`, and the quasi-sober
-- component is exactly `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`.
theorem sober_iff_forall {U : ι → Opens X} (hU : IsOpenCover U) :
    (T0Space X ↔ ∀ i, T0Space (U i)) ∧ (QuasiSober X ↔ ∀ i, QuasiSober (U i)) := sorry

end TopologicalSpace.IsOpenCover
