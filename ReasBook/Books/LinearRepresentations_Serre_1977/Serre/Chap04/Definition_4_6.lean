import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `Measure.haarMeasure` is the generic mathlib Haar owner, while Chapter 4
-- already fixes the normalized compact-group owner as `normalizedHaarMeasure`, with normalization
-- recorded by `normalizedHaarMeasure_univ`.

universe u

section

variable (G : Type u) [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]

/- Source/core/bridge triage:
- `source-facing`: Definition 4-6 names the measure `dt` from Theorem 4-5 as the invariant or
  Haar measure of `G`, normalized by total mass `1`;
- `core/canonical`: `normalizedHaarMeasure`;
- `bridge/view`: `μG` is the textbook shorthand for that measure, and
  `normalizedHaarMeasure_univ` / `μG_univ` are the source-facing normalization companions.

This item is therefore recall-only: the owner already exists in the Chapter 4 API, so the refined
surface keeps the canonical recall and exposes only the textbook shorthand and normalization
companions needed downstream. -/

/- Definition 4-6: the measure `dt` of Theorem 4-5, called the invariant measure or Haar
measure of `G`, is the canonical Chapter 4 owner `normalizedHaarMeasure`. -/
recall normalizedHaarMeasure

/- The textbook notation `μ_G`, written in Lean as `μG`, is the Chapter 4 shorthand for the
normalized Haar measure of `G`. -/
recall μG

/- The normalization of the Haar measure from Definition 4-6 is the companion theorem
`normalizedHaarMeasure_univ`, stating that the total mass of `normalizedHaarMeasure` is `1`. -/
recall normalizedHaarMeasure_univ

/- In the textbook shorthand, the normalized Haar measure satisfies `μG Set.univ = 1`. -/
theorem μG_univ : μG (Set.univ : Set G) = 1 := by
  rw [μG]
  exact (normalizedHaarMeasure_univ : normalizedHaarMeasure (Set.univ : Set G) = 1)

end
