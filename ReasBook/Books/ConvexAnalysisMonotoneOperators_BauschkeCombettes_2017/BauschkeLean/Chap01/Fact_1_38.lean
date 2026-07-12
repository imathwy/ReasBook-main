import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} [MetricSpace X]
variable {Y : Type v} [TopologicalSpace Y]

/-- Fact 1.38: for a map from a metric space to a topological space, continuity is equivalent to
sequential continuity; no Hausdorff assumption on the codomain is needed. -/
-- Proof sketch: A metric space is first countable, hence a sequential space. Apply the existing
-- theorem `continuous_iff_seqContinuous` for maps out of sequential spaces.
theorem continuous_iff_seqContinuous_of_metricSpace {f : X → Y} :
    Continuous f ↔ SeqContinuous f := by
  -- Metric spaces are sequential spaces, so the general sequential-space criterion applies.
  -- This matches the textbook route while delegating the topology infrastructure to mathlib.
  simpa using (continuous_iff_seqContinuous : Continuous f ↔ SeqContinuous f)
