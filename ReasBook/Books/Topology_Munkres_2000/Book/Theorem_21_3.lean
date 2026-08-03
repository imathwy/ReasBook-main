module

import Mathlib.Topology.Sequences

public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Theorem 21.3 (1): A continuous function preserves limits of sequences. -/
#check Continuous.seqContinuous

variable [TopologicalSpace.MetrizableSpace X]

/- Theorem 21.3 (2): On a metrizable domain, preservation of sequential limits
implies continuity. -/
#check (SeqContinuous.continuous : ∀ {f : X → Y}, SeqContinuous f → Continuous f)
