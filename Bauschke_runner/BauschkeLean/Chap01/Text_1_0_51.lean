import Mathlib.Topology.Instances.EReal.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

/-- Text 1.0.51: the extended real line `EReal = [-∞, +∞]`, equipped with its canonical order
topology, is compact. The textbook description by real intervals together with rays at `⊥` and
`⊤` describes this same topology. -/
theorem extendedReal_compactSpace : CompactSpace EReal := inferInstance
