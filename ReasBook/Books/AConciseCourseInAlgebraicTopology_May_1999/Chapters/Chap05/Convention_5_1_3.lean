import Mathlib.Tactic.Recall
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Convention 5.1.3: compact spaces are understood in the Bourbaki sense, namely as compact
Hausdorff spaces. In mathlib this is expressed by combining the standard `CompactSpace` and
`T2Space` hypotheses; `CompactSpace` alone does not bundle Hausdorff separation. -/
recall CompactSpace (X : Type u) [TopologicalSpace X] : Prop
recall T2Space (X : Type u) [TopologicalSpace X] : Prop
