module

import Mathlib.Topology.Compactness.CompactlyCoherentSpace
import Mathlib.Topology.Sequences

public section

universe u

/-
Lemma 46.3. If `X` is weakly locally compact, or if `X` is first countable, then `X` is
compactly generated in the sense of `CompactlyCoherentSpace`.
-/
#check fun (X : Type u) [TopologicalSpace X] [WeaklyLocallyCompactSpace X] ↦
  (inferInstance : CompactlyCoherentSpace X)

#check fun (X : Type u) [TopologicalSpace X] [FirstCountableTopology X] ↦
  (inferInstance : CompactlyCoherentSpace X)
