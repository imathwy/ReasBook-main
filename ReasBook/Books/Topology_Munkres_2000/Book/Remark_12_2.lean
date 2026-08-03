module

import Mathlib.Topology.Order

/-
Remark 12.2. If the collection of open sets of `𝒯'` contains that of `𝒯`,
then `𝒯'` may be called larger than `𝒯`, and `𝒯` smaller than `𝒯'`.
This is the same comparison as saying that `𝒯'` is finer than `𝒯`; in Lean's
reversed order on topologies it is written `𝒯' ≤ 𝒯`.
-/
#check TopologicalSpace.le_def
