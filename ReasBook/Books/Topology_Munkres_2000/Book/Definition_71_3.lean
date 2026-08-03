module

import Mathlib.Topology.Coherent

/-
Definition 71.3. For an indexed family `Xα : J → Set X` whose members cover `X`,
the topology of `X` is coherent with the family when it is
`Topology.IsCoherentWith (Set.range Xα)`. The covering condition
`⋃ α, Xα α = Set.univ` is separate from coherence. Closedness and, equivalently,
openness are detected by restriction to every member of the family.
-/
#check Topology.IsCoherentWith
#check Topology.IsCoherentWith.isClosed_iff
#check Topology.IsCoherentWith.isOpen_iff
