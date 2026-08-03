module

public import Mathlib.Topology.Compactness.CompactlyCoherentSpace

public section

/-
Definition 46.4. A compactly generated space in the sense of Munkres is mathlib's
`CompactlyCoherentSpace`; openness is characterized by restriction to every compact
subspace via `CompactlyCoherentSpace.isOpen_iff`.
-/
#check CompactlyCoherentSpace
#check CompactlyCoherentSpace.isOpen_iff
