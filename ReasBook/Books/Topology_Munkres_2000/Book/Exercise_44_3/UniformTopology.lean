module

public import Topology_Munkres_2000.Book.Exercise_20_8.EventuallyZero

public section

/-- Eventually-zero real sequences equipped with the induced uniform topology. -/
noncomputable abbrev EventuallyZeroRealUniform :=
  WithTopology eventuallyZeroRealSequences eventuallyZeroRealUniformTopology
