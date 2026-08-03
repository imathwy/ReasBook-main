module

import Mathlib.Geometry.Manifold.Instances.Real

public section

universe u

/- Definition 78.2: A surface with boundary is a Hausdorff second-countable space
locally modeled on open subsets of `ℝ²` or `EuclideanHalfSpace 2`. The latter is
the canonical chart model: its interior charts also cover the `ℝ²` alternative. -/
#check fun (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 2) X] [T2Space X]
    [SecondCountableTopology X] ↦ X
