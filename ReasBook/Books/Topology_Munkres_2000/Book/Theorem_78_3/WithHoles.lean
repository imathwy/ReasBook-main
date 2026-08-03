module

public import Topology_Munkres_2000.Book.Definition_78_4.Holes

public section

universe u v

namespace Surface

/-- A space is an `X`-with-`k`-holes when it is homeomorphic to the complement obtained
from some chosen family of `k` disjoint disk charts in `X`. -/
def IsWithHoles (Y : Type u) (X : Type v) [TopologicalSpace Y]
    [TopologicalSpace X] (k : ℕ) : Prop :=
  ∃ charts : HoleCharts X k, Nonempty (Y ≃ₜ withHoles charts)

/-- The relational view of an `X`-with-`k`-holes is witnessed by chosen hole charts and
a homeomorphism to their complement. -/
theorem isWithHoles_iff (Y : Type u) (X : Type v) [TopologicalSpace Y]
    [TopologicalSpace X] (k : ℕ) :
    IsWithHoles Y X k ↔
      ∃ charts : HoleCharts X k, Nonempty (Y ≃ₜ withHoles charts) := sorry


end Surface
