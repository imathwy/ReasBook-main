module

public import Topology_Munkres_2000.Book.Definition_13_3.RealLine

public section

/-- The real line equipped with the `K`-topology. -/
@[expose]
def RealKLine := ℝ

namespace RealKLine

/-- `RealKLine` has the field structure of the underlying real line. -/
noncomputable instance instField : Field RealKLine := inferInstanceAs (Field ℝ)

/-- `RealKLine` has the linear order of the underlying real line. -/
noncomputable instance instLinearOrder : LinearOrder RealKLine :=
  inferInstanceAs (LinearOrder ℝ)

/-- The field operations and order on `RealKLine` form a strictly ordered ring. -/
instance instIsStrictOrderedRing : IsStrictOrderedRing RealKLine :=
  inferInstanceAs (IsStrictOrderedRing ℝ)

/-- The topology on `RealKLine` is the `K`-topology. -/
instance instTopologicalSpace : TopologicalSpace RealKLine := RealTopology.k

/-- The topology on `RealKLine` is `RealTopology.k`. -/
theorem topology_eq_k :
    (inferInstance : TopologicalSpace RealKLine) = RealTopology.k := rfl

end RealKLine


end
