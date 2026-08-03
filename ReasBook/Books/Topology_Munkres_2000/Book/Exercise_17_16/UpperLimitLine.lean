module

public import Topology_Munkres_2000.Book.Exercise_13_7
import Topology_Munkres_2000.Book.Lemma_13_4

public section

/-- The real line equipped with the upper-limit topology. -/
@[expose]
def UpperLimitLine := ℝ

namespace UpperLimitLine

/-- The carrier equivalence from the upper-limit line to the real numbers. -/
def toReal : UpperLimitLine ≃ ℝ := Equiv.refl ℝ

/-- The topology on `UpperLimitLine` is the upper-limit topology. -/
instance instTopologicalSpace : TopologicalSpace UpperLimitLine := RealTopology.upperLimit

/-- The topology on `UpperLimitLine` is `RealTopology.upperLimit`. -/
theorem topology_eq_upperLimit :
    (inferInstance : TopologicalSpace UpperLimitLine) = RealTopology.upperLimit := rfl

/-- The upper-limit line is Hausdorff. -/
instance instT2Space : T2Space UpperLimitLine := by
  -- Hausdorffness passes from the standard topology to the finer upper-limit topology.
  exact @t2Space_antitone ℝ RealTopology.upperLimit _
    (RealTopology.upperLimit_lt_k.le.trans (RealTopology.k_lt_standard).le) inferInstance

end UpperLimitLine


end
