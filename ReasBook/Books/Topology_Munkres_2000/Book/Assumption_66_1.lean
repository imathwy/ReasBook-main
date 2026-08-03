module

public import Mathlib.Analysis.Complex.CauchyIntegral
import Topology_Munkres_2000.Book.Remark_65_1
import Topology_Munkres_2000.Book.Theorem_9_0_1

/- Assumption 66.1: We assume a reformulated Cauchy integral formula and use it,
together with the Jordan-curve and winding-number theorems, to derive the classical
version. The following checks record the corresponding available results. -/
#check jordanCurve_complement_components
#check PuncturedPlaneMap.windingNumber_eq_one_or_neg_one_of_originComponent_bounded
#check Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
