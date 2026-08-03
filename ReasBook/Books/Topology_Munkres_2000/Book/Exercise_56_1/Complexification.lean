module

public import Topology_Munkres_2000.Book.Exercise_56_1.RootBound
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped BigOperators

public section

namespace Polynomial.IsRoot

/-- A complex root of a monic real polynomial lies in the open unit ball when the sum of the
norms of its non-leading coefficients is less than `1`. -/
theorem norm_lt_one_of_monic_real_map_of_sum_norm_lt_one (p : Polynomial ℝ) (hp : p.Monic)
    (hcoeff : (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) < 1) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) : ‖z‖ < 1 := by
  simpa using
    hz.norm_lt_one_of_monic_of_sum_norm_lt_one (p.map (algebraMap ℝ ℂ)) (hp.map _) (by simpa)

end Polynomial.IsRoot
