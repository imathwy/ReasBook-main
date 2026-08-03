module

import Topology_Munkres_2000.Book.Example_40_1
import Topology_Munkres_2000.Book.Example_40_2

open Set

/- Exercise 40.1 (Example 40.1): Open sets are `Gδ`; singletons are `Gδ` in
first-countable Hausdorff spaces; and `{Ω}` in `S̄_Ω` is not `Gδ`. -/
#check fun {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) ↦ hA.isGδ
#check fun {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (x : X) ↦ IsGδ.singleton x
#check ClosedOmegaOne.singleton_omega_not_isGδ

/- Exercise 40.1 (Example 40.2): Closed sets in metric spaces are `Gδ`, with
the stated presentation as intersections of open thickenings of radii `1 / (n + 1)`. -/
#check fun {X : Type*} [MetricSpace X] {A : Set X} (hA : IsClosed A) ↦ hA.isGδ
#check IsClosed.eq_iInter_thickening_inv_nat
