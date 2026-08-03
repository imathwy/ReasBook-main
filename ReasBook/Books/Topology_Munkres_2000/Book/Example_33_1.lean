module

import Topology_Munkres_2000.Book.Example_31_2.Instances
import Topology_Munkres_2000.Book.Example_31_3.Separation
import Topology_Munkres_2000.Book.Example_32_2.Separation
import Mathlib.Topology.Separation.CompletelyRegular

universe u

/- Example 33.1 (1): The Sorgenfrey plane is completely regular. -/
#check (inferInstance : T35Space (SorgenfreyLine × SorgenfreyLine))

/- Example 33.1 (2): The Sorgenfrey plane is not normal in Munkres's convention. -/
#check SorgenfreyPlane.notT4

/- Example 33.1 (3): The product `S_Ω × S̄_Ω` is completely regular. -/
#check (inferInstance : T35Space (OpenOmegaOne.{u} × ClosedOmegaOne.{u}))

/- Example 33.1 (4): The product `S_Ω × S̄_Ω` is not normal in Munkres's convention. -/
#check OpenOmegaOne.prodClosedOmegaOne_notT4
