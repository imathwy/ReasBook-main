module

public import Topology_Munkres_2000.Book.Example_10_1.TwoCopiesPNat

import Mathlib.Order.Fin.Basic

public section

/- Example 10.1: The dictionary order well-orders the two successive sequences
`TwoCopiesPNat.a 1, TwoCopiesPNat.a 2, ...` and
`TwoCopiesPNat.b 1, TwoCopiesPNat.b 2, ...`. -/
#check (inferInstance : IsWellOrder TwoCopiesPNat (· < ·))
