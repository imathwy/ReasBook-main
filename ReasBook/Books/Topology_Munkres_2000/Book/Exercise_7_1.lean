module

public import Topology_Munkres_2000.Book.Definition_7_1.CountablyInfinite
import Mathlib.Data.Rat.Denumerable

public section

/-- Exercise 7.1: The rational numbers `ℚ` are countably infinite. -/
theorem rationals_countablyInfinite : (Set.univ : Set ℚ).CountablyInfinite :=
  Set.CountablyInfinite.ofEquiv
    ((Equiv.Set.univ ℚ).trans ((Denumerable.eqv ℚ).trans Equiv.pnatEquivNat.symm))

/- Mathlib's canonical type-level form of countable infinitude for `ℚ`. -/
#check Rat.instDenumerable
