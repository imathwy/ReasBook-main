module

import Mathlib.Topology.Category.CompHaus.Basic

public section

open CategoryTheory

/- Exercise 38.10 (1): The Stone–Čech functor sends the identity map of a completely
regular space to the identity map of its Stone–Čech compactification. -/
#check topToCompHaus.map_id

/- Exercise 38.10 (2): The Stone–Čech functor sends a composite of maps between
completely regular spaces to the composite of their induced maps. -/
#check topToCompHaus.map_comp
