module

import Mathlib.Topology.Basic

/- Exercise 17.4 (1): If `U` is open and `A` is closed, then `U \ A` is open. -/
#check IsOpen.sdiff

/- Exercise 17.4 (2): If `A` is closed and `U` is open, then `A \ U` is closed. -/
#check IsClosed.sdiff
