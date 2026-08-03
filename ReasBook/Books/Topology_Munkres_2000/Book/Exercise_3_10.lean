module

import Topology_Munkres_2000.Book.Example_3_9.OrderIso

/- Exercise 3.10 (a): The map `openUnitIntervalToReal` is strictly order-preserving. -/
#check openUnitIntervalToReal_strictMono

/- Exercise 3.10 (b): The inverse formula is
`y ↦ 2 * y / (1 + Real.sqrt (1 + 4 * y ^ 2))`. -/
#check realToOpenUnitIntervalValue

/- The displayed formula lies in `Set.Ioo (-1 : ℝ) 1`, so it defines the interval-valued
function `realToOpenUnitInterval`. -/
#check realToOpenUnitIntervalValue_mem
#check realToOpenUnitInterval

/- The interval-valued function is a left inverse of `openUnitIntervalToReal`. -/
#check realToOpenUnitInterval_leftInverse

/- The interval-valued function is a right inverse of `openUnitIntervalToReal`. -/
#check realToOpenUnitInterval_rightInverse
