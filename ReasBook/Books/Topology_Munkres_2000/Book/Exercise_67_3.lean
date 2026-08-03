module

public import Mathlib.LinearAlgebra.Determinant

public section

/- Exercise 67.3 is blocked pending authoritative corrected coefficients or explicit
authorization to replace the printed positive claim by its counterstatement. For the
displayed family, the basis-relative coefficient matrix has determinant `-5`, which is
not a unit in `ℤ`; the canonical determinant criterion below therefore obstructs the
printed conclusion. -/
#check Module.Basis.is_basis_iff_det
