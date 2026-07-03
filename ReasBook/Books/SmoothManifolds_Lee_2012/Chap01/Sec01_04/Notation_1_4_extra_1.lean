import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Defs

-- Declarations for this item will be appended below by the statement pipeline.

section

open Module

/- Notation 1.4-extra-1: Lean keeps Einstein-style coordinate expansions explicit through
`Basis.sum_repr`, the canonical basis-expansion theorem writing a vector as the finite sum of its
coordinate functions against a chosen basis. This is the library-facing replacement for the
textbook abbreviation `x^i E_i`. -/
#check Basis.sum_repr

/- Standard-coordinate companion: on Euclidean space, the canonical orthonormal basis
`EuclideanSpace.basisFun` has coordinates given by the component functions, matching the textbook
convention that points of `R^n` are written with upper-indexed coordinates. -/
#check EuclideanSpace.basisFun_repr

end
