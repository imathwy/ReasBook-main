module

import Mathlib.Topology.Algebra.Support

public section

/- Definition 36.3. For `φ : X → ℝ`, the support of `φ` is
`tsupport φ = closure (φ ⁻¹' ({0}ᶜ : Set ℝ))`. Equivalently, a point lies
outside `tsupport φ` exactly when `φ` is eventually equal to zero in its
neighborhood filter. -/
#check tsupport
#check notMem_tsupport_iff_eventuallyEq
