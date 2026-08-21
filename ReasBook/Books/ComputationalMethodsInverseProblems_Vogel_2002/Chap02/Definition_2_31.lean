module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public section

/- Definition 2.31.

For a map `A : H₁ → H₂` between real normed spaces, Fréchet differentiability
at `f` is the canonical mathlib notion `DifferentiableAt ℝ A f`, with explicit
derivative witness `HasFDerivAt A A' f`.

Equation `(2.34)` is formalized by
`hasFDerivAt_iff_isLittleO_nhds_zero`. Higher derivatives are represented
recursively by `HasFDerivAt (fderiv ℝ A) A'' f`, where
`A'' : H₁ →L[ℝ] H₁ →L[ℝ] H₂`. The source bilinear map
`(h, k) ↦ (A'' k) h` is obtained from `A''` by `ContinuousLinearMap.flip`; the
pointwise coordinate swap, bounded bilinearity, and symmetry are recorded by
the checked declarations below.
-/

#check DifferentiableAt
#check HasFDerivAt
#check hasFDerivAt_iff_isLittleO_nhds_zero
#check ContinuousLinearMap.flip
#check ContinuousLinearMap.flip_apply
#check ContinuousLinearMap.isBoundedBilinearMap
#check second_derivative_symmetric_of_eventually_of_real
