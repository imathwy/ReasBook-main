import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark II.2-extra-4: for complex-valued functions on an open set, holomorphicity and
analyticity are equivalent. -/
recall Complex.analyticOnNhd_iff_differentiableOn

/- A holomorphic function on an open subset of `ℂ` is `C^n` there for every order `n`, hence in
particular it is infinitely differentiable and continuously differentiable. -/
recall DifferentiableOn.contDiffOn

/- The derivative of a holomorphic function on an open subset of `ℂ` is again holomorphic there. -/
recall DifferentiableOn.deriv
