import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped InnerProductSpace

/-
Source/core/bridge triage:
- `source-facing`: Text 6.1 introduces the Euclidean distance formula
  `d(x, y) = |x - y| = √(re ⟪x - y, x - y⟫)`.
- `core/canonical`: the owner abstraction is the ambient metric `dist` on an affine
  `NormedAddTorsor` over an inner-product space.
- `bridge/view`: `dist_eq_norm_vsub` rewrites that metric as the norm of the displacement vector,
  and
  `norm_eq_sqrt_re_inner` rewrites the norm through the inner product at the `RCLike` level.
- Primitive data vs derived API: the metric on points is primitive owner data; the norm and
  inner-product formulas are direct bridge statements on displacement vectors.
- Domain-style sampling used here: `dist_eq_norm_sub`, `dist_eq_norm_vsub`,
  and `norm_eq_sqrt_re_inner`.
- Layer target: the main entry is `core/canonical` with `vsub`, exposed under the owner namespace
  `NormedAddTorsor`; the subtraction theorem is the source-facing bridge specialization.
- Ambient minimization: the owner-level bridge only needs an `RCLike` scalar and an inner-product
  space structure.
-/

section ReInnerVSub

variable {𝕜 F P : Type*}
variable [RCLike 𝕜] [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [PseudoMetricSpace P] [NormedAddTorsor F P]

namespace NormedAddTorsor

/- Owner bridge: the distance identity with displacement vector is `dist_eq_norm_vsub`. -/
recall dist_eq_norm_vsub

/- Inner-product bridge at the weakest scalar layer (`RCLike`). -/
recall norm_eq_sqrt_re_inner

-- Proof sketch: compose the owner rewrites `dist_eq_norm_vsub` and `norm_eq_sqrt_re_inner`.
/-- In an affine `NormedAddTorsor` over an inner product space with `RCLike` scalar, distance is
the square root of the real part of the self-inner-product of the displacement vector. -/
theorem dist_eq_sqrt_re_inner (x y : P) :
    dist x y = √(RCLike.re ⟪x -ᵥ y, x -ᵥ y⟫_𝕜) := by
  simpa only [dist_eq_norm_vsub F] using norm_eq_sqrt_re_inner (x -ᵥ y)

end NormedAddTorsor

end ReInnerVSub

section ReInnerSub

variable {𝕜 F : Type*}
variable [RCLike 𝕜] [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Source-facing subtraction bridge of `NormedAddTorsor.dist_eq_sqrt_re_inner`. -/
theorem dist_eq_sqrt_re_inner_sub (x y : F) :
    dist x y = √(RCLike.re ⟪x - y, x - y⟫_𝕜) := by
  simp [dist_eq_norm_sub]

end ReInnerSub

end
