import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.MFDeriv.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section

universe uM

variable {n : ℕ} [NeZero n]
variable (M : Type uM) [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

/-- Definition 5.35-extra-3: a boundary defining function on a smooth manifold with boundary is a
smooth real-valued function that is nonnegative everywhere, vanishes exactly on the manifold
boundary, and has nonzero manifold derivative at every boundary point. -/
structure BoundaryDefiningFunction where
  /-- The underlying smooth real-valued function. -/
  toSmoothMap : C^∞⟮𝓡∂ n, M; ℝ⟯
  /-- The function takes values in `[0, ∞)`. -/
  nonneg_toSmoothMap : ∀ x : M, 0 ≤ toSmoothMap x
  /-- The zero set of the function is exactly the boundary of the manifold. -/
  zero_preimage : toSmoothMap ⁻¹' {0} = (𝓡∂ n).boundary M
  /-- The manifold derivative is nonzero at every boundary point. -/
  mfderiv_ne_zero :
    ∀ p : M, p ∈ (𝓡∂ n).boundary M → mfderiv (𝓡∂ n) 𝓘(ℝ) toSmoothMap p ≠ 0

/-- A boundary defining function can be used as its underlying real-valued function. -/
noncomputable instance : CoeFun (@BoundaryDefiningFunction n _ M _ _) (fun _ ↦ M → ℝ) where
  coe f := f.toSmoothMap

end
