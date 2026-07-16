import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: the session did not provide `lean_leansearch`, so this statement uses the
-- chapter's verified `SmoothManifoldWithBoundary` owner and packages the defining-function
-- conditions in a local proof-only class to keep the proposition atomic.

open scoped Manifold

noncomputable section

section

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M]

/-- A boundary defining function is a smooth nonnegative real-valued function whose zero set is the
manifold boundary and whose manifold derivative is nonzero at every boundary point. -/
class IsBoundaryDefiningFunction (f : M → ℝ) : Prop where
  /-- The function is smooth as a map from the manifold with boundary to `ℝ`. -/
  contMDiff : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f
  /-- The function is nonnegative everywhere on the manifold. -/
  nonneg : ∀ x : M, 0 ≤ f x
  /-- The zero set of the function is exactly the boundary of the manifold. -/
  zero_preimage :
    f ⁻¹' {0} = {p : M | (𝓡∂ (n + 1)).IsBoundaryPoint p}
  /-- The manifold derivative is nonzero at every boundary point. -/
  mfderiv_ne_zero :
    ∀ p : M, (𝓡∂ (n + 1)).IsBoundaryPoint p →
      mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f p ≠ 0

/-- Proposition 5.43: every smooth manifold with boundary admits a boundary defining function. -/
theorem exists_boundary_defining_function :
    ∃ f : M → ℝ, @IsBoundaryDefiningFunction n M _ _ f := sorry

end
