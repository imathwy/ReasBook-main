import Mathlib.Analysis.InnerProductSpace.Projection.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section LinearImageCompatibleSmul

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {𝕜 : Type v} [Semiring 𝕜]
variable {E : Type w} [AddCommMonoid E] [Module 𝕜 E] [SMul R E]
variable {F : Type x} [AddCommMonoid F] [Module 𝕜 F] [SMul R F]
variable [LinearMap.CompatibleSMul E F R 𝕜]

/-- A convex set stays `R`-convex under a `𝕜`-linear map compatible with the `R`-action. -/
theorem Convex.linear_image_of_compatibleSMul
    {C : Set E} (hC : Convex R C) (f : E →ₗ[𝕜] F) :
    Convex R (f '' C) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  refine ⟨a • x' + b • y', hC hx' hy' ha hb hab, ?_⟩
  simp [map_add]

end LinearImageCompatibleSmul

section OrthogonalProjection

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Corollary 3.4.1: the orthogonal projection of an `R`-convex subset of an inner-product space
onto a subspace is again `R`-convex. -/
theorem Convex.orthogonalProjection_image [SMul R E] {C : Set E} (hC : Convex R C)
    (L : Submodule 𝕜 E) [L.HasOrthogonalProjection] [SMul R L]
    [LinearMap.CompatibleSMul E L R 𝕜] :
    Convex R (L.orthogonalProjection '' C) := by
  simpa using hC.linear_image_of_compatibleSMul (f := L.orthogonalProjection.toLinearMap)

end OrthogonalProjection
