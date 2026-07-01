import Mathlib
import SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_8
import SmoothManifoldsLee.Chap04.Sec04_27.Problem_4_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Proposition_4_8`, `Problem_4_1`, and mathlib's interior/boundary API for local diffeomorphisms.

open scoped Manifold ContDiff
open Manifold

universe uM uN

section TargetBoundary

variable {m n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n) N]
  [IsManifold (𝓡∂ n) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "J_n" => 𝓡∂ n

/-- Helper for Exercise 4.9: at a fixed point, an immersion and smooth submersion into a target
with boundary have invertible manifold derivative. -/
lemma mfderiv_isInvertible_of_immersion_and_submersion_target_boundary_point
    {F : M → N} (hFimm : IsImmersion I_m J_n ∞ F) (hFsubm : IsSmoothSubmersion I_m J_n F)
    (p : M) :
    (mfderiv I_m J_n F p).IsInvertible := by
  have hSmooth : ContMDiff I_m J_n ∞ F := hFsubm.contMDiff
  letI : NormedAddCommGroup (TangentSpace I_m p) := by
    change NormedAddCommGroup (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I_m p) := by
    change NormedSpace ℝ (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : CompleteSpace (TangentSpace I_m p) := by
    change CompleteSpace (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : NormedAddCommGroup (TangentSpace J_n (F p)) := by
    change NormedAddCommGroup (EuclideanSpace ℝ (Fin n))
    infer_instance
  letI : NormedSpace ℝ (TangentSpace J_n (F p)) := by
    change NormedSpace ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  letI : CompleteSpace (TangentSpace J_n (F p)) := by
    change CompleteSpace (EuclideanSpace ℝ (Fin n))
    infer_instance
  -- The immersion/submersion characterizations give pointwise injectivity and surjectivity.
  have hinj : Function.Injective (mfderiv I_m J_n F p) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv hSmooth).mp hFimm p
  have hsurj : Function.Surjective (mfderiv I_m J_n F p) :=
    hFsubm.surjective_mfderiv p
  -- A bijective continuous linear map between the tangent spaces is invertible.
  exact ContinuousLinearMap.isInvertible_of_bijective hinj hsurj

/-- Exercise 4.9 (1): Proposition 4.8 (1) still holds when the target `N` is allowed to be a
smooth manifold with boundary, while the source `M` remains boundaryless. -/
theorem is_local_diffeomorph_iff_is_immersion_and_is_smooth_submersion_target_boundary
    {F : M → N} :
    IsLocalDiffeomorph I_m J_n ∞ F ↔
      IsImmersion I_m J_n ∞ F ∧ IsSmoothSubmersion I_m J_n F := by
  refine ⟨fun hF ↦ ⟨hF.isImmersion, hF.isSmoothSubmersion⟩, ?_⟩
  rintro ⟨hFimm, hFsubm⟩
  have hSmooth : ContMDiff I_m J_n ∞ F := hFsubm.contMDiff
  intro p
  -- The boundaryless source lets the inverse function theorem use the invertible `mfderiv`.
  have hInv : (mfderiv I_m J_n F p).IsInvertible :=
    mfderiv_isInvertible_of_immersion_and_submersion_target_boundary_point hFimm hFsubm p
  exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
    (I := I_m) (J := J_n) (n := ∞) (by simp)
    BoundarylessManifold.isInteriorPoint hSmooth hInv

/-- Exercise 4.9 (2): if the source is boundaryless, then Proposition 4.8 (2) still holds when the
target is a smooth manifold with boundary of the same dimension. -/
theorem is_local_diffeomorph_of_is_immersion_of_eq_dim_target_boundary {F : M → N}
    (hmn : m = n) (hF : IsImmersion I_m J_n ∞ F) :
    IsLocalDiffeomorph I_m J_n ∞ F :=
  hF.isLocalDiffeomorph_of_eq_finrank (by
    simpa [finrank_euclideanSpace_fin] using hmn)

/-- Exercise 4.9 (3): if the source is boundaryless, then Proposition 4.8 (3) still holds when the
target is a smooth manifold with boundary of the same dimension. -/
theorem is_local_diffeomorph_of_is_smooth_submersion_of_eq_dim_target_boundary {F : M → N}
    (hmn : m = n) (hF : IsSmoothSubmersion I_m J_n F) :
    IsLocalDiffeomorph I_m J_n ∞ F :=
  hF.isLocalDiffeomorph_of_eq_finrank (by
    simpa [finrank_euclideanSpace_fin] using hmn)

end TargetBoundary

section SourceBoundary

variable (n : ℕ) [NeZero n]

/-- Helper for Exercise 4.9: the manifold derivative of the half-space inclusion is the identity
at every point of the half-space model. -/
lemma euclidean_half_space_inclusion_mfderiv_eq_id (p : EuclideanHalfSpace n) :
    mfderiv (𝓡∂ n) (𝓡 n) (EuclideanHalfSpace.inclusion n) p =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) p) := by
  -- The inclusion is the model-with-corners map itself, so its derivative is the model identity.
  simpa [EuclideanHalfSpace.inclusion] using ((𝓡∂ n).hasMFDerivAt (x := p)).mfderiv

/-- Exercise 4.9 (4): Proposition 4.8 (2) fails if the source manifold is allowed to have
boundary; the canonical inclusion `ℍ^n ↪ ℝ^n` is a same-dimensional smooth immersion, but it is
not a local diffeomorphism. -/
theorem euclidean_half_space_inclusion_is_immersion_not_local_diffeomorph :
    IsImmersion (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) ∧
      ¬ IsLocalDiffeomorph (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) := by
  refine ⟨?_, euclideanHalfSpace_inclusion_not_isLocalDiffeomorph n⟩
  -- Rewriting the derivative to `id` shows injectivity at every point.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv
    (euclideanHalfSpace_inclusion_contMDiff n)).2 ?_
  intro p
  rw [euclidean_half_space_inclusion_mfderiv_eq_id (n := n) p]
  intro x y hxy
  simpa using hxy

end SourceBoundary
