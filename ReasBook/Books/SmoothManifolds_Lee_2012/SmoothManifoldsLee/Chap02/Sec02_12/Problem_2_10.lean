import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

-- Declarations for this item will be appended below by the statement pipeline.

universe uM uN uE uH uE' uH'

open scoped Manifold ContDiff

section ContinuousPullback

variable {M : Type uM} [TopologicalSpace M]
variable {N : Type uN} [TopologicalSpace N]

/- Problem 2-10 (1): pullback along a continuous map is the canonical `ℝ`-algebra homomorphism on
continuous real-valued functions, namely `ContinuousMap.compRightAlgHom ℝ ℝ`. Its linearity is
derived from this owner rather than exposed through a parallel `IsLinearMap` wrapper. -/
#check (ContinuousMap.compRightAlgHom ℝ ℝ : C(M, N) → C(N, ℝ) →ₐ[ℝ] C(M, ℝ))

end ContinuousPullback

section SmoothPullback

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

-- Proof sketch: If `F` is smooth, compose any bundled smooth function `f : C^∞⟮J, N; ℝ⟯` with
-- `F`. Conversely, apply the hypothesis to enough smooth coordinate functions and use the standard
-- smoothness criterion in charts.
/-- Problem 2-10 (2): A map between smooth manifolds is smooth exactly when pullback along it sends
every smooth real-valued function on the target to a smooth real-valued function on the source. -/
theorem smooth_iff_pullback_preserves_smooth_real_functions {F : M → N} :
    ContMDiff I J ∞ F ↔
      ∀ f : C^∞⟮J, N; ℝ⟯, ContMDiff I 𝓘(ℝ) ∞ (f ∘ F) := sorry

-- Proof sketch: Apply part (2) to the forward map of the homeomorphism.
/-- Problem 2-10 (3): For a homeomorphism `F`, smoothness of the forward map is equivalent to
pullback by `F` preserving smooth real-valued functions. -/
theorem homeomorph_contMDiff_iff_pullback_preserves_smooth_real_functions
    (F : M ≃ₜ N) :
    ContMDiff I J ∞ F ↔
      ∀ f : C^∞⟮J, N; ℝ⟯, ContMDiff I 𝓘(ℝ) ∞ (f ∘ F) := sorry

-- Proof sketch: Apply part (2) to the inverse homeomorphism `F.symm`.
/-- Problem 2-10 (4): For a homeomorphism `F`, smoothness of the inverse map is equivalent to
pullback by `F.symm` preserving smooth real-valued functions. -/
theorem homeomorph_symm_contMDiff_iff_pullback_preserves_smooth_real_functions
    (F : M ≃ₜ N) :
    ContMDiff J I ∞ F.symm ↔
      ∀ g : C^∞⟮I, M; ℝ⟯, ContMDiff J 𝓘(ℝ) ∞ (g ∘ F.symm) := sorry

end SmoothPullback
