import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Proposition_4_22

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` confirmed the canonical sphere-inclusion smoothness theorem
-- `contMDiff_coe_sphere`.
-- The Chapter 4 embedding upgrade is
-- `smooth_embedding_of_compact_source_injective_isImmersion`.

open scoped Manifold ContDiff

/-- Helper for Example 4.23: the unit-sphere inclusion is smooth at every finite order, hence in
particular at `C^∞`. -/
lemma unitSphereInclusion_contMDiff (n : ℕ) :
    ContMDiff
      (𝓡 n)
      (𝓡 (n + 1))
      (∞ : ℕ∞ω)
      (Subtype.val :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
          EuclideanSpace ℝ (Fin (n + 1))) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  -- This is the canonical smoothness theorem for the sphere subtype inclusion.
  simpa using
    (contMDiff_coe_sphere (n := n) :
      ContMDiff
        (𝓡 n)
        (𝓡 (n + 1))
        (∞ : ℕ∞ω)
        ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
          EuclideanSpace ℝ (Fin (n + 1))))

/-- Injectivity of the unit-sphere inclusion used in Example 4.23. -/
theorem unitSphereInclusion_injective (n : ℕ) :
    Function.Injective
      (Subtype.val :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
          EuclideanSpace ℝ (Fin (n + 1))) := by
  -- The inclusion is the subtype coercion, so injectivity is immediate.
  exact Subtype.val_injective

/-- Smooth-immersion property of the unit-sphere inclusion used in Example 4.23. -/
theorem unitSphereInclusion_isImmersion (n : ℕ) :
    Manifold.IsImmersion
      (𝓡 n)
      (𝓡 (n + 1))
      (∞ : ℕ∞ω)
      (Subtype.val :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
          EuclideanSpace ℝ (Fin (n + 1))) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  -- The finite-dimensional criterion reduces immersion to injectivity of `mfderiv`.
  refine
    (Manifold.is_immersion_iff_forall_injective_mfderiv
      (unitSphereInclusion_contMDiff n)).2 ?_
  intro x
  -- Mathlib already proves the manifold derivative of the sphere inclusion is injective.
  simpa using mfderiv_coe_sphere_injective (n := n) x

/-- Example 4.23: because `S^n` is compact, the inclusion `ι : S^n ↪ ℝ^(n+1)` is a smooth
embedding. -/
theorem unitSphereInclusion_isSmoothEmbedding (n : ℕ) :
    Manifold.IsSmoothEmbedding
      (𝓡 n)
      (𝓡 (n + 1))
      (∞ : ℕ∞ω)
      (Subtype.val :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
          EuclideanSpace ℝ (Fin (n + 1))) := by
  -- Proposition 4.22 upgrades an injective smooth immersion from a compact source to an
  -- embedding.
  exact smooth_embedding_of_compact_source_injective_isImmersion
    (unitSphereInclusion_injective n)
    (unitSphereInclusion_isImmersion n)
