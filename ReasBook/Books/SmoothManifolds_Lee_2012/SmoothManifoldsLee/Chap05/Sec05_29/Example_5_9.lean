import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

/- Example 5.9 is source-facing: the owner is the chapter's `IsEmbeddedSubmanifold`, while the
sphere's manifold structure and smooth subtype inclusion come from mathlib's canonical sphere API.
-/

/-- Helper for Example 5.9: the canonical inclusion of the unit sphere into Euclidean space is
smooth at top regularity. -/
lemma unitSphere_subtype_val_contMDiff_top (n : ℕ) :
    ContMDiff
      (𝓡 n)
      (𝓡 (n + 1))
      (⊤ : ℕ∞ω)
      ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        EuclideanSpace ℝ (Fin (n + 1))) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  -- This is the canonical smoothness theorem for the sphere subtype inclusion.
  exact contMDiff_coe_sphere

/-- Helper for Example 5.9: the canonical inclusion of the unit sphere into Euclidean space is a
smooth immersion. -/
lemma unitSphere_subtype_val_isImmersion_infty (n : ℕ) :
    Manifold.IsImmersion
      (𝓡 n)
      (𝓡 (n + 1))
      (∞ : ℕ∞ω)
      ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        EuclideanSpace ℝ (Fin (n + 1))) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  have hSmooth :
      ContMDiff
        (𝓡 n)
        (𝓡 (n + 1))
        (∞ : ℕ∞ω)
        ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
          EuclideanSpace ℝ (Fin (n + 1))) :=
    (unitSphere_subtype_val_contMDiff_top n).of_le le_top
  -- At `C^∞`, the derivative criterion reduces immersion to injectivity of `mfderiv`.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hSmooth).2 ?_
  intro x
  -- Mathlib already identifies the sphere inclusion derivative and proves its injectivity.
  simpa using mfderiv_coe_sphere_injective (n := n) x

/-- Helper for Example 5.9: the canonical inclusion of the unit sphere into Euclidean space is a
smooth immersion. -/
lemma unitSphere_subtype_val_isImmersion (n : ℕ) :
    Manifold.IsImmersion
      (𝓡 n)
      (𝓡 (n + 1))
      (⊤ : ℕ∞ω)
      ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        EuclideanSpace ℝ (Fin (n + 1))) := by
  -- The analytic `ω`-regularity packaging for the canonical sphere inclusion is deferred here.
  sorry

/-- Helper for Example 5.9: the subtype inclusion of the unit sphere is a smooth embedding. -/
lemma unitSphere_subtype_val_isSmoothEmbedding (n : ℕ) :
    Manifold.IsSmoothEmbedding
      (𝓡 n)
      (𝓡 (n + 1))
      (⊤ : ℕ∞ω)
      ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        EuclideanSpace ℝ (Fin (n + 1))) := by
  -- For a subtype inclusion, smooth embedding is exactly immersion plus topological embedding.
  exact ⟨unitSphere_subtype_val_isImmersion n, Topology.IsEmbedding.subtypeVal⟩

/-- Example 5.9 (Spheres as Submanifolds): with the standard smooth structure on `𝕊^n` from
Chapter 1, the unit sphere `𝕊^n ⊆ ℝ^(n+1)` is an embedded submanifold of Euclidean space. -/
instance unitSphere_isEmbeddedSubmanifold (n : ℕ) :
    IsEmbeddedSubmanifold
      (𝓡 (n + 1))
      (𝓡 n)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) where
  -- The canonical sphere manifold structure is boundaryless.
  toBoundarylessManifold := inferInstance
  -- The remaining embedded-submanifold field is the smooth-embedding statement above.
  isSmoothEmbedding_subtype_val := unitSphere_subtype_val_isSmoothEmbedding n
