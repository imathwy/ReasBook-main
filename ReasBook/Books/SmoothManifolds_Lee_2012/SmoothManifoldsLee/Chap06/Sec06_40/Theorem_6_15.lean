import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.Maps.Proper.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold

section

universe uM

variable {n : ℕ}

/-- Whitney embedding helper: any compact smooth manifold modeled on `I` admits a smooth embedding
into some finite-dimensional Euclidean space. -/
lemma existsIsSmoothEmbeddingEuclidean_ofCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [CompactSpace M] :
    ∃ N : ℕ, ∃ F : M → EuclideanSpace ℝ (Fin N), IsSmoothEmbedding I (𝓡 N) ∞ F := by
  -- Start from mathlib's compact Whitney embedding theorem.
  have hEmbedding :
      ∃ N : ℕ, ∃ F : M → EuclideanSpace ℝ (Fin N),
        ContMDiff I (𝓡 N) ∞ F ∧ Topology.IsClosedEmbedding F ∧
          ∀ x : M, Function.Injective (mfderiv I (𝓡 N) F x) := by
    simpa using exists_embedding_euclidean_of_compact
  rcases hEmbedding with ⟨N, F, hFcontMDiff, hFclosed, hFmfderiv⟩
  refine ⟨N, F, ?_⟩
  -- Repackage the immersion and topological embedding fields into `IsSmoothEmbedding`.
  rw [isSmoothEmbedding_iff]
  constructor
  · exact (Manifold.is_immersion_iff_forall_injective_mfderiv hFcontMDiff).2 hFmfderiv
  · exact hFclosed.isEmbedding

-- Semantic recall note: `lean_leansearch` surfaced mathlib's compact Whitney theorem
-- `exists_embedding_euclidean_of_compact`; the source-facing API below is split across the repo's
-- canonical boundaryless and with-boundary manifold owners.

section Boundaryless

variable {M : Type uM} [TopologicalSpace M]
variable [TopologicalManifold n M] [IsManifold (𝓡 n) ∞ M]

/-- Theorem 6.15 (1) (Whitney Embedding Theorem). Every smooth `n`-manifold without boundary
admits a proper smooth embedding into `ℝ^(2n+1)`. -/
theorem weak_whitney_embedding_boundaryless :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ F ∧
        IsProperMap F := sorry

end Boundaryless

section WithBoundary

variable {M : Type uM} [TopologicalSpace M]
variable [SmoothManifoldWithBoundary n M]

/-- Whitney embedding helper: once a smooth manifold with boundary admits some smooth Euclidean
embedding, Lemma 6.14 upgrades it to a proper smooth embedding into `ℝ^(2 * n + 1)`. -/
lemma existsProperTargetEmbedding_ofExistsEuclideanEmbedding_withBoundary
    (h :
      ∃ N : ℕ, ∃ F : M → EuclideanSpace ℝ (Fin N),
        IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F) :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ F ∧
        IsProperMap F := sorry

/-- Whitney embedding helper: the compact with-boundary case follows immediately from the compact
Whitney embedding theorem and the properization wrapper above. -/
lemma existsProperTargetEmbedding_ofCompact_withBoundary [CompactSpace M] :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ F ∧
        IsProperMap F := by
  -- First embed the compact manifold into some Euclidean space.
  have hCompact :
      ∃ N : ℕ, ∃ F : M → EuclideanSpace ℝ (Fin N),
        IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F := by
    simpa using
      (existsIsSmoothEmbeddingEuclidean_ofCompact :
        ∃ N : ℕ, ∃ F : M → EuclideanSpace ℝ (Fin N),
          IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F)
  rcases hCompact with ⟨N, F, hF⟩
  -- Then apply the fixed-target properization step.
  exact
    existsProperTargetEmbedding_ofExistsEuclideanEmbedding_withBoundary ⟨N, F, hF⟩

/-- Whitney embedding helper: every smooth manifold with boundary admits a smooth embedding into
some finite-dimensional Euclidean space. -/
lemma existsIsSmoothEmbeddingEuclidean_withBoundary :
    ∃ N : ℕ, ∃ F : M → EuclideanSpace ℝ (Fin N),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F := sorry

/-- Theorem 6.15 (2) (Whitney Embedding Theorem). Every smooth `n`-manifold with boundary
admits a proper smooth embedding into `ℝ^(2n+1)`. -/
theorem weak_whitney_embedding_with_boundary :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ F ∧
        IsProperMap F := sorry

end WithBoundary

end
