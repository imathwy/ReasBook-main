import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Proposition_4_22
import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_1
import SmoothManifolds_Lee_2012.Chap06.Sec06_40.Corollary_6_16
import SmoothManifolds_Lee_2012.Chap06.Sec06_40.Lemma_6_13
import SmoothManifolds_Lee_2012.Chap06.Sec06_40.Theorem_6_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Semantic recall note: `lean_leansearch` returned the canonical embedding owner
-- `exists_embedding_euclidean_of_compact` together with `Manifold.IsSmoothEmbedding`; the
-- source-facing approximation surface follows the local constant-`ε` Euclidean pattern from
-- Problem 6-12, split into boundaryless and with-boundary owners to match Lee's
-- "with or without boundary" statement in this repo.

namespace Manifold

noncomputable section

universe uM

section GraphHelpers

universe uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N m : ℕ}

/-- Helper for Corollary 6.17: if `e : M → ℝ^m` is a smooth embedding and
`f : M → ℝ^N` is smooth, then the graph map `x ↦ (e x, f x)` is a smooth embedding into the
product Euclidean target. -/
lemma smoothEmbedding_pair_of_leftEmbedding
    (f : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (he : IsSmoothEmbedding I (𝓡 m) ∞ e) :
    IsSmoothEmbedding I ((𝓡 m).prod (𝓡 N)) ∞ (fun x ↦ (e x, f x)) := by
  let Φ : M → EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) := fun x ↦ (e x, f x)
  have heCont : ContMDiff I (𝓡 m) ∞ e := he.isImmersion.contMDiff
  have hΦcont : ContMDiff I ((𝓡 m).prod (𝓡 N)) ∞ Φ := by
    -- The graph map is smooth because both components are smooth.
    simpa [Φ] using heCont.prodMk f.contMDiff
  have he_mfderiv :
      ∀ x : M, Function.Injective (mfderiv I (𝓡 m) e x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).1 he.isImmersion
  have hImm : IsImmersion I ((𝓡 m).prod (𝓡 N)) ∞ Φ := by
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hΦcont).2 ?_
    intro x v w hvw
    have hDeriv :
        mfderiv I ((𝓡 m).prod (𝓡 N)) Φ x =
          (mfderiv I (𝓡 m) e x).prod (mfderiv I (𝓡 N) (fun y : M ↦ f y) x) := by
      -- The derivative of a product map splits componentwise.
      simpa [Φ] using
        (mfderiv_prodMk
          (I := I)
          (I' := 𝓡 m)
          (I'' := 𝓡 N)
          (f := e)
          (g := fun y : M ↦ f y)
          (x := x)
          (heCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (f.contMDiff.contDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hFirst :
        ((mfderiv I ((𝓡 m).prod (𝓡 N)) Φ x) v).1 =
          ((mfderiv I ((𝓡 m).prod (𝓡 N)) Φ x) w).1 := by
      exact congrArg Prod.fst hvw
    -- Injectivity of the first derivative component already forces `v = w`.
    exact he_mfderiv x <| by
      simpa [hDeriv] using hFirst
  have hGraphEmb : Topology.IsEmbedding (fun x : M ↦ (x, f x)) :=
    isEmbedding_graph f.continuous
  have hProdEmb :
      Topology.IsEmbedding
        (Prod.map e (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))) :=
    he.isEmbedding.prodMap Topology.IsEmbedding.id
  have hEmb : Topology.IsEmbedding Φ := by
    -- Factor the graph through the known embedding `e` in the first coordinate.
    simpa [Φ, Function.comp] using hProdEmb.comp hGraphEmb
  exact ⟨hImm, hEmb⟩

end GraphHelpers

section CompactApproximation

universe uH

variable {n N : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [CompactSpace M]
variable [ChartedSpace H M] [IsManifold I ∞ M]

/-- Helper for Corollary 6.17: a continuous Euclidean-valued map on a compact source manifold has
a uniform norm bound on its range. -/
lemma existsUniformNormBound {m : ℕ} {F : M → EuclideanSpace ℝ (Fin m)}
    (hF : Continuous F) :
    ∃ C : ℝ, ∀ x : M, ‖F x‖ ≤ C := by
  -- Compactness turns the Euclidean image into a bounded set.
  simpa using hF.isCompact_range.isBounded.exists_norm_le'

/-- Helper for Corollary 6.17: pack `ℝ^N × ℝ^m` into `ℝ^(N + m)` by placing the `ℝ^N`
coordinates first and the `ℝ^m` coordinates last. -/
noncomputable def packEuclideanCoordinates (N m : ℕ)
    : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + m)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)).symm

/-- Helper for Corollary 6.17: forget the last `m` coordinates of `ℝ^(N + m)`. -/
noncomputable def truncateTailCoordinates (N m : ℕ)
    : EuclideanSpace ℝ (Fin (N + m)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearMap.fst ℝ
    (EuclideanSpace ℝ (Fin N))
    (EuclideanSpace ℝ (Fin m)) |>.comp
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)).toContinuousLinearMap

/-- Helper for Corollary 6.17: packing followed by truncation recovers the original `ℝ^N`
component. -/
lemma truncateTailCoordinates_packEuclideanCoordinates
    {m : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin m)) :
    truncateTailCoordinates N m (packEuclideanCoordinates N m (x, y)) = x := by
  -- The first `N` packed coordinates are exactly the original `ℝ^N` coordinates.
  simpa [truncateTailCoordinates, packEuclideanCoordinates] using
    congrArg Prod.fst
      (ContinuousLinearEquiv.apply_symm_apply
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m))
        (x, y))

/-- Helper for Corollary 6.17: the packing map is a smooth embedding because it is induced by a
continuous linear equivalence. -/
lemma packEuclideanCoordinates_isSmoothEmbedding (N m : ℕ) :
    IsSmoothEmbedding
      ((𝓡 N).prod (𝓡 m))
      (𝓡 (N + m))
      ∞
      (packEuclideanCoordinates N m) := by
  -- The coordinate packing equivalence is a diffeomorphism of Euclidean model spaces.
  simpa [packEuclideanCoordinates] using
    (packEuclideanCoordinates N m).toDiffeomorph.isSmoothEmbedding

/-- Helper for Corollary 6.17: after swapping the graph factors and packing coordinates, the map
`x ↦ (f x, e x)` becomes a smooth embedding into one Euclidean target. -/
lemma packedGraph_isSmoothEmbedding
    {m : ℕ}
    (f : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (he : IsSmoothEmbedding I (𝓡 m) ∞ e) :
    IsSmoothEmbedding
      I
      (𝓡 (N + m))
      ∞
      (fun x ↦ packEuclideanCoordinates N m (f x, e x)) := by
  let G : M → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) := fun x ↦ (f x, e x)
  have hGraphLeft :
      IsSmoothEmbedding
        I
        ((𝓡 m).prod (𝓡 N))
        ∞
        (fun x ↦ (e x, f x)) :=
    smoothEmbedding_pair_of_leftEmbedding (I := I) (N := N) (m := m) f he
  have hSwap :
      IsSmoothEmbedding
        ((𝓡 m).prod (𝓡 N))
        ((𝓡 N).prod (𝓡 m))
        ∞
        (ContinuousLinearEquiv.prodComm
          ℝ
          (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin N))) := by
    -- Swapping the product factors is a diffeomorphism of Euclidean spaces.
    simpa using
      (ContinuousLinearEquiv.prodComm
        ℝ
        (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin N))).toDiffeomorph.isSmoothEmbedding
  have hGraphRightImm :
      IsImmersion
        I
        ((𝓡 N).prod (𝓡 m))
        ∞
        G := by
    -- Reorder the graph so the `ℝ^N` coordinates come first before packing.
    simpa [G, Function.comp] using
      Manifold.IsImmersion.ex416_comp hSwap.isImmersion hGraphLeft.isImmersion
  have hGraphRightEmb : Topology.IsEmbedding G := by
    -- The reordered graph is a composition of embeddings with the factor-swap homeomorphism.
    let σ :
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) →
          EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) :=
      ContinuousLinearEquiv.prodComm
        ℝ
        (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin N))
    have hσ : Topology.IsEmbedding σ := σ.isEmbedding
    simpa [G, σ, Function.comp] using hσ.comp hGraphLeft.isEmbedding
  have hPackedImm :
      IsImmersion
        I
        (𝓡 (N + m))
        ∞
        (fun x ↦ packEuclideanCoordinates N m (G x)) := by
    -- Compose the reordered graph immersion with the ambient coordinate packing diffeomorphism.
    simpa [G, Function.comp] using
      Manifold.IsImmersion.ex416_comp
        (packEuclideanCoordinates_isSmoothEmbedding N m).isImmersion
        hGraphRightImm
  have hPackedEmb :
      Topology.IsEmbedding (fun x ↦ packEuclideanCoordinates N m (G x)) := by
    -- The coordinate packing is a homeomorphism, so it preserves embeddings.
    simpa [G, Function.comp] using
      (packEuclideanCoordinates N m).isEmbedding.comp hGraphRightEmb
  exact ⟨hPackedImm, hPackedEmb⟩

/-- Helper for Corollary 6.17: once a compact source manifold is smoothly embedded in
`ℝ^(2 * n + 1)`, the remaining approximation problem is exactly the compact codimension-drop step
for the graph embedding into `ℝ^(2 * n + 1) × ℝ^N`. -/
lemma smoothMapToEuclideanCanBeUniformlyApproximatedByEmbeddings_ofWhitneyEmbedding
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (he : IsSmoothEmbedding I (𝓡 (2 * n + 1)) ∞ e)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding I (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  let G₀ : M → EuclideanSpace ℝ (Fin (N + (2 * n + 1))) :=
    fun x ↦ packEuclideanCoordinates N (2 * n + 1) (f x, e x)
  have hGraph :
      IsSmoothEmbedding
        I
        (𝓡 (N + (2 * n + 1)))
        ∞
        G₀ := by
    -- The graph of `(f, e)` is a smooth embedding after swapping and packing coordinates.
    simpa [G₀] using
      packedGraph_isSmoothEmbedding (I := I) (N := N) (m := 2 * n + 1) f he
  obtain ⟨C, hC⟩ :=
    existsUniformNormBound
      (M := M)
      (F := G₀)
      hGraph.isEmbedding.continuous
  have hProjection :
      ∀ x : M, truncateTailCoordinates N (2 * n + 1) (G₀ x) = f x := by
    intro x
    -- The standard coordinate truncation on the packed graph already recovers `f`.
    simpa [G₀] using
      truncateTailCoordinates_packEuclideanCoordinates
        (N := N)
        (m := 2 * n + 1)
        (x := f x)
        (y := e x)
  -- Route correction: the graph front end is now entirely in the packed ambient
  -- `ℝ^(N + (2 * n + 1))`, and the compact range bound is attached to that packed graph itself.
  -- The only remaining step is the codimension-drop argument: choose one oblique projection near
  -- the standard tail truncation, iterate it `2 * n + 1` times, and compare the final standard
  -- truncation chain with `truncateTailCoordinates`, hence with `f` by `hProjection`.
  have _ := hN
  have _ := hε
  have _ := hGraph
  have _ := G₀
  have _ := C
  have _ := hC
  have _ := hProjection
  -- TODO: prove the compact codimension-drop lemma in the packed Euclidean ambient.
  -- First choose a good oblique-projection direction near the last basis vector by applying
  -- `dense_oblique_projection_directions_restrict_to_injective_immersion` to `Set.range G₀`
  -- via `_root_.smoothEmbeddingRangeData`; then bound the projection error on the compact range
  -- of `G₀` and iterate this one-step descent `2 * n + 1` times to compress back to `ℝ^N`.
  sorry

end CompactApproximation

section Boundaryless

variable {n N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [CompactSpace M]
variable [TopologicalManifold n M] [IsManifold (𝓡 n) ∞ M]

/-- Boundaryless companion to Corollary 6.17: if `M` is a compact smooth boundaryless
`n`-manifold and `N ≥ 2 * n + 1`, then every smooth map from `M` to `ℝ^N` can be uniformly
approximated, to any prescribed positive constant error, by smooth embeddings. -/
theorem smooth_map_to_euclidean_can_be_uniformly_approximated_by_embeddings_boundaryless
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding (𝓡 n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  obtain ⟨e, he, -⟩ := _root_.weak_whitney_embedding_boundaryless (M := M) (n := n)
  -- The boundaryless owner is now reduced to the single generic compact graph-compression step.
  exact
    smoothMapToEuclideanCanBeUniformlyApproximatedByEmbeddings_ofWhitneyEmbedding
      (I := 𝓡 n)
      (M := M)
      hN
      f
      he
      hε

end Boundaryless

section WithBoundary

variable {n N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [CompactSpace M] [SmoothManifoldWithBoundary n M]

/-- Corollary 6.17: suppose `M` is a compact smooth `n`-manifold with or without boundary. If
`N ≥ 2 * n + 1`, then every smooth map from `M` to `ℝ^N` can be uniformly approximated, to any
prescribed positive constant error, by smooth embeddings. The boundaryless case is recorded
separately in `smooth_map_to_euclidean_can_be_uniformly_approximated_by_embeddings_boundaryless`,
while this theorem is the repo's with-boundary owner. -/
theorem smooth_map_to_euclidean_can_be_uniformly_approximated_by_embeddings
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮leeBoundaryModelWithCorners n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮leeBoundaryModelWithCorners n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  obtain ⟨e, he, -⟩ := _root_.weak_whitney_embedding_with_boundary (M := M) (n := n)
  -- The with-boundary owner is the same compact graph-compression step with the Lee boundary
  -- source model.
  exact
    smoothMapToEuclideanCanBeUniformlyApproximatedByEmbeddings_ofWhitneyEmbedding
      (I := leeBoundaryModelWithCorners n)
      (M := M)
      hN
      f
      he
      hε

end WithBoundary

end
end Manifold
