import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_10
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Proposition_4_22
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Exercise_4_16
import SmoothManifolds_Lee_2012.Chap05.Sec05_37.Problem_5_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Semantic search note: the `lean_leansearch` tool requested by the statement policy was
-- unavailable in this session, so the statement surface below was chosen by checking the nearby
-- immersion precedent in Chapter 6 together with mathlib's manifold immersion and approximation
-- APIs directly.

namespace Manifold

section

universe uM

section ZeroDimensional

variable {N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold 0 M]
  [IsManifold (𝓡 0) ∞ M]

/-- Helper for Problem 6-12: on a `0`-dimensional smooth manifold, every manifold derivative has
trivial source tangent space, so it is automatically injective. -/
lemma injective_mfderiv_zero_dimensional
    (f : C^∞⟮𝓡 0, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯) (x : M) :
    Function.Injective (mfderiv (𝓡 0) (𝓡 N) f x) := by
  -- The source tangent space of a `0`-manifold has dimension `0`.
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 0) x) = 0 :=
    tangentSpace_finrank_eq_of_n_dimensional_manifold x
  -- Therefore every tangent vector is zero, so any linear map out of it is injective.
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 0) x) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 0))
    infer_instance
  have hzero : ∀ v : TangentSpace (𝓡 0) x, v = 0 :=
    finrank_zero_iff_forall_zero.mp hfin
  intro v w hvw
  rw [hzero v, hzero w]

end ZeroDimensional

variable {n N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold n M] [CompactSpace M]
  [IsManifold (𝓡 n) ∞ M]

/-- Helper for Problem 6-12: if `e : M → ℝ^m` is a smooth embedding and `f : M → ℝ^N` is smooth,
then the graph map `x ↦ (e x, f x)` is a smooth embedding into the product Euclidean target. -/
lemma smoothEmbedding_pair_of_leftEmbedding {m : ℕ}
    (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (heCont : ContMDiff (𝓡 n) (𝓡 m) ∞ e)
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ e) :
    IsSmoothEmbedding (𝓡 n) ((𝓡 m).prod (𝓡 N)) ∞ (fun x ↦ (e x, f x)) := by
  let Φ : M → EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) := fun x ↦ (e x, f x)
  have hfCont : ContMDiff (𝓡 n) (𝓡 N) ∞ (fun y : M ↦ f y) := by
    simpa using f.2
  have hΦcont : ContMDiff (𝓡 n) ((𝓡 m).prod (𝓡 N)) ∞ Φ := by
    -- The graph map is smooth because both component maps are smooth.
    simpa [Φ] using heCont.prodMk hfCont
  have he_mfderiv :
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 m) e x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).1 he.isImmersion
  have hImm : IsImmersion (𝓡 n) ((𝓡 m).prod (𝓡 N)) ∞ Φ := by
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hΦcont).2 ?_
    intro x v w hvw
    have hDeriv :
        mfderiv (𝓡 n) ((𝓡 m).prod (𝓡 N)) Φ x =
          (mfderiv (𝓡 n) (𝓡 m) e x).prod
            (mfderiv (𝓡 n) (𝓡 N) (fun y : M ↦ f y) x) := by
      -- The derivative of a product map splits componentwise.
      simpa [Φ] using
        (mfderiv_prodMk
          (I := 𝓡 n)
          (I' := 𝓡 m)
          (I'' := 𝓡 N)
          (f := e)
          (g := fun y : M ↦ f y)
          (x := x)
          (heCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (hfCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hFirst :
        ((mfderiv (𝓡 n) ((𝓡 m).prod (𝓡 N)) Φ x) v).1 =
          ((mfderiv (𝓡 n) ((𝓡 m).prod (𝓡 N)) Φ x) w).1 := by
      exact congrArg Prod.fst hvw
    -- Injectivity of the first derivative component already forces `v = w`.
    exact he_mfderiv x <| by
      simpa [hDeriv] using hFirst
  have hGraphEmb : Topology.IsEmbedding (fun x : M ↦ (x, f x)) :=
    isEmbedding_graph hfCont.continuous
  have hProdEmb :
      Topology.IsEmbedding
        (Prod.map e (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))) :=
    he.isEmbedding.prodMap Topology.IsEmbedding.id
  have hEmb : Topology.IsEmbedding Φ := by
    -- Factor the graph through the known embedding `e` in the first coordinate.
    simpa [Φ, Function.comp] using hProdEmb.comp hGraphEmb
  exact ⟨hImm, hEmb⟩

/-- Helper for Problem 6-12: pack `ℝ^N × ℝ^m` into `ℝ^(N + m)` by placing the `ℝ^N`
coordinates first and the `ℝ^m` coordinates last. -/
noncomputable def packEuclideanCoordinates (N m : ℕ) :
    (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + m)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)).symm

/-- Helper for Problem 6-12: forget the last `m` coordinates of `ℝ^(N + m)`. -/
noncomputable def truncateTailCoordinates (N m : ℕ) :
    EuclideanSpace ℝ (Fin (N + m)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearMap.fst ℝ
    (EuclideanSpace ℝ (Fin N))
    (EuclideanSpace ℝ (Fin m)) |>.comp
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)).toContinuousLinearMap

/-- Helper for Problem 6-12: packing followed by truncation recovers the original `ℝ^N`
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

/-- Helper for Problem 6-12: the packing map is a smooth embedding because it is induced by a
continuous linear equivalence. -/
lemma packEuclideanCoordinates_isSmoothEmbedding (N m : ℕ) :
    IsSmoothEmbedding
      ((𝓡 N).prod (𝓡 m))
      (𝓡 (N + m))
      ∞
      (packEuclideanCoordinates N m) := by
  -- The continuous linear equivalence is a diffeomorphism of Euclidean model spaces.
  simpa [packEuclideanCoordinates] using
    (packEuclideanCoordinates N m).toDiffeomorph.isSmoothEmbedding

/-- Helper for Problem 6-12: after swapping the graph factors and packing coordinates, the map
`x ↦ (f x, e x)` becomes a smooth embedding into a single Euclidean target. -/
lemma packedGraph_isSmoothEmbedding
    {m : ℕ}
    (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (heCont : ContMDiff (𝓡 n) (𝓡 m) ∞ e)
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ e) :
    IsSmoothEmbedding
      (𝓡 n)
      (𝓡 (N + m))
      ∞
      (fun x ↦ packEuclideanCoordinates N m (f x, e x)) := by
  let G : M → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) := fun x ↦ (f x, e x)
  have hGraphLeft :
      IsSmoothEmbedding
        (𝓡 n)
        ((𝓡 m).prod (𝓡 N))
        ∞
        (fun x ↦ (e x, f x)) :=
    smoothEmbedding_pair_of_leftEmbedding (n := n) (N := N) f heCont he
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
        (𝓡 n)
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
        (𝓡 n)
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

/-- Helper for Problem 6-12: mathlib's compact Whitney theorem yields a smooth Euclidean embedding
of a compact smooth manifold. -/
lemma compactWhitneyEuclideanSmoothEmbedding :
    ∃ m : ℕ, ∃ e : M → EuclideanSpace ℝ (Fin m),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ e := by
  -- Start from the compact Whitney embedding theorem in mathlib.
  have _ : T2Space M := by infer_instance
  have hEmbedding :
      ∃ m : ℕ, ∃ e : M → EuclideanSpace ℝ (Fin m),
        ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ Topology.IsClosedEmbedding e ∧
          ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 m) e x) :=
    by
      simpa using exists_embedding_euclidean_of_compact
  rcases hEmbedding with
    ⟨m, e, heSmooth, heClosed, heMfderiv⟩
  have heCont : ContMDiff (𝓡 n) (𝓡 m) ∞ e := by
    simpa using heSmooth
  refine ⟨m, e, heCont, ?_⟩
  -- Repackage the closed embedding and pointwise injective derivative into `IsSmoothEmbedding`.
  rw [isSmoothEmbedding_iff]
  constructor
  · rw [is_immersion_iff_forall_injective_mfderiv heCont]
    intro x
    simpa using heMfderiv x
  · exact heClosed.isEmbedding

/-- Helper for Problem 6-12: the singleton `{0} ⊆ ℝ^N` carries the canonical boundaryless
`0`-manifold structure used by the origin-target packaging in the transversality route. -/
lemma originSingletonSubmanifold :
    ∃ cs : ChartedSpace
        (EuclideanSpace ℝ (Fin 0))
        ({(0 : EuclideanSpace ℝ (Fin N))} : Set (EuclideanSpace ℝ (Fin N))),
      ∃ hs : IsManifold
          (𝓡 0)
          (⊤ : ℕ∞ω)
          ({(0 : EuclideanSpace ℝ (Fin N))} : Set (EuclideanSpace ℝ (Fin N))),
        let _ : ChartedSpace
            (EuclideanSpace ℝ (Fin 0))
            ({(0 : EuclideanSpace ℝ (Fin N))} : Set (EuclideanSpace ℝ (Fin N))) := cs
        let _ : IsManifold
            (𝓡 0)
            (⊤ : ℕ∞ω)
            ({(0 : EuclideanSpace ℝ (Fin N))} : Set (EuclideanSpace ℝ (Fin N))) := hs
        BoundarylessManifold
          (𝓡 0)
          ({(0 : EuclideanSpace ℝ (Fin N))} : Set (EuclideanSpace ℝ (Fin N))) := by
  let S : Set (EuclideanSpace ℝ (Fin N)) := {(0 : EuclideanSpace ℝ (Fin N))}
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin 0)) S := by
    -- The singleton subtype is discrete, so the `0`-dimensional Euclidean model supplies charts.
    letI : DiscreteTopology S := by infer_instance
    exact ChartedSpace.of_discreteTopology
  let hs : IsManifold (𝓡 0) (⊤ : ℕ∞ω) S := by
    -- A discrete singleton is automatically a smooth `0`-manifold.
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) S := cs
    letI : DiscreteTopology S := by infer_instance
    exact
      IsManifold.of_discreteTopology
        (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin 0))
        (M := S)
        (n := (⊤ : ℕ∞ω))
  refine ⟨cs, hs, ?_⟩
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) S := cs
  let _ : IsManifold (𝓡 0) (⊤ : ℕ∞ω) S := hs
  -- The `0`-dimensional Euclidean model is boundaryless, so the singleton inherits that property.
  infer_instance

/-- Helper for Problem 6-12: evaluation at a nonzero Euclidean vector is surjective on the space
of continuous linear maps into another Euclidean space. -/
lemma linearMapEval_surjective_of_ne_zero {k N : ℕ}
    (v : EuclideanSpace ℝ (Fin k)) (hv : v ≠ 0) :
    Function.Surjective
      (fun A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin N) ↦ A v) := by
  intro w
  -- Use the rank-one operator built from the Euclidean dual vector corresponding to `v`.
  let A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    (1 / ‖v‖ ^ 2) • ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))) v).smulRight w
  refine ⟨A, ?_⟩
  -- Evaluating at `v` collapses to the scalar factor `‖v‖^2 / ‖v‖^2 = 1`.
  have hvn : ‖v‖ ≠ 0 := by
    simpa [norm_eq_zero] using hv
  simp [A, hvn]

/-- Helper for Problem 6-12: the standard inclusion of `ℝ^(2n)` into the product-model
`ℝ^(2n + (N - 2n))`, obtained by splitting the target into `ℝ^(2n) × ℝ^(N - 2n)` and inserting
zero in the second factor. -/
noncomputable def euclideanInclusionCLM :
    EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n + (N - 2 * n))) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := N - 2 * n)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ
      (EuclideanSpace ℝ (Fin (2 * n)))
      (EuclideanSpace ℝ (Fin (N - 2 * n))))

/-- Helper for Problem 6-12: after applying the canonical splitting of
`ℝ^(2n + (N - 2n))`, the Euclidean
inclusion becomes the obvious map `x ↦ (x, 0)`. -/
lemma finAddEquivProd_euclideanInclusionCLM
    (x : EuclideanSpace ℝ (Fin (2 * n))) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := N - 2 * n))
      (euclideanInclusionCLM (n := n) (N := N) x) = (x, 0) := by
  -- Unfold the inclusion and cancel the inverse equivalence.
  simpa [euclideanInclusionCLM] using
    (ContinuousLinearEquiv.apply_symm_apply
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := N - 2 * n))
      ((ContinuousLinearMap.inl ℝ
        (EuclideanSpace ℝ (Fin (2 * n)))
        (EuclideanSpace ℝ (Fin (N - 2 * n))) x)))

/-- Helper for Problem 6-12: the canonical Euclidean inclusion into the product-model ambient
space is injective. -/
lemma euclideanInclusionCLM_injective :
    Function.Injective (euclideanInclusionCLM (n := n) (N := N)) := by
  intro x y hxy
  -- Compare first coordinates after transporting to the product model.
  have hfst :
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := N - 2 * n))
          (euclideanInclusionCLM (n := n) (N := N) x)).1 =
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := N - 2 * n))
          (euclideanInclusionCLM (n := n) (N := N) y)).1 := by
    exact
      congrArg Prod.fst
        (congrArg
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := N - 2 * n))
          hxy)
  simpa [finAddEquivProd_euclideanInclusionCLM (n := n) (N := N)] using hfst

/-- Helper for Problem 6-12: the canonical Euclidean inclusion into the product-model ambient
space is itself a smooth immersion. -/
lemma isImmersion_euclideanInclusion :
    IsImmersion
      (𝓡 (2 * n))
      (𝓡 (2 * n + (N - 2 * n)))
      ∞
  (euclideanInclusionCLM (n := n) (N := N)) := by
  let j := euclideanInclusionCLM (n := n) (N := N)
  have hjCont : ContMDiff (𝓡 (2 * n)) (𝓡 (2 * n + (N - 2 * n))) ∞ j := j.contMDiff
  -- The manifold derivative of a continuous linear map is the map itself, so injectivity of the
  -- derivative reduces to injectivity of the inclusion.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hjCont).2 ?_
  intro x
  simpa [j, ContinuousLinearMap.mfderiv_eq] using
    (euclideanInclusionCLM_injective (n := n) (N := N))

/-- Helper for Problem 6-12: composing a `2n`-dimensional immersion with the canonical Euclidean
inclusion produces an immersion into the product-model ambient space
`ℝ^(2n + (N - 2n))`, hence also into `ℝ^N` after rewriting by `Nat.add_sub_of_le`. -/
lemma isImmersion_comp_euclideanInclusion {e : M → EuclideanSpace ℝ (Fin (2 * n))}
    (he : IsImmersion (𝓡 n) (𝓡 (2 * n)) ∞ e) :
    IsImmersion
      (𝓡 n)
      (𝓡 (2 * n + (N - 2 * n)))
      ∞
      (fun x ↦ euclideanInclusionCLM (n := n) (N := N) (e x)) := by
  -- Compose the given immersion with the ambient linear inclusion.
  simpa [Function.comp] using
    Manifold.IsImmersion.ex416_comp
      (isImmersion_euclideanInclusion (n := n) (N := N))
      he

/-- Helper for Problem 6-12: a continuous map from the compact source manifold into Euclidean space
has a uniform norm bound on its range. -/
lemma existsUniformNormBound {m : ℕ} {e : M → EuclideanSpace ℝ (Fin m)}
    (heCont : Continuous e) :
    ∃ C : ℝ, ∀ x : M, ‖e x‖ ≤ C := by
  -- Compactness turns the Euclidean range into a bounded set.
  have hBddAbove :
      BddAbove ((fun y : EuclideanSpace ℝ (Fin m) ↦ ‖y‖) '' Set.range e) :=
    ((isCompact_range heCont).image
      (continuous_norm : Continuous fun y : EuclideanSpace ℝ (Fin m) ↦ ‖y‖)).bddAbove
  rcases hBddAbove with ⟨C, hC⟩
  refine ⟨max C 0, ?_⟩
  intro x
  have hx :
      ‖e x‖ ∈ (fun y : EuclideanSpace ℝ (Fin m) ↦ ‖y‖) '' Set.range e :=
    ⟨e x, Set.mem_range_self x, rfl⟩
  exact (hC hx).trans (le_max_left _ _)

/-- Problem 6-12: if `M` is a compact smooth `n`-manifold and `N ≥ 2n`, then every smooth map
`M → ℝ^N` can be uniformly approximated, to any prescribed positive constant error, by smooth
immersions. -/
theorem smooth_map_to_euclidean_can_be_uniformly_approximated_by_immersions
    (hN : 2 * n ≤ N) (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsImmersion (𝓡 n) (𝓡 N) ∞ g ∧ ∀ x : M, dist (g x) (f x) < ε := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨f, ?_, ?_⟩
    -- In dimension `0`, the immersion criterion reduces to injectivity on trivial tangent spaces.
    · exact (Manifold.is_immersion_iff_forall_injective_mfderiv f.contMDiff).2
        (fun x ↦ injective_mfderiv_zero_dimensional f x)
    · intro x
      simpa using hε
  · -- Route correction: the old branch hid two separate issues. The local ambient-space transport
    -- is now replaced by the packed graph route, which keeps the approximation problem in one
    -- Euclidean ambient space instead of relying on the broken sharp-immersion shortcut chain.
    have hPositive : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨m, e, heCont, he⟩ :=
      (compactWhitneyEuclideanSmoothEmbedding :
        ∃ m : ℕ, ∃ e : M → EuclideanSpace ℝ (Fin m),
          ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ e)
    let G₀ : M → EuclideanSpace ℝ (Fin (N + m)) :=
      fun x ↦ packEuclideanCoordinates N m (f x, e x)
    have hGraph :
        IsSmoothEmbedding
          (𝓡 n)
          (𝓡 (N + m))
          ∞
          G₀ := by
      -- The graph of `(f, e)` is a smooth embedding after swapping and packing coordinates.
      simpa [G₀] using packedGraph_isSmoothEmbedding (n := n) (N := N) f heCont he
    obtain ⟨C, hC⟩ :=
      existsUniformNormBound
        (M := M)
        (e := G₀)
        hGraph.isEmbedding.continuous
    have hProjection :
        ∀ x : M, truncateTailCoordinates N m (G₀ x) = f x := by
      intro x
      -- The standard coordinate truncation on the packed graph already recovers `f`.
      simpa [G₀] using
        truncateTailCoordinates_packEuclideanCoordinates
          (N := N)
          (m := m)
          (x := f x)
          (y := e x)
    -- The verified frontier is now explicit: the packed graph embedding and its compact norm bound
    -- are in place, and the target map `f` is the standard truncation of that graph.
    --
    -- TODO: prove the packed-ambient codimension-drop owner: starting from the smooth embedding
    -- `G₀ : M → ℝ^(N + m)`, choose a linear projection `π : ℝ^(N + m) →L[ℝ] ℝ^N` that is
    -- `ε / C`-close to `truncateTailCoordinates N m` on the compact range of `G₀` and whose
    -- composition `π ∘ G₀` is immersive. The graph/unit-tangent measure-zero route should choose
    -- `π` from a small ball around the truncation map while avoiding the bad tangent directions.
    have _ := hN
    have _ := hC
    have _ := hPositive
    have _ := hProjection
    have _ := hGraph
    sorry

end

end Manifold
