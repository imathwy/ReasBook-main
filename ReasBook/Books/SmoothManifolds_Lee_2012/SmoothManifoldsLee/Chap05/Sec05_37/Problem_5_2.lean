import SmoothManifolds_Lee_2012.Chap01.Sec01_05.Proposition_1_38
import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: the source-facing owner is the Chapter 5 predicate
-- `IsEmbeddedSubmanifold`, and the manifold boundary is the canonical subset
-- `(𝓡∂ (n + 1)).boundary M`.

open scoped Manifold

universe u

/-- Helper for Problem 5-2: inserting a zero boundary coordinate realizes the standard inclusion
`ℝ^n ↪ ℝ^(n+1)` into the half-space model. -/
noncomputable def boundaryCoordsInv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanHalfSpace (n + 1) :=
  fun y ↦
    ⟨(EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (Fin.insertNth (0 : Fin (n + 1)) (0 : ℝ) ((EuclideanSpace.equiv (Fin n) ℝ) y)),
      by simp⟩

/-- Helper for Problem 5-2: the canonical boundary chart uses the same source condition as the
ambient boundary chart. -/
lemma boundarySubtypeChart_source
    {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M]
    (x : ((𝓡∂ (n + 1)).boundary M)) :
    (chartAt (EuclideanSpace ℝ (Fin n)) x).source =
      {y : ((𝓡∂ (n + 1)).boundary M) |
        y.1 ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source} := by
  -- Proposition 1.38 builds the boundary chart by restricting the ambient chart source.
  rfl

/-- Helper for Problem 5-2: the inverse of the canonical boundary chart is the ambient inverse
applied to the zero-insertion map. -/
lemma boundarySubtypeChart_symm_val
    {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M]
    (x : ((𝓡∂ (n + 1)).boundary M)) (z : EuclideanSpace ℝ (Fin n)) :
    (((chartAt (EuclideanSpace ℝ (Fin n)) x).symm z : ((𝓡∂ (n + 1)).boundary M)).1) =
      (chartAt (EuclideanHalfSpace (n + 1)) x.1).symm (boundaryCoordsInv n z) := by
  -- Proposition 1.38 defines the boundary-chart inverse by ambient inversion after zero insertion.
  rfl

/-- Helper for Problem 5-2: the standard zero-tail inclusion identifies
`ℝ^n × ℝ` with `ℝ^(n+1)` in the chart normal form. -/
noncomputable def boundaryInsertionEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  ((EuclideanSpace.equiv (Fin n) ℝ).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans <|
    (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans <|
      (Fin.consEquivL ℝ (fun _ : Fin (n + 1) ↦ ℝ)).trans <|
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm

/-- Helper for Problem 5-2: the linear normal form inserts a zero first coordinate. -/
lemma boundaryInsertionEquiv_zeroTail (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    boundaryInsertionEquiv n (z, 0) = (boundaryCoordsInv n z).1 := by
  -- Read the composed linear equivalence on coordinates: it is exactly first-coordinate insertion.
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [boundaryInsertionEquiv, boundaryCoordsInv]
  · intro j
    simp [boundaryInsertionEquiv, boundaryCoordsInv]

/-- Helper for Problem 5-2: the canonical boundary inclusion is an immersion once its canonical
boundary-chart written-in-charts formula is exposed. -/
lemma boundarySubtypeVal_isImmersion
    {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M] :
    Manifold.IsImmersion
      (𝓡 n)
      (𝓡∂ (n + 1))
      (⊤ : WithTop ℕ∞)
      (Subtype.val : ((𝓡∂ (n + 1)).boundary M) → M) := by
  refine ⟨ℝ, inferInstance, inferInstance, ?_⟩
  intro x
  let domChart : OpenPartialHomeomorph ((𝓡∂ (n + 1)).boundary M)
      (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  let codChart : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
    chartAt (EuclideanHalfSpace (n + 1)) x.1
  -- Route correction: the old regular-level-set proof only produced an existential smooth
  -- structure on the zero set. Here we instead read the canonical boundary chart definition
  -- directly and show that `Subtype.val` is written as first-coordinate insertion.
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuousAt_subtype_val (boundaryInsertionEquiv n) domChart codChart ?_ ?_ ?_ ?_ ?_
  · -- The preferred boundary chart is centered at the point in question.
    simp [domChart]
  · -- The preferred ambient boundary chart is likewise centered at `x.1`.
    simp [codChart]
  · -- Both chosen charts are preferred charts, hence lie in the relevant maximal atlases.
    simpa [domChart] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n)
        (n := (⊤ : WithTop ℕ∞)) (x := x))
  · -- The ambient chart source condition is exactly the boundary chart source condition.
    simpa [codChart] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (n + 1))
        (n := (⊤ : WithTop ℕ∞)) (x := x.1))
  · intro z hz
    have hzTarget :
        z ∈ domChart.target := by
      -- On the boundaryless source model `𝓡 n`, the extended target is the ordinary chart target.
      simpa [domChart, OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hz
    have hzSource : domChart.symm z ∈ domChart.source := domChart.map_target hzTarget
    have hzAmbientSource :
        ((domChart.symm z : ((𝓡∂ (n + 1)).boundary M)).1) ∈ codChart.source := by
      -- The boundary chart source is defined by the ambient chart source.
      simpa [domChart, codChart, boundarySubtypeChart_source] using hzSource
    -- In these charts, the subtype inclusion is literally the zero-tail insertion map.
    calc
      ((codChart.extend (𝓡∂ (n + 1))) ∘ Subtype.val ∘ (domChart.extend (𝓡 n)).symm) z
          = (codChart.extend (𝓡∂ (n + 1))) ((domChart.symm z).1) := by
              simp [Function.comp, domChart]
      _ = (codChart.extend (𝓡∂ (n + 1)))
            (codChart.symm (boundaryCoordsInv n z)) := by
              rw [boundarySubtypeChart_symm_val (x := x) (z := z)]
      _ = (boundaryCoordsInv n z).1 := by
            have hzAmbientTarget : boundaryCoordsInv n z ∈ codChart.target :=
              codChart.map_source hzAmbientSource
            simpa [codChart, OpenPartialHomeomorph.extend_coe] using
              congrArg Subtype.val (codChart.right_inv hzAmbientTarget)
      _ = boundaryInsertionEquiv n (z, 0) := by
            symm
            exact boundaryInsertionEquiv_zeroTail n z

/-- Helper for Problem 5-2: once the immersion statement is isolated, the canonical subtype
inclusion is a smooth embedding because it is already a topological embedding. -/
lemma boundarySubtypeVal_isSmoothEmbedding
    {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M] :
    Manifold.IsSmoothEmbedding
      (𝓡 n)
      (𝓡∂ (n + 1))
      (⊤ : WithTop ℕ∞)
      (Subtype.val : ((𝓡∂ (n + 1)).boundary M) → M) := by
  -- The topological embedding of a subtype inclusion is canonical, so only immersion is
  -- substantive here.
  exact ⟨boundarySubtypeVal_isImmersion, Topology.IsEmbedding.subtypeVal⟩

/-- Problem 5-2: the boundary of a smooth manifold with boundary is an embedded submanifold of the
ambient manifold. -/
theorem manifoldBoundary_isEmbeddedSubmanifold
    {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M] :
    IsEmbeddedSubmanifold
      (𝓡∂ (n + 1))
      (𝓡 n)
      ((𝓡∂ (n + 1)).boundary M) := by
  -- Route correction: avoid transporting the existential regular-level-set structure. The
  -- canonical boundaryless structure is already provided by Proposition 1.38, so only the smooth
  -- embedding of the fixed subtype inclusion remains.
  refine
    { toBoundarylessManifold := manifoldBoundary_boundaryless n
      isSmoothEmbedding_subtype_val := boundarySubtypeVal_isSmoothEmbedding }
