import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.ManifoldBoundary

open scoped Manifold

attribute [-instance] ManifoldBoundary.boundaryEuclideanChartedSpace

-- Semantic recall: `lean_leansearch` surfaced `SingularManifold.sum`, and mathlib's bordism file
-- still lists bordism groups as future work, so this item uses the local quotient of
-- `ClosedSmoothManifold n` by `cobordant n`.

/-- Helper for Definition 25.1.2: a diffeomorphism from a closed smooth manifold transports
boundarylessness onto the target manifold. -/
theorem boundarylessManifoldOfClosedSmoothDiffeomorph {n : ℕ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
    (X : ClosedSmoothManifold n)
    (e : Diffeomorph (𝓡 n) (𝓡 n) X.M Y ⊤) :
    BoundarylessManifold (𝓡 n) Y := by
  -- The diffeomorphism identifies `Y` with a boundaryless closed manifold, so boundarylessness
  -- transports directly across that equivalence.
  simpa using e.boundarylessManifold (n := ⊤) (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

/-- Helper for Definition 25.1.2: Chapter 21 already proves the boundary manifold law on its
canonical boundary charted-space owner. -/
theorem canonicalBoundaryIsManifoldOnChapter21Owner {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)] :
    @IsManifold
      ℝ
      DenselyNormedField.toNontriviallyNormedField
      (EuclideanSpace ℝ (Fin n))
      (PiLp.normedAddCommGroup 2 fun _ ↦ ℝ)
      (PiLp.normedSpace 2 ℝ fun _ ↦ ℝ)
      (EuclideanSpace ℝ (Fin n))
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (𝓡 n)
      ⊤
      (manifoldBoundary (n + 1) W)
      instTopologicalSpaceSubtype
      (ManifoldBoundary.boundaryEuclideanChartedSpace (n := n) (W := W)) := by
  -- Lower the ambient smoothness level once, then reuse the canonical Chapter 21 owner theorem.
  let _ : IsManifold (𝓡∂ (n + 1)) (n + 1) W := by
    exact IsManifold.of_le (show ((n + 1 : ℕ) : WithTop ℕ∞) ≤ ⊤ by simp)
  exact ManifoldBoundary.boundary_isManifold (n := n) (W := W)

/-- Helper for Definition 25.1.2: the local Chapter 25 boundary chart uses the same restricted
ambient source set as the Chapter 21 Euclidean boundary chart. -/
theorem boundaryChartAt_source_eq_chapter21 {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    (x : ((𝓡∂ (n + 1)).boundary W)) :
    (boundaryChartAt (n := n) x).source =
      (ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) x).source := by
  -- Both boundary-chart owners restrict the same ambient chart source before changing coordinates.
  simp [boundaryChartAt, boundaryChartSourceOpens, boundaryChartSourceSet,
    ManifoldBoundary.boundaryEuclideanChartAt, ManifoldBoundary.boundaryChartAt]

/-- Helper for Definition 25.1.2: source membership for the Chapter 25 boundary chart is
equivalent to source membership for the Chapter 21 Euclidean boundary chart. -/
theorem mem_boundaryChartAt_source_iff_chapter21 {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    (x z : ((𝓡∂ (n + 1)).boundary W)) :
    z ∈ (boundaryChartAt (n := n) x).source ↔
      z ∈ (ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) x).source := by
  -- Repackage the source-equality bridge into the membership form used in chartwise comparisons.
  rw [boundaryChartAt_source_eq_chapter21 (n := n) (W := W) x]

/-- Helper for Definition 25.1.2: deleting the distinguished boundary coordinate in the Chapter 25
boundary model agrees with the Chapter 21 boundary-hyperplane coordinate deletion on the same
ambient vector. -/
theorem boundaryModelHomeomorph_apply_eq_boundaryHyperplaneHomeomorph {n : ℕ}
    (y : BoundaryModel n) :
    boundaryModelHomeomorph n y =
      ManifoldBoundary.boundaryHyperplaneHomeomorph n ⟨y.1.1, y.2⟩ := by
  -- Both homeomorphisms forget the distinguished boundary coordinate and keep the remaining ones.
  simp [boundaryModelHomeomorph, boundaryModelToEuclidean,
    ManifoldBoundary.boundaryHyperplaneHomeomorph,
    ManifoldBoundary.boundaryHyperplaneLinearEquivEuclidean]

/-- Helper for Definition 25.1.2: the inverse of the boundary-chart source inclusion recovers the
same boundary point together with its source-membership proof. -/
theorem boundaryChartSourceSubtypeCoe_symm_eq {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    (x z : ((𝓡∂ (n + 1)).boundary W)) (hz : z ∈ (boundaryChartAt (n := n) x).source) :
    ((boundaryChartSourceOpens x).openPartialHomeomorphSubtypeCoe
      (boundaryChartSourceOpens_nonempty x)).symm z =
      ⟨z, by
        simpa [boundaryChartAt, boundaryChartSourceOpens, boundaryChartSourceSet] using hz⟩ := by
  have hz_target :
      z ∈ ((boundaryChartSourceOpens x).openPartialHomeomorphSubtypeCoe
        (boundaryChartSourceOpens_nonempty x)).target := by
    -- Rewrite the target of the open-set inclusion back to the concrete boundary-chart source set.
    simpa [boundaryChartAt, boundaryChartSourceOpens, boundaryChartSourceSet,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hz
  -- Equality in the source-open subtype reduces to equality of the underlying boundary points.
  apply Subtype.ext
  simpa using
    (((boundaryChartSourceOpens x).openPartialHomeomorphSubtypeCoe
      (boundaryChartSourceOpens_nonempty x)).right_inv hz_target)

/-- Helper for Definition 25.1.2: on the common source, the Chapter 25 boundary chart and the
Chapter 21 Euclidean boundary chart produce the same Euclidean coordinates. -/
theorem boundaryChartAt_apply_eq_chapter21 {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    (x z : ((𝓡∂ (n + 1)).boundary W))
    (hz : z ∈ (boundaryChartAt (n := n) x).source) :
    boundaryChartAt (n := n) x z =
      ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) x z := by
  have hz' : z.1 ∈ (boundaryAmbientChart x).source := by
    -- Source membership for the Chapter 25 chart is just source membership for the ambient chart.
    simpa [boundaryChartAt, boundaryChartSourceOpens, boundaryChartSourceSet] using hz
  have hchart :
      boundaryChartAt (n := n) x z =
        boundaryChartSourceHomeomorph x
          (((boundaryChartSourceOpens x).openPartialHomeomorphSubtypeCoe
            (boundaryChartSourceOpens_nonempty x)).symm z) := by
    -- Unfold the assembled chart only up to the source homeomorphism on the preferred source-open.
    simp [boundaryChartAt, boundaryChartSourceOpens, boundaryChartSourceSet]
    rfl
  -- Replace the source-open inverse by the canonical source witness, then compare the two
  -- coordinate-forgetting homeomorphisms on the same ambient chart value.
  rw [hchart, boundaryChartSourceSubtypeCoe_symm_eq (n := n) (W := W) x z hz]
  simp [boundaryChartSourceHomeomorph, boundaryChartSourceForward,
    ManifoldBoundary.boundaryEuclideanChartAt, ManifoldBoundary.boundaryChartAt,
    boundaryModelHomeomorph_apply_eq_boundaryHyperplaneHomeomorph, hz']

/-- Helper for Definition 25.1.2: each Chapter 25 boundary chart is equivalent on its source to
the Chapter 21 Euclidean boundary chart at the same boundary point. -/
theorem boundaryChartAt_eqOnSource_chapter21 {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    (x : ((𝓡∂ (n + 1)).boundary W)) :
    boundaryChartAt (n := n) x ≈
      ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) x := by
  refine ⟨boundaryChartAt_source_eq_chapter21 (n := n) (W := W) x, ?_⟩
  intro z hz
  -- The pointwise chart comparison closes the `EqOnSource` bridge once the sources are identified.
  exact boundaryChartAt_apply_eq_chapter21 (n := n) (W := W) x z hz

/-- Helper for Definition 25.1.2: the transition map between two Chapter 25 boundary charts is
`C^∞` because it is equivalent on source to the Chapter 21 boundary-chart transition. -/
theorem boundaryChartTransition_mem_contDiffGroupoid_chapter21 {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)]
    (x y : ((𝓡∂ (n + 1)).boundary W)) :
    (boundaryChartAt (n := n) x).symm.trans (boundaryChartAt (n := n) y) ∈
      contDiffGroupoid ⊤ (𝓡 n) := by
  have htransitionEq :
      (boundaryChartAt (n := n) x).symm.trans (boundaryChartAt (n := n) y) ≈
        (ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) x).symm.trans
          (ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) y) := by
    -- Transport the transition map across the chartwise `EqOnSource` bridges at the two endpoints.
    exact OpenPartialHomeomorph.EqOnSource.trans'
      (OpenPartialHomeomorph.EqOnSource.symm'
        (boundaryChartAt_eqOnSource_chapter21 (n := n) (W := W) x))
      (boundaryChartAt_eqOnSource_chapter21 (n := n) (W := W) y)
  have hChapter21 :
      (ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) x).symm.trans
          (ManifoldBoundary.boundaryEuclideanChartAt (n := n) (W := W) y) ∈
        contDiffGroupoid ⊤ (𝓡 n) := by
    -- Local instance justification (owner bridge): the Chapter 21 atlas-membership theorem is
    -- stated for its own charted-space owner, and this local scope imports that owner only long
    -- enough to apply the Chapter 21 compatibility theorem before transporting the result back.
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary W) :=
      ManifoldBoundary.boundaryEuclideanChartedSpace (n := n) (W := W)
    letI : IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W) :=
      canonicalBoundaryIsManifoldOnChapter21Owner (n := n) (W := W)
    -- Under the Chapter 21 owner, compatibility of preferred boundary charts is standard.
    exact IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := (⊤ : WithTop ℕ∞)) x)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := (⊤ : WithTop ℕ∞)) y)
  -- Move the Chapter 21 transition membership across the `EqOnSource` comparison.
  exact StructureGroupoid.mem_of_eqOnSource (G := contDiffGroupoid ⊤ (𝓡 n))
    hChapter21 htransitionEq

/-- Helper for Definition 25.1.2: the Chapter 25 boundary owner carries the same canonical
`n`-manifold structure as the Chapter 21 owner theorem. -/
theorem canonicalBoundaryIsManifold {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)] :
    IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W) := by
  -- Route correction: reduce the owner transport to a chart-by-chart maximal-atlas comparison
  -- instead of asking `simpa` to cross the non-definitional charted-space boundary owner change.
  refine isManifold_of_contDiffOn (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W) ?_
  intro e e' he he'
  rcases he with ⟨x, rfl⟩
  rcases he' with ⟨y, rfl⟩
  -- The Chapter 25 transition is `EqOnSource`-equivalent to the Chapter 21 transition, so the
  -- Chapter 21 compatibility theorem supplies the needed `ContDiffOn` statement.
  simpa [contDiffGroupoid, contDiffPregroupoid] using
    (mem_groupoid_of_pregroupoid.mp <|
      boundaryChartTransition_mem_contDiffGroupoid_chapter21 (n := n) (W := W) x y).1

/-- Helper for Definition 25.1.2: once the ambient boundary subtype already has the manifold and
boundaryless structures, those data package into `BoundarySmoothStructure`. -/
theorem boundarySmoothStructureOfBoundaryData {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    [IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W)]
    [BoundarylessManifold (𝓡 n) ((𝓡∂ (n + 1)).boundary W)] :
    BoundarySmoothStructure n W := by
  -- `BoundarySmoothStructure` records exactly these two boundary facts on the canonical boundary
  -- charted-space owner.
  exact
    { isManifold := inferInstance
      boundaryless := inferInstance }

/-- Helper for Definition 25.1.2: if the boundary subtype of `W` is already known to be an
`n`-manifold, then a diffeomorphism from a closed smooth manifold supplies the boundaryless part of
the induced boundary smooth structure. -/
theorem boundarySmoothStructureOfBoundaryDiffeomorph {n : ℕ} {X W : Type}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) ⊤ X] [BoundarylessManifold (𝓡 n) X]
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    [IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W)]
    (e : Diffeomorph (𝓡 n) (𝓡 n) X ((𝓡∂ (n + 1)).boundary W) ⊤) :
    BoundarySmoothStructure n W := by
  -- The target boundary subtype already has the required manifold law, so only boundarylessness
  -- needs to be transported across the diffeomorphism.
  exact
    { isManifold := inferInstance
      boundaryless := e.boundarylessManifold (n := ⊤) (by simp : (⊤ : WithTop ℕ∞) ≠ 0) }

/-- Helper for Definition 25.1.2: if the boundary subtype of `W` is already known to be an
`n`-manifold, then a diffeomorphism from a closed smooth manifold supplies the boundaryless part of
the induced boundary smooth structure. -/
theorem boundarySmoothStructureOfClosedSmoothBoundaryDiffeomorph {n : ℕ} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    [IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W)]
    (X : ClosedSmoothManifold n)
    (e : Diffeomorph (𝓡 n) (𝓡 n) X.M ((𝓡∂ (n + 1)).boundary W) ⊤) :
    BoundarySmoothStructure n W := by
  -- Specialize the generic packaging theorem to the closed smooth source used in cobordism.
  exact boundarySmoothStructureOfBoundaryDiffeomorph e

/-- Helper for Definition 25.1.2: for witness packaging, a diffeomorphism from the disjoint union
source manifold to the ambient boundary subtype is enough once the boundary subtype is already an
`n`-manifold. -/
theorem boundarySmoothStructureOfBoundarySourceDiffeomorph {n : ℕ}
    {M N : ClosedSmoothManifold n} {W : Type}
    [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W]
    [IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W)]
    (e : Diffeomorph (𝓡 n) (𝓡 n) (M.sum N).M ((𝓡∂ (n + 1)).boundary W) ⊤) :
    BoundarySmoothStructure n W := by
  -- Specialize the previous transport lemma to the source shape used in cobordism witnesses.
  exact boundarySmoothStructureOfClosedSmoothBoundaryDiffeomorph (X := M.sum N) e

/-- Helper for Definition 25.1.2: once an ambient compact smooth manifold-with-boundary already
has the induced `BoundarySmoothStructure`, any smooth identification of its boundary with
`(M.sum N).M` packages directly into a `CobordismWitness`. -/
noncomputable def cobordismWitnessOfBoundaryDiffeomorph {n : ℕ}
    (M N : ClosedSmoothManifold n) {W : Type}
    [TopologicalSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W] [CompactSpace W] [BoundarySmoothStructure n W]
    (e : Diffeomorph (𝓡 n) (𝓡 n) (M.sum N).M ((𝓡∂ (n + 1)).boundary W) ⊤) :
    CobordismWitness n M N :=
  { W := W
    topologicalSpaceW := inferInstance
    t2SpaceW := inferInstance
    chartedSpaceW := inferInstance
    isManifoldW := inferInstance
    compactSpaceW := inferInstance
    boundarySmoothStructure := inferInstance
    boundaryDiffeomorph := e }

/-- Helper for Definition 25.1.2: the product model `ℝ^n × ℍ^1` is canonically homeomorphic to
the half-space model `ℍ^(n+1)`. -/
noncomputable def euclideanProdHalfSpaceHomeomorph (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace (n + 1) where
  toFun x :=
    ⟨show EuclideanSpace ℝ (Fin (n + 1)) from
        WithLp.toLp 2 (Fin.cons (x.2.1 0) x.1), by
      -- The distinguished half-space coordinate is exactly the nonnegative interval coordinate.
      simpa using x.2.2⟩
  invFun y :=
    (show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 fun i ↦ y.1 (Fin.succ i),
      ⟨show EuclideanSpace ℝ (Fin 1) from WithLp.toLp 2 fun _ ↦ y.1 0, by
        -- Recover the one-dimensional half-space coordinate from the first ambient coordinate.
        simpa using y.2⟩)
  left_inv x := by
    rcases x with ⟨v, t⟩
    -- Check the inverse on the Euclidean factor and the half-space factor separately.
    apply Prod.ext
    · ext i
      simp
    · apply EuclideanHalfSpace.ext
      ext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      simp
  right_inv y := by
    -- Compare the recovered half-space point coordinatewise.
    apply EuclideanHalfSpace.ext
    ext i
    cases i using Fin.cases with
    | zero =>
        simp
    | succ i =>
        simp
  continuous_toFun := by
    -- The forward map is assembled coordinatewise from the interval endpoint and Euclidean tail.
    apply Continuous.subtype_mk
    refine (PiLp.continuous_toLp 2 _).comp ?_
    exact continuous_pi fun i ↦ by
      cases i using Fin.cases with
      | zero =>
          simpa using
            (PiLp.continuous_apply 2 (fun _ : Fin 1 ↦ ℝ) 0).comp
              (continuous_subtype_val.comp continuous_snd)
      | succ i =>
          simpa using
            (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).comp continuous_fst
  continuous_invFun := by
    -- The inverse splits the ambient half-space vector into its tail and first coordinate.
    have hfst :
        Continuous fun y : EuclideanHalfSpace (n + 1) ↦
          (show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 fun i ↦ y.1 (Fin.succ i)) := by
      refine (PiLp.continuous_toLp 2 _).comp ?_
      exact continuous_pi fun i ↦
        (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) (Fin.succ i)).comp
          continuous_subtype_val
    have hsnd :
        Continuous fun y : EuclideanHalfSpace (n + 1) ↦
          (⟨show EuclideanSpace ℝ (Fin 1) from WithLp.toLp 2 fun _ ↦ y.1 0, by
              simpa using y.2⟩ : EuclideanHalfSpace 1) := by
      let hsndBase :
          Continuous fun y : EuclideanHalfSpace (n + 1) ↦
            (show EuclideanSpace ℝ (Fin 1) from WithLp.toLp 2 fun _ ↦ y.1 0) := by
        refine (PiLp.continuous_toLp 2 _).comp ?_
        exact continuous_pi fun _ : Fin 1 ↦
          (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) 0).comp
            continuous_subtype_val
      -- Repackage the first ambient coordinate as a one-dimensional half-space point.
      exact hsndBase.subtype_mk fun y ↦ by simpa using y.2
    exact Continuous.prodMk hfst hsnd

/-- Helper for Definition 25.1.2: use the global model homeomorphism to view
`ℝ^n × ℍ^1` as a one-chart manifold over `ℍ^(n+1)`. -/
noncomputable abbrev euclideanProdHalfSpaceChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
  (euclideanProdHalfSpaceHomeomorph n).toOpenPartialHomeomorph.singletonChartedSpace (by simp)

/-- Helper for Definition 25.1.2: under the transported half-space owner on
`ℝ^n × ℍ^1`, the preferred chart is exactly the global model homeomorphism. -/
@[simp] theorem euclideanProdHalfSpaceChartAt_eq (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    @chartAt
        (EuclideanHalfSpace (n + 1))
        instTopologicalSpaceSubtype
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
        instTopologicalSpaceProd
        (euclideanProdHalfSpaceChartedSpace n)
        x =
      (euclideanProdHalfSpaceHomeomorph n).toOpenPartialHomeomorph := by
  -- The transported owner is a singleton atlas, so every preferred chart is the same global one.
  simpa using
    ((euclideanProdHalfSpaceHomeomorph n).toOpenPartialHomeomorph.singletonChartedSpace_chartAt_eq
      (h := rfl) (x := x))

/-- Helper for Definition 25.1.2: the preferred chart of the transported half-space owner has
source `univ`, because the model homeomorphism is globally defined. -/
@[simp] theorem euclideanProdHalfSpaceChartAt_source (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (@chartAt
        (EuclideanHalfSpace (n + 1))
        instTopologicalSpaceSubtype
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
        instTopologicalSpaceProd
        (euclideanProdHalfSpaceChartedSpace n)
        x).source = Set.univ := by
  -- This is the source computation for the unique chart in the singleton transported atlas.
  simpa using
    ((euclideanProdHalfSpaceHomeomorph n).toOpenPartialHomeomorph
      .singletonChartedSpace_chartAt_source (h := rfl) (x := x))

/-- Helper for Definition 25.1.2: the global product-to-half-space model homeomorphism is an open
embedding. -/
theorem euclideanProdHalfSpaceHomeomorph_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) := by
  -- The model comparison map is a homeomorphism, hence in particular an open embedding.
  exact (euclideanProdHalfSpaceHomeomorph n).isOpenEmbedding

/-- Helper for Definition 25.1.2: under the transported singleton owner on `ℝ^n × ℍ^1`,
the model homeomorphism itself upgrades to a diffeomorphism onto `ℍ^(n + 1)`. -/
noncomputable abbrev euclideanProdHalfSpaceDiffeomorph (n : ℕ) :=
  let h : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
    euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
  let _ : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    h.singletonChartedSpace
  show
      Diffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
        (EuclideanHalfSpace (n + 1)) ⊤ from
    { toEquiv := (euclideanProdHalfSpaceHomeomorph n).toEquiv
      contMDiff_toFun := by
        -- Under the singleton owner, the forward map is smooth by the open-embedding chart theorem.
        simpa using
          (contMDiff_isOpenEmbedding (I := 𝓡∂ (n + 1)) (h := h) (n := (⊤ : WithTop ℕ∞)))
      contMDiff_invFun := by
        -- The inverse is smooth on the full target because the model homeomorphism is surjective.
        have hrange :
            Set.range (euclideanProdHalfSpaceHomeomorph n) = Set.univ := by
          ext y
          constructor
          · intro _
            simp
          · intro _
            refine ⟨(euclideanProdHalfSpaceHomeomorph n).symm y, ?_⟩
            simp
        have hsymm :
            ⇑(Topology.IsOpenEmbedding.toOpenPartialHomeomorph
                (euclideanProdHalfSpaceHomeomorph n) h).symm =
              ⇑(euclideanProdHalfSpaceHomeomorph n).symm := by
          funext y
          apply (euclideanProdHalfSpaceHomeomorph n).injective
          have hy : y ∈ Set.range (euclideanProdHalfSpaceHomeomorph n) := by
            refine ⟨(euclideanProdHalfSpaceHomeomorph n).symm y, ?_⟩
            simp
          rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
              (f := euclideanProdHalfSpaceHomeomorph n) (h := h) hy]
          simp
        rw [← contMDiffOn_univ]
        simpa only [hsymm, hrange.symm] using
          (contMDiffOn_isOpenEmbedding_symm (I := 𝓡∂ (n + 1)) (h := h)
            (n := (⊤ : WithTop ℕ∞))) }

/-- Helper for Definition 25.1.2: under the transported one-chart atlas, the product model
`ℝ^n × ℍ^1` is itself a smooth manifold with boundary modelled on `ℍ^(n+1)`. -/
theorem euclideanProdHalfSpaceIsManifold (n : ℕ) {m : WithTop ℕ∞} :
    @IsManifold
      ℝ
      DenselyNormedField.toNontriviallyNormedField
      (EuclideanSpace ℝ (Fin (n + 1)))
      (PiLp.normedAddCommGroup 2 fun _ ↦ ℝ)
      (PiLp.normedSpace 2 ℝ fun _ ↦ ℝ)
      (EuclideanHalfSpace (n + 1))
      instTopologicalSpaceSubtype
      (𝓡∂ (n + 1))
      m
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      instTopologicalSpaceProd
      (euclideanProdHalfSpaceChartedSpace n) := by
  -- The global homeomorphism gives a singleton atlas whose only chart is smooth by construction.
  exact
    (euclideanProdHalfSpaceHomeomorph n).toOpenPartialHomeomorph.isManifold_singleton (by simp)

/-- Helper for Definition 25.1.2: under the transported singleton owner on `ℝ^n × ℍ^1`, the
product-to-half-space model homeomorphism is globally smooth. -/
theorem contMDiff_euclideanProdHalfSpaceHomeomorph_singleton (n : ℕ) :
    let h : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
      euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
    letI : ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      h.singletonChartedSpace
    letI : IsManifold (𝓡∂ (n + 1)) ⊤
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      h.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ⊤
      (euclideanProdHalfSpaceHomeomorph n) := by
  let h : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
    euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
  letI : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    h.singletonChartedSpace
  letI : IsManifold (𝓡∂ (n + 1)) ⊤
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    h.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
  -- This is exactly the forward smoothness field of the singleton-atlas diffeomorphism.
  simpa [euclideanProdHalfSpaceDiffeomorph] using
    (euclideanProdHalfSpaceDiffeomorph n).contMDiff_toFun

/-- Helper for Definition 25.1.2: under the transported singleton owner on `ℝ^n × ℍ^1`, the
inverse product-to-half-space model homeomorphism is globally smooth. -/
theorem contMDiff_euclideanProdHalfSpaceHomeomorph_symm_singleton (n : ℕ) :
    let h : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
      euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
    letI : ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      h.singletonChartedSpace
    letI : IsManifold (𝓡∂ (n + 1)) ⊤
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      h.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ⊤
      (euclideanProdHalfSpaceHomeomorph n).symm := by
  let h : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
    euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
  letI : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    h.singletonChartedSpace
  letI : IsManifold (𝓡∂ (n + 1)) ⊤
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    h.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
  -- The inverse smoothness is the second field of the same singleton-atlas diffeomorphism.
  simpa [euclideanProdHalfSpaceDiffeomorph] using
    (euclideanProdHalfSpaceDiffeomorph n).contMDiff_invFun

/-- Helper for Definition 25.1.2: the product-to-half-space model homeomorphism is globally smooth
for the original product owner `((𝓡 n).prod (𝓡∂ 1))`. -/
theorem contMDiff_euclideanProdHalfSpaceHomeomorph_product (n : ℕ) :
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ⊤ (euclideanProdHalfSpaceHomeomorph n) := by
  -- Reduce model-space smoothness to the ambient coordinate formula
  -- `(v, t) ↦ (t₀, v)` on `ℝⁿ × ℝ`.
  rw [contMDiff_iff]
  refine ⟨(euclideanProdHalfSpaceHomeomorph n).continuous, ?_⟩
  let ambientMap :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) →
        EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x ↦
      show EuclideanSpace ℝ (Fin (n + 1)) from
        WithLp.toLp 2 (Fin.cons ((x.2).ofLp 0) x.1.ofLp)
  have hAmbient : ContDiff ℝ ⊤ ambientMap := by
    -- Each output coordinate is a coordinate projection on the ambient product vector space.
    refine PiLp.contDiff_toLp.comp ?_
    refine
      contDiff_pi' (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
        (ι := Fin (n + 1)) (F' := fun _ : Fin (n + 1) ↦ ℝ) ?_
    intro i
    cases i using Fin.cases with
    | zero =>
        simpa using
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := (0 : Fin 1))).comp contDiff_snd
    | succ j =>
        simpa using
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := j)).comp contDiff_fst
  intro x y
  refine hAmbient.contDiffOn.congr ?_
  intro z hz
  have hzHalfSpace : z.2 ∈ Set.range (𝓡∂ 1) := by
    -- Points in the product target are exactly those whose second coordinate lies in the
    -- one-dimensional half-space range.
    simpa [ModelWithCorners.prod, Set.mem_prod, and_left_comm, and_assoc] using hz.1.1
  ext i
  cases i using Fin.cases with
  | zero =>
      -- The leading ambient coordinate records the half-space coordinate.
      have hcoord :=
        congrArg (fun w : EuclideanSpace ℝ (Fin 1) => w.ofLp 0) ((𝓡∂ 1).right_inv hzHalfSpace)
      simpa [ambientMap, ModelWithCorners.prod] using hcoord
  | succ j =>
      -- The remaining coordinates are copied unchanged from the Euclidean factor.
      change
        (show EuclideanSpace ℝ (Fin (n + 1)) from
          WithLp.toLp 2
            (Fin.cons ((((𝓡∂ 1).symm z.2 : EuclideanHalfSpace 1).1).ofLp 0) z.1.ofLp)).ofLp
          j.succ = z.1.ofLp j
      simp

/-- Helper for Definition 25.1.2: the inverse product-to-half-space model homeomorphism is
globally smooth for the original product owner `((𝓡 n).prod (𝓡∂ 1))`. -/
theorem contMDiff_euclideanProdHalfSpaceHomeomorph_symm_product (n : ℕ) :
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
      (euclideanProdHalfSpaceHomeomorph n).symm := by
  -- Reduce the inverse map to the ambient coordinate split
  -- `y ↦ (tail y, head y)` on `ℝⁿ⁺¹`.
  rw [contMDiff_iff]
  refine ⟨(euclideanProdHalfSpaceHomeomorph n).symm.continuous, ?_⟩
  let ambientMap :
      EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) :=
    fun y ↦
      (show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 (fun i ↦ y.ofLp (Fin.succ i)),
        show EuclideanSpace ℝ (Fin 1) from WithLp.toLp 2 (fun _ ↦ y.ofLp 0))
  have hAmbientFst :
      ContDiff ℝ ⊤
        (fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦
          show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 (fun i ↦ y.ofLp (Fin.succ i))) := by
    -- The tail coordinates are ordinary ambient coordinate projections.
    refine PiLp.contDiff_toLp.comp ?_
    refine
      contDiff_pi' (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))
        (ι := Fin n) (F' := fun _ : Fin n ↦ ℝ) ?_
    intro i
    simpa using
      (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := Fin.succ i) : _)
  have hAmbientSnd :
      ContDiff ℝ ⊤
        (fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦
          show EuclideanSpace ℝ (Fin 1) from WithLp.toLp 2 (fun _ ↦ y.ofLp 0)) := by
    -- The head coordinate is the distinguished half-space coordinate.
    refine PiLp.contDiff_toLp.comp ?_
    refine
      contDiff_pi' (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))
        (ι := Fin 1) (F' := fun _ : Fin 1 ↦ ℝ) ?_
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simpa using
      (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := (0 : Fin (n + 1))) : _)
  have hAmbient : ContDiff ℝ ⊤ ambientMap := hAmbientFst.prodMk hAmbientSnd
  intro x y
  refine hAmbient.contDiffOn.congr ?_
  intro z hz
  have hzHalfSpace : z ∈ Set.range (𝓡∂ (n + 1)) := by
    -- On the half-space model, the target of the extended chart is exactly the half-space range.
    simpa using hz.1
  apply Prod.ext
  · ext i
    -- The Euclidean tail coordinates come from the corresponding ambient coordinates of `z`.
    have hcoord :=
      congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w.ofLp (Fin.succ i))
        ((𝓡∂ (n + 1)).right_inv hzHalfSpace)
    simpa [ambientMap, ModelWithCorners.prod] using hcoord
  · ext i
    -- The one-dimensional half-space factor is recovered from the distinguished ambient
    -- coordinate.
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have hcoord :=
      congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w.ofLp 0)
        ((𝓡∂ (n + 1)).right_inv hzHalfSpace)
    simpa [ambientMap, ModelWithCorners.prod] using hcoord

/-- Helper for Definition 25.1.2: compose the cylinder's product atlas with the fixed model
homeomorphism `ℝ^n × ℍ^1 ≃ ℍ^(n + 1)` to install the half-space chart owner explicitly. -/
noncomputable abbrev cylinderHalfSpaceChartedSpace (n : ℕ) (M : ClosedSmoothManifold n) :
    ChartedSpace (EuclideanHalfSpace (n + 1)) (M.M × Set.Icc (0 : ℝ) 1) := by
  -- First view the product model itself as a one-chart half-space manifold, then compose that
  -- owner with the cylinder's existing product charted-space structure.
  let _ : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    euclideanProdHalfSpaceChartedSpace n
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      (M.M × Set.Icc (0 : ℝ) 1) := by
    simpa [ModelProd] using
      (inferInstance :
        ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))
          (M.M × Set.Icc (0 : ℝ) 1))
  exact ChartedSpace.comp (EuclideanHalfSpace (n + 1))
    (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
    (M.M × Set.Icc (0 : ℝ) 1)

/-- Helper for Definition 25.1.2: under the product-model owner, the cylinder boundary is exactly
the two endpoint slices `M × {0, 1}`. -/
theorem cylinderBoundary_eq_endpointSlices (n : ℕ) (M : ClosedSmoothManifold n) :
    ((𝓡 n).prod (𝓡∂ 1)).boundary (M.M × Set.Icc (0 : ℝ) 1) =
      Set.prod (Set.univ : Set M.M) ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) := by
  -- The closed manifold factor is boundaryless, so only the interval endpoints contribute.
  simpa using
    (boundary_product (I := 𝓡 n) (M := M.M) (x := (0 : ℝ)) (y := (1 : ℝ)))

/-- Helper for Definition 25.1.2: under the product owner, the cylinder boundary subtype is
equivalent to the two endpoint slices. -/
noncomputable abbrev productCylinderBoundarySubtypeEquivEndpointSlices (n : ℕ)
    (M : ClosedSmoothManifold n) :
    ((𝓡 n).prod (𝓡∂ 1)).boundary (M.M × Set.Icc (0 : ℝ) 1) ≃
      M.M × ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) :=
  (Equiv.setCongr (cylinderBoundary_eq_endpointSlices n M)).trans
    ((Equiv.setCongr
        (by
          rfl :
            Set.prod (Set.univ : Set M.M) ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) =
              (Set.univ : Set M.M) ×ˢ ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)))).trans
      ((Equiv.Set.prod (Set.univ : Set M.M) ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1))).trans
        (Equiv.prodCongr (Equiv.Set.univ M.M)
          (Equiv.refl ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1))))))

/-- Helper for Definition 25.1.2: the two endpoint slices of the cylinder are indexed by the two
summands of `M ⊔ M`. -/
noncomputable def cylinderEndpointEquiv (n : ℕ) (M : ClosedSmoothManifold n) :
    (M.sum M).M ≃ M.M × ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) where
  toFun
    | Sum.inl x =>
        -- The left summand lands on the bottom endpoint slice.
        (x, ⟨⊥, by simp⟩)
    | Sum.inr x =>
        -- The right summand lands on the top endpoint slice.
        (x, ⟨⊤, by simp⟩)
  invFun p := by
    rcases p with ⟨x, t⟩
    -- The endpoint tag decides which copy of `M` the point belongs to.
    by_cases hbot : (t : Set.Icc (0 : ℝ) 1) = ⊥
    · exact Sum.inl x
    · exact Sum.inr x
  left_inv x := by
    -- Sending a summand to its endpoint slice and back just evaluates the endpoint test.
    cases x <;> simp
  right_inv p := by
    rcases p with ⟨x, t⟩
    rcases t with ⟨t, ht⟩
    -- Each endpoint slice returns to the matching summand and then back to the same endpoint.
    rcases ht with rfl | rfl <;> simp

/-- Helper for Definition 25.1.2: compose the endpoint-slice identification with the product-owner
boundary equivalence so the cylinder boundary comparison is a single named equivalence. -/
noncomputable abbrev productCylinderBoundaryEquiv (n : ℕ) (M : ClosedSmoothManifold n) :
    (M.sum M).M ≃ ((𝓡 n).prod (𝓡∂ 1)).boundary (M.M × Set.Icc (0 : ℝ) 1) :=
  -- First index the two endpoint slices by `M ⊕ M`, then move back to the product-owner boundary.
  (cylinderEndpointEquiv n M).trans (productCylinderBoundarySubtypeEquivEndpointSlices n M).symm

/-- Helper for Definition 25.1.2: the cylinder endpoint equivalence sends the left summand to the
bottom endpoint slice. -/
@[simp] theorem cylinderEndpointEquiv_apply_inl (n : ℕ) (M : ClosedSmoothManifold n)
    (x : M.M) :
    cylinderEndpointEquiv n M (Sum.inl x) = (x, ⟨⊥, by simp⟩) := by
  -- The equivalence is defined by cases on the boundary-sum source.
  rfl

/-- Helper for Definition 25.1.2: the cylinder endpoint equivalence sends the right summand to the
top endpoint slice. -/
@[simp] theorem cylinderEndpointEquiv_apply_inr (n : ℕ) (M : ClosedSmoothManifold n)
    (x : M.M) :
    cylinderEndpointEquiv n M (Sum.inr x) = (x, ⟨⊤, by simp⟩) := by
  -- The equivalence is defined by cases on the boundary-sum source.
  rfl

/-- Helper for Definition 25.1.2: the identity map from the transported singleton half-space
owner on `ℝ^n × ℍ^1` to the original product owner is smooth. -/
theorem contMDiff_id_euclideanProdHalfSpace_singleton_to_product (n : ℕ) :
    let hOpen : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
      euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
    letI : ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      hOpen.singletonChartedSpace
    letI : IsManifold (𝓡∂ (n + 1)) ⊤
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      hOpen.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
      (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) := by
  let hOpen : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
    euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
  letI : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    hOpen.singletonChartedSpace
  letI : IsManifold (𝓡∂ (n + 1)) ⊤
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    hOpen.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
  have h :
      ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
        (⇑(euclideanProdHalfSpaceHomeomorph n).symm ∘
          ⇑(euclideanProdHalfSpaceHomeomorph n)) := by
    -- Compose the singleton-owner forward model map with the product-owner inverse model map.
    exact (contMDiff_euclideanProdHalfSpaceHomeomorph_symm_product n).comp
      (contMDiff_euclideanProdHalfSpaceHomeomorph_singleton n)
  -- The composite is definitionally the identity because the model homeomorphism is invertible.
  simpa [Function.comp] using
    h.congr (fun x ↦ ((euclideanProdHalfSpaceHomeomorph n).left_inv x).symm)

/-- Helper for Definition 25.1.2: the identity map from the original product owner on
`ℝ^n × ℍ^1` to the transported singleton half-space owner is smooth. -/
theorem contMDiff_id_euclideanProdHalfSpace_product_to_singleton (n : ℕ) :
    let hOpen : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
      euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
    letI : ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      hOpen.singletonChartedSpace
    letI : IsManifold (𝓡∂ (n + 1)) ⊤
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      hOpen.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ⊤
      (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) := by
  let hOpen : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
    euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
  letI : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    hOpen.singletonChartedSpace
  letI : IsManifold (𝓡∂ (n + 1)) ⊤
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    hOpen.isManifold_singleton (I := 𝓡∂ (n + 1)) (n := ⊤)
  have h :
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ⊤
        (⇑(euclideanProdHalfSpaceHomeomorph n).symm ∘
          ⇑(euclideanProdHalfSpaceHomeomorph n)) := by
    -- Compose the product-owner forward model map with the singleton-owner inverse model map.
    exact (contMDiff_euclideanProdHalfSpaceHomeomorph_symm_singleton n).comp
      (contMDiff_euclideanProdHalfSpaceHomeomorph_product n)
  -- The same inverse relation now gives the owner change in the opposite direction.
  simpa [Function.comp] using
    h.congr (fun x ↦ ((euclideanProdHalfSpaceHomeomorph n).left_inv x).symm)

/-- Helper for Definition 25.1.2: the local half-space owner on `ℝ^n × ℍ^1` is defined by the
singleton atlas coming from `euclideanProdHalfSpaceHomeomorph n`. -/
theorem euclideanProdHalfSpaceChartedSpace_eq_singleton (n : ℕ) :
    euclideanProdHalfSpaceChartedSpace n =
      (euclideanProdHalfSpaceHomeomorph n).toOpenPartialHomeomorph.singletonChartedSpace (by simp) := by
  -- This records the exact owner spelling used by the local chapter abbreviation.
  rfl

/-- Helper for Definition 25.1.2: a product-owner `ContMDiffOn` statement coming from the model
groupoid can be reinterpreted on the concrete product charted-space owner. -/
theorem contMDiffOn_modelProdSelf_to_productOwner {n : ℕ}
    {e : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)}
    (he : e ∈ contDiffGroupoid ⊤ ((𝓡 n).prod (𝓡∂ 1))) :
    ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤ (↑e) e.source := by
  -- Convert the model-self charted-space statement to the concrete product owner once and for all.
  convert contMDiffOn_of_mem_contDiffGroupoid he using 1 <;>
    simp [ModelProd, chartedSpaceSelf_prod]

/-- Helper for Definition 25.1.2: the open-embedding partial homeomorphism induced by the product
model homeomorphism has the same inverse map as the homeomorphism itself. -/
theorem euclideanProdHalfSpaceOpenPartialHomeomorph_symm_eq (n : ℕ) :
    let h : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
      euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
    ⇑(Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (euclideanProdHalfSpaceHomeomorph n) h).symm =
      ⇑(euclideanProdHalfSpaceHomeomorph n).symm := by
  let h : Topology.IsOpenEmbedding (euclideanProdHalfSpaceHomeomorph n) :=
    euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n
  -- Every target point lies in the range of the homeomorphism, so the partial inverse agrees
  -- pointwise with the global inverse.
  funext y
  apply (euclideanProdHalfSpaceHomeomorph n).injective
  have hy : y ∈ Set.range (euclideanProdHalfSpaceHomeomorph n) := by
    refine ⟨(euclideanProdHalfSpaceHomeomorph n).symm y, ?_⟩
    simp
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (f := euclideanProdHalfSpaceHomeomorph n) (h := h) hy]
  simp

/-- Helper for Definition 25.1.2: the homeomorphism-based singleton chart and the
open-embedding-based singleton chart on `ℝ^n × ℍ^1` coincide. -/
theorem euclideanProdHalfSpaceOpenPartialHomeomorph_eq (n : ℕ) :
    (euclideanProdHalfSpaceHomeomorph n).toOpenPartialHomeomorph =
      (euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n).toOpenPartialHomeomorph
        (euclideanProdHalfSpaceHomeomorph n) := by
  -- The forward maps agree by definition, and the inverse maps agree by the previous lemma.
  ext x <;> simp [euclideanProdHalfSpaceOpenPartialHomeomorph_symm_eq]

/-- Helper for Definition 25.1.2: the named singleton charted-space owner agrees with the
open-embedding singleton owner used by the identity smoothness lemmas. -/
theorem euclideanProdHalfSpaceChartedSpace_eq_openEmbeddingSingleton (n : ℕ) :
    (euclideanProdHalfSpaceChartedSpace n :
      ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)) =
      (euclideanProdHalfSpaceHomeomorph_isOpenEmbedding n).singletonChartedSpace := by
  -- Rewrite the named owner to the homeomorphism singleton chart, then compare the two
  -- singleton charts through the underlying partial homeomorphism.
  rw [euclideanProdHalfSpaceChartedSpace_eq_singleton]
  ext1
  · simp [ChartedSpace.atlas, euclideanProdHalfSpaceOpenPartialHomeomorph_eq]
  · simp [ChartedSpace.chartAt, euclideanProdHalfSpaceOpenPartialHomeomorph_eq]

/-- Helper for Definition 25.1.2: the identity map from the named singleton half-space owner on
`ℝ^n × ℍ^1` to the original product owner is smooth. -/
theorem contMDiff_id_euclideanProdHalfSpace_namedSingleton_to_product (n : ℕ) :
    letI : ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      euclideanProdHalfSpaceChartedSpace n
    letI : IsManifold (𝓡∂ (n + 1)) ⊤
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      euclideanProdHalfSpaceIsManifold n
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
      (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) := by
  -- Reuse the existing singleton-owner identity theorem after normalizing the owner spelling.
  convert (contMDiff_id_euclideanProdHalfSpace_singleton_to_product n) using 1
  exact euclideanProdHalfSpaceChartedSpace_eq_openEmbeddingSingleton n

/-- Helper for Definition 25.1.2: the identity map from the original product owner on
`ℝ^n × ℍ^1` to the named singleton half-space owner is smooth. -/
theorem contMDiff_id_euclideanProdHalfSpace_product_to_namedSingleton (n : ℕ) :
    letI : ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      euclideanProdHalfSpaceChartedSpace n
    letI : IsManifold (𝓡∂ (n + 1)) ⊤
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      euclideanProdHalfSpaceIsManifold n
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ⊤
      (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) := by
  -- The reverse identity smoothness uses the same owner normalization bridge.
  convert (contMDiff_id_euclideanProdHalfSpace_product_to_singleton n) using 1
  exact euclideanProdHalfSpaceChartedSpace_eq_openEmbeddingSingleton n

/-- Helper for Definition 25.1.2: every product-model local structomorphism on
`ℝ^n × ℍ^1` is also a local structomorphism for the transported singleton half-space owner. -/
theorem euclideanProdHalfSpaceHomeomorph_localStructomorph {n : ℕ}
    {e : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)}
    (he : e ∈ contDiffGroupoid ⊤ ((𝓡 n).prod (𝓡∂ 1))) :
    letI : ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      euclideanProdHalfSpaceChartedSpace n
    letI : IsManifold (𝓡∂ (n + 1)) ⊤
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
      euclideanProdHalfSpaceIsManifold n
    ChartedSpace.LiftPropOn
      (StructureGroupoid.IsLocalStructomorphWithinAt
        (contDiffGroupoid ⊤ (𝓡∂ (n + 1))))
      (↑e) e.source := by
  -- Route correction: the owner-change proof should pass through global smoothness of the
  -- identity between the product owner and the transported singleton owner, then package that
  -- bridge via `isLocalStructomorphOn_contDiffGroupoid_iff`.
  letI : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    euclideanProdHalfSpaceChartedSpace n
  letI : IsManifold (𝓡∂ (n + 1)) ⊤
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    euclideanProdHalfSpaceIsManifold n
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  constructor
  · have hprod :
        ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤ (↑e) e.source :=
      contMDiffOn_modelProdSelf_to_productOwner he
    have hleft :
        ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
          (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) e.source :=
      (contMDiff_id_euclideanProdHalfSpace_namedSingleton_to_product n).contMDiffOn
    have hright :
        ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ⊤
          (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) e.target :=
      (contMDiff_id_euclideanProdHalfSpace_product_to_namedSingleton n).contMDiffOn
    -- First change the domain owner from the singleton atlas to the product owner.
    have hmid :
        ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
          ((↑e) ∘ (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x)) e.source := by
      simpa [Function.comp] using (hprod.comp' hleft)
    have hsource :
        e.source ∩ (↑e ∘ (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x)) ⁻¹' e.target =
          e.source := by
      -- An open partial homeomorphism maps every source point into its target.
      ext x
      simp [Function.comp, and_iff_left_iff_imp]
      intro hx
      exact e.source_preimage_target hx
    -- Then change the codomain owner back to the singleton atlas.
    have hfinal :
        ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ⊤
          ((fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) ∘
            ((↑e) ∘ (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x))) e.source := by
      simpa [Function.comp, hsource] using (hright.comp' hmid)
    simpa [Function.comp] using hfinal
  · have hprod :
        ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤ (↑e.symm) e.target := by
      exact contMDiffOn_modelProdSelf_to_productOwner (StructureGroupoid.symm _ he)
    have hleft :
        ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
          (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) e.target :=
      (contMDiff_id_euclideanProdHalfSpace_namedSingleton_to_product n).contMDiffOn
    have hright :
        ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ⊤
          (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) e.source :=
      (contMDiff_id_euclideanProdHalfSpace_product_to_namedSingleton n).contMDiffOn
    -- Repeat the same owner-change argument for the inverse local structomorphism.
    have hmid :
        ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ⊤
          ((↑e.symm) ∘ (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x)) e.target := by
      simpa [Function.comp] using (hprod.comp' hleft)
    have hsource :
        e.target ∩ (↑e.symm ∘ (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x)) ⁻¹' e.source =
          e.target := by
      -- The inverse partial homeomorphism maps every target point back into the source.
      ext x
      simp [Function.comp, and_iff_left_iff_imp]
      intro hx
      exact e.symm.source_preimage_target hx
    have hfinal :
        ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ⊤
          ((fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x) ∘
            ((↑e.symm) ∘ (fun x : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 ↦ x))) e.target := by
      simpa [Function.comp, hsource] using (hright.comp' hmid)
    simpa [Function.comp] using hfinal

/-- Helper for Definition 25.1.2: under the explicit half-space owner, the cylinder carries the
ambient smooth manifold-with-boundary structure needed for the reflexive witness. -/
-- Route correction: the remaining cylinder blocker is now isolated as the ambient manifold law
-- for the transported half-space owner, rather than the whole witness packaging.
theorem cylinderIsManifold (n : ℕ) (M : ClosedSmoothManifold n) :
    letI := cylinderHalfSpaceChartedSpace n M
    IsManifold (𝓡∂ (n + 1)) ⊤ (M.M × Set.Icc (0 : ℝ) 1) := by
  let hProductChart :
      ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
        (M.M × Set.Icc (0 : ℝ) 1) := by
    -- Recover the cylinder's original product-owner charted space before composing owners.
    simpa [ModelProd] using
      (inferInstance :
        ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))
          (M.M × Set.Icc (0 : ℝ) 1))
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) (M.M × Set.Icc (0 : ℝ) 1) :=
    cylinderHalfSpaceChartedSpace n M
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      (M.M × Set.Icc (0 : ℝ) 1) := hProductChart
  letI : IsManifold ((𝓡 n).prod (𝓡∂ 1)) ⊤ (M.M × Set.Icc (0 : ℝ) 1) := inferInstance
  let hProductHasGroupoid :
      HasGroupoid (M.M × Set.Icc (0 : ℝ) 1)
        (contDiffGroupoid ⊤ ((𝓡 n).prod (𝓡∂ 1))) :=
    inferInstance
  let hModelChart :
      ChartedSpace (EuclideanHalfSpace (n + 1))
        (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    euclideanProdHalfSpaceChartedSpace n
  letI : ChartedSpace (EuclideanHalfSpace (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) := hModelChart
  letI : IsManifold (𝓡∂ (n + 1)) ⊤
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
    euclideanProdHalfSpaceIsManifold n
  let hHalfSpaceHasGroupoid :
      HasGroupoid (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
        (contDiffGroupoid ⊤ (𝓡∂ (n + 1))) :=
    inferInstance
  let hComp :
      HasGroupoid (M.M × Set.Icc (0 : ℝ) 1)
        (contDiffGroupoid ⊤ (𝓡∂ (n + 1))) :=
    @StructureGroupoid.HasGroupoid.comp
      (EuclideanHalfSpace (n + 1)) _
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) _
      (M.M × Set.Icc (0 : ℝ) 1) _
      hModelChart hProductChart
      (contDiffGroupoid ⊤ (𝓡∂ (n + 1))) hHalfSpaceHasGroupoid inferInstance
      (contDiffGroupoid ⊤ ((𝓡 n).prod (𝓡∂ 1))) hProductHasGroupoid
      (fun e he ↦ euclideanProdHalfSpaceHomeomorph_localStructomorph (n := n) he)
  letI : HasGroupoid (M.M × Set.Icc (0 : ℝ) 1)
      (contDiffGroupoid ⊤ (𝓡∂ (n + 1))) := hComp
  -- Once the composed atlas has the half-space groupoid, the manifold structure is immediate.
  exact IsManifold.mk' (𝓡∂ (n + 1)) ⊤ (M.M × Set.Icc (0 : ℝ) 1)

/-- Helper for Definition 25.1.2: once the cylinder carries the half-space owner, its boundary is
canonically diffeomorphic to the two endpoint copies of `M`. -/
noncomputable def cylinderBoundaryDiffeomorph (n : ℕ) (M : ClosedSmoothManifold n) :
    letI := cylinderHalfSpaceChartedSpace n M
    letI : IsManifold (𝓡∂ (n + 1)) ⊤ (M.M × Set.Icc (0 : ℝ) 1) := cylinderIsManifold n M
    Diffeomorph (𝓡 n) (𝓡 n) (M.sum M).M
      ((𝓡∂ (n + 1)).boundary (M.M × Set.Icc (0 : ℝ) 1)) ⊤ := by
  -- TODO: first upgrade the named product-owner boundary equivalence
  -- `productCylinderBoundaryEquiv n M` to a diffeomorphism, then transport that boundary through
  -- the explicit half-space owner.
  -- The failed refactor here showed the first missing API concretely: the product-owner boundary
  -- subtype does not yet come with a reusable `ChartedSpace (EuclideanSpace ...)` interface.
  sorry

/-- Helper for Definition 25.1.2: the cylinder over a closed smooth `n`-manifold provides the
reflexive cobordism witness. -/
-- Route correction: package the cylinder witness directly from the ambient manifold law and the
-- boundary identification, so only those two geometric helpers remain open.
noncomputable def cylinderCobordismWitness (n : ℕ) (M : ClosedSmoothManifold n) :
    CobordismWitness n M M := by
  -- Install the explicit half-space owner on the cylinder before packaging the witness.
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) (M.M × Set.Icc (0 : ℝ) 1) :=
    cylinderHalfSpaceChartedSpace n M
  letI : IsManifold (𝓡∂ (n + 1)) ⊤ (M.M × Set.Icc (0 : ℝ) 1) :=
    cylinderIsManifold n M
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
    ⟨finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)⟩
  letI : IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary (M.M × Set.Icc (0 : ℝ) 1)) :=
    canonicalBoundaryIsManifold (n := n) (W := M.M × Set.Icc (0 : ℝ) 1)
  let e :
      Diffeomorph (𝓡 n) (𝓡 n) (M.sum M).M
        ((𝓡∂ (n + 1)).boundary (M.M × Set.Icc (0 : ℝ) 1)) ⊤ :=
    cylinderBoundaryDiffeomorph n M
  -- The boundary diffeomorphism supplies the induced boundary smooth structure on the cylinder.
  letI : BoundarySmoothStructure n (M.M × Set.Icc (0 : ℝ) 1) :=
    boundarySmoothStructureOfBoundarySourceDiffeomorph (M := M) (N := M) e
  -- With those boundary data in place, the generic witness constructor applies directly.
  exact cobordismWitnessOfBoundaryDiffeomorph (M := M) (N := M) e

/-- Cobordism is reflexive on closed smooth `n`-manifolds. -/
theorem cobordant_refl (n : ℕ) (M : ClosedSmoothManifold n) :
    cobordant n M M := by
  -- Repackage the witness-level cylinder constructor as a cobordism proof.
  exact ⟨cylinderCobordismWitness n M⟩

/-- Helper for Definition 25.1.2: a cobordism witness can be reindexed along a diffeomorphism of
the full boundary disjoint union. -/
theorem cobordant_of_boundaryDiffeomorph {n : ℕ}
    {M N M' N' : ClosedSmoothManifold n} (h : cobordant n M N)
    (e : Diffeomorph (𝓡 n) (𝓡 n) (M'.sum N').M (M.sum N).M ⊤) :
    cobordant n M' N' := by
  rcases h with ⟨B⟩
  -- Reuse the ambient manifold and only replace the boundary identification.
  exact ⟨{
    W := B.W
    topologicalSpaceW := B.topologicalSpaceW
    t2SpaceW := B.t2SpaceW
    chartedSpaceW := B.chartedSpaceW
    isManifoldW := B.isManifoldW
    compactSpaceW := B.compactSpaceW
    boundarySmoothStructure := B.boundarySmoothStructure
    boundaryDiffeomorph := e.trans B.boundaryDiffeomorph
  }⟩

/-- Helper for Definition 25.1.2: diffeomorphic closed smooth `n`-manifolds are cobordant. -/
theorem cobordant_of_diffeomorph {n : ℕ} {M N : ClosedSmoothManifold n}
    (e : Diffeomorph (𝓡 n) (𝓡 n) M.M N.M ⊤) : cobordant n M N := by
  -- Compare `M ⊕ N` with `N ⊕ N` and reuse reflexivity on `N`.
  exact cobordant_of_boundaryDiffeomorph
    (M := N) (N := N) (M' := M) (N' := N)
    (cobordant_refl n N)
    (Diffeomorph.sumCongr e (Diffeomorph.refl (𝓡 n) N.M ⊤))

/-- Cobordism is symmetric on closed smooth `n`-manifolds. -/
theorem cobordant_symm {n : ℕ} {M N : ClosedSmoothManifold n}
    (h : cobordant n M N) : cobordant n N M := by
  -- Swap the two boundary components of the existing witness.
  exact cobordant_of_boundaryDiffeomorph h
    (Diffeomorph.sumComm (𝓡 n) N.M ⊤ M.M)

/-- Helper for Definition 25.1.2: gluing two cobordism witnesses along the common boundary
component produces a witness for transitivity. -/
-- Route correction: isolate the missing collar/gluing input as a witness-level helper rather
-- than leaving the relation proof opaque.
-- TODO: invoke a dependency-closed collar/gluing theorem for compact smooth manifolds with
-- boundary to glue `B₁.W` and `B₂.W` along the shared `N`-boundary component. The local geometric
-- probes above did not uncover an in-file route around that prerequisite, so this remains the
-- nonlocal frontier once the cylinder-owner bridge and boundary-inclusion smoothness lemmas exist.
noncomputable def gluedCobordismWitness {n : ℕ} {M N P : ClosedSmoothManifold n}
    (B₁ : CobordismWitness n M N) (B₂ : CobordismWitness n N P) :
    CobordismWitness n M P := sorry

/-- Cobordism is transitive on closed smooth `n`-manifolds. -/
theorem cobordant_trans {n : ℕ} {M N P : ClosedSmoothManifold n}
    (hMN : cobordant n M N) (hNP : cobordant n N P) : cobordant n M P := by
  rcases hMN with ⟨B₁⟩
  rcases hNP with ⟨B₂⟩
  -- Repackage witness gluing as the transitivity proof.
  exact ⟨gluedCobordismWitness B₁ B₂⟩

/-- The setoid on compact closed smooth `n`-manifolds induced by the cobordism relation. -/
def unorientedCobordismSetoid (n : ℕ) : Setoid (ClosedSmoothManifold n) where
  r M N := cobordant n M N
  iseqv := ⟨cobordant_refl n, cobordant_symm, cobordant_trans⟩

/-- Helper for Definition 25.1.2: reassociate the four boundary-source summands into the order
used by disjoint union on cobordism classes. -/
noncomputable def sumBoundaryReassociation {n : ℕ}
    (M₁ M₂ N₁ N₂ : ClosedSmoothManifold n) :
    Diffeomorph (𝓡 n) (𝓡 n)
      (((M₁.sum M₂).sum (N₁.sum N₂)).M)
      (((M₁.sum N₁).sum (M₂.sum N₂)).M) ⊤ :=
  let h₁ :
      Diffeomorph (𝓡 n) (𝓡 n)
        (((M₁.sum M₂).sum (N₁.sum N₂)).M)
        (M₁.M ⊕ (M₂.M ⊕ (N₁.M ⊕ N₂.M))) ⊤ :=
    Diffeomorph.sumAssoc (𝓡 n) M₁.M ⊤ M₂.M (N₁.sum N₂).M
  let h₂ :
      Diffeomorph (𝓡 n) (𝓡 n)
        (M₁.M ⊕ (M₂.M ⊕ (N₁.M ⊕ N₂.M)))
        (M₁.M ⊕ ((M₂.M ⊕ N₁.M) ⊕ N₂.M)) ⊤ :=
    Diffeomorph.sumCongr
      (Diffeomorph.refl (𝓡 n) M₁.M ⊤)
      ((Diffeomorph.sumAssoc (𝓡 n) M₂.M ⊤ N₁.M N₂.M).symm)
  let h₃ :
      Diffeomorph (𝓡 n) (𝓡 n)
        (M₁.M ⊕ ((M₂.M ⊕ N₁.M) ⊕ N₂.M))
        (M₁.M ⊕ ((N₁.M ⊕ M₂.M) ⊕ N₂.M)) ⊤ :=
    Diffeomorph.sumCongr
      (Diffeomorph.refl (𝓡 n) M₁.M ⊤)
      (Diffeomorph.sumCongr
        (Diffeomorph.sumComm (𝓡 n) M₂.M ⊤ N₁.M)
        (Diffeomorph.refl (𝓡 n) N₂.M ⊤))
  let h₄ :
      Diffeomorph (𝓡 n) (𝓡 n)
        (M₁.M ⊕ ((N₁.M ⊕ M₂.M) ⊕ N₂.M))
        (M₁.M ⊕ (N₁.M ⊕ (M₂.M ⊕ N₂.M))) ⊤ :=
    Diffeomorph.sumCongr
      (Diffeomorph.refl (𝓡 n) M₁.M ⊤)
      (Diffeomorph.sumAssoc (𝓡 n) N₁.M ⊤ M₂.M N₂.M)
  let h₅ :
      Diffeomorph (𝓡 n) (𝓡 n)
        (M₁.M ⊕ (N₁.M ⊕ (M₂.M ⊕ N₂.M)))
        (((M₁.sum N₁).sum (M₂.sum N₂)).M) ⊤ :=
    (Diffeomorph.sumAssoc (𝓡 n) M₁.M ⊤ N₁.M (M₂.sum N₂).M).symm
  -- Reassociate once on each side and swap the middle pair.
  h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Definition 25.1.2: combine two boundary identifications and reorder the source
into the standard grouped disjoint-union form. -/
noncomputable def sumBoundaryDiffeomorph {n : ℕ}
    {M₁ M₂ N₁ N₂ : ClosedSmoothManifold n} {A B : Type*}
    [TopologicalSpace A] [ChartedSpace (EuclideanSpace ℝ (Fin n)) A]
    [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
    (eM : Diffeomorph (𝓡 n) (𝓡 n) (M₁.sum M₂).M A ⊤)
    (eN : Diffeomorph (𝓡 n) (𝓡 n) (N₁.sum N₂).M B ⊤) :
    Diffeomorph (𝓡 n) (𝓡 n) ((M₁.sum N₁).sum (M₂.sum N₂)).M (A ⊕ B) ⊤ :=
  -- First move to the four-summand source order used by `sumCongr`, then combine the two
  -- boundary identifications componentwise.
  (sumBoundaryReassociation M₁ M₂ N₁ N₂).symm.trans
    (Diffeomorph.sumCongr eM eN)

/-- Helper for Definition 25.1.2: the boundary of a disjoint union is equivalent to the disjoint
union of the two boundary subtypes. -/
noncomputable def boundaryDisjointUnionEquiv {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂] :
    ((𝓡∂ (n + 1)).boundary W₁) ⊕ ((𝓡∂ (n + 1)).boundary W₂) ≃
      ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂)) where
  toFun
    | Sum.inl x =>
        -- The left boundary component stays on the left inside the disjoint union.
        ⟨Sum.inl x.1, ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2⟩
    | Sum.inr x =>
        -- The right boundary component stays on the right inside the disjoint union.
        ⟨Sum.inr x.1, ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2⟩
  invFun x := by
    rcases x with ⟨z, hz⟩
    cases z with
    | inl y =>
        -- A boundary point coming from the left summand forces a boundary point on that summand.
        refine Sum.inl ⟨y, ?_⟩
        have hz_not_interior :
            ¬ (𝓡∂ (n + 1)).IsInteriorPoint (Sum.inl y : W₁ ⊕ W₂) := by
          simpa [(𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := Sum.inl y)] using hz
        by_contra hy_boundary
        exact hz_not_interior <|
          ModelWithCorners.interiorPoint_inl (I := 𝓡∂ (n + 1)) y
            (((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := y)).2 hy_boundary)
    | inr y =>
        -- The same contradiction argument works for a boundary point on the right summand.
        refine Sum.inr ⟨y, ?_⟩
        have hz_not_interior :
            ¬ (𝓡∂ (n + 1)).IsInteriorPoint (Sum.inr y : W₁ ⊕ W₂) := by
          simpa [(𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := Sum.inr y)] using hz
        by_contra hy_boundary
        exact hz_not_interior <|
          ModelWithCorners.interiorPoint_inr (I := 𝓡∂ (n + 1)) y
            (((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := y)).2 hy_boundary)
  left_inv x := by
    -- The inverse just recovers which disjoint-union side the boundary point came from.
    cases x <;> rfl
  right_inv x := by
    -- The forward map preserves the ambient sum tag, so the round trip is definitional.
    rcases x with ⟨z, hz⟩
    cases z <;> rfl

/-- Helper for Definition 25.1.2: the forward boundary equivalence of a disjoint union is
continuous as a map of topological spaces. -/
theorem continuous_boundaryDisjointUnionEquiv {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂] :
    Continuous (boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂)) := by
  let f :
      ((𝓡∂ (n + 1)).boundary W₁) ⊕ ((𝓡∂ (n + 1)).boundary W₂) →
        ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂)) :=
    Sum.elim
      (fun x : ((𝓡∂ (n + 1)).boundary W₁) ↦
        (⟨Sum.inl x.1, ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2⟩ :
          ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))))
      (fun x : ((𝓡∂ (n + 1)).boundary W₂) ↦
        (⟨Sum.inr x.1, ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2⟩ :
          ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))))
  -- The equivalence is defined by continuous maps on the left and right boundary summands.
  have hf : Continuous f := by
    -- Each branch is continuous before the disjoint-union elimination packages them together.
    exact Continuous.sumElim
      (Continuous.subtype_mk
        (continuous_inl.comp continuous_subtype_val)
        (fun x ↦ ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2))
      (Continuous.subtype_mk
        (continuous_inr.comp continuous_subtype_val)
        (fun x ↦ ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2))
  have hf_eq :
      f = boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂) := by
    -- The named auxiliary function is exactly the equivalence defined by cases on the two summands.
    funext x
    cases x <;> rfl
  simpa [hf_eq] using hf

/-- Helper for Definition 25.1.2: the canonical left inclusion of the left boundary component into
the boundary of the disjoint union is continuous. -/
theorem continuous_boundaryDisjointUnionInl {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂] :
    Continuous fun x : ((𝓡∂ (n + 1)).boundary W₁) ↦
      (⟨Sum.inl x.1, ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2⟩ :
        ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))) := by
  -- The left branch is the ambient left inclusion followed by cod-restriction to the boundary.
  exact Continuous.subtype_mk
    (continuous_inl.comp continuous_subtype_val)
    (fun x ↦ ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2)

/-- Helper for Definition 25.1.2: the canonical right inclusion of the right boundary component
into the boundary of the disjoint union is continuous. -/
theorem continuous_boundaryDisjointUnionInr {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂] :
    Continuous fun x : ((𝓡∂ (n + 1)).boundary W₂) ↦
      (⟨Sum.inr x.1, ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2⟩ :
        ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))) := by
  -- The right branch is the symmetric cod-restriction of the ambient right inclusion.
  exact Continuous.subtype_mk
    (continuous_inr.comp continuous_subtype_val)
    (fun x ↦ ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2)

/-- Helper for Definition 25.1.2: on the left boundary summand, the disjoint-union boundary
equivalence is the evident inclusion into the left ambient summand. -/
@[simp] theorem boundaryDisjointUnionEquiv_apply_inl {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    (x : ((𝓡∂ (n + 1)).boundary W₁)) :
    boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂) (Sum.inl x) =
      ⟨Sum.inl x.1, ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2⟩ := by
  -- The equivalence definition is by cases on the source summand.
  rfl

/-- Helper for Definition 25.1.2: on the right boundary summand, the disjoint-union boundary
equivalence is the evident inclusion into the right ambient summand. -/
@[simp] theorem boundaryDisjointUnionEquiv_apply_inr {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    (x : ((𝓡∂ (n + 1)).boundary W₂)) :
    boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂) (Sum.inr x) =
      ⟨Sum.inr x.1, ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2⟩ := by
  -- The equivalence definition is by cases on the source summand.
  rfl

/-- Helper for Definition 25.1.2: the inverse of the disjoint-union boundary equivalence sends
the left ambient boundary inclusion back to the left boundary summand. -/
@[simp] theorem boundaryDisjointUnionEquiv_symm_apply_inl {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    (x : ((𝓡∂ (n + 1)).boundary W₁)) :
    (boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂)).symm
        ⟨Sum.inl x.1, ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2⟩ =
      Sum.inl x := by
  -- The left inverse of the equivalence identifies the left boundary inclusion with its source.
  exact (boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂)).left_inv (Sum.inl x)

/-- Helper for Definition 25.1.2: the inverse of the disjoint-union boundary equivalence sends
the right ambient boundary inclusion back to the right boundary summand. -/
@[simp] theorem boundaryDisjointUnionEquiv_symm_apply_inr {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    (x : ((𝓡∂ (n + 1)).boundary W₂)) :
    (boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂)).symm
        ⟨Sum.inr x.1, ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2⟩ =
      Sum.inr x := by
  -- The left inverse of the equivalence identifies the right boundary inclusion with its source.
  exact (boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂)).left_inv (Sum.inr x)

/-- Helper for Definition 25.1.2: a boundary point of `W₁ ⊕ W₂` lying on the left summand comes
from a boundary point of `W₁`. -/
theorem isBoundaryPoint_of_sumBoundaryPoint_inl {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    {y : W₁} (hy : (𝓡∂ (n + 1)).IsBoundaryPoint (Sum.inl y : W₁ ⊕ W₂)) :
    (𝓡∂ (n + 1)).IsBoundaryPoint y := by
  have hy_not_interior :
      ¬ (𝓡∂ (n + 1)).IsInteriorPoint (Sum.inl y : W₁ ⊕ W₂) := by
    -- Rephrase the boundary hypothesis as failure of interiority on the left ambient summand.
    simpa [(𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := Sum.inl y)] using hy
  by_contra hy_boundary
  -- An interior point on the left summand would stay interior in the disjoint union.
  exact hy_not_interior <|
    ModelWithCorners.interiorPoint_inl (I := 𝓡∂ (n + 1)) y
      (((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := y)).2 hy_boundary)

/-- Helper for Definition 25.1.2: a boundary point of `W₁ ⊕ W₂` lying on the right summand comes
from a boundary point of `W₂`. -/
theorem isBoundaryPoint_of_sumBoundaryPoint_inr {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    {y : W₂} (hy : (𝓡∂ (n + 1)).IsBoundaryPoint (Sum.inr y : W₁ ⊕ W₂)) :
    (𝓡∂ (n + 1)).IsBoundaryPoint y := by
  have hy_not_interior :
      ¬ (𝓡∂ (n + 1)).IsInteriorPoint (Sum.inr y : W₁ ⊕ W₂) := by
    -- Rephrase the boundary hypothesis as failure of interiority on the right ambient summand.
    simpa [(𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := Sum.inr y)] using hy
  by_contra hy_boundary
  -- An interior point on the right summand would stay interior in the disjoint union.
  exact hy_not_interior <|
    ModelWithCorners.interiorPoint_inr (I := 𝓡∂ (n + 1)) y
      (((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint (x := y)).2 hy_boundary)

/-- Helper for Definition 25.1.2: the inverse boundary equivalence is the ambient case split on
the disjoint-union tag of the boundary point. -/
theorem boundaryDisjointUnionEquiv_symm_eq_match {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    (x : ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))) :
    (boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂)).symm x =
      match x with
      | ⟨Sum.inl y, hy⟩ =>
          Sum.inl ⟨y, isBoundaryPoint_of_sumBoundaryPoint_inl (W₂ := W₂) hy⟩
      | ⟨Sum.inr y, hy⟩ =>
          Sum.inr ⟨y, isBoundaryPoint_of_sumBoundaryPoint_inr (W₁ := W₁) hy⟩ := by
  rcases x with ⟨z, hz⟩
  cases z with
  | inl y =>
      have hleft :
          (⟨Sum.inl y,
              ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) y
                (isBoundaryPoint_of_sumBoundaryPoint_inl (W₂ := W₂) hz)⟩ :
            ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))) =
            ⟨Sum.inl y, hz⟩ := by
        -- The ambient boundary subtype ignores the proof component once the sum tag is fixed.
        apply Subtype.ext
        rfl
      -- Rewrite to the canonical left-branch boundary point and apply the earlier simp lemma.
      rw [← hleft]
      simpa using
        (boundaryDisjointUnionEquiv_symm_apply_inl (n := n) (W₁ := W₁) (W₂ := W₂)
          ⟨y, isBoundaryPoint_of_sumBoundaryPoint_inl (W₂ := W₂) hz⟩)
  | inr y =>
      have hright :
          (⟨Sum.inr y,
              ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) y
                (isBoundaryPoint_of_sumBoundaryPoint_inr (W₁ := W₁) hz)⟩ :
            ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))) =
            ⟨Sum.inr y, hz⟩ := by
        -- The ambient boundary subtype ignores the proof component once the sum tag is fixed.
        apply Subtype.ext
        rfl
      -- Rewrite to the canonical right-branch boundary point and apply the earlier simp lemma.
      rw [← hright]
      simpa using
        (boundaryDisjointUnionEquiv_symm_apply_inr (n := n) (W₁ := W₁) (W₂ := W₂)
          ⟨y, isBoundaryPoint_of_sumBoundaryPoint_inr (W₁ := W₁) hz⟩)

/-- Helper for Definition 25.1.2: the forward boundary equivalence is the explicit branchwise
`Sum.elim` map obtained from the left and right boundary inclusions. -/
theorem boundaryDisjointUnionEquiv_eq_sumElim {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂] :
    boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂) =
      Sum.elim
        (fun x : ((𝓡∂ (n + 1)).boundary W₁) ↦
          (⟨Sum.inl x.1, ModelWithCorners.boundaryPoint_inl (I := 𝓡∂ (n + 1)) x.1 x.2⟩ :
            ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))))
        (fun x : ((𝓡∂ (n + 1)).boundary W₂) ↦
          (⟨Sum.inr x.1, ModelWithCorners.boundaryPoint_inr (I := 𝓡∂ (n + 1)) x.1 x.2⟩ :
            ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂)))) := by
  -- This normal form exposes the two forward boundary branches for later `ContMDiff.sumElim`.
  funext x
  cases x <;> rfl

/-- Helper for Definition 25.1.2: the boundary equivalence of a disjoint union is smooth in both
directions, so it upgrades to a boundary diffeomorphism. -/
-- Route correction: whole-goal `fun_prop` does not solve this `ContMDiff` packaging step.
-- The next pass should start from the explicit branchwise normal form above. Shell probes show
-- that `ContMDiff.sumElim` reduces `contMDiff_toFun` exactly to the two branch maps
-- `x ↦ ⟨Sum.inl x.1, ...⟩` and `x ↦ ⟨Sum.inr x.1, ...⟩`; the missing API is a boundary-owner
-- compatibility lemma proving those canonical boundary inclusions are smooth for the induced
-- boundary charted-space owner on `((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))`.
noncomputable def boundaryDisjointUnionDiffeomorph {n : ℕ} {W₁ W₂ : Type*}
    [TopologicalSpace W₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₁]
    [TopologicalSpace W₂] [ChartedSpace (EuclideanHalfSpace (n + 1)) W₂]
    [IsManifold (𝓡∂ (n + 1)) ⊤ W₁] [IsManifold (𝓡∂ (n + 1)) ⊤ W₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary W₁)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary W₂)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))] :
    Diffeomorph (𝓡 n) (𝓡 n)
      (((𝓡∂ (n + 1)).boundary W₁) ⊕ ((𝓡∂ (n + 1)).boundary W₂))
      ((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂)) ⊤ where
  toEquiv := boundaryDisjointUnionEquiv (n := n) (W₁ := W₁) (W₂ := W₂)
  contMDiff_toFun := by
    -- TODO: the `Sum.elim` normalization is established, and the branch maps are now isolated as
    -- continuous canonical boundary inclusions. The remaining step is a smooth cod-restriction
    -- bridge upgrading those inclusions from `Continuous` to `ContMDiff` for the induced boundary
    -- charted-space owner on `((𝓡∂ (n + 1)).boundary (W₁ ⊕ W₂))`.
    sorry
  contMDiff_invFun := by
    -- TODO: rewrite the inverse through an explicit ambient `Sum` case split and prove each
    -- branch smooth after transporting the boundary proof back to the chosen summand.
    sorry

/-- Helper for Definition 25.1.2: disjoint union of cobordism witnesses yields a cobordism witness
for the disjoint unions of the boundary manifolds. -/
-- Route correction: keep the source reassociation in `sumBoundaryDiffeomorph` and package the
-- ambient disjoint union directly, leaving only the target-side boundary diffeomorphism open.
noncomputable def sumCobordismWitness {n : ℕ} {M₁ M₂ N₁ N₂ : ClosedSmoothManifold n}
    (B₁ : CobordismWitness n M₁ M₂) (B₂ : CobordismWitness n N₁ N₂) :
    CobordismWitness n (M₁.sum N₁) (M₂.sum N₂) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
    ⟨finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)⟩
  letI : IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary (B₁.W ⊕ B₂.W)) :=
    canonicalBoundaryIsManifold (n := n) (W := B₁.W ⊕ B₂.W)
  let e :
      Diffeomorph (𝓡 n) (𝓡 n) ((M₁.sum N₁).sum (M₂.sum N₂)).M
        ((𝓡∂ (n + 1)).boundary (B₁.W ⊕ B₂.W)) ⊤ :=
    (sumBoundaryDiffeomorph B₁.boundaryDiffeomorph B₂.boundaryDiffeomorph).trans
      (boundaryDisjointUnionDiffeomorph (n := n) (W₁ := B₁.W) (W₂ := B₂.W))
  -- Use the combined boundary diffeomorphism to install the induced boundary smooth structure.
  letI : BoundarySmoothStructure n (B₁.W ⊕ B₂.W) :=
    boundarySmoothStructureOfBoundarySourceDiffeomorph
      (M := M₁.sum N₁) (N := M₂.sum N₂) e
  -- The ambient disjoint union is compact and smooth with boundary, so the generic witness
  -- packaging theorem finishes the construction.
  exact cobordismWitnessOfBoundaryDiffeomorph
    (M := M₁.sum N₁) (N := M₂.sum N₂) e

/-- Disjoint union respects cobordism on both variables for compact closed smooth
`n`-manifolds. -/
theorem cobordant_sum {n : ℕ} {M₁ M₂ N₁ N₂ : ClosedSmoothManifold n}
    (hM : cobordant n M₁ M₂) (hN : cobordant n N₁ N₂) :
    cobordant n (M₁.sum N₁) (M₂.sum N₂) := by
  rcases hM with ⟨B₁⟩
  rcases hN with ⟨B₂⟩
  -- Repackage the witness-level disjoint-union constructor as a cobordism proof.
  exact ⟨sumCobordismWitness B₁ B₂⟩

/-- Definition 25.1.2. The unoriented cobordism group `N_n` consists of cobordism classes of
compact smooth closed `n`-manifolds, with disjoint union inducing the addition on classes. -/
abbrev UnorientedCobordismGroup (n : ℕ) :=
  Quotient (unorientedCobordismSetoid n)

syntax "N_(" term ")" : term

macro_rules
  | `(N_($n)) => `(UnorientedCobordismGroup.{0} $n)

namespace ClosedSmoothManifold

/-- The empty closed smooth `n`-manifold. -/
noncomputable def empty (n : ℕ) : ClosedSmoothManifold n :=
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) PEmpty :=
    ChartedSpace.empty (EuclideanSpace ℝ (Fin n)) PEmpty
  { toSingularManifold :=
      SingularManifold.empty PUnit PEmpty
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
    t2Space := inferInstance }

/-- Helper for Definition 25.1.2: the underlying type of `ClosedSmoothManifold.empty n` is empty.
-/
instance instIsEmptyEmpty (n : ℕ) : IsEmpty (empty n).M := by
  -- The empty manifold is built on `PEmpty`.
  change IsEmpty PEmpty
  infer_instance

/-- The unoriented cobordism class of a closed smooth `n`-manifold. -/
def cobordismClass {n : ℕ} (M : ClosedSmoothManifold n) : N_(n) :=
  Quotient.mk (unorientedCobordismSetoid n) M

end ClosedSmoothManifold

/-- Disjoint union induces addition on `N_(n)`. -/
noncomputable instance instAddUnorientedCobordismGroup (n : ℕ) : Add (N_(n)) :=
  ⟨Quotient.map₂ (fun M N ↦ M.sum N)
      (fun _ _ hM _ _ hN ↦
        cobordant_sum hM hN)⟩

/-- The zero element of `N_(n)` is the cobordism class of the empty closed
smooth `n`-manifold. -/
noncomputable instance instZeroUnorientedCobordismGroup
    (n : ℕ) : Zero (N_(n)) :=
  ⟨(ClosedSmoothManifold.empty n).cobordismClass⟩

/-- In unoriented cobordism, negation is represented by the same cobordism class. -/
instance instNegUnorientedCobordismGroup (n : ℕ) : Neg (N_(n)) :=
  ⟨fun x ↦ x⟩

/-- `N_(n)` carries the canonical additive commutative group structure induced
by disjoint union, with the empty manifold as zero and the identity map as negation. -/
noncomputable instance instAddCommGroupUnorientedCobordismGroup (n : ℕ) :
    AddCommGroup (N_(n)) where
  __ := instAddUnorientedCobordismGroup n
  __ := instZeroUnorientedCobordismGroup n
  __ := instNegUnorientedCobordismGroup n
  add_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro M N P
    -- Replace both representatives by the canonically diffeomorphic reassociation.
    exact Quotient.sound <|
      cobordant_of_diffeomorph
        (M := (M.sum N).sum P)
        (N := M.sum (N.sum P))
        (Diffeomorph.sumAssoc (𝓡 n) M.M ⊤ N.M P.M)
  zero_add := by
    intro a
    refine Quotient.inductionOn a ?_
    intro M
    -- Move the empty summand to the right and then remove it.
    exact Quotient.sound <|
      cobordant_of_diffeomorph
        (M := (ClosedSmoothManifold.empty n).sum M)
        (N := M)
        ((Diffeomorph.sumComm (𝓡 n) (ClosedSmoothManifold.empty n).M ⊤ M.M).trans
          (Diffeomorph.sumEmpty (𝓡 n) M.M (M' := (ClosedSmoothManifold.empty n).M) ⊤))
  add_zero := by
    intro a
    refine Quotient.inductionOn a ?_
    intro M
    -- Remove the empty summand on the right.
    exact Quotient.sound <|
      cobordant_of_diffeomorph
        (M := M.sum (ClosedSmoothManifold.empty n))
        (N := M)
        (Diffeomorph.sumEmpty (𝓡 n) M.M (M' := (ClosedSmoothManifold.empty n).M) ⊤)
  add_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro M N
    -- Commute the two boundary components.
    exact Quotient.sound <|
      cobordant_of_diffeomorph
        (M := M.sum N)
        (N := N.sum M)
        (Diffeomorph.sumComm (𝓡 n) M.M ⊤ N.M)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    intro a
    refine Quotient.inductionOn a ?_
    intro M
    -- Route correction: reuse the reflexive witness for `M` and remove the extra empty summand on
    -- the boundary source.
    exact Quotient.sound <|
      cobordant_of_boundaryDiffeomorph
        (M := M) (N := M) (M' := M.sum M) (N' := ClosedSmoothManifold.empty n)
        (cobordant_refl n M)
        (Diffeomorph.sumEmpty (𝓡 n) (M.sum M).M
          (M' := (ClosedSmoothManifold.empty n).M) ⊤)

/-- The zero class in `N_(n)` is represented by the empty closed smooth
`n`-manifold. -/
@[simp] theorem unorientedCobordismGroup_zero_eq_empty_cobordismClass {n : ℕ} :
    (0 : N_(n)) = (ClosedSmoothManifold.empty n).cobordismClass := by
  -- The zero class was defined to be the class of the empty manifold.
  rfl

namespace ClosedSmoothManifold

/-- Two compact closed smooth `n`-manifolds determine the same unoriented cobordism class exactly
when they are cobordant. -/
theorem cobordismClass_eq_iff_cobordant {n : ℕ} {M N : ClosedSmoothManifold n} :
    M.cobordismClass = N.cobordismClass ↔ cobordant n M N := by
  constructor
  · intro h
    -- Equality in the quotient recovers the defining setoid relation.
    simpa [cobordismClass, unorientedCobordismSetoid] using Quotient.exact h
  · intro h
    -- The defining relation descends to equality of quotient classes.
    simpa [cobordismClass, unorientedCobordismSetoid] using
      (Quotient.sound h :
        Quotient.mk (unorientedCobordismSetoid n) M =
          Quotient.mk (unorientedCobordismSetoid n) N)

/-- Negation on unoriented cobordism classes is represented by the same closed smooth
`n`-manifold. -/
@[simp] theorem neg_cobordismClass {n : ℕ} (M : ClosedSmoothManifold n) :
    -M.cobordismClass = M.cobordismClass := by
  -- Negation is definitionally the identity on cobordism classes.
  rfl

/-- Addition of represented cobordism classes is represented by disjoint union. -/
@[simp] theorem cobordismClass_sum {n : ℕ} (M N : ClosedSmoothManifold n) :
    M.cobordismClass + N.cobordismClass = (M.sum N).cobordismClass := by
  -- Addition was defined by quotienting the disjoint union on representatives.
  rfl

end ClosedSmoothManifold
