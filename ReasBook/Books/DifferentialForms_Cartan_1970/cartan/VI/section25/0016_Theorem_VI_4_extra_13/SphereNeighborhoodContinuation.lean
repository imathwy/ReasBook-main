import DifferentialForms_Cartan_1970.VI.section25.«0016_Theorem_VI_4_extra_13».SphereNeighborhoodSourceContinuation

universe u

open scoped Complex.UnitDisc Manifold

open Filter

section

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the target-side transition domain for
two local sphere charts. A target point of `d` belongs to this open subset exactly when the
`d`-branch lands in the source of `c`, so the `c`-coordinate can be evaluated there. -/
def sphereNeighborhoodChartTargetTransitionDomain
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c d : SphereNeighborhoodChart X) :
    TopologicalSpace.Opens d.target :=
  ⟨{z | d.branch z ∈ c.source}, by
    -- This domain is the branch-preimage of the open source of `c`.
    simpa [Set.preimage] using
      c.source.isOpen.preimage (SphereNeighborhoodChart.branch_mdifferentiable d).continuous⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the target-side transition map from
`d`-coordinates to `c`-coordinates on the source-overlap region. -/
noncomputable def sphereNeighborhoodChartTargetTransition
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c d : SphereNeighborhoodChart X) :
    sphereNeighborhoodChartTargetTransitionDomain c d → c.target :=
  fun z ↦ c.equiv ⟨d.branch z.1, z.2⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a common-source point determines the
canonical hand-off point in the target-side transition domain. -/
noncomputable def sphereNeighborhoodChartTargetTransitionPoint
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    sphereNeighborhoodChartTargetTransitionDomain c d :=
  ⟨d.equiv ⟨x.1, x.2.2⟩, by
    -- The `d`-branch of the hand-off coordinate is the original common-source point.
    change d.branch (d.equiv ⟨x.1, x.2.2⟩) ∈ c.source
    rw [d.branch_coord]
    exact x.2.1⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: at the common-source hand-off point,
the target transition really evaluates to the `c`-coordinate of that point. -/
lemma sphereNeighborhoodChartTargetTransition_point
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    sphereNeighborhoodChartTargetTransition c d
        (sphereNeighborhoodChartTargetTransitionPoint x) =
      c.equiv ⟨x.1, x.2.1⟩ := by
  -- The hand-off point is chosen so that the `d`-branch recovers the original source point.
  simp [sphereNeighborhoodChartTargetTransition, sphereNeighborhoodChartTargetTransitionPoint,
    SphereNeighborhoodChart.branch_coord]

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the target-side transition remains
holomorphic on its natural overlap domain. -/
lemma sphereNeighborhoodChartTargetTransition_mdifferentiable
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c d : SphereNeighborhoodChart X) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sphereNeighborhoodChartTargetTransition c d) := by
  let U := sphereNeighborhoodChartTargetTransitionDomain c d
  let lift : U → c.source := fun z ↦ ⟨d.branch z.1, z.2⟩
  have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : U → d.target) :=
    contMDiff_subtype_val
  have hbranchAmbient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ lift) := by
    -- Forget the target subtype of `c` only after composing the `d`-branch with the open
    -- inclusion of the overlap domain into `d.target`.
    have hbranchSource : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (d.equiv.symm ∘ (Subtype.val : U → d.target)) :=
      d.equiv.symm.contMDiff_toFun.comp hsub
    simpa [lift, SphereNeighborhoodChart.branch, Function.comp] using
      (contMDiff_subtype_val.comp hbranchSource)
  have hlift : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 lift :=
    (contMDiff_subtypeValComp_iff (Z := U) (Y := X) (U := c.source) (f := lift)).mp
      hbranchAmbient
  -- After lifting the branch back into the source subtype of `c`, compose with the `c`-chart.
  simpa [sphereNeighborhoodChartTargetTransition, lift, Function.comp] using
    (c.equiv.contMDiff_toFun.mdifferentiable one_ne_zero).comp (hlift.mdifferentiable one_ne_zero)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the target-side transition is
injective, because both local branches recover the same source point. -/
lemma sphereNeighborhoodChartTargetTransition_injective
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c d : SphereNeighborhoodChart X) :
    Function.Injective (sphereNeighborhoodChartTargetTransition c d) := by
  intro z₁ z₂ hz
  apply Subtype.ext
  have hbranchEq : d.branch z₁.1 = d.branch z₂.1 := by
    -- Compare both `d`-branches by passing through the common `c`-coordinate.
    calc
      d.branch z₁.1 = c.branch (sphereNeighborhoodChartTargetTransition c d z₁) := by
        simp [sphereNeighborhoodChartTargetTransition, SphereNeighborhoodChart.branch_coord]
      _ = c.branch (sphereNeighborhoodChartTargetTransition c d z₂) := by
        rw [hz]
      _ = d.branch z₂.1 := by
        simp [sphereNeighborhoodChartTargetTransition, SphereNeighborhoodChart.branch_coord]
  have hsourceEq :
      (⟨d.branch z₁.1, d.branch_mem_source z₁.1⟩ : d.source) =
        ⟨d.branch z₂.1, d.branch_mem_source z₂.1⟩ := by
    apply Subtype.ext
    simpa using hbranchEq
  -- Re-apply the `d`-chart to the equal source-side points to recover equal target points.
  simpa [SphereNeighborhoodChart.branch] using congrArg d.equiv hsourceEq

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: at a common-source hand-off point,
the target-side transition is locally biholomorphic. This isolates the local inverse branch that
the later chart reparameterization step will consume. -/
lemma sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) 1 (sphereNeighborhoodChartTargetTransition c d)
      (sphereNeighborhoodChartTargetTransitionPoint x) := by
  -- Proposition 6.1 applies once the target-side transition is packaged as a simple holomorphic
  -- map between one-dimensional complex manifolds.
  exact simple_holomorphic_map_isLocalDiffeomorphAt
    (f := sphereNeighborhoodChartTargetTransition c d)
    (sphereNeighborhoodChartTargetTransition_mdifferentiable c d)
    (sphereNeighborhoodChartTargetTransition_injective c d)
    (sphereNeighborhoodChartTargetTransitionPoint x)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: after restricting the target of `d`
to the ambient open coming from `Φ.target`, one may postcompose the restricted chart by the local
inverse equivalence induced by `Φ`. This is the chart-level reparameterization step needed at a
common-source hand-off point. -/
noncomputable def sphereNeighborhoodChart_reparametrizeTarget
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c d : SphereNeighborhoodChart X)
    (Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) c.target (sphereNeighborhoodChartTargetTransitionDomain c d) 1) :
    SphereNeighborhoodChart X := by
  let targetOpen : TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d) :=
    ⟨Φ.target, Φ.open_target⟩
  let sourceOpen : TopologicalSpace.Opens c.target := ⟨Φ.source, Φ.open_source⟩
  let W : TopologicalSpace.Opens d.target :=
    ambientOpenOfOpenSubset (sphereNeighborhoodChartTargetTransitionDomain c d) targetOpen
  let dW := sphereNeighborhoodChart_restrictTarget d W
  let eΦ : sourceOpen ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ targetOpen :=
    openPartialHomeomorph_complexManifoldEquivSourceTarget
      (f := Φ.toOpenPartialHomeomorph) Φ.contMDiffOn_toFun Φ.contMDiffOn_invFun
  -- Compose the restricted chart with the ambient-open transport on both sphere-side endpoints.
  exact
    { source := dW.source
      target := ambientOpenOfOpenSubset c.target sourceOpen
      equiv :=
        dW.equiv.trans
          ((ambientOpenOfOpenSubsetEquiv d.target W).trans
            ((ambientOpenOfOpenSubsetEquiv
                (sphereNeighborhoodChartTargetTransitionDomain c d) targetOpen).trans
              (eΦ.symm.trans (ambientOpenOfOpenSubsetEquiv c.target sourceOpen).symm))) }

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the hand-off source point of a
common-source overlap belongs to the source of the reparameterized chart built from the local
inverse branch of the target-side transition. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_point_mem_source
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    x.1 ∈ c'.source := by
  dsimp [sphereNeighborhoodChart_reparametrizeTarget]
  -- Unfold the restricted-source condition once and supply the canonical transition-point witness.
  refine ⟨⟨x.1, x.2.2⟩, ?_, rfl⟩
  · -- The `d`-coordinate of the hand-off point belongs to the target transition domain because
    -- its `d`-coordinate lies in the ambient lift of the local-inverse target.
    refine (mem_ambientOpenOfOpenSubset (U := sphereNeighborhoodChartTargetTransitionDomain c d)).2 ?_
    refine ⟨?_, ?_⟩
    · -- The `d`-branch of the hand-off coordinate is the original common-source point.
      change d.branch (d.equiv ⟨x.1, x.2.2⟩) ∈ c.source
      simpa [SphereNeighborhoodChart.branch_coord] using x.2.1
    · -- The same target transition point lies in the local-inverse target by construction.
      simpa [sphereNeighborhoodChartTargetTransitionPoint] using
        (sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
          (c := c) (d := d) x).localInverse_mem_target

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the reparameterized chart has the
same sphere coordinate as the original chart on their common source. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_coord_eq
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    sphereNeighborhoodChartLeftCoord c c' = sphereNeighborhoodChartRightCoord c c' := by
  let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
  let Φ := hf.localInverse
  let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
  change sphereNeighborhoodChartLeftCoord c c' = sphereNeighborhoodChartRightCoord c c'
  funext y
  -- Unpack the reparameterized-source membership into the `d`-source witness together with the
  -- information that the `d`-coordinate lies in the local-inverse target.
  have hyc' :
      ∃ hy_d : y.1 ∈ d.source,
        ∃ hy_dom : d.equiv ⟨y.1, hy_d⟩ ∈ sphereNeighborhoodChartTargetTransitionDomain c d,
          (⟨d.equiv ⟨y.1, hy_d⟩, hy_dom⟩ : sphereNeighborhoodChartTargetTransitionDomain c d) ∈
            (⟨Φ.target, Φ.open_target⟩ :
              TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d)) := by
    simpa [c', sphereNeighborhoodChart_reparametrizeTarget, sphereNeighborhoodChart_restrictTarget,
      mem_ambientOpenOfOpenSubset] using y.2.2
  rcases hyc' with ⟨hy_d, hy_dom, hy_target⟩
  have hEq :
      sphereNeighborhoodChartTargetTransition c d ⟨d.equiv ⟨y.1, hy_d⟩, hy_dom⟩ =
        Φ.symm ⟨d.equiv ⟨y.1, hy_d⟩, hy_dom⟩ := by
    -- The chosen local branch `Φ.symm` agrees with the target transition on `Φ.target`.
    exact hf.choose_spec.2 (hf.choose.symm_target ▸ hy_target)
  have hLeft :
      sphereNeighborhoodChartLeftCoord c c' y =
        (↑(Φ.symm ⟨d.equiv ⟨y.1, hy_d⟩, hy_dom⟩) : RiemannSphere) := by
    -- The target transition evaluated at the `d`-coordinate of `y` is exactly the `c`-coordinate.
    simpa [sphereNeighborhoodChartLeftCoord, SphereNeighborhoodChart.coord,
      sphereNeighborhoodChartTargetTransition, SphereNeighborhoodChart.branch_coord] using
      congrArg Subtype.val hEq
  have hRight :
      sphereNeighborhoodChartRightCoord c c' y =
        (↑(Φ.symm ⟨d.equiv ⟨y.1, hy_d⟩, hy_dom⟩) : RiemannSphere) := by
    -- Unfolding the reparameterized chart shows that its coordinate is the same `Φ.symm` branch.
    dsimp [sphereNeighborhoodChartRightCoord, SphereNeighborhoodChart.coord, c',
      sphereNeighborhoodChart_reparametrizeTarget, sphereNeighborhoodChart_restrictTarget,
      ambientOpenOfOpenSubsetEquiv, mem_ambientOpenOfOpenSubset]
    rfl
  exact hLeft.trans hRight.symm

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the reparameterized target-side
local inverse pulls back to source-side coordinate agreement near the hand-off point. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_coord_eq_near
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    let x' : sphereNeighborhoodChartCommonSource c c' :=
      ⟨x.1, x.2.1, sphereNeighborhoodChart_reparametrizeTarget_point_mem_source (c := c) (d := d) x⟩
    sphereNeighborhoodChartLeftCoord c c' =ᶠ[nhds x']
      sphereNeighborhoodChartRightCoord c c' :=
by
  intro hf Φ c' x'
  -- The stronger pointwise equality proved just above immediately implies the neighborhood-wise
  -- coordinate agreement at the hand-off point.
  exact Filter.EventuallyEq.of_eq
    (sphereNeighborhoodChart_reparametrizeTarget_coord_eq (c := c) (d := d) x)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: one target-side local inverse branch
packages to a source-side continuation witness between the original chart and the reparameterized
chart. -/
noncomputable def sphereNeighborhoodChart_continueAtTargetPoint
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    SphereNeighborhoodChartCoordContinuation c c' :=
  let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
  let Φ := hf.localInverse
  let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
  let x' : sphereNeighborhoodChartCommonSource c c' :=
    ⟨x.1, x.2.1, sphereNeighborhoodChart_reparametrizeTarget_point_mem_source (c := c) (d := d) x⟩
  ⟨x', sphereNeighborhoodChart_reparametrizeTarget_coord_eq_near (c := c) (d := d) x⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the chart obtained by
reparameterizing `d` through a target-side local inverse is still a restriction of `d`, so its
source stays inside `d.source`. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_source_subset
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    (c'.source : Set X) ⊆ d.source := by
  intro hf Φ c' y hy
  -- Unpack the restricted-source witness and keep only the underlying `d.source` membership.
  have hy' :
      ∃ hy_d : y ∈ d.source,
        ∃ hy_dom : d.equiv ⟨y, hy_d⟩ ∈ sphereNeighborhoodChartTargetTransitionDomain c d,
          (⟨d.equiv ⟨y, hy_d⟩, hy_dom⟩ : sphereNeighborhoodChartTargetTransitionDomain c d) ∈
            (⟨Φ.target, Φ.open_target⟩ :
              TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d)) := by
    simpa [c', sphereNeighborhoodChart_reparametrizeTarget, sphereNeighborhoodChart_restrictTarget,
      mem_ambientOpenOfOpenSubset] using hy
  exact hy'.1

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: any point of the local-inverse target
for the target-side hand-off lies in the source of the reparameterized chart after applying the
raw chart branch. This is the transport step that turns a target-side local inverse witness back
into a source-side chart-membership statement. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_branch_mem_source
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    ∀ z : sphereNeighborhoodChartTargetTransitionDomain c d,
      z ∈ Φ.target → d.branch z.1 ∈ c'.source := by
  intro hf Φ c' z hz
  -- Reuse `z` itself as the target witness for the restricted chart.
  have hz' :
      d.equiv ⟨d.branch z.1, d.branch_mem_source z.1⟩ ∈
        ambientOpenOfOpenSubset (sphereNeighborhoodChartTargetTransitionDomain c d)
          (⟨Φ.target, Φ.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d)) := by
    have hcoord :
        d.equiv ⟨d.branch z.1, d.branch_mem_source z.1⟩ = z.1 := by
      simpa [SphereNeighborhoodChart.coord] using d.coord_branch z.1
    rw [hcoord]
    exact
      (mem_ambientOpenOfOpenSubset (U := sphereNeighborhoodChartTargetTransitionDomain c d)).2
        ⟨z.2, hz⟩
  -- After unfolding the reparameterized chart source, the previous target witness is exactly the
  -- required source-membership condition.
  dsimp [c', sphereNeighborhoodChart_reparametrizeTarget, sphereNeighborhoodChart_restrictTarget]
  exact
    (mem_ambientOpenOfOpenSubset (U := d.source)).2
      ⟨d.branch_mem_source z.1, hz'⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the explicit local-inverse
target window, source membership in the reparameterized chart is exactly the raw `d`-coordinate
window condition. This is the target-side bridge used in the fixed-chart frontier argument. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset (sphereNeighborhoodChartTargetTransitionDomain c d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d))
    ∀ y : X,
      y ∈ c'.source ↔
        ∃ hy_d : y ∈ d.source, d.equiv ⟨y, hy_d⟩ ∈ W := by
  intro hf Φ c' W y
  constructor
  · intro hy
    -- Unfolding the reparameterized source already exposes the required raw `d`-coordinate
    -- witness in the explicit target window `W`.
    have hy' :
        ∃ hy_d : y ∈ d.source,
          d.equiv ⟨y, hy_d⟩ ∈ W := by
      simpa [c', W, sphereNeighborhoodChart_reparametrizeTarget, sphereNeighborhoodChart_restrictTarget,
        mem_ambientOpenOfOpenSubset] using hy
    exact hy'
  · rintro ⟨hy_d, hyW⟩
    -- Conversely, a point of `d.source` whose `d`-coordinate lies in the local-inverse target
    -- window belongs to the reparameterized source by the same explicit unpacking.
    have hy' : y ∈ c'.source := by
      simpa [c', W, sphereNeighborhoodChart_reparametrizeTarget, sphereNeighborhoodChart_restrictTarget,
        mem_ambientOpenOfOpenSubset] using
        (show ∃ hy_d : y ∈ d.source, d.equiv ⟨y, hy_d⟩ ∈ W from ⟨hy_d, hyW⟩)
    exact hy'

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: after reparameterizing a fixed raw
chart `d` by a local inverse, applying the raw branch turns membership in `Φ.target` exactly into
source membership of the new chart. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_branch_mem_source_iff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    ∀ z : sphereNeighborhoodChartTargetTransitionDomain c d,
      d.branch z.1 ∈ c'.source ↔ z ∈ Φ.target := by
  intro hf Φ c' z
  constructor
  · intro hzSource
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset (sphereNeighborhoodChartTargetTransitionDomain c d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d))
    have hzW :
        ∃ hz_d : d.branch z.1 ∈ d.source, d.equiv ⟨d.branch z.1, hz_d⟩ ∈ W :=
      (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff (c := c) (d := d) x)
        (y := d.branch z.1) |>.1 hzSource
    rcases hzW with ⟨hz_d, hzW⟩
    have hcoord :
        d.equiv ⟨d.branch z.1, hz_d⟩ = z.1 := by
      -- Re-applying the `d`-chart after the raw branch returns the original target coordinate.
      apply Subtype.ext
      simpa [SphereNeighborhoodChart.coord] using d.coord_branch z.1
    have hzAmbient :
        z.1 ∈ W := by
      simpa [hcoord] using hzW
    -- Membership in the ambient window is exactly the original `Φ.target` condition.
    exact (mem_ambientOpenOfOpenSubset
      (U := sphereNeighborhoodChartTargetTransitionDomain c d)
      (V := ⟨Φ.target, Φ.open_target⟩)
      (y := z.1)).1 hzAmbient |>.2
  · intro hz
    -- The forward implication is the already proved branch-transport lemma.
    exact
      sphereNeighborhoodChart_reparametrizeTarget_branch_mem_source
        (c := c) (d := d) x z hz

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: if a seeded chart and a raw chart
meet at a common source point, one target-side continuation step produces a new seeded chart that
covers that point inside the raw chart source. -/
lemma seededSphereNeighborhoodChart_continueAtCommonSource
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X}
    (c : SeededSphereNeighborhoodChart c₀) {d : SphereNeighborhoodChart X} {x : X}
    (hx : x ∈ c.chart.source) (hd : x ∈ d.source) :
    ∃ c' : SeededSphereNeighborhoodChart c₀,
      x ∈ c'.chart.source ∧ (c'.chart.source : Set X) ⊆ d.source := by
  let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨x, hx, hd⟩
  let hstep :=
    sphereNeighborhoodChart_continueAtTargetPoint (c := c.chart) (d := d) xcommon
  let c' : SeededSphereNeighborhoodChart c₀ :=
    seededSphereNeighborhoodChart_of_continuation c hstep
  refine ⟨c', ?_, ?_⟩
  · -- The hand-off point belongs to the new seeded chart by the local-inverse construction.
    simpa [c', hstep, xcommon] using
      (sphereNeighborhoodChart_reparametrizeTarget_point_mem_source
        (c := c.chart) (d := d) xcommon)
  · -- The new chart is still a restriction of the chosen raw chart `d`.
    simpa [c', hstep, xcommon] using
      (sphereNeighborhoodChart_reparametrizeTarget_source_subset
        (c := c.chart) (d := d) xcommon)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: along a path issuing from a seed point,
every parameter value should be covered by some seeded continuation chart. This is the precise
global propagation owner still missing from the seeded continuation argument. -/
lemma seededSphereNeighborhoodChart_continueNearPathTime
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (t : unitInterval)
    (c : SeededSphereNeighborhoodChart c₀) (htc : γ t ∈ c.chart.source)
    (d : SphereNeighborhoodChart X) (htd : γ t ∈ d.source) :
    ∃ c' : SeededSphereNeighborhoodChart c₀,
      (c'.chart.source : Set X) ⊆ d.source ∧
        ∃ U ∈ nhds t, ∀ s ∈ U, γ s ∈ c'.chart.source := by
  rcases seededSphereNeighborhoodChart_continueAtCommonSource c htc htd with
    ⟨c', hcenter, hsubset⟩
  refine ⟨c', hsubset, ?_⟩
  -- Pull back the open source of the continued chart to a time-neighborhood of `t`.
  have hpreimage :
      γ ⁻¹' (c'.chart.source : Set X) ∈ nhds t := by
    exact γ.continuous.continuousAt.preimage_mem_nhds
      (c'.chart.source.isOpen.mem_nhds hcenter)
  refine ⟨γ ⁻¹' (c'.chart.source : Set X), hpreimage, ?_⟩
  intro s hs
  exact hs

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: when a seeded chart is continued at a
common source point into a fixed raw chart `d`, the nearby path image lands in one explicit
target window of `d`. This keeps the local inverse window visible for the later target-side
clopen argument instead of discarding it behind a bare source-membership witness. -/
lemma seededSphereNeighborhoodChart_continueNearPathTime_targetWindow
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (t : unitInterval)
    (c : SeededSphereNeighborhoodChart c₀) (htc : γ t ∈ c.chart.source)
    (d : SphereNeighborhoodChart X) (htd : γ t ∈ d.source) :
    let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨γ t, htc, htd⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) xcommon
    let Φ := hf.localInverse
    let c' : SeededSphereNeighborhoodChart c₀ :=
      seededSphereNeighborhoodChart_of_continuation c
        (sphereNeighborhoodChart_continueAtTargetPoint (c := c.chart) (d := d) xcommon)
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    (c'.chart.source : Set X) ⊆ d.source ∧
      ∃ U ∈ nhds t, ∀ s ∈ U, ∃ hs_d : γ s ∈ d.source, d.equiv ⟨γ s, hs_d⟩ ∈ W := by
  intro xcommon hf Φ c' W
  have hsubset :
      (c'.chart.source : Set X) ⊆ d.source := by
    -- The explicit continued chart is still a restriction of the fixed raw chart `d`.
    simpa [c', xcommon] using
      (sphereNeighborhoodChart_reparametrizeTarget_source_subset
        (c := c.chart) (d := d) xcommon)
  have hcenter : γ t ∈ c'.chart.source := by
    -- The hand-off point belongs to the explicit continued chart by construction.
    simpa [c', xcommon] using
      (sphereNeighborhoodChart_reparametrizeTarget_point_mem_source
        (c := c.chart) (d := d) xcommon)
  have hpreimage :
      γ ⁻¹' (c'.chart.source : Set X) ∈ nhds t := by
    -- Pull back the open source of the explicit continued chart to a time neighborhood of `t`.
    exact γ.continuous.continuousAt.preimage_mem_nhds (c'.chart.source.isOpen.mem_nhds hcenter)
  refine ⟨hsubset, γ ⁻¹' (c'.chart.source : Set X), hpreimage, ?_⟩
  intro s hs
  have hsSource : γ s ∈ c'.chart.source := hs
  -- Convert the visible continued-chart source membership back into the explicit raw target
  -- window condition in `d.target`.
  exact
    (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
      (c := c.chart) (d := d) xcommon) (y := γ s) |>.1 <| by
        simpa [c', W, xcommon] using hsSource

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: for a fixed raw chart `d`, two path
times are adjacent when some seeded chart subordinate to `d.source` covers both of them. This is
the one-step relation used in the later fixed-chart reachability argument. -/
def seededSphereNeighborhoodChartStep
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) :
    unitInterval → unitInterval → Prop :=
  fun s t ↦
    ∃ c : SeededSphereNeighborhoodChart c₀,
      (c.chart.source : Set X) ⊆ d.source ∧
        γ s ∈ c.chart.source ∧ γ t ∈ c.chart.source

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the fixed-chart one-step relation is
symmetrical, since a single subordinate seeded chart covers its two time parameters in either
order. -/
lemma seededSphereNeighborhoodChartStep_symmetric
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) :
    Symmetric (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) := by
  intro s t hst
  rcases hst with ⟨c, hsubset, hs, ht⟩
  -- The same subordinate seeded chart witnesses the reversed step as well.
  exact ⟨c, hsubset, ht, hs⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: along the reflexive-transitive
closure of the fixed-chart step relation, subordinate seeded-chart coverage propagates from the
starting time to the endpoint. -/
lemma seededSphereNeighborhoodChart_reflTransGen_hasSubordinateChart
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval}
    (hst :
      Relation.ReflTransGen
        (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s t)
    (hs :
      ∃ c : SeededSphereNeighborhoodChart c₀,
        (c.chart.source : Set X) ⊆ d.source ∧ γ s ∈ c.chart.source) :
    ∃ c : SeededSphereNeighborhoodChart c₀,
      (c.chart.source : Set X) ⊆ d.source ∧ γ t ∈ c.chart.source := by
  induction hst generalizing hs with
  | refl =>
      exact hs
  | tail hab hbc ih =>
      -- Move the subordinate seeded-chart witness along the last one-step edge of the chain.
      rcases hbc with ⟨c', hsubset', _hb, hc⟩
      exact ⟨c', hsubset', hc⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: inside a fixed raw chart `d`, the
reachability class of a time already covered by a subordinate seeded chart is open. This isolates
the open half of the fixed-chart component argument used later in the pathwise propagation proof.
-/
lemma seededSphereNeighborhoodChart_reachClass_isOpen
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    (s : unitInterval)
    (hs :
      ∃ c : SeededSphereNeighborhoodChart c₀,
        (c.chart.source : Set X) ⊆ d.source ∧ γ s ∈ c.chart.source) :
    IsOpen {t : unitInterval |
      Relation.ReflTransGen
        (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s t} := by
  refine isOpen_iff_mem_nhds.2 ?_
  intro t ht
  rcases seededSphereNeighborhoodChart_reflTransGen_hasSubordinateChart
      (γ := γ) (d := d) ht hs with ⟨c, hsubset, hct⟩
  -- A neighborhood contained in the same subordinate seeded chart stays in the same class by one
  -- extra reachability step.
  refine Filter.mem_of_superset
    (γ.continuous.continuousAt.preimage_mem_nhds (c.chart.source.isOpen.mem_nhds hct)) ?_
  intro u hu
  exact Relation.ReflTransGen.tail ht ⟨c, hsubset, hct, hu⟩

end
