import DifferentialForms_Cartan_1970.VI.section25.«0016_Theorem_VI_4_extra_13».SphereNeighborhoodContinuation

universe u

open scoped Complex.UnitDisc Manifold
open Filter

section

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the raw coordinate of a point in a
chart does not depend on which proof of source membership is used. -/
lemma sphereNeighborhoodChart_coord_eq_of_sourcePoint
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (d : SphereNeighborhoodChart X) {x : X} {hx₁ hx₂ : x ∈ d.source} :
    d.equiv ⟨x, hx₁⟩ = d.equiv ⟨x, hx₂⟩ := by
  -- Both subtype points have the same underlying manifold point, so the chart coordinate agrees.
  have hsource : (⟨x, hx₁⟩ : d.source) = ⟨x, hx₂⟩ := by
    apply Subtype.ext
    rfl
  exact congrArg d.equiv hsource

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: at the chosen hand-off point, the raw
`d`-coordinate already lies in the canonical local-inverse target window. -/
lemma sphereNeighborhoodChart_handoffCoord_memCanonicalTargetWindow
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c) (d := d) x
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d))
    d.equiv ⟨x.1, x.2.2⟩ ∈ W := by
  intro hf Φ W
  -- The hand-off coordinate belongs to the transition domain because the raw branch returns the
  -- common-source point, which lies in `c.source`.
  refine (mem_ambientOpenOfOpenSubset
    (U := sphereNeighborhoodChartTargetTransitionDomain c d)).2 ?_
  refine ⟨?_, hf.localInverse_mem_target⟩
  change d.branch (d.equiv ⟨x.1, x.2.2⟩) ∈ c.source
  simpa [SphereNeighborhoodChart.branch_coord] using x.2.1

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once the fixed center interval and the
nearby subordinate hand-off point are chosen, the remaining blocker is purely target-side: the
fixed `d`-coordinate of the center time should lie in the explicit local-inverse window used to
continue the subordinate chart into `d`. -/
lemma sphereNeighborhoodChart_centerIntervalTargetImage_preconnected
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) {s t : unitInterval}
    {a b : unitInterval}
    (hIcc_subset : ∀ {w : Set.uIcc s t},
      w.1 ∈ Set.Icc a b → γ w.1 ∈ d.source)
    {v : Set.uIcc s t} (hvU : v.1 ∈ Set.Icc a b) :
    let J : Type _ := {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}
    let coordJ : J → d.target := fun w ↦ d.equiv ⟨γ w.1.1, hIcc_subset (w := w.1) w.2⟩
    let Z : Set d.target := Set.range coordJ
    IsPreconnected Z ∧ coordJ ⟨v, hvU⟩ ∈ Z := by
  intro J coordJ Z
  let K : Set unitInterval := Set.uIcc s t ∩ Set.Icc a b
  let coordK : K → d.target := fun w ↦
    let wu : Set.uIcc s t := ⟨w.1, w.2.1⟩
    d.equiv ⟨γ w.1, hIcc_subset (w := wu) (by simpa [wu] using w.2.2)⟩
  have hcoordK_cont : Continuous coordK := by
    -- View the reduced interval directly as a subset of `unitInterval`, then apply the raw chart
    -- coordinate on `d.source`.
    refine d.equiv.toHomeomorph.continuous_toFun.comp ?_
    exact Continuous.subtype_mk
      (γ.continuous.comp continuous_subtype_val)
      (fun w ↦ by
        let wu : Set.uIcc s t := ⟨w.1, w.2.1⟩
        exact hIcc_subset (w := wu) (by simpa [wu] using w.2.2))
  have hKpre : IsPreconnected K := by
    -- In `unitInterval`, the reduced center interval is just the intersection of two order
    -- intervals, hence still preconnected.
    exact
      (((isPreconnected_uIcc : IsPreconnected (Set.uIcc s t)).ordConnected).inter
        (isPreconnected_Icc : IsPreconnected (Set.Icc a b)).ordConnected).isPreconnected
  letI : PreconnectedSpace K := Subtype.preconnectedSpace hKpre
  have hrange_eq : Set.range coordJ = Set.range coordK := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨⟨w.1.1, ⟨w.1.2, w.2⟩⟩, ?_⟩
      rfl
    · rintro ⟨w, rfl⟩
      refine ⟨⟨⟨w.1, w.2.1⟩, w.2.2⟩, ?_⟩
      rfl
  refine ⟨?_, ?_⟩
  · -- The fixed `d`-coordinate image of the reduced interval is still a continuous image of a
    -- preconnected source.
    change IsPreconnected (Set.range coordJ)
    rw [hrange_eq]
    simpa using isPreconnected_range (f := coordK) hcoordK_cont
  · -- The chosen hand-off time is one explicit point of that image.
    exact ⟨⟨v, hvU⟩, rfl⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the reduced center-interval hand-off
coordinate already lies in the explicit local-inverse target window attached to the subordinate
chart `c`. -/
lemma sphereNeighborhoodChart_centerIntervalHandoffCoord_memCanonicalTargetWindow
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X) {s t : unitInterval}
    {a b : unitInterval}
    (hIcc_subset : ∀ {w : Set.uIcc s t},
      w.1 ∈ Set.Icc a b → γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    {v : Set.uIcc s t} {c : SeededSphereNeighborhoodChart c₀}
    (hvU : v.1 ∈ Set.Icc a b)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hcv : γ v.1 ∈ c.chart.source) :
    let J : Type _ := {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}
    let coordJ : J → d.target := fun w ↦ d.equiv ⟨γ w.1.1, (hIcc_subset (w := w.1) w.2).2⟩
    let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨γ v.1, hcv, hcsub hcv⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) xcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    coordJ ⟨v, hvU⟩ ∈ W := by
  intro J coordJ xcommon hf Φ W
  have hcoord_v :
      coordJ ⟨v, hvU⟩ = d.equiv ⟨γ v.1, hcsub hcv⟩ := by
    -- Both target coordinates use the same hand-off point of `d.source`; only the proof term
    -- differs.
    exact sphereNeighborhoodChart_coord_eq_of_sourcePoint d
  -- After normalizing the reduced-interval coordinate spelling, the existing hand-off lemma
  -- applies directly.
  rw [hcoord_v]
  exact sphereNeighborhoodChart_handoffCoord_memCanonicalTargetWindow (c := c.chart) (d := d) xcommon

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: reparameterizing a raw chart `d`
through the local inverse of the transition from `c` does not leave the original chart `c` on the
source side. The new chart only changes the target coordinate system on the same overlap region. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_source_subset_left
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    (c'.source : Set X) ⊆ c.source := by
  intro hf Φ c' y hy
  have hy' :
      ∃ hy_d : y ∈ d.source,
        ∃ hy_dom : d.equiv ⟨y, hy_d⟩ ∈ sphereNeighborhoodChartTargetTransitionDomain c d,
          (⟨d.equiv ⟨y, hy_d⟩, hy_dom⟩ : sphereNeighborhoodChartTargetTransitionDomain c d) ∈
            (⟨Φ.target, Φ.open_target⟩ :
              TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d)) := by
    -- Unfold the restricted-source witness until the original transition-domain membership is
    -- visible again.
    simpa [c', sphereNeighborhoodChart_reparametrizeTarget, sphereNeighborhoodChart_restrictTarget,
      mem_ambientOpenOfOpenSubset] using hy
  rcases hy' with ⟨hy_d, hy_dom, _hy_target⟩
  -- The transition-domain witness says exactly that the `d`-branch of the visible `d`-coordinate
  -- lands in the original source of `c`.
  change d.branch (d.equiv ⟨y, hy_d⟩) ∈ c.source at hy_dom
  simpa [SphereNeighborhoodChart.branch_coord] using hy_dom

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: if a chart `c` is already
subordinate to a fixed raw chart `d`, then any further continuation of `c` into that same `d`
still has source contained in `c.source`. This isolates the fixed-`d` uniqueness step that the
reduced-interval closure argument needs after it produces a second continuation chart. -/
lemma sphereNeighborhoodChart_secondContinuation_source_subset
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X}
    (hcsub : (c.source : Set X) ⊆ d.source)
    {y : X} (hy : y ∈ c.source) :
    let ycommon : sphereNeighborhoodChartCommonSource c d := ⟨y, hy, hcsub hy⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) ycommon
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    (c'.source : Set X) ⊆ c.source := by
  intro ycommon hf Φ c'
  -- A second continuation only changes the target coordinate system on the already visible
  -- overlap with `d`, so its source cannot leave the current chart source.
  simpa [c', ycommon] using
    (sphereNeighborhoodChart_reparametrizeTarget_source_subset_left
      (c := c) (d := d) ycommon)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once a chart `c₁` is obtained by
continuing `c` into a fixed raw chart `d`, any second continuation of `c₁` into that same `d`
uses a canonical target window contained in the first one. This is the nonrecursive target-side
comparison needed before the reduced-interval clopen argument can even ask for closedness. -/
lemma sphereNeighborhoodChart_secondCanonicalWindow_subset
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X}
    (x : sphereNeighborhoodChartCommonSource c d) :
    let hf₁ := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c) (d := d) x
    let Φ₁ := hf₁.localInverse
    let c₁ := sphereNeighborhoodChart_reparametrizeTarget c d Φ₁
    let W₁ : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c d)
        (⟨Φ₁.target, Φ₁.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c d))
    ∀ {y : X} (hy : y ∈ c₁.source),
      let ycommon : sphereNeighborhoodChartCommonSource c₁ d :=
        ⟨y, hy,
          (sphereNeighborhoodChart_reparametrizeTarget_source_subset
            (c := c) (d := d) x) hy⟩
      let hf₂ := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
        (c := c₁) (d := d) ycommon
      let Φ₂ := hf₂.localInverse
      let W₂ : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c₁ d)
          (⟨Φ₂.target, Φ₂.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c₁ d))
      (W₂ : Set d.target) ⊆ W₁ := by
  intro hf₁ Φ₁ c₁ W₁ y hy
  intro ycommon hf₂ Φ₂ W₂ z hzW₂
  have hzDomain₂ :
      z ∈ sphereNeighborhoodChartTargetTransitionDomain c₁ d := by
    -- Unpack the second ambient window membership into the explicit second transition domain.
    exact (mem_ambientOpenOfOpenSubset
      (U := sphereNeighborhoodChartTargetTransitionDomain c₁ d)
      (V := ⟨Φ₂.target, Φ₂.open_target⟩)
      (y := z)).1 hzW₂ |>.1
  have hzSource₁ : d.branch z ∈ c₁.source := by
    -- Being in the second transition domain is exactly the statement that the `d`-branch lands
    -- in the first continued chart source.
    simpa [sphereNeighborhoodChartTargetTransitionDomain] using hzDomain₂
  have hzSource : d.branch z ∈ c.source := by
    -- A first continuation stays inside the original chart source, so the same branch point
    -- belongs to the original source as well.
    exact
      (sphereNeighborhoodChart_reparametrizeTarget_source_subset_left
        (c := c) (d := d) x) hzSource₁
  let z₁ : sphereNeighborhoodChartTargetTransitionDomain c d := ⟨z, hzSource⟩
  have hzTarget₁ : z₁ ∈ Φ₁.target := by
    -- Route correction: instead of recursing on source neighborhoods, use the first continuation
    -- membership bridge to read `d.branch z ∈ c₁.source` back as `z ∈ Φ₁.target`.
    exact
      (sphereNeighborhoodChart_reparametrizeTarget_branch_mem_source_iff
        (c := c) (d := d) x) z₁ |>.1 hzSource₁
  -- Repackage the first target-domain membership and the recovered `Φ₁.target` witness as
  -- membership in the ambient first window `W₁`.
  exact
    (mem_ambientOpenOfOpenSubset
      (U := sphereNeighborhoodChartTargetTransitionDomain c d)
      (V := ⟨Φ₁.target, Φ₁.open_target⟩)
      (y := z)).2 ⟨hzSource, hzTarget₁⟩
end
