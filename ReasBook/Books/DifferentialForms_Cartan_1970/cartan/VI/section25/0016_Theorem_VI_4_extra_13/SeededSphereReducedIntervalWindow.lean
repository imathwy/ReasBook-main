import DifferentialForms_Cartan_1970.VI.section25.«0016_Theorem_VI_4_extra_13».SeededSphereIntervalPropagation
import DifferentialForms_Cartan_1970.VI.section25.«0016_Theorem_VI_4_extra_13».SphereNeighborhoodCanonicalWindow

universe u

open scoped Complex.UnitDisc Manifold
open Filter

section

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the reduced interval subtype cut out by
`Set.uIcc s t` and `Set.Icc a b` is preconnected. This packages the interval-intersection topology
used by the target-window clopen argument. -/
lemma sphereNeighborhoodChart_reducedInterval_preconnectedSpace
    {s t a b : unitInterval} :
    let J : Type _ := {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}
    PreconnectedSpace J := by
  intro J
  let S : Set (Set.uIcc s t) := {w | w.1 ∈ Set.Icc a b}
  have hSpre : IsPreconnected S := by
    have hImg : Subtype.val '' S = Set.uIcc s t ∩ Set.Icc a b := by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u.2, hu⟩
      · rintro ⟨hwst, hwab⟩
        exact ⟨⟨w, hwst⟩, hwab, rfl⟩
    -- The reduced interval is the intersection of two order intervals inside `unitInterval`.
    refine (Topology.IsInducing.subtypeVal.isPreconnected_image).mp ?_
    rw [hImg]
    simpa [Set.inter_comm] using
      ((((isPreconnected_uIcc : IsPreconnected (Set.uIcc s t)).ordConnected).inter
        (isPreconnected_Icc : IsPreconnected (Set.Icc a b)).ordConnected).isPreconnected :
          IsPreconnected (Set.uIcc s t ∩ Set.Icc a b))
  -- Repackage the interval intersection as the desired subtype `J`.
  simpa [J, S] using (Subtype.preconnectedSpace hSpre : PreconnectedSpace S)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: every neighborhood in the reduced
interval subtype already contains a smaller ambient `unitInterval` interval. This normalizes
neighborhoods on the nested subtype before the continued-chart target-window comparison. -/
lemma sphereNeighborhoodChart_reducedIntervalIccBasisAt
    {s t a b : unitInterval}
    (u : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b})
    {N : Set {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}}
    (hN : N ∈ nhds u) :
    ∃ a' b' : unitInterval,
      u.1.1 ∈ Set.Icc a' b' ∧
        {w : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b} | w.1.1 ∈ Set.Icc a' b'} ∈ nhds u ∧
        {w : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b} | w.1.1 ∈ Set.Icc a' b'} ⊆ N := by
  let J : Type _ := {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}
  let K : Type _ := {w : unitInterval // w ∈ Set.uIcc s t ∩ Set.Icc a b}
  let toK : J → K := fun w ↦ ⟨w.1.1, ⟨w.1.2, w.2⟩⟩
  let fromK : K → J := fun w ↦ ⟨⟨w.1, w.2.1⟩, w.2.2⟩
  have hfrom_to : ∀ w : J, fromK (toK w) = w := by
    intro w
    cases w
    rfl
  have hto_cont : Continuous toK := by
    -- Repackage the nested subtype as the explicit intersection subtype inside `unitInterval`.
    exact
      Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun w ↦ ⟨w.1.2, w.2⟩)
  have hfrom_cont : Continuous fromK := by
    -- Lower back from the explicit intersection subtype to the reduced interval subtype.
    let hbase : Continuous fun w : K ↦ (⟨w.1, w.2.1⟩ : Set.uIcc s t) :=
      Continuous.subtype_mk continuous_subtype_val (fun w ↦ w.2.1)
    exact Continuous.subtype_mk hbase (fun w ↦ w.2.2)
  have hN_K : fromK ⁻¹' N ∈ nhds (toK u) := by
    simpa [hfrom_to u] using hfrom_cont.continuousAt.preimage_mem_nhds hN
  obtain ⟨aK, bK, huIcc, hIcc_nhds, hIcc_subset⟩ :=
    exists_Icc_mem_subset_of_mem_nhds hN_K
  let M : Set J := {w | w.1.1 ∈ Set.Icc aK.1 bK.1}
  have hM_eq : M = toK ⁻¹' Set.Icc aK bK := by
    ext w
    -- The explicit `unitInterval` interval on `K` is exactly the ambient-coordinate interval on
    -- the reduced interval subtype `J`.
    change (w.1.1 ∈ Set.Icc aK.1 bK.1) ↔ toK w ∈ Set.Icc aK bK
    change (aK.1 ≤ w.1.1 ∧ w.1.1 ≤ bK.1) ↔
      (aK.1 ≤ w.1.1 ∧ w.1.1 ≤ bK.1)
    rfl
  refine ⟨aK.1, bK.1, ?_, ?_, ?_⟩
  · -- Forget the explicit intersection subtype back to the ambient time parameter.
    simpa [toK, Set.mem_Icc] using huIcc
  · -- Pull the interval neighborhood on `K` back across the identification map `toK`.
    change M ∈ nhds u
    rw [hM_eq]
    exact hto_cont.continuousAt.preimage_mem_nhds hIcc_nhds
  · intro w hw
    have hwK : toK w ∈ Set.Icc aK bK := by
      change w ∈ M at hw
      rw [hM_eq] at hw
      exact hw
    -- Push the interval inclusion into `fromK ⁻¹' N` back through the inverse identification.
    simpa [fromK, hfrom_to w] using hIcc_subset hwK

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the reduced interval subtype `J`,
continuing a subordinate seeded chart at one hand-off time still covers a neighborhood of that
hand-off time inside `J`. This isolates the already-available pointwise neighborhood statement
before the remaining uniform center-return upgrade. -/
lemma sphereNeighborhoodChart_reducedIntervalContinuedChart_mem_nhds
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval} {a b : unitInterval}
    (hIcc_subset : ∀ {w : Set.uIcc s t},
      w.1 ∈ Set.Icc a b → γ w.1 ∈ d.source)
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    {v : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}}
    (hvSource : γ v.1.1 ∈ c.chart.source) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ v.1.1, hvSource, hcsub hvSource⟩
    let c' : SeededSphereNeighborhoodChart c₀ :=
      seededSphereNeighborhoodChart_of_continuation c
        (sphereNeighborhoodChart_continueAtTargetPoint
          (c := c.chart) (d := d) vcommon)
    ∃ V ∈ nhds v,
      ∀ {w : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}},
        w ∈ V → γ w.1.1 ∈ c'.chart.source := by
  intro vcommon c'
  let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
    (c := c.chart) (d := d) vcommon
  let Φ := hf.localInverse
  let W : TopologicalSpace.Opens d.target :=
    ambientOpenOfOpenSubset
      (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
      (⟨Φ.target, Φ.open_target⟩ :
        TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
  rcases seededSphereNeighborhoodChart_continueNearPathTime_targetWindow
      (c₀ := c₀) (γ := γ) (t := v.1.1) c hvSource d (hcsub hvSource) with
    ⟨hc'sub, U, hU_nhds, hU⟩
  let pathJ : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b} → unitInterval := fun w ↦ w.1.1
  have hpathJ : Continuous pathJ := by
    -- Forget the two subtype layers back to the ambient time parameter.
    exact continuous_subtype_val.comp continuous_subtype_val
  refine ⟨pathJ ⁻¹' U, hpathJ.continuousAt.preimage_mem_nhds hU_nhds, ?_⟩
  intro w hw
  rcases hU w.1.1 hw with ⟨hw_d, hwW⟩
  -- Pull the ambient target-window witness back to the reduced interval subtype, then convert it
  -- back into source membership of the explicit continued chart.
  exact
    (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
      (c := c.chart) (d := d) vcommon) (y := γ w.1.1) |>.2 <| by
        refine ⟨hw_d, ?_⟩
        simpa [c', W, hf, Φ, vcommon] using hwW

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the reduced interval subtype `J`,
source membership in the explicit continued chart is equivalent to the fixed raw `d`-coordinate
lying in that continuation's canonical local-inverse window. This keeps the remaining center-return
blocker on the target side. -/
lemma sphereNeighborhoodChart_reducedInterval_mem_continuedChart_iff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval} {a b : unitInterval}
    (hIcc_subset : ∀ {w : Set.uIcc s t},
      w.1 ∈ Set.Icc a b → γ w.1 ∈ d.source)
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    {v : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}}
    (hvSource : γ v.1.1 ∈ c.chart.source) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ v.1.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let c' : SeededSphereNeighborhoodChart c₀ :=
      seededSphereNeighborhoodChart_of_continuation c
        (sphereNeighborhoodChart_continueAtTargetPoint
          (c := c.chart) (d := d) vcommon)
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∀ {w : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}},
      γ w.1.1 ∈ c'.chart.source ↔
        d.equiv ⟨γ w.1.1, hIcc_subset (w := w.1) w.2⟩ ∈ W := by
  intro vcommon hf Φ c' W w
  constructor
  · intro hwSource
    rcases
        (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
          (c := c.chart) (d := d) vcommon) (y := γ w.1.1) |>.1 hwSource with
      ⟨hw_d, hwW⟩
    -- Normalize the visible `d`-coordinate of `γ w` to the proof spelling dictated by the
    -- reduced-interval membership witness.
    have hcoord :
        d.equiv ⟨γ w.1.1, hw_d⟩ =
          d.equiv ⟨γ w.1.1, hIcc_subset (w := w.1) w.2⟩ :=
      sphereNeighborhoodChart_coord_eq_of_sourcePoint d
    exact hcoord ▸ hwW
  · intro hwW
    -- Convert the fixed `d`-target-window witness back into source membership of the explicit
    -- continued chart.
    exact
      (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
        (c := c.chart) (d := d) vcommon) (y := γ w.1.1) |>.2 <| by
          refine ⟨hIcc_subset (w := w.1) w.2, ?_⟩
          simpa [W] using hwW

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: after continuing a subordinate chart
at one reduced-interval hand-off point, nearby reduced-interval points already have their fixed
raw `d`-coordinates inside the explicit canonical target window of that continuation. This is the
pointwise target-side owner that the remaining uniform center-return step must later absorb over
one fixed reduced subinterval. -/
lemma sphereNeighborhoodChart_reducedIntervalCoord_memCanonicalWindow_nhds
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval} {a b : unitInterval}
    (hIcc_subset : ∀ {w : Set.uIcc s t},
      w.1 ∈ Set.Icc a b → γ w.1 ∈ d.source)
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    {v : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}}
    (hvSource : γ v.1.1 ∈ c.chart.source) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ v.1.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let c' : SeededSphereNeighborhoodChart c₀ :=
      seededSphereNeighborhoodChart_of_continuation c
        (sphereNeighborhoodChart_continueAtTargetPoint
          (c := c.chart) (d := d) vcommon)
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∃ V ∈ nhds v,
      ∀ {w : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}},
        w ∈ V →
          d.equiv ⟨γ w.1.1, hIcc_subset (w := w.1) w.2⟩ ∈ W := by
  intro vcommon hf Φ c' W
  rcases
    sphereNeighborhoodChart_reducedIntervalContinuedChart_mem_nhds
      (c₀ := c₀) (γ := γ) (d := d) hIcc_subset c hcsub (v := v) hvSource with
    ⟨V, hV_nhds, hV⟩
  refine ⟨V, hV_nhds, ?_⟩
  intro w hw
  -- Translate the visible source-neighborhood statement to the explicit target-window spelling
  -- attached to the continued chart at `v`.
  have hiff :
      γ w.1.1 ∈ c'.chart.source ↔
        d.equiv ⟨γ w.1.1, hIcc_subset (w := w.1) w.2⟩ ∈ W := by
    simpa [vcommon, hf, Φ, c', W] using
      sphereNeighborhoodChart_reducedInterval_mem_continuedChart_iff
        (c₀ := c₀) (γ := γ) (d := d) hIcc_subset c hcsub (v := v) hvSource (w := w)
  exact hiff.1 (hV hw)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the fixed `d`-coordinate image of the
smaller interval `Set.uIcc a' b'` is preconnected. This isolates the topological input for the
remaining target-window propagation step. -/
lemma sphereNeighborhoodChart_smallIntervalCoord_continuous
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ d.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦ d.equiv ⟨γ w.1, hsmall_uIcc (w := w)⟩
    Continuous coordK := by
  intro coordK
  -- The fixed chart coordinate is continuous along the smaller interval because the path stays
  -- inside `d.source` there.
  refine d.equiv.toHomeomorph.continuous_toFun.comp ?_
  exact Continuous.subtype_mk
    (γ.continuous.comp continuous_subtype_val)
    (fun w ↦ hsmall_uIcc (w := w))

/-- Helper for Theorem VI.4-extra-13: a continuous map from a compact space to a Hausdorff target
is still a closed map after restricting its codomain to the range subtype. This is the exact
range-factor transport needed when the reduced-interval argument passes from the time parameter to
the target-image subtype. -/
lemma continuous_subtypeRange_isClosedMap
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : K → Y} (hf : Continuous f) :
    IsClosedMap (fun x : K ↦ (⟨f x, Set.mem_range_self x⟩ : Set.range f)) := by
  have hToRange :
      Continuous (fun x : K ↦ (⟨f x, Set.mem_range_self x⟩ : Set.range f)) := by
    -- The range-factor map is just the original continuous map repackaged into the subtype.
    exact Continuous.subtype_mk hf (fun x ↦ Set.mem_range_self x)
  -- Compact-to-Hausdorff closedness applies directly once the codomain is the range subtype.
  exact hToRange.isClosedMap

/-- Helper for Theorem VI.4-extra-13: the slice of a range subtype cut out by `W` is exactly the
image of the corresponding slice upstairs. This normalizes the target-image closure argument to the
plain interval-side set `{x | f x ∈ W}` before any compactness transport is applied. -/
lemma subtypeRange_preimage_eq_image
    {K : Type*} {Y : Type*} {f : K → Y} {W : Set Y} :
    ((Subtype.val : Set.range f → Y) ⁻¹' W) =
      (fun x : K ↦ (⟨f x, Set.mem_range_self x⟩ : Set.range f)) '' {x : K | f x ∈ W} := by
  ext z
  constructor
  · intro hz
    rcases z.2 with ⟨x, hxEq⟩
    refine ⟨x, ?_, ?_⟩
    · change f x ∈ W
      exact hxEq.symm ▸ hz
    · apply Subtype.ext
      exact hxEq
  · rintro ⟨x, hx, rfl⟩
    exact hx

/-- Helper for Theorem VI.4-extra-13: a cluster point of the `W`-slice in a range subtype lifts to
an interval-side cluster point of `{x | f x ∈ W}`. This is the compact/closed-map transport step
in the fixed-canonical-window closed-half argument. -/
lemma subtypeRange_cluster_liftsToClosure
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : K → Y} (hf : Continuous f) {W : Set Y}
    {z0 : Set.range f}
    (hz0 : z0 ∈ closure ((Subtype.val : Set.range f → Y) ⁻¹' W)) :
    ∃ x : K, x ∈ closure {x : K | f x ∈ W} ∧
      (⟨f x, Set.mem_range_self x⟩ : Set.range f) = z0 := by
  let g : K → Set.range f := fun x ↦ ⟨f x, Set.mem_range_self x⟩
  have hgClosed : IsClosedMap g := by
    -- Package the compact-to-range transport once so the closure argument can stay on the
    -- interval-side set `{x | f x ∈ W}`.
    simpa [g] using continuous_subtypeRange_isClosedMap hf
  have hslice :
      ((Subtype.val : Set.range f → Y) ⁻¹' W) = g '' {x : K | f x ∈ W} := by
    -- Normalize the target-image slice to the direct image of the interval-side slice.
    simpa [g] using subtypeRange_preimage_eq_image (f := f) (W := W)
  have hsubset :
      ((Subtype.val : Set.range f → Y) ⁻¹' W) ⊆ g '' closure {x : K | f x ∈ W} := by
    intro z hz
    rw [hslice] at hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, subset_closure hx, rfl⟩
  have hclosedImage : IsClosed (g '' closure {x : K | f x ∈ W}) := by
    -- Closedness now comes only from the compact closed-map bridge.
    exact hgClosed _ isClosed_closure
  have hz0Lift : z0 ∈ g '' closure {x : K | f x ∈ W} := by
    -- Push the given cluster point through the closed image that already contains the original
    -- slice.
    exact closure_minimal hsubset hclosedImage hz0
  rcases hz0Lift with ⟨x, hx, hxEq⟩
  exact ⟨x, hx, hxEq⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the smaller interval, belonging to
the canonical target window is an open condition on the time parameter once the fixed `d`-coordinate
map is used. This isolates the easy half of the later clopen argument. -/
lemma sphereNeighborhoodChart_smallIntervalCanonicalWindow_isOpen
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d : SphereNeighborhoodChart X) {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ d.source)
    {v : Set.uIcc a' b'} {c : SeededSphereNeighborhoodChart c₀}
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ v.1 ∈ c.chart.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦ d.equiv ⟨γ w.1, hsmall_uIcc (w := w)⟩
    let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨γ v.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) xcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    IsOpen {w : Set.uIcc a' b' | coordK w ∈ W} := by
  intro coordK xcommon hf _ W
  have hcoord_cont : Continuous coordK := by
    -- Reuse the fixed-interval continuity owner before pulling back the open target window.
    simpa [coordK] using
      sphereNeighborhoodChart_smallIntervalCoord_continuous
        (γ := γ) (d := d) hsmall_uIcc
  -- Pull back the canonical target window along the fixed `d`-coordinate map.
  simpa [coordK, Set.preimage] using W.isOpen.preimage hcoord_cont

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the fixed `d`-coordinate image of the
smaller interval `Set.uIcc a' b'` is preconnected. This isolates the topological input for the
remaining target-window propagation step. -/
lemma sphereNeighborhoodChart_smallIntervalTargetImage_preconnected
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ d.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦ d.equiv ⟨γ w.1, hsmall_uIcc (w := w)⟩
    let Z : Set d.target := Set.range coordK
    IsPreconnected Z := by
  intro coordK Z
  have hcoordK_cont : Continuous coordK := by
    -- Reuse the continuity owner so the remaining proof only packages the preconnected image step.
    simpa [coordK] using
      sphereNeighborhoodChart_smallIntervalCoord_continuous
        (γ := γ) (d := d) hsmall_uIcc
  letI : PreconnectedSpace (Set.uIcc a' b') := by
    -- The smaller interval is itself an order interval in `unitInterval`.
    exact Subtype.preconnectedSpace (isPreconnected_uIcc : IsPreconnected (Set.uIcc a' b'))
  -- Continuous images of preconnected spaces are preconnected.
  simpa [Z] using isPreconnected_range (f := coordK) hcoordK_cont

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: at the hand-off point of the smaller
interval, the fixed `d`-coordinate already lies in the canonical local-inverse target window used
to continue the subordinate chart `c` into `d`. -/
lemma sphereNeighborhoodChart_smallIntervalHandoffCoord_memCanonicalTargetWindow
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d : SphereNeighborhoodChart X) {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ d.source)
    {v : Set.uIcc a' b'} {c : SeededSphereNeighborhoodChart c₀}
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ v.1 ∈ c.chart.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦ d.equiv ⟨γ w.1, hsmall_uIcc (w := w)⟩
    let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨γ v.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) xcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    coordK v ∈ W := by
  intro coordK xcommon hf Φ W
  have hcoord_v :
      coordK v = d.equiv ⟨γ v.1, hcsub hvSource⟩ :=
    sphereNeighborhoodChart_coord_eq_of_sourcePoint d
  -- After normalizing the fixed-coordinate spelling, the generic hand-off target-window lemma
  -- applies directly.
  rw [hcoord_v]
  exact sphereNeighborhoodChart_handoffCoord_memCanonicalTargetWindow
    (c := c.chart) (d := d) xcommon

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the fixed smaller interval, once
the canonical target-window slice of the raw `d`-coordinate image is known to be closed, the
preconnected-image argument forces that window to contain the whole image. This isolates the
clopen packaging so the remaining blocker is only the closed half. -/
lemma sphereNeighborhoodChart_centerIntervalCanonicalWindow_eq_univ_of_isClosedInTargetImage
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d : SphereNeighborhoodChart X) {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ d.source)
    {v : Set.uIcc a' b'} {c : SeededSphereNeighborhoodChart c₀}
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ v.1 ∈ c.chart.source)
    (hclosed :
      let coordK : Set.uIcc a' b' → d.target := fun w ↦
        d.equiv ⟨γ w.1, hsmall_uIcc (w := w)⟩
      let Z : Set d.target := Set.range coordK
      let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨γ v.1, hvSource, hcsub hvSource⟩
      let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
        (c := c.chart) (d := d) xcommon
      let Φ := hf.localInverse
      let W : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
          (⟨Φ.target, Φ.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
      IsClosed ((Subtype.val : Z → d.target) ⁻¹' (W : Set d.target))) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦ d.equiv ⟨γ w.1, hsmall_uIcc (w := w)⟩
    let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨γ v.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) xcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∀ w : Set.uIcc a' b', coordK w ∈ W := by
  intro coordK xcommon hf Φ W w
  let Z : Set d.target := Set.range coordK
  let A : Set Z := (Subtype.val : Z → d.target) ⁻¹' (W : Set d.target)
  have hAopen : IsOpen A := by
    -- Restrict the canonical window to the preconnected target-image subtype.
    simpa [A] using W.isOpen.preimage continuous_subtype_val
  have hAclosed : IsClosed A := by
    -- Route correction: the clopen packaging is separated from the still-missing closed-half
    -- owner, so later work only has to prove this one closedness input.
    simpa [coordK, Z, xcommon, hf, Φ, W, A] using hclosed
  have hZpre : IsPreconnected Z := by
    -- The fixed raw-coordinate image of the smaller interval is already known to be preconnected.
    simpa [coordK, Z] using
      sphereNeighborhoodChart_smallIntervalTargetImage_preconnected
        (γ := γ) (d := d) hsmall_uIcc
  letI : PreconnectedSpace Z := Subtype.preconnectedSpace hZpre
  have hAnonempty : A.Nonempty := by
    -- The hand-off point supplies one explicit target-image point inside the canonical window.
    refine ⟨⟨coordK v, ⟨v, rfl⟩⟩, ?_⟩
    simpa [coordK, xcommon, hf, Φ, W, A] using
      sphereNeighborhoodChart_smallIntervalHandoffCoord_memCanonicalTargetWindow
        (c₀ := c₀) (γ := γ) (d := d) hsmall_uIcc hcsub hvSource
  have hAuniv : A = Set.univ := by
    -- A nonempty clopen subset of the preconnected image must be the whole image.
    exact IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAnonempty
  have hwA : (⟨coordK w, ⟨w, rfl⟩⟩ : Z) ∈ A := by
    simpa [A, hAuniv]
  -- Forget the range subtype again to recover the desired canonical-window membership.
  exact hwA

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the reduced interval subtype `J`,
nearby points already lying in one fixed continued chart `c` should force the center point into the
second continuation of `c` through the same raw chart `d`. This isolates the only remaining local
center-return kernel in the target-window clopen argument. -/
lemma sphereNeighborhoodChart_centerCoord_memCanonicalTargetWindow_on_smallInterval
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X) {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (v : Set.uIcc a' b') (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ v.1 ∈ c.chart.source) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ v.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∃ U ∈ nhds v.1,
      ∀ {w : Set.uIcc a' b'}, w.1 ∈ U →
        d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩ ∈ W := by
  intro vcommon hf Φ W
  let c' : SeededSphereNeighborhoodChart c₀ :=
    seededSphereNeighborhoodChart_of_continuation c
      (sphereNeighborhoodChart_continueAtTargetPoint
        (c := c.chart) (d := d) vcommon)
  have hnearW :
      (c'.chart.source : Set X) ⊆ d.source ∧
        ∃ U ∈ nhds v.1,
          ∀ s ∈ U, ∃ hs_d : γ s ∈ d.source, d.equiv ⟨γ s, hs_d⟩ ∈ W := by
    -- Route correction: the valid owner here is only a one-sided neighborhood of the hand-off
    -- time `v.1`; the earlier whole-small-interval statement was too strong.
    simpa [c', vcommon, hf, Φ, W] using
      seededSphereNeighborhoodChart_continueNearPathTime_targetWindow
        (c₀ := c₀) (γ := γ) (t := v.1) c hvSource d ((hsmall_uIcc (w := v)).2)
  rcases hnearW with ⟨_hc'sub_d, U, hU_nhds, hUW⟩
  refine ⟨U, hU_nhds, ?_⟩
  intro w hwU
  rcases hUW w.1 hwU with ⟨hw_d, hwW⟩
  have hcoord_w :
      d.equiv ⟨γ w.1, hw_d⟩ = d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩ :=
    sphereNeighborhoodChart_coord_eq_of_sourcePoint d
  -- Replace the neighborhood witness by the canonical `hsmall_uIcc` source proof.
  exact hcoord_w ▸ hwW

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on one fixed reduced interval and for
one fixed hand-off time `vSmall`, membership in the canonical `d`-target window is exactly source
membership in the continued chart obtained from `c` at `vSmall`. This names the fixed-window
normal form so later arguments can stay source-side until the last conversion step. -/
lemma sphereNeighborhoodChart_fixedCanonicalWindow_mem_iff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (wSmall vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let c' : SeededSphereNeighborhoodChart c₀ :=
      seededSphereNeighborhoodChart_of_continuation c
        (sphereNeighborhoodChart_continueAtTargetPoint
          (c := c.chart) (d := d) vcommon)
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    γ wSmall.1 ∈ c'.chart.source ↔
      d.equiv ⟨γ wSmall.1, (hsmall_uIcc (w := wSmall)).2⟩ ∈ W := by
  intro vcommon hf Φ c' W
  constructor
  · intro hwSource
    rcases
        (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
          (c := c.chart) (d := d) vcommon) (y := γ wSmall.1) |>.1 hwSource with
      ⟨hw_d, hwW⟩
    -- Normalize the `d`-coordinate proof so the fixed reduced-interval spelling can be reused.
    exact (sphereNeighborhoodChart_coord_eq_of_sourcePoint d).symm ▸ hwW
  · intro hwW
    -- Convert the fixed canonical-window membership directly back into source membership of the
    -- continuation at `vSmall`.
    exact
      (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
        (c := c.chart) (d := d) vcommon) (y := γ wSmall.1) |>.2 <| by
          refine ⟨(hsmall_uIcc (w := wSmall)).2, ?_⟩
          simpa [W] using hwW

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once one reduced-interval time already
lies in the fixed canonical target window attached to the hand-off chart `c` at `vSmall`, that
same fixed window contains a whole neighborhood of the time. This packages the second-window
comparison so later closedness arguments can treat the fixed window as locally stable on the
smaller interval. -/
lemma sphereNeighborhoodChart_fixedCanonicalWindow_mem_nhds
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (wSmall vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source)
    (hwW :
      let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
        ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
      let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
        (c := c.chart) (d := d) vcommon
      let Φ := hf.localInverse
      let W : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
          (⟨Φ.target, Φ.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
      d.equiv ⟨γ wSmall.1, (hsmall_uIcc (w := wSmall)).2⟩ ∈ W) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∃ U ∈ nhds wSmall.1,
      ∀ {zSmall : Set.uIcc a' b'}, zSmall.1 ∈ U →
        d.equiv ⟨γ zSmall.1, (hsmall_uIcc (w := zSmall)).2⟩ ∈ W := by
  intro vcommon hf Φ W
  let c' : SeededSphereNeighborhoodChart c₀ :=
    seededSphereNeighborhoodChart_of_continuation c
      (sphereNeighborhoodChart_continueAtTargetPoint
        (c := c.chart) (d := d) vcommon)
  have hwSource : γ wSmall.1 ∈ c'.chart.source := by
    -- Rewrite the fixed-window condition as source membership in the first continuation.
    have hiff :
        γ wSmall.1 ∈ c'.chart.source ↔
          d.equiv ⟨γ wSmall.1, (hsmall_uIcc (w := wSmall)).2⟩ ∈ W := by
      simpa [c', vcommon, hf, Φ, W] using
        sphereNeighborhoodChart_fixedCanonicalWindow_mem_iff
          (c₀ := c₀) (γ := γ) (d := d) (e := e)
          hsmall_uIcc wSmall vSmall c hcsub hvSource
    exact hiff.mpr hwW
  have hc'sub : (c'.chart.source : Set X) ⊆ d.source := by
    -- The first continuation still stays inside the fixed raw chart `d`.
    simpa [c', vcommon] using
      (sphereNeighborhoodChart_reparametrizeTarget_source_subset
        (c := c.chart) (d := d) vcommon)
  rcases
      sphereNeighborhoodChart_centerCoord_memCanonicalTargetWindow_on_smallInterval
        (c₀ := c₀) (γ := γ) (d := d) (e := e)
        hsmall_uIcc wSmall c' hc'sub hwSource with
    ⟨U, hU_nhds, hU⟩
  have hsubsetW :
      let ycommon : sphereNeighborhoodChartCommonSource c'.chart d :=
        ⟨γ wSmall.1, hwSource, hc'sub hwSource⟩
      let hf₂ := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
        (c := c'.chart) (d := d) ycommon
      let Φ₂ := hf₂.localInverse
      let W₂ : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c'.chart d)
          (⟨Φ₂.target, Φ₂.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c'.chart d))
      (W₂ : Set d.target) ⊆ W := by
    -- A second continuation through the same raw chart only shrinks the visible target window.
    simpa [c', vcommon, hf, Φ, W] using
      (sphereNeighborhoodChart_secondCanonicalWindow_subset
        (c := c.chart) (d := d) vcommon) hwSource
  refine ⟨U, hU_nhds, ?_⟩
  intro zSmall hzU
  -- The neighborhood produced at `wSmall` lands in the smaller second window, which is already
  -- contained in the original fixed window `W`.
  exact hsubsetW (hU hzU)

/-- Helper for Theorem VI.4-extra-13: the target of an explicit continuation chart obtained by
reparameterizing `d` through the local inverse of the transition from `c` is an ambient-open
subset of the original target of `c`. This gives the reduced-interval file its own stable owner
for forgetting the continued-target subtype back to the original chart target. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_target_subset_original
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    (c'.target : Set RiemannSphere) ⊆ c.target := by
  intro hf Φ c' z hz
  have hz' :
      ∃ hz_c : z ∈ c.target,
        (⟨z, hz_c⟩ : c.target) ∈
          (⟨Φ.source, Φ.open_source⟩ : TopologicalSpace.Opens c.target) := by
    -- Unfold the continued target once so only the ambient-open transport back to `c.target`
    -- remains visible.
    simpa [c', sphereNeighborhoodChart_reparametrizeTarget, mem_ambientOpenOfOpenSubset] using hz
  exact hz'.1

/-- Helper for Theorem VI.4-extra-13: on the whole visible target of the explicit continuation
chart obtained from `c` through `d`, the old inverse branch of `c` and the new inverse branch of
the continued chart agree pointwise. This exposes the branch-level continuation API needed before
the remaining target-image closed-half can compare cluster points through one fixed raw chart. -/
lemma sphereNeighborhoodChart_reparametrizeTarget_branch_eq_original
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c d : SphereNeighborhoodChart X} (x : sphereNeighborhoodChartCommonSource c d) :
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt (c := c) (d := d) x
    let Φ := hf.localInverse
    let c' := sphereNeighborhoodChart_reparametrizeTarget c d Φ
    ∀ z : c'.target,
      c.branch
        ⟨(z : RiemannSphere),
          sphereNeighborhoodChart_reparametrizeTarget_target_subset_original
            (c := c) (d := d) x z.2⟩ =
        c'.branch z := by
  intro hf Φ c' z
  let y : c'.source := ⟨c'.branch z, c'.branch_mem_source z⟩
  let hyc : c'.branch z ∈ c.source :=
    sphereNeighborhoodChart_reparametrizeTarget_source_subset_left
      (c := c) (d := d) x y.2
  let ycommon : sphereNeighborhoodChartCommonSource c c' := ⟨c'.branch z, hyc, y.2⟩
  have hcoord :
      c.coord ⟨c'.branch z, hyc⟩ = c'.coord y := by
    -- Compare the old and new coordinates at the point obtained by applying the continued
    -- inverse branch. This is the source-side equality already owned by the continuation API.
    simpa [sphereNeighborhoodChartLeftCoord, sphereNeighborhoodChartRightCoord, y, ycommon] using
      congrFun (sphereNeighborhoodChart_reparametrizeTarget_coord_eq (c := c) (d := d) x) ycommon
  have hcoord' :
      c.coord ⟨c'.branch z, hyc⟩ = z := by
    -- Evaluate the continued chart coordinate at its own inverse branch to recover the target
    -- point `z`.
    calc
      c.coord ⟨c'.branch z, hyc⟩ = c'.coord y := hcoord
      _ = z := by
        simpa [y] using c'.coord_branch z
  have htarget :
      c.equiv ⟨c'.branch z, hyc⟩ =
        ⟨(z : RiemannSphere),
          sphereNeighborhoodChart_reparametrizeTarget_target_subset_original
            (c := c) (d := d) x z.2⟩ := by
    -- Forget the subtype wrappers and compare the underlying sphere coordinates.
    apply Subtype.ext
    simpa [SphereNeighborhoodChart.coord] using hcoord'
  -- Move the recovered coordinate identity back through the original inverse branch.
  calc
    c.branch
        ⟨(z : RiemannSphere),
          sphereNeighborhoodChart_reparametrizeTarget_target_subset_original
            (c := c) (d := d) x z.2⟩ =
        c.branch (c.equiv ⟨c'.branch z, hyc⟩) := by
          rw [← htarget]
    _ = c'.branch z := by
      simpa [SphereNeighborhoodChart.branch] using c.branch_coord ⟨c'.branch z, hyc⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once the fixed center time
`uSmall.1` is known to lie in the one-sided target-window neighborhood returned at the nearby
hand-off time `vSmall.1`, the remaining reduced-interval source-membership statement is just the
existing target/source equivalence specialized at `uSmall`. -/
lemma sphereNeighborhoodChart_reducedIntervalCenterSource_of_memWindowNeighborhood
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (uSmall vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source)
    {U : Set unitInterval}
    (hW :
      let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
        ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
      let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
        (c := c.chart) (d := d) vcommon
      let Φ := hf.localInverse
      let W : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
          (⟨Φ.target, Φ.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
      ∀ {w : Set.uIcc a' b'}, w.1 ∈ U →
        d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩ ∈ W)
    (huU : uSmall.1 ∈ U)
    (hiff :
      let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
        ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
      let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
        (c := c.chart) (d := d) vcommon
      let Φ := hf.localInverse
      let c' : SeededSphereNeighborhoodChart c₀ :=
        seededSphereNeighborhoodChart_of_continuation c
          (sphereNeighborhoodChart_continueAtTargetPoint
            (c := c.chart) (d := d) vcommon)
      let W : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
          (⟨Φ.target, Φ.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
      γ uSmall.1 ∈ c'.chart.source ↔
        d.equiv ⟨γ uSmall.1, (hsmall_uIcc (w := uSmall)).2⟩ ∈ W) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let c' : SeededSphereNeighborhoodChart c₀ :=
      seededSphereNeighborhoodChart_of_continuation c
        (sphereNeighborhoodChart_continueAtTargetPoint
          (c := c.chart) (d := d) vcommon)
    γ uSmall.1 ∈ c'.chart.source := by
  intro vcommon hf Φ c'
  -- The one-sided neighborhood already gives the raw `d`-target window condition at `uSmall`.
  have huW :
      let W : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
          (⟨Φ.target, Φ.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
      d.equiv ⟨γ uSmall.1, (hsmall_uIcc (w := uSmall)).2⟩ ∈ W := by
    simpa using hW (w := uSmall) huU
  -- The reduced-interval membership equivalence closes the goal once the target-window side is
  -- available at the fixed center time.
  exact hiff.mpr huW

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the canonical target-window condition
for the fixed continuation at `vSmall` already forces the center point to lie in the original
subordinate chart `c`. This exposes the extra source-membership content hidden inside the target
window conclusion. -/
lemma sphereNeighborhoodChart_centerMemSource_of_memCanonicalWindow
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (uSmall vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source) :
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    d.equiv ⟨γ uSmall.1, (hsmall_uIcc (w := uSmall)).2⟩ ∈ W →
      γ uSmall.1 ∈ c.chart.source := by
  intro vcommon hf Φ W huW
  let c' : SeededSphereNeighborhoodChart c₀ :=
    seededSphereNeighborhoodChart_of_continuation c
      (sphereNeighborhoodChart_continueAtTargetPoint
        (c := c.chart) (d := d) vcommon)
  have hiff :
      γ uSmall.1 ∈ c'.chart.source ↔
        d.equiv ⟨γ uSmall.1, (hsmall_uIcc (w := uSmall)).2⟩ ∈ W := by
    -- Convert the target-window membership back into source membership of the explicit continued
    -- chart built from `c` at the hand-off point `vSmall`.
    simpa [c', vcommon, hf, Φ, W] using
      sphereNeighborhoodChart_fixedCanonicalWindow_mem_iff
        (c₀ := c₀) (γ := γ) (d := d) (e := e)
        hsmall_uIcc uSmall vSmall c hcsub hvSource
  have huSource' : γ uSmall.1 ∈ c'.chart.source := by
    -- The fixed-window equivalence records the source-side meaning of the canonical target window.
    exact hiff.mpr huW
  have hc'sub_c : (c'.chart.source : Set X) ⊆ c.chart.source := by
    -- Reparameterizing `d` through the local inverse at `vSmall` never leaves the original chart
    -- `c.chart` on the source side.
    simpa [c', vcommon, hf, Φ] using
      sphereNeighborhoodChart_reparametrizeTarget_source_subset_left
        (c := c.chart) (d := d) vcommon
  -- The center point first enters the fixed continued chart and then shrinks back to `c.chart`.
  exact hc'sub_c huSource'

/-- Helper for Theorem VI.4-extra-13: a closure point of the fixed canonical-window slice already
lies in the original source chart `c.chart`. This separates the easy source-membership transport
from the remaining harder step of proving actual membership in the canonical target window `W`. -/
lemma sphereNeighborhoodChart_memSource_of_fixedCanonicalWindowClosure
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦
      d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∀ u0 : Set.uIcc a' b',
      u0 ∈ closure {w : Set.uIcc a' b' | coordK w ∈ W} →
        γ u0.1 ∈ c.chart.source := by
  -- TODO: the reduced-interval closed-half still needs the fixed canonical-window closure bridge.
  -- The intended route is to lift a nearby point already in the canonical window, transport the
  -- window membership along the reduced interval, and then convert that back to source membership
  -- through `sphereNeighborhoodChart_centerMemSource_of_memCanonicalWindow`.
  sorry

/-- Helper for Theorem VI.4-extra-13: after lifting a cluster point in the target-image slice back
to the reduced interval, the remaining closed-half step is to show the lifted interval point still
lies in the fixed canonical target window. This isolates the only analytic input left in the
reduced-interval argument after the compact/closed-map transport is settled. -/
lemma sphereNeighborhoodChart_fixedCanonicalWindowPreimage_mem_of_mem_closure
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦
      d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∀ u0 : Set.uIcc a' b', u0 ∈ closure {w : Set.uIcc a' b' | coordK w ∈ W} → coordK u0 ∈ W := by
  intro coordK vcommon hf Φ W u0 hu0Closure
  have hu0Source : γ u0.1 ∈ c.chart.source := by
    -- First isolate the easy part of the closure transport: the center time already lands back
    -- in the original source chart `c.chart`.
    exact
      sphereNeighborhoodChart_memSource_of_fixedCanonicalWindowClosure
        (c₀ := c₀) (γ := γ) (d := d) (e := e)
        hsmall_uIcc vSmall c hcsub hvSource u0 hu0Closure
  -- TODO: finish the interval-side closure bridge. The remaining route is to choose a reduced
  -- interval point already in `{w | coordK w ∈ W}` near `u0`, use `hu0Source` together with
  -- source-side continuation propagation to show the explicit continuation through `vSmall`
  -- still covers `γ u0.1`, and only then transport that fixed-window membership back with
  -- `sphereNeighborhoodChart_fixedCanonicalWindow_mem_nhds`,
  -- `sphereNeighborhoodChart_reducedIntervalCenterSource_of_memWindowNeighborhood`, and
  -- `sphereNeighborhoodChart_centerMemSource_of_memCanonicalWindow`, and then normalize the final
  -- target/source comparison with
  -- `sphereNeighborhoodChart_fixedCanonicalWindow_mem_iff` together with
  -- `sphereNeighborhoodChart_reparametrizeTarget_branch_eq_original`.
  have _hu0Source_d : γ u0.1 ∈ d.source := (hsmall_uIcc (w := u0)).2
  let c' : SeededSphereNeighborhoodChart c₀ :=
    seededSphereNeighborhoodChart_of_continuation c
      (sphereNeighborhoodChart_continueAtTargetPoint
        (c := c.chart) (d := d) vcommon)
  have _hu0InTransitionDomain :
      coordK u0 ∈ sphereNeighborhoodChartTargetTransitionDomain c.chart d := by
    -- Once `γ u0.1` is known to stay in both source charts, its fixed raw `d`-coordinate lies in
    -- the transition domain from `c.chart` to `d`.
    change d.branch (coordK u0) ∈ c.chart.source
    simpa [coordK, SphereNeighborhoodChart.branch_coord] using hu0Source
  sorry

/-- Helper for Theorem VI.4-extra-13: the target-image closure point in the fixed canonical-window
slice lifts to a reduced-interval closure point of the interval-side slice `{w | coordK w ∈ W}`.
This isolates all range-subtype bookkeeping before the remaining interval-side analytic bridge. -/
lemma sphereNeighborhoodChart_fixedCanonicalWindow_cluster_liftsToIntervalClosure
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦
      d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩
    let Z : Set d.target := Set.range coordK
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∀ z0 : Z,
      z0 ∈ closure ((Subtype.val : Z → d.target) ⁻¹' (W : Set d.target)) →
        ∃ u0 : Set.uIcc a' b',
          u0 ∈ closure {w : Set.uIcc a' b' | coordK w ∈ W} ∧
            (⟨coordK u0, Set.mem_range_self u0⟩ : Z) = z0 := by
  intro coordK Z vcommon hf Φ W z0 hz0
  letI : CompactSpace (Set.uIcc a' b') :=
    (isCompact_iff_compactSpace.mp (isCompact_uIcc : IsCompact (Set.uIcc a' b')))
  have hcoordK_cont : Continuous coordK := by
    -- Reuse the fixed-coordinate continuity owner before transporting closure through the range
    -- subtype.
    simpa [coordK] using
      sphereNeighborhoodChart_smallIntervalCoord_continuous
        (γ := γ) (d := d) (hsmall_uIcc := fun {w} ↦ (hsmall_uIcc (w := w)).2)
  -- The closed-map transport is now a direct application of the generic range-subtype bridge.
  simpa [coordK, Z, W] using
    subtypeRange_cluster_liftsToClosure (f := coordK) hcoordK_cont (W := (W : Set d.target)) hz0

/-- Helper for Theorem VI.4-extra-13: the remaining closed-half step for the fixed canonical
window should be stated directly on the target-image subtype `Z`. This isolates the missing bridge
from cluster points of the restricted slice on `Z` back to fixed-window membership at the cluster
point itself. -/
lemma sphereNeighborhoodChart_fixedCanonicalWindow_cluster_mem_of_mem_closure
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦
      d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩
    let Z : Set d.target := Set.range coordK
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    ∀ z0 : Z,
      z0 ∈ closure ((Subtype.val : Z → d.target) ⁻¹' (W : Set d.target)) →
        z0.1 ∈ W := by
  intro coordK Z vcommon hf Φ W z0 hz0
  obtain ⟨u0, hu0Closure, hu0Eq⟩ :=
    sphereNeighborhoodChart_fixedCanonicalWindow_cluster_liftsToIntervalClosure
      (c₀ := c₀) (γ := γ) (d := d) (e := e)
      hsmall_uIcc vSmall c hcsub hvSource z0 hz0
  have hu0W : coordK u0 ∈ W := by
    -- Route correction: the range-subtype closure transport is complete, so only the interval-side
    -- fixed-window closure bridge remains.
    exact
      sphereNeighborhoodChart_fixedCanonicalWindowPreimage_mem_of_mem_closure
        (c₀ := c₀) (γ := γ) (d := d) (e := e)
        hsmall_uIcc vSmall c hcsub hvSource u0 hu0Closure
  have hz0Eq : coordK u0 = z0.1 := congrArg Subtype.val hu0Eq
  -- Re-express the lifted interval point as the original cluster point in the target image.
  simpa [hz0Eq] using hu0W

/-- Helper for Theorem VI.4-extra-13: package the fixed canonical-window closed-half owner in the
exact `IsClosed` form consumed by the smaller-interval clopen argument. -/
lemma sphereNeighborhoodChart_fixedCanonicalWindow_isClosedInTargetImage
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x)
    (d e : SphereNeighborhoodChart X)
    {a' b' : unitInterval}
    (hsmall_uIcc : ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source)
    (vSmall : Set.uIcc a' b')
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hvSource : γ vSmall.1 ∈ c.chart.source) :
    let coordK : Set.uIcc a' b' → d.target := fun w ↦
      d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩
    let Z : Set d.target := Set.range coordK
    let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
      ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
    let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
      (c := c.chart) (d := d) vcommon
    let Φ := hf.localInverse
    let W : TopologicalSpace.Opens d.target :=
      ambientOpenOfOpenSubset
        (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
        (⟨Φ.target, Φ.open_target⟩ :
          TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
    IsClosed ((Subtype.val : Z → d.target) ⁻¹' (W : Set d.target)) := by
  intro coordK Z vcommon hf Φ W
  rw [← closure_subset_iff_isClosed]
  intro z0 hz0
  -- Reduce closedness to the dedicated cluster-point owner on the target image.
  exact
    sphereNeighborhoodChart_fixedCanonicalWindow_cluster_mem_of_mem_closure
      (c₀ := c₀) (γ := γ) (d := d) (e := e)
      hsmall_uIcc vSmall c hcsub hvSource z0 hz0

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once one time `s` is covered by a
seeded chart subordinate to a fixed raw chart `d`, every time in the same connected component of
`γ ⁻¹' d.source` should inherit such a subordinate seeded chart. This is the fixed-chart coverage
adapter consumed by the pathwise closedness proof. -/
lemma seededSphereNeighborhoodChart_centerNeighborhood_absorbsReachable
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval}
    (hs :
      ∃ c : SeededSphereNeighborhoodChart c₀,
        (c.chart.source : Set X) ⊆ d.source ∧ γ s ∈ c.chart.source)
    (hsegment : Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X))
    (u : Set.uIcc s t) :
    ∃ U ∈ nhds u,
      ∀ ⦃v : Set.uIcc s t⦄, v ∈ U →
        Relation.ReflTransGen
          (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s v.1 →
        Relation.ReflTransGen
          (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s u.1 := by
  rcases seededSphereNeighborhoodChart_centerChartInterval
      (γ := γ) (d := d) hsegment u with
    ⟨_, _, a, b, huIcc, hIcc_nhds, hIcc_subset⟩
  let uReduced : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b} := ⟨u, huIcc⟩
  rcases sphereNeighborhoodChart_reducedCenterChartInterval
      (γ := γ) (d := d)
      (hIcc_subset := fun {_} hw ↦ (hIcc_subset hw).2) uReduced with
    ⟨eSmall, a', b', _, huSmallIcc, hsmall_nhds, hsmall⟩
  have hsmall_uIcc :
      ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ eSmall.source ∧ γ w.1 ∈ d.source := by
    -- Normalize the reduced interval back to the plain `Set.uIcc a' b'` spelling used by the
    -- fixed canonical-window helpers.
    exact
      sphereNeighborhoodChart_reducedCenterChartInterval_mem_sources_uIcc
        (γ := γ) (d := d) (e := eSmall) uReduced huSmallIcc hsmall
  let U : Set (Set.uIcc s t) := {v | v.1 ∈ Set.Icc a' b'}
  refine ⟨U, ?_, ?_⟩
  · -- The reduced center interval is already a neighborhood of `u` inside the segment subtype.
    rw [nhds_subtype_eq_comap] at hsmall_nhds
    let Ua : Set (Set.uIcc s t) := {v | v.1 ∈ Set.Icc a b}
    have hUa_nhds : Ua ∈ nhds u := by
      simpa [Ua] using
        continuous_subtype_val.continuousAt.preimage_mem_nhds hIcc_nhds
    rcases hsmall_nhds with ⟨V, hV_nhds, hV_subset⟩
    refine Filter.mem_of_superset (inter_mem hV_nhds hUa_nhds) ?_
    intro v hv
    rcases hv with ⟨hvV, hvUa⟩
    have hvReduced : (⟨v, hvUa⟩ : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}) ∈
        Subtype.val ⁻¹' V := hvV
    have hvSmall : (⟨v, hvUa⟩ : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}) ∈
        {w : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b} | w.1.1 ∈ Set.Icc a' b'} :=
      hV_subset hvReduced
    exact hvSmall
  · intro v hvU hvR
    let uSmall : Set.uIcc a' b' := ⟨u.1, Set.Icc_subset_uIcc huSmallIcc⟩
    let vSmall : Set.uIcc a' b' := ⟨v.1, Set.Icc_subset_uIcc hvU⟩
    rcases seededSphereNeighborhoodChart_reflTransGen_hasSubordinateChart
        (γ := γ) (d := d) hvR hs with ⟨c, hcsub, hvSource⟩
    have huWindow :
        let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
          ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
        let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
          (c := c.chart) (d := d) vcommon
        let Φ := hf.localInverse
        let W : TopologicalSpace.Opens d.target :=
          ambientOpenOfOpenSubset
            (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
            (⟨Φ.target, Φ.open_target⟩ :
              TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
        d.equiv ⟨γ uSmall.1, (hsmall_uIcc (w := uSmall)).2⟩ ∈ W := by
      have hclosed :
          let coordK : Set.uIcc a' b' → d.target := fun w ↦
            d.equiv ⟨γ w.1, (hsmall_uIcc (w := w)).2⟩
          let Z : Set d.target := Set.range coordK
          let vcommon : sphereNeighborhoodChartCommonSource c.chart d :=
            ⟨γ vSmall.1, hvSource, hcsub hvSource⟩
          let hf := sphereNeighborhoodChartTargetTransition_isLocalDiffeomorphAt
            (c := c.chart) (d := d) vcommon
          let Φ := hf.localInverse
      let W : TopologicalSpace.Opens d.target :=
        ambientOpenOfOpenSubset
          (sphereNeighborhoodChartTargetTransitionDomain c.chart d)
          (⟨Φ.target, Φ.open_target⟩ :
            TopologicalSpace.Opens (sphereNeighborhoodChartTargetTransitionDomain c.chart d))
      IsClosed ((Subtype.val : Z → d.target) ⁻¹' (W : Set d.target)) := by
        -- Delegate the fixed target-image closed-half packaging to the dedicated helper above so
        -- the main reachable-center argument only depends on the cleaned `IsClosed` interface.
        simpa using
          sphereNeighborhoodChart_fixedCanonicalWindow_isClosedInTargetImage
            (c₀ := c₀) (γ := γ) (d := d) (e := eSmall)
            hsmall_uIcc vSmall c hcsub hvSource
      -- Once the closed-half owner is supplied, the clopen argument forces every reduced-interval
      -- coordinate, in particular the center coordinate, into the same canonical window.
      exact
        sphereNeighborhoodChart_centerIntervalCanonicalWindow_eq_univ_of_isClosedInTargetImage
          (c₀ := c₀) (γ := γ) (d := d)
          (hsmall_uIcc := fun {w} ↦ (hsmall_uIcc (w := w)).2)
          hcsub hvSource hclosed uSmall
    have huSource :
        γ u.1 ∈ c.chart.source := by
      -- Convert the fixed target-window membership at the center time back into source
      -- membership of the original reachable chart `c`.
      simpa [uSmall] using
        sphereNeighborhoodChart_centerMemSource_of_memCanonicalWindow
          (c₀ := c₀) (γ := γ) (d := d) (e := eSmall)
          hsmall_uIcc uSmall vSmall c hcsub hvSource huWindow
    -- One final edge from the reachable time `v` to the center time `u` closes the absorption
    -- step once the center lies in the same subordinate chart.
    exact Relation.ReflTransGen.tail hvR ⟨c, hcsub, hvSource, huSource⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once one time `s` is covered by a
seeded chart subordinate to a fixed raw chart `d`, every time in the same connected component of
`γ ⁻¹' d.source` should inherit such a subordinate seeded chart. This is the fixed-chart coverage
adapter consumed by the pathwise closedness proof. -/
lemma seededSphereNeighborhoodChart_fixedRawChartComponentCoverage
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval}
    (hs :
      ∃ c : SeededSphereNeighborhoodChart c₀,
        (c.chart.source : Set X) ⊆ d.source ∧ γ s ∈ c.chart.source)
    (ht : t ∈ connectedComponentIn (γ ⁻¹' (d.source : Set X)) s) :
    ∃ c : SeededSphereNeighborhoodChart c₀,
      (c.chart.source : Set X) ⊆ d.source ∧ γ t ∈ c.chart.source := by
  let K : Set unitInterval := Set.uIcc s t
  let R : Set K := {u |
    Relation.ReflTransGen
      (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s u.1}
  have hsegment : K ⊆ γ ⁻¹' (d.source : Set X) := by
    -- The whole unordered segment from `s` to `t` stays inside the chosen raw chart.
    simpa [K] using
      seededSphereNeighborhoodChart_uIcc_subset_rawChartPreimage
        (γ := γ) (d := d) ht
  have hRopen : IsOpen R := by
    -- The local reachability interval lemma already gives the open half of the clopen argument on
    -- the segment subtype.
    simpa [R, K] using
      seededSphereNeighborhoodChart_reachableSet_isOpen
        (c₀ := c₀) (γ := γ) (d := d) hs hsegment
  have hsR : (⟨s, Set.left_mem_uIcc⟩ : K) ∈ R := by
    -- The seed time is reachable from itself before any continuation step is taken.
    simpa [R] using
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen
          (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s s)
  have hRclosed : IsClosed R := by
    rw [← closure_subset_iff_isClosed]
    intro u huClosure
    rcases seededSphereNeighborhoodChart_centerNeighborhood_absorbsReachable
        (c₀ := c₀) (γ := γ) (d := d) hs hsegment u with
      ⟨U, hU_nhds, hU_absorb⟩
    rcases (mem_closure_iff_nhds.1 huClosure) U hU_nhds with ⟨v, hvU, hvR⟩
    exact hU_absorb hvU hvR
  haveI : PreconnectedSpace K := by
    -- The unordered interval `Set.uIcc s t` is preconnected, so a nonempty clopen subset of it
    -- must be all of `K`.
    refine Subtype.preconnectedSpace ?_
    simpa [K] using (isPreconnected_uIcc : IsPreconnected (Set.uIcc s t))
  have hRuniv : R = Set.univ := by
    -- The reachable-time subset is now both open and closed and still contains the seed time.
    exact IsClopen.eq_univ ⟨hRclosed, hRopen⟩ ⟨⟨s, Set.left_mem_uIcc⟩, hsR⟩
  have htR : (⟨t, Set.right_mem_uIcc⟩ : K) ∈ R := by
    simpa [hRuniv] using (Set.mem_univ (⟨t, Set.right_mem_uIcc⟩ : K))
  have htReach :
      Relation.ReflTransGen
        (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s t := by
    simpa [R] using htR
  -- The fixed-chart reachability owner converts the terminal reachability chain back into one
  -- subordinate seeded chart covering the target time `t`.
  exact seededSphereNeighborhoodChart_reflTransGen_hasSubordinateChart
    (γ := γ) (d := d) htReach hs
end
