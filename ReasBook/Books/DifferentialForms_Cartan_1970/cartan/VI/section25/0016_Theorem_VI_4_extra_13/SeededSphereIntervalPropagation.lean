import DifferentialForms_Cartan_1970.VI.section25.«0016_Theorem_VI_4_extra_13».SphereNeighborhoodContinuation

universe u

open scoped Complex.UnitDisc Manifold
open Filter

section

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on `unitInterval`, the connected
component of the raw-chart preimage is order-connected, so every interval between the seed time
and another time in that component stays inside the same raw-chart preimage. -/
lemma seededSphereNeighborhoodChart_uIcc_subset_rawChartPreimage
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) {s t : unitInterval}
    (ht : t ∈ connectedComponentIn (γ ⁻¹' (d.source : Set X)) s) :
    Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X) := by
  let N : Set unitInterval := γ ⁻¹' (d.source : Set X)
  have hNnonempty : (connectedComponentIn N s).Nonempty := ⟨t, ht⟩
  have hsN : s ∈ N := (connectedComponentIn_nonempty_iff.mp hNnonempty)
  have hsC : s ∈ connectedComponentIn N s := mem_connectedComponentIn hsN
  have hOrd :
      Set.OrdConnected (connectedComponentIn N s) :=
    (isPreconnected_connectedComponentIn (x := s) (F := N)).ordConnected
  exact
    (hOrd.uIcc_subset hsC ht).trans
      (connectedComponentIn_subset N s)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once one time `s` is covered by a
seeded chart subordinate to a fixed raw chart `d`, the whole connected component of
`γ ⁻¹' d.source` containing `s` should be covered by subordinate seeded charts as well. This is
the remaining fixed-chart propagation owner needed to close the pathwise continuation theorem. -/
lemma seededSphereNeighborhoodChart_localSubordinateChartInterval
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval}
    (hs :
      ∃ c : SeededSphereNeighborhoodChart c₀,
        (c.chart.source : Set X) ⊆ d.source ∧ γ s ∈ c.chart.source)
    (hsegment : Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X))
    {u : Set.uIcc s t}
    (hu :
      Relation.ReflTransGen
        (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s u.1) :
    ∃ c' : SeededSphereNeighborhoodChart c₀, ∃ a b : Set.uIcc s t,
      (c'.chart.source : Set X) ⊆ d.source ∧
        u ∈ Set.Icc a b ∧
        Set.Icc a b ∈ nhds u ∧
        ∀ v ∈ Set.Icc a b, γ v.1 ∈ c'.chart.source := by
  rcases seededSphereNeighborhoodChart_reflTransGen_hasSubordinateChart
      (γ := γ) (d := d) hu hs with ⟨c, _hsubset, hcu⟩
  have hud : γ u.1 ∈ d.source := hsegment u.2
  rcases seededSphereNeighborhoodChart_continueNearPathTime
      (γ := γ) (t := u.1) c hcu d hud with
    ⟨c', hsubset', U, hU_nhds, hU⟩
  have hKU_nhds : ((↑) : Set.uIcc s t → unitInterval) ⁻¹' U ∈ nhds u := by
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hU_nhds
  obtain ⟨a, b, huab, hab_nhds, hab_subset⟩ := exists_Icc_mem_subset_of_mem_nhds hKU_nhds
  refine ⟨c', a, b, hsubset', huab, hab_nhds, ?_⟩
  intro v hv
  exact hU v.1 (hab_subset hv)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once one time `s` is covered by a
seeded chart subordinate to a fixed raw chart `d`, the whole connected component of
`γ ⁻¹' d.source` containing `s` should be covered by subordinate seeded charts as well. This is
the remaining fixed-chart propagation owner needed to close the pathwise continuation theorem. -/
lemma seededSphereNeighborhoodChart_localReachabilityInterval
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval}
    (hs :
      ∃ c : SeededSphereNeighborhoodChart c₀,
        (c.chart.source : Set X) ⊆ d.source ∧ γ s ∈ c.chart.source)
    (hsegment : Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X))
    {u : Set.uIcc s t}
    (hu :
      Relation.ReflTransGen
        (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s u.1) :
    ∃ a b : Set.uIcc s t,
      u ∈ Set.Icc a b ∧
        Set.Icc a b ∈ nhds u ∧
        ∀ v ∈ Set.Icc a b,
          Relation.ReflTransGen
            (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s v.1 := by
  rcases seededSphereNeighborhoodChart_localSubordinateChartInterval
      (c₀ := c₀) (γ := γ) (d := d) hs hsegment hu with
    ⟨c', a, b, hsubset', huab, hab_nhds, hab⟩
  refine ⟨a, b, huab, hab_nhds, ?_⟩
  intro v hv
  have hu' : γ u.1 ∈ c'.chart.source := hab u huab
  have hv' : γ v.1 ∈ c'.chart.source := hab v hv
  exact Relation.ReflTransGen.tail hu ⟨c', hsubset', hu', hv'⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on a fixed segment `Set.uIcc s t`
inside `γ ⁻¹' d.source`, the times reachable from `s` by the subordinate-chart step relation form
an open subset of the segment subtype. This packages the easy half of the later clopen argument
before the remaining closed-half transport is addressed. -/
lemma seededSphereNeighborhoodChart_reachableSet_isOpen
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval}
    (hs :
      ∃ c : SeededSphereNeighborhoodChart c₀,
        (c.chart.source : Set X) ⊆ d.source ∧ γ s ∈ c.chart.source)
    (hsegment : Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X)) :
    IsOpen {u : Set.uIcc s t |
      Relation.ReflTransGen
        (seededSphereNeighborhoodChartStep (c₀ := c₀) γ d) s u.1} := by
  refine isOpen_iff_mem_nhds.2 ?_
  intro u hu
  rcases seededSphereNeighborhoodChart_localReachabilityInterval
      (c₀ := c₀) (γ := γ) (d := d) hs hsegment hu with
    ⟨a, b, huab, hab_nhds, hab⟩
  -- The interval returned by the local reachability lemma is a neighborhood of `u` contained in
  -- the reachable-time set.
  refine Filter.mem_of_superset hab_nhds ?_
  intro v hv
  exact hab v hv

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the fixed raw-chart coordinate image
of the path segment `Set.uIcc s t` is preconnected, and both endpoint coordinates lie in that
image. This packages the connected target-side object used by the remaining clopen argument. -/
lemma seededSphereNeighborhoodChart_pathTargetImage_preconnected
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) {s t : unitInterval}
    (hsegment : Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X)) :
    let K : Set unitInterval := Set.uIcc s t
    let coordK : K → d.target := fun u ↦ d.equiv ⟨γ u.1, hsegment u.2⟩
    let Z : Set d.target := Set.range coordK
    IsPreconnected Z ∧
      coordK ⟨s, Set.left_mem_uIcc⟩ ∈ Z ∧
      coordK ⟨t, Set.right_mem_uIcc⟩ ∈ Z := by
  intro K coordK Z
  have hcoord_cont : Continuous coordK := by
    refine d.equiv.toHomeomorph.continuous_toFun.comp ?_
    exact Continuous.subtype_mk
      (γ.continuous.comp continuous_subtype_val)
      (fun u ↦ hsegment u.2)
  haveI : PreconnectedSpace K := by
    refine Subtype.preconnectedSpace ?_
    simpa [K] using (isPreconnected_uIcc : IsPreconnected (Set.uIcc s t))
  refine ⟨?_, ?_, ?_⟩
  · simpa [Z] using isPreconnected_range (f := coordK) hcoord_cont
  · exact ⟨⟨s, Set.left_mem_uIcc⟩, rfl⟩
  · exact ⟨⟨t, Set.right_mem_uIcc⟩, rfl⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: if a seeded chart subordinate to a
fixed raw chart `d` covers one time `u`, then the canonical target window produced by continuing
that chart into `d` at `u` yields a genuine one-step reachability witness for any other time `v`
whose fixed `d`-coordinate lies in that same window. -/
lemma seededSphereNeighborhoodChart_step_of_memCanonicalTargetWindow
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval}
    (hsegment : Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X))
    {u v : Set.uIcc s t}
    (c : SeededSphereNeighborhoodChart c₀)
    (hcsub : (c.chart.source : Set X) ⊆ d.source)
    (hcu : γ u.1 ∈ c.chart.source) :
    let coordK : Set.uIcc s t → d.target := fun w ↦ d.equiv ⟨γ w.1, hsegment w.2⟩
    let xcommon : sphereNeighborhoodChartCommonSource c.chart d := ⟨γ u.1, hcu, hcsub hcu⟩
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
    coordK v ∈ W →
      seededSphereNeighborhoodChartStep (c₀ := c₀) γ d u.1 v.1 := by
  intro coordK xcommon hf Φ c' W hvW
  have hsubset' :
      (c'.chart.source : Set X) ⊆ d.source := by
    simpa [c', xcommon] using
      (sphereNeighborhoodChart_reparametrizeTarget_source_subset
        (c := c.chart) (d := d) xcommon)
  have hcenter :
      γ u.1 ∈ c'.chart.source := by
    simpa [c', xcommon] using
      (sphereNeighborhoodChart_reparametrizeTarget_point_mem_source
        (c := c.chart) (d := d) xcommon)
  have hvSource :
      γ v.1 ∈ c'.chart.source := by
    exact
      (sphereNeighborhoodChart_reparametrizeTarget_mem_source_iff
        (c := c.chart) (d := d) xcommon) (y := γ v.1) |>.2 <| by
          refine ⟨hsegment v.2, ?_⟩
          change d.equiv ⟨γ v.1, hsegment v.2⟩ ∈ W
          simpa [coordK] using hvW
  exact ⟨c', hsubset', hcenter, hvSource⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: around a fixed center time `u`,
choose one ambient interval in `unitInterval` on which both the fixed raw chart `d` and one raw
chart centered at `γ u.1` are defined. This packages the interval-normalization side conditions
needed before comparing nearby continuations. -/
lemma seededSphereNeighborhoodChart_centerChartInterval
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X) {s t : unitInterval}
    (hsegment : Set.uIcc s t ⊆ γ ⁻¹' (d.source : Set X))
    (u : Set.uIcc s t) :
    ∃ e : SphereNeighborhoodChart X,
      γ u.1 ∈ e.source ∧
        ∃ a b : unitInterval,
          u.1 ∈ Set.Icc a b ∧
            Set.Icc a b ∈ nhds u.1 ∧
              ∀ {v : Set.uIcc s t},
                v.1 ∈ Set.Icc a b →
                  γ v.1 ∈ e.source ∧ γ v.1 ∈ d.source := by
  rcases point_has_sphereNeighborhoodChart (X := X) (γ u.1) with ⟨e, hue⟩
  have hpre_e :
      γ ⁻¹' (e.source : Set X) ∈ nhds u.1 := by
    exact γ.continuous.continuousAt.preimage_mem_nhds (e.source.isOpen.mem_nhds hue)
  have hpre_d :
      γ ⁻¹' (d.source : Set X) ∈ nhds u.1 := by
    exact γ.continuous.continuousAt.preimage_mem_nhds
      (d.source.isOpen.mem_nhds (hsegment u.2))
  have hpre_ed :
      (γ ⁻¹' (e.source : Set X)) ∩ (γ ⁻¹' (d.source : Set X)) ∈ nhds u.1 :=
    inter_mem hpre_e hpre_d
  obtain ⟨a, b, huIcc, hIcc_nhds, hIcc_subset⟩ := exists_Icc_mem_subset_of_mem_nhds hpre_ed
  refine ⟨e, hue, a, b, huIcc, hIcc_nhds, ?_⟩
  intro v hvIcc
  exact hIcc_subset hvIcc

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the reduced interval subtype `J`,
nearby points already lying in one fixed continued chart `c` should force the center point into the
second continuation of `c` through the same raw chart `d`. The interval returned here is packaged
directly on `unitInterval`, so later target-side arguments do not need to reconstruct ambient
membership for points of the smaller interval. -/
lemma sphereNeighborhoodChart_reducedCenterChartInterval
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {x₀ x : X} (γ : Path x₀ x) (d : SphereNeighborhoodChart X)
    {s t : unitInterval} {a b : unitInterval}
    (hIcc_subset : ∀ {w : Set.uIcc s t},
      w.1 ∈ Set.Icc a b → γ w.1 ∈ d.source)
    (u : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}) :
    ∃ e : SphereNeighborhoodChart X, ∃ a' b' : unitInterval,
      γ u.1.1 ∈ e.source ∧
        u.1.1 ∈ Set.Icc a' b' ∧
        {w : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b} | w.1.1 ∈ Set.Icc a' b'} ∈ nhds u ∧
        ∀ {w : unitInterval},
          w ∈ Set.Icc a' b' → γ w ∈ e.source ∧ γ w ∈ d.source := by
  let J : Type _ := {w : Set.uIcc s t // w.1 ∈ Set.Icc a b}
  let K : Type _ := {w : unitInterval // w ∈ Set.uIcc s t ∩ Set.Icc a b}
  let toK : J → K := fun w ↦ ⟨w.1.1, ⟨w.1.2, w.2⟩⟩
  let fromK : K → J := fun w ↦ ⟨⟨w.1, w.2.1⟩, w.2.2⟩
  have hfrom_to : ∀ w : J, fromK (toK w) = w := by
    intro w
    cases w
    rfl
  have hto_cont : Continuous toK := by
    -- Repackage the reduced interval subtype as the explicit interval intersection in
    -- `unitInterval`.
    exact
      Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun w ↦ ⟨w.1.2, w.2⟩)
  have hfrom_cont : Continuous fromK := by
    -- Forget the explicit interval-intersection subtype back to the reduced interval subtype.
    let hbase : Continuous fun w : K ↦ (⟨w.1, w.2.1⟩ : Set.uIcc s t) :=
      Continuous.subtype_mk continuous_subtype_val (fun w ↦ w.2.1)
    exact Continuous.subtype_mk hbase (fun w ↦ w.2.2)
  rcases point_has_sphereNeighborhoodChart (X := X) (γ u.1.1) with ⟨e, hue⟩
  let N : Set J := {w | γ w.1.1 ∈ e.source}
  have hN : N ∈ nhds u := by
    have hpathJ : Continuous (fun w : J ↦ γ w.1.1) := by
      exact γ.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    -- Pull the source neighborhood of the center chart back to the reduced interval subtype.
    simpa [N] using hpathJ.continuousAt.preimage_mem_nhds (e.source.isOpen.mem_nhds hue)
  have hN_K : fromK ⁻¹' N ∈ nhds (toK u) := by
    have hN' : N ∈ nhds (fromK (toK u)) := by
      simpa [hfrom_to u] using hN
    simpa [N] using hfrom_cont.continuousAt.preimage_mem_nhds hN'
  obtain ⟨aK, bK, huIcc, hIcc_nhds, hIcc_subsetK⟩ :=
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
  refine ⟨e, aK.1, bK.1, hue, ?_, ?_, ?_⟩
  · -- The chosen center time lies in the explicit reduced subinterval returned by the interval
    -- basis on `K`.
    simpa [toK, Set.mem_Icc] using huIcc
  · -- Pull the interval neighborhood on `K` back across the explicit identification `toK`.
    change M ∈ nhds u
    rw [hM_eq]
    exact hto_cont.continuousAt.preimage_mem_nhds hIcc_nhds
  · intro w hw
    have hwab' : w ∈ Set.uIcc aK.1 bK.1 := Set.Icc_subset_uIcc hw
    have hwst : w ∈ Set.uIcc s t := by
      exact Set.uIcc_subset_uIcc aK.2.1 bK.2.1 hwab'
    have hwab : w ∈ Set.Icc a b := by
      exact ⟨le_trans aK.2.2.1 hw.1, le_trans hw.2 bK.2.2.2⟩
    let wK : K := ⟨w, ⟨hwst, hwab⟩⟩
    have hwK : wK ∈ Set.Icc aK bK := by
      change aK.1 ≤ w ∧ w ≤ bK.1
      exact hw
    have hwN : fromK wK ∈ N := hIcc_subsetK hwK
    have hwe : γ w ∈ e.source := by
      -- Re-express the reduced-subtype source membership back on the ambient time parameter.
      simpa [N, fromK, wK] using hwN
    exact ⟨hwe, hIcc_subset (w := ⟨w, hwst⟩) hwab⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once the reduced center interval
`[a', b']` is chosen, every point of the ambient unordered interval `Set.uIcc a' b'` already lies
in the two raw chart sources tracked by that choice. This isolates the only transport needed
before later arguments can work on the smaller interval itself. -/
lemma sphereNeighborhoodChart_reducedCenterChartInterval_mem_sources_uIcc
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    {x₀ x : X} (γ : Path x₀ x) (d e : SphereNeighborhoodChart X)
    {s t : unitInterval} {a b : unitInterval}
    (u : {w : Set.uIcc s t // w.1 ∈ Set.Icc a b})
    {a' b' : unitInterval}
    (huIcc : u.1.1 ∈ Set.Icc a' b')
    (hsmall :
      ∀ {w : unitInterval},
        w ∈ Set.Icc a' b' → γ w ∈ e.source ∧ γ w ∈ d.source) :
    ∀ {w : Set.uIcc a' b'}, γ w.1 ∈ e.source ∧ γ w.1 ∈ d.source := by
  have hab' : a' ≤ b' := le_trans huIcc.1 huIcc.2
  intro w
  -- On the chosen interval, `Set.uIcc a' b'` is the ordinary closed interval `Set.Icc a' b'`.
  have hwIcc : w.1 ∈ Set.Icc a' b' := by
    simpa [Set.uIcc_of_le hab'] using w.2
  exact hsmall hwIcc

end
