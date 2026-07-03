import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Exercise_4_4
import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped Topology ContDiff

noncomputable section

namespace Manifold

universe u𝕜 uE uF uG uH uH' uH'' uM uN uP

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
variable {K : ModelWithCorners 𝕜 G H''}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
variable {n : ℕ∞ω}
variable {f : M → N} {g : N → P}

namespace IsImmersionAtOfComplement

/-- Helper for Exercise 4.16: an immersion at a point is automatically continuous at that point,
because in its chosen charts it agrees near the point with the continuous standard inclusion
`u ↦ (u, 0)`. -/
lemma ex416_continuousAt {x : M} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (h : IsImmersionAtOfComplement F' I J n f x) :
    ContinuousAt f x := by
  -- Work on the source chart neighborhood where the immersion normal form is valid.
  have hdomChart_source : h.domChart.source ∈ 𝓝 x :=
    IsOpen.mem_nhds h.domChart.open_source h.mem_domChart_source
  have hsource : f ⁻¹' h.codChart.source ∈ 𝓝 x :=
    Filter.mem_of_superset hdomChart_source h.source_subset_preimage_source
  have hEqOn :
      Set.EqOn ((h.codChart.extend J) ∘ f)
        (h.equiv ∘ fun y : M ↦ (h.domChart.extend I y, (0 : F')))
        h.domChart.source := by
    intro y hy
    -- Rewrite the chart expression at the concrete source point `y`.
    have hy_target :
        h.domChart.extend I y ∈ (h.domChart.extend I).target :=
      (h.domChart.extend I).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, OpenPartialHomeomorph.extend_coe, h.domChart.left_inv hy] using
      h.writtenInCharts hy_target
  have hEq :
      ((h.codChart.extend J) ∘ f) =ᶠ[𝓝 x]
        h.equiv ∘ fun y : M ↦ (h.domChart.extend I y, (0 : F')) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hcont_rhs :
      ContinuousAt
        (h.equiv ∘ fun y : M ↦ (h.domChart.extend I y, (0 : F'))) x := by
    -- The right-hand side is a continuous linear map applied to the source chart coordinates.
    have hcont_dom : ContinuousAt (h.domChart.extend I) x :=
      h.domChart.continuousAt_extend h.mem_domChart_source
    have hcont_pair :
        ContinuousAt (fun y : M ↦ (h.domChart.extend I y, (0 : F'))) x :=
      hcont_dom.prodMk continuousAt_const
    simpa [Function.comp] using ContinuousAt.comp h.equiv.continuousAt hcont_pair
  have hcont_extend : ContinuousAt ((h.codChart.extend J) ∘ f) x :=
    hcont_rhs.congr hEq.symm
  have hcont_chart : ContinuousAt (h.codChart ∘ f) x := by
    -- The codomain chart is obtained from the extended chart by composing with `J.symm`.
    convert J.continuousAt_symm.comp hcont_extend using 1
    funext y
    simp [Function.comp]
  -- Translate continuity of the chart expression back to continuity of `f`.
  exact (h.codChart.continuousAt_iff_continuousAt_comp_left hsource).2 hcont_chart

/-- Helper for Exercise 4.16: postcomposing a chart already in the smooth maximal atlas with a
smooth model-space self-chart change keeps it in the same maximal atlas. -/
lemma trans_mem_maximalAtlas_of_mem_groupoid
    {e : OpenPartialHomeomorph P H''}
    (he : e ∈ IsManifold.maximalAtlas K n P)
    {chi : OpenPartialHomeomorph H'' H''}
    (hchi : chi ∈ contDiffGroupoid n K) :
    e.trans chi ∈ IsManifold.maximalAtlas K n P := by
  -- Membership in the maximal atlas is tested by compatibility with the original atlas.
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have hcompat := IsManifold.mem_maximalAtlas_iff.mp he e' he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid n K := by
    -- The old transition from `e` to any atlas chart is already smooth.
    exact hcompat.1
  have hright : e'.symm.trans e ∈ contDiffGroupoid n K := by
    -- Likewise for the reverse transition.
    exact hcompat.2
  constructor
  · -- The new left transition factors through `chi.symm` and the old transition from `e`.
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n K).trans ((contDiffGroupoid n K).symm hchi) hleft
  · -- The new right transition factors through the old transition followed by `chi`.
    have hright' : (e'.symm.trans e).trans chi ∈ contDiffGroupoid n K := by
      exact (contDiffGroupoid n K).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Helper for Exercise 4.16: changing the codomain chart of an immersion witness rewrites the
extended-chart expression by the corresponding manifold coordinate change. -/
lemma ex416_change_codomain_chart_raw {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] (hf : IsImmersionAtOfComplement Ff I J n f x)
    (codChart : OpenPartialHomeomorph N H') :
    Set.EqOn
      (((codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm))
      (fun u ↦ J.extendCoordChange hf.codChart codChart (hf.equiv (u, (0 : Ff))))
      (hf.domChart.extend I).target := by
  intro u hu
  -- First insert the old codomain chart, then rewrite that chart expression using `hf`.
  have hu_source :
      (hf.domChart.extend I).symm u ∈ hf.domChart.source := by
    simpa [OpenPartialHomeomorph.extend_source] using (hf.domChart.extend I).map_target hu
  have hfu_source :
      f ((hf.domChart.extend I).symm u) ∈ hf.codChart.source :=
    hf.source_subset_preimage_source hu_source
  have hinsert :
      (hf.codChart.extend J).symm
          (((hf.codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u) =
        f ((hf.domChart.extend I).symm u) := by
    -- Apply the old codomain chart and immediately undo it inside its source.
    simpa [Function.comp] using hf.codChart.extend_left_inv (I := J) hfu_source
  calc
    ((codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u
        = ((codChart.extend J) ∘ (hf.codChart.extend J).symm)
            (((hf.codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u) := by
            simpa [Function.comp] using congrArg (codChart.extend J) hinsert.symm
    _ = ((codChart.extend J) ∘ (hf.codChart.extend J).symm) (hf.equiv (u, (0 : Ff))) := by
          -- Rewrite the old codomain chart expression using the immersion normal form for `hf`.
          simpa [Function.comp] using
            congrArg ((codChart.extend J) ∘ (hf.codChart.extend J).symm) (hf.writtenInCharts hu)
    _ = J.extendCoordChange hf.codChart codChart (hf.equiv (u, (0 : Ff))) := by
          rfl

/-- Helper for Exercise 4.16: once the source point already lands in the middle chart chosen for
`g`, the composition can be rewritten in raw coordinates by inserting that middle chart and then
using the two written-in-charts identities. -/
theorem ex416_comp_raw_middle_change {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {u : E}
    (hu : u ∈ (hf.domChart.extend I).target)
    (hmid : f ((hf.domChart.extend I).symm u) ∈ hg.domChart.source) :
    ((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u =
      hg.equiv
        (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) := by
  have hchange :
      ((hg.domChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u =
        J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))) :=
    ex416_change_codomain_chart_raw (hf := hf) (codChart := hg.domChart) hu
  have hmid_target :
      J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))) ∈
        (hg.domChart.extend J).target := by
    -- Reinterpret the middle coordinate change as the extended middle chart applied to
    -- the actual point `f ((hf.domChart.extend I).symm u)`.
    have hmid_ext :
        f ((hf.domChart.extend I).symm u) ∈ (hg.domChart.extend J).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hmid
    rw [← hchange]
    exact (hg.domChart.extend J).map_source hmid_ext
  have hinsert :
      (hg.domChart.extend J).symm
          (((hg.domChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u) =
        f ((hf.domChart.extend I).symm u) := by
    -- Insert the middle chart and its inverse around the intermediate point.
    simpa [Function.comp] using hg.domChart.extend_left_inv (I := J) hmid
  calc
    ((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u
        = ((hg.codChart.extend K) ∘ g ∘ (hg.domChart.extend J).symm)
            (((hg.domChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u) := by
            -- Since the intermediate point lies in `hg.domChart.source`, we may insert
            -- `hg.domChart.extend` and its inverse before applying `g`.
            simpa [Function.comp] using congrArg ((hg.codChart.extend K) ∘ g) hinsert.symm
    _ = ((hg.codChart.extend K) ∘ g ∘ (hg.domChart.extend J).symm)
          (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff)))) := by
          rw [hchange]
    _ = hg.equiv
          (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) := by
          simpa [Function.comp] using hg.writtenInCharts hmid_target

/-- Helper for Exercise 4.16: after restricting the source chart of `hf` to an open neighborhood
on which `f` lands in `hg.domChart.source`, the raw middle-change formula from
`ex416_comp_raw_middle_change` still holds on the restricted chart target. -/
theorem ex416_comp_raw_middle_change_on_restr {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {U : Set M} (hU_open : IsOpen U)
    (hU_dom : U ⊆ hf.domChart.source) (hU_mid : U ⊆ f ⁻¹' hg.domChart.source) :
    Set.EqOn
      (((hg.codChart.extend K) ∘ g ∘ f ∘ ((hf.domChart.restr U).extend I).symm))
      (fun u ↦ hg.equiv
        (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)))
      ((hf.domChart.restr U).extend I).target := by
  intro u hu
  -- Read the restricted target point back in the restricted chart to recover a source point in `U`.
  have hu_restr_source :
      ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.restr U).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((hf.domChart.restr U).extend I).map_target hu
  have hu_source :
      ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source := by
    have hu_restr_source' :
        ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source ∩ U := by
      have hu_restr_source'' := hu_restr_source
      rw [hf.domChart.restr_source' U hU_open] at hu_restr_source''
      exact hu_restr_source''
    exact hU_dom hu_restr_source'.2
  have hu_mid :
      f (((hf.domChart.restr U).extend I).symm u) ∈ hg.domChart.source :=
    hU_mid <| by
      have hu_restr_source' :
          ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source ∩ U := by
        have hu_restr_source'' := hu_restr_source
        rw [hf.domChart.restr_source' U hU_open] at hu_restr_source''
        exact hu_restr_source''
      exact hu_restr_source'.2
  -- The restricted extended chart agrees with the original one on this restricted target point.
  have hu_eq :
      (hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u) = u := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp] using
      (((hf.domChart.restr U).extend I).right_inv hu)
  have hu_target :
      u ∈ (hf.domChart.extend I).target := by
    have hu_source_ext :
        ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hu_source
    have hu_target' :
        (hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u) ∈
          (hf.domChart.extend I).target :=
      (hf.domChart.extend I).map_source hu_source_ext
    exact hu_eq ▸ hu_target'
  have hu_symm_eq :
      ((hf.domChart.restr U).extend I).symm u = (hf.domChart.extend I).symm u := by
    -- Apply the original chart inverse to the shared chart value `u`.
    have hu_source_ext :
        ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hu_source
    have hu_symm_eq' :
        (hf.domChart.extend I).symm
            ((hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u)) =
          ((hf.domChart.restr U).extend I).symm u :=
      (hf.domChart.extend I).left_inv hu_source_ext
    rwa [hu_eq] at hu_symm_eq'
  -- Route correction: the remaining composition formula is exactly the earlier raw lemma once the
  -- restricted inverse is rewritten back to the original inverse.
  calc
    ((hg.codChart.extend K) ∘ g ∘ f ∘ ((hf.domChart.restr U).extend I).symm) u
        = ((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u := by
            simpa [Function.comp] using
              congrArg ((hg.codChart.extend K) ∘ g ∘ f) hu_symm_eq
    _ = hg.equiv
          (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) :=
      ex416_comp_raw_middle_change (hg := hg) (hf := hf) (hu := hu_target) hu_mid

/-- Helper for Exercise 4.16: for any local chart `e`, points in the target of the restricted
extended chart also lie in the target of the original extended chart. -/
lemma ex416_restr_extend_target_mem_of_openPartialHomeomorph
    {e : OpenPartialHomeomorph M H} {U : Set M} (hU_open : IsOpen U) {u : E}
    (hu : u ∈ ((e.restr U).extend I).target) :
    u ∈ (e.extend I).target := by
  -- Read the restricted target point back to the source and then evaluate the original chart.
  have hu_restr_source :
      ((e.restr U).extend I).symm u ∈ (e.restr U).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((e.restr U).extend I).map_target hu
  have hu_source :
      ((e.restr U).extend I).symm u ∈ e.source := by
    have hu_restr_source' := hu_restr_source
    rw [e.restr_source' U hU_open] at hu_restr_source'
    exact hu_restr_source'.1
  have hu_eq :
      (e.extend I) (((e.restr U).extend I).symm u) = u := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp] using
      (((e.restr U).extend I).right_inv hu)
  have hu_source_ext :
      ((e.restr U).extend I).symm u ∈ (e.extend I).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hu_source
  have hu_target' :
      (e.extend I) (((e.restr U).extend I).symm u) ∈ (e.extend I).target :=
    (e.extend I).map_source hu_source_ext
  exact hu_eq ▸ hu_target'

/-- Helper for Exercise 4.16: for any local chart `e`, the restricted extended-chart inverse
agrees with the original extended-chart inverse on the restricted target. -/
lemma ex416_restr_extend_symm_eq_of_openPartialHomeomorph
    {e : OpenPartialHomeomorph M H} {U : Set M} (hU_open : IsOpen U) {u : E}
    (hu : u ∈ ((e.restr U).extend I).target) :
    ((e.restr U).extend I).symm u = (e.extend I).symm u := by
  -- Both inverses recover the same source point because the original chart still sends it to `u`.
  have hu_restr_source :
      ((e.restr U).extend I).symm u ∈ (e.restr U).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((e.restr U).extend I).map_target hu
  have hu_source :
      ((e.restr U).extend I).symm u ∈ e.source := by
    have hu_restr_source' := hu_restr_source
    rw [e.restr_source' U hU_open] at hu_restr_source'
    exact hu_restr_source'.1
  have hu_eq :
      (e.extend I) (((e.restr U).extend I).symm u) = u := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp] using
      (((e.restr U).extend I).right_inv hu)
  have hu_source_ext :
      ((e.restr U).extend I).symm u ∈ (e.extend I).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hu_source
  have hu_symm_eq' :
      (e.extend I).symm ((e.extend I) (((e.restr U).extend I).symm u)) =
        ((e.restr U).extend I).symm u :=
    (e.extend I).left_inv hu_source_ext
  rwa [hu_eq] at hu_symm_eq'

/-- Helper for Exercise 4.16: a point in the target of the restricted extended chart is also in the
target of the original extended chart. -/
lemma ex416_restr_extend_target_mem {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] (hf : IsImmersionAtOfComplement Ff I J n f x)
    {U : Set M} (hU_open : IsOpen U) {u : E}
    (hu : u ∈ ((hf.domChart.restr U).extend I).target) :
    u ∈ (hf.domChart.extend I).target := by
  -- Read the restricted target point back to the source and then evaluate the original chart.
  have hu_restr_source :
      ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.restr U).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((hf.domChart.restr U).extend I).map_target hu
  have hu_source :
      ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source := by
    have hu_restr_source' := hu_restr_source
    rw [hf.domChart.restr_source' U hU_open] at hu_restr_source'
    exact hu_restr_source'.1
  have hu_eq :
      (hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u) = u := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp] using
      (((hf.domChart.restr U).extend I).right_inv hu)
  have hu_source_ext :
      ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.extend I).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hu_source
  have hu_target' :
      (hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u) ∈
        (hf.domChart.extend I).target :=
    (hf.domChart.extend I).map_source hu_source_ext
  exact hu_eq ▸ hu_target'

/-- Helper for Exercise 4.16: on the target of a restricted extended chart, the restricted inverse
agrees with the original extended-chart inverse. -/
lemma ex416_restr_extend_symm_eq {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] (hf : IsImmersionAtOfComplement Ff I J n f x)
    {U : Set M} (hU_open : IsOpen U) {u : E}
    (hu : u ∈ ((hf.domChart.restr U).extend I).target) :
    ((hf.domChart.restr U).extend I).symm u = (hf.domChart.extend I).symm u := by
  -- Both inverses recover the same point because the original extended chart sends it back to `u`.
  have hu_restr_source :
      ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.restr U).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((hf.domChart.restr U).extend I).map_target hu
  have hu_source :
      ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source := by
    have hu_restr_source' := hu_restr_source
    rw [hf.domChart.restr_source' U hU_open] at hu_restr_source'
    exact hu_restr_source'.1
  have hu_eq :
      (hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u) = u := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp] using
      (((hf.domChart.restr U).extend I).right_inv hu)
  have hu_source_ext :
      ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.extend I).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hu_source
  have hu_symm_eq' :
      (hf.domChart.extend I).symm
          ((hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u)) =
        ((hf.domChart.restr U).extend I).symm u :=
    (hf.domChart.extend I).left_inv hu_source_ext
  rwa [hu_eq] at hu_symm_eq'

/-- Helper for Exercise 4.16: points coming from the restricted source chart still land in the
source of the middle coordinate change used to straighten the composition. -/
lemma ex416_immersion_coordinate_mem_extendCoordChange_source_of_restr_target {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {U : Set M} (hU_open : IsOpen U)
    (hU_mid : U ⊆ f ⁻¹' hg.domChart.source) {u : E}
    (hu : u ∈ ((hf.domChart.restr U).extend I).target) :
    hf.equiv (u, (0 : Ff)) ∈ (J.extendCoordChange hf.codChart hg.domChart).source := by
  -- Recover the actual source point in `U`, then rewrite the immersion coordinates of `hf`.
  have hu_restr_source :
      ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.restr U).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((hf.domChart.restr U).extend I).map_target hu
  have hu_restr_source' :
      ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source ∩ U := by
    have hu_restr_source'' := hu_restr_source
    rw [hf.domChart.restr_source' U hU_open] at hu_restr_source''
    exact hu_restr_source''
  have hu_source :
      ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source :=
    hu_restr_source'.1
  have hu_mid :
      f (((hf.domChart.restr U).extend I).symm u) ∈ hg.domChart.source :=
    hU_mid hu_restr_source'.2
  have hu_target :
      u ∈ (hf.domChart.extend I).target :=
    ex416_restr_extend_target_mem (hf := hf) (U := U) hU_open hu
  have hu_symm_eq :
      ((hf.domChart.restr U).extend I).symm u = (hf.domChart.extend I).symm u :=
    ex416_restr_extend_symm_eq (hf := hf) (U := U) hU_open hu
  have hfu_source :
      f (((hf.domChart.restr U).extend I).symm u) ∈ hf.codChart.source :=
    hf.source_subset_preimage_source hu_source
  have hz_image :
      (hf.codChart.extend J) (f (((hf.domChart.restr U).extend I).symm u)) ∈
        (J.extendCoordChange hf.codChart hg.domChart).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (I := J)
      (f := hf.codChart) (f' := hg.domChart)]
    exact ⟨f (((hf.domChart.restr U).extend I).symm u), ⟨hfu_source, hu_mid⟩, rfl⟩
  have hwritten :
      hf.equiv (u, (0 : Ff)) =
        (hf.codChart.extend J) (f (((hf.domChart.restr U).extend I).symm u)) := by
    calc
      hf.equiv (u, (0 : Ff))
          = (hf.codChart.extend J) (f ((hf.domChart.extend I).symm u)) := by
              -- Switch from the written-in-charts identity for `hf` to the actual source point.
              simpa [Function.comp] using (hf.writtenInCharts hu_target).symm
      _ = (hf.codChart.extend J) (f (((hf.domChart.restr U).extend I).symm u)) := by
            rw [hu_symm_eq]
  exact hwritten ▸ hz_image

/-- Helper for Exercise 4.16: on the restricted source-chart target used in the composition proof,
the raw middle-change expression already lies in the codomain extended-chart target. -/
lemma ex416_raw_middle_change_mem_codomain_target {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {U : Set M} (hU_open : IsOpen U)
    (hU_dom : U ⊆ hf.domChart.source) (hU_mid : U ⊆ f ⁻¹' hg.domChart.source) {u : E}
    (hu : u ∈ ((hf.domChart.restr U).extend I).target) :
    hg.equiv
        (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) ∈
      (hg.codChart.extend K).target := by
  -- The raw formula agrees with the actual composed chart expression, whose target-membership is
  -- immediate from the fact that the restricted source point maps into `hg.codChart.source`.
  have hu_restr_source :
      ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.restr U).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((hf.domChart.restr U).extend I).map_target hu
  have hu_mid :
      f (((hf.domChart.restr U).extend I).symm u) ∈ hg.domChart.source := by
    have hu_restr_source' :
        ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source ∩ U := by
      have hu_restr_source'' := hu_restr_source
      rw [hf.domChart.restr_source' U hU_open] at hu_restr_source''
      exact hu_restr_source''
    exact hU_mid hu_restr_source'.2
  have hgf_source :
      g (f (((hf.domChart.restr U).extend I).symm u)) ∈ hg.codChart.source :=
    hg.source_subset_preimage_source hu_mid
  have htarget :
      ((hg.codChart.extend K) ∘ g ∘ f ∘ ((hf.domChart.restr U).extend I).symm) u ∈
        (hg.codChart.extend K).target := by
    -- The composed point lies in the source of the codomain extended chart.
    have hgf_source_ext :
        g (f (((hf.domChart.restr U).extend I).symm u)) ∈ (hg.codChart.extend K).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hgf_source
    simpa [Function.comp, OpenPartialHomeomorph.extend_source] using
      (hg.codChart.extend K).map_source hgf_source_ext
  rw [ex416_comp_raw_middle_change_on_restr
    (hg := hg) (hf := hf) (U := U) hU_open hU_dom hU_mid hu] at htarget
  exact htarget

/-- Helper for Exercise 4.16: the inverse middle coordinate change straightens the first factor of
the raw product-model map arising in the composition proof. -/
lemma ex416_middle_change_prod_apply {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {z : F}
    (hz : z ∈ (J.extendCoordChange hf.codChart hg.domChart).source) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    (fun p : F × Fg ↦ (θ.symm p.1, p.2)) (θ z, (0 : Fg)) = (z, 0) := by
  -- The product straightening map simply applies the inverse middle coordinate change on the
  -- first factor and leaves the complement factor fixed.
  dsimp
  have hleft :
      (J.extendCoordChange hf.codChart hg.domChart).symm
          ((J.extendCoordChange hf.codChart hg.domChart) z) = z :=
    (J.extendCoordChange hf.codChart hg.domChart).left_inv hz
  simpa using congrArg (fun w : F ↦ (w, (0 : Fg))) hleft

/-- Helper for Exercise 4.16: pairing the identity on the second factor with a `C^n` first-factor
map gives a `C^n` product map on the corresponding product source. -/
lemma ex416_contDiffOn_prod_map_snd {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    {s : Set F} {φ : F → F} (hφ : ContDiffOn 𝕜 n φ s) :
    ContDiffOn 𝕜 n (fun p : F × Fg ↦ (φ p.1, p.2)) (Prod.fst ⁻¹' s) := by
  -- Smoothness on the product comes from composing the first-coordinate map with `Prod.fst`
  -- and pairing it with the unchanged second coordinate.
  have hfst :
      ContDiffOn 𝕜 n (fun p : F × Fg ↦ φ p.1) (Prod.fst ⁻¹' s) := by
    refine hφ.comp contDiff_fst.contDiffOn ?_
    intro p hp
    exact hp
  have hsnd :
      ContDiffOn 𝕜 n (fun p : F × Fg ↦ p.2) (Prod.fst ⁻¹' s) := by
    refine (contDiff_snd.contDiffOn : ContDiffOn 𝕜 n (fun p : F × Fg ↦ p.2) Set.univ).mono ?_
    intro p hp
    simp
  simpa using hfst.prodMk hsnd

/-- Helper for Exercise 4.16: the middle coordinate change and its inverse are `C^n` after being
promoted to the product-model maps that fix the complement factor. -/
lemma ex416_middle_change_prod_contDiff {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    ContDiffOn 𝕜 n (fun p : F × Fg ↦ (θ.symm p.1, p.2)) (Prod.fst ⁻¹' θ.target) ∧
      ContDiffOn 𝕜 n (fun p : F × Fg ↦ (θ p.1, p.2)) (Prod.fst ⁻¹' θ.source) := by
  -- Combine smoothness of the middle coordinate change with the identity on the complement factor.
  dsimp
  constructor
  · exact ex416_contDiffOn_prod_map_snd
      (F := F) (Fg := Fg)
      (J.contDiffOn_extendCoordChange_symm
        hf.codChart_mem_maximalAtlas hg.domChart_mem_maximalAtlas)
  · exact ex416_contDiffOn_prod_map_snd
      (F := F) (Fg := Fg)
      (J.contDiffOn_extendCoordChange
        hf.codChart_mem_maximalAtlas hg.domChart_mem_maximalAtlas)

/-- Helper for Exercise 4.16: package the product-model straightening map as an explicit
`PartialEquiv` so later chart conjugations can compose it without re-expanding the product map. -/
def ex416_middle_change_prod_chart {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) :
    PartialEquiv (F × Fg) (F × Fg) :=
  (J.extendCoordChange hf.codChart hg.domChart).symm.prod (PartialEquiv.refl Fg)

/-- Helper for Exercise 4.16: the packaged product straightening chart sends the raw middle term
to the standard product inclusion `(z, 0)`. -/
lemma ex416_middle_change_prod_chart_apply {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {z : F}
    (hz : z ∈ (J.extendCoordChange hf.codChart hg.domChart).source) :
    ex416_middle_change_prod_chart (hg := hg) (hf := hf)
      (J.extendCoordChange hf.codChart hg.domChart z, (0 : Fg)) = (z, 0) := by
  -- Unfold the packaged chart and apply the explicit first-factor straightening formula.
  simpa [ex416_middle_change_prod_chart] using
    ex416_middle_change_prod_apply (hg := hg) (hf := hf) (z := z) hz

/-- Helper for Exercise 4.16: conjugating the product straightening map by `hg.equiv` already
gives the codomain-model normal form on `G`; only the final transport through `K` remains. -/
lemma ex416_codomain_straightening_model_chart_apply {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {u : E}
    (hu : u ∈ (hf.domChart.extend I).target)
    (hmid : f ((hf.domChart.extend I).symm u) ∈ hg.domChart.source) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    ((eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv)
      (hg.equiv (θ (hf.equiv (u, (0 : Ff))), (0 : Fg))) =
        hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)) := by
  -- Read the source point of `u` back through the original immersion chart for `hf`.
  have hu_source :
      (hf.domChart.extend I).symm u ∈ hf.domChart.source := by
    simpa [OpenPartialHomeomorph.extend_source] using (hf.domChart.extend I).map_target hu
  have hfu_source :
      f ((hf.domChart.extend I).symm u) ∈ hf.codChart.source :=
    hf.source_subset_preimage_source hu_source
  have hz_source :
      hf.equiv (u, (0 : Ff)) ∈ (J.extendCoordChange hf.codChart hg.domChart).source := by
    -- The middle coordinate-change source is exactly the image of points lying in both middle
    -- charts, and our intermediate point lies in that overlap.
    have hz_image :
        (hf.codChart.extend J) (f ((hf.domChart.extend I).symm u)) ∈
          (J.extendCoordChange hf.codChart hg.domChart).source := by
      rw [← OpenPartialHomeomorph.extend_image_source_inter (I := J)
        (f := hf.codChart) (f' := hg.domChart)]
      exact ⟨f ((hf.domChart.extend I).symm u), ⟨hfu_source, hmid⟩, rfl⟩
    have hwritten :
        hf.equiv (u, (0 : Ff)) =
          (hf.codChart.extend J) (f ((hf.domChart.extend I).symm u)) := by
      -- The immersion normal form for `hf` identifies the raw first factor with the codomain
      -- extended chart of the actual image point.
      simpa [Function.comp] using (hf.writtenInCharts hu).symm
    exact hwritten ▸ hz_image
  -- After the source-membership bookkeeping, the conjugated chart change is just `hg.equiv`
  -- applied to the product straightening formula.
  simpa [ex416_middle_change_prod_chart, PartialEquiv.trans_apply] using
    congrArg hg.equiv (ex416_middle_change_prod_apply (hg := hg) (hf := hf)
      (z := hf.equiv (u, (0 : Ff))) hz_source)

/-- Helper for Exercise 4.16: after restricting the source chart once so that `f` lands in the
middle chart chosen for `g`, the conjugated model-space straightening map already sends the raw
codomain expression of `g ∘ f` to the standard product inclusion. -/
lemma comp_written_in_conjugated_codomain_model_chart_on_restr {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {U : Set M} (hU_open : IsOpen U)
    (hU_dom : U ⊆ hf.domChart.source) (hU_mid : U ⊆ f ⁻¹' hg.domChart.source) :
    let domChart0 := hf.domChart.restr U
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    Set.EqOn
      (fun u ↦ xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u))
      (fun u ↦ hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)))
      (domChart0.extend I).target := by
  dsimp
  have hraw :
      Set.EqOn
        (((hg.codChart.extend K) ∘ g ∘ f ∘ ((hf.domChart.restr U).extend I).symm))
        (fun u ↦
          hg.equiv
            (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)))
        ((hf.domChart.restr U).extend I).target := by
    -- The restricted source chart already gives the raw middle-change formula on its whole target.
    simpa using
      ex416_comp_raw_middle_change_on_restr
        (hg := hg) (hf := hf) (U := U) hU_open hU_dom hU_mid
  have hraw_target :
      ∀ ⦃u : E⦄, u ∈ ((hf.domChart.restr U).extend I).target →
        hg.equiv
            (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) ∈
          (hg.codChart.extend K).target := by
    intro u hu
    -- This is the target-membership part of the restricted raw chart formula.
    simpa using
      ex416_raw_middle_change_mem_codomain_target
        (hg := hg) (hf := hf) (U := U) hU_open hU_dom hU_mid hu
  have hmid_source :
      ∀ ⦃u : E⦄, u ∈ ((hf.domChart.restr U).extend I).target →
        f ((hf.domChart.extend I).symm u) ∈ hg.domChart.source := by
    intro u hu
    -- Rewriting the restricted inverse back to the original inverse recovers the middle-chart
    -- source condition needed for the model-space straightening map.
    have hu_restr_source :
        (((hf.domChart.restr U).extend I).symm u) ∈ (hf.domChart.restr U).source := by
      simpa [OpenPartialHomeomorph.extend_source] using ((hf.domChart.restr U).extend I).map_target hu
    have hu_restr_source' :
        (((hf.domChart.restr U).extend I).symm u) ∈ hf.domChart.source ∩ U := by
      have hu_restr_source'' := hu_restr_source
      rw [hf.domChart.restr_source' U hU_open] at hu_restr_source''
      exact hu_restr_source''
    have hu_mid :
        f (((hf.domChart.restr U).extend I).symm u) ∈ hg.domChart.source :=
      hU_mid hu_restr_source'.2
    have hu_symm_eq :
        ((hf.domChart.restr U).extend I).symm u = (hf.domChart.extend I).symm u := by
      simpa using ex416_restr_extend_symm_eq (hf := hf) (U := U) hU_open hu
    simpa [hu_symm_eq] using hu_mid
  let rho : PartialEquiv (F × Fg) (F × Fg) := ex416_middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  have hxi_eq :
      Set.EqOn
        (fun u ↦
          ((eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv)
            (hg.equiv
              (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg))))
        (fun u ↦ hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)))
        ((hf.domChart.restr U).extend I).target := by
    intro u hu
    have hu_target :
        u ∈ (hf.domChart.extend I).target := by
      simpa using ex416_restr_extend_target_mem (hf := hf) (U := U) hU_open hu
    -- The model-space straightening identity applies on the original source-chart target.
    simpa [rho, eG] using
      ex416_codomain_straightening_model_chart_apply
        (hg := hg) (hf := hf) (u := u) hu_target (hmid_source hu)
  intro u hu
  -- Combine the raw restricted chart formula with the model-space straightening identity.
  change
    ((eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv)
      (((hg.codChart.extend K) ∘ g ∘ f ∘ ((hf.domChart.restr U).extend I).symm) u) =
    hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg))
  rw [hraw hu]
  exact hxi_eq hu

/-- Helper for Exercise 4.16: the conjugated model-space straightening map
`xi = eG ∘ rho ∘ eG.symm` is `C^n` on its source, and so is its inverse on its target. -/
lemma ex416_codomain_straightening_model_contDiff {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let xi : PartialEquiv G G :=
      ((hg.equiv.toHomeomorph.toOpenPartialHomeomorph).toPartialEquiv.symm.trans rho).trans
        (hg.equiv.toHomeomorph.toOpenPartialHomeomorph).toPartialEquiv
    ContDiffOn 𝕜 n xi xi.source ∧ ContDiffOn 𝕜 n xi.symm xi.target := by
  dsimp
  let rho : PartialEquiv (F × Fg) (F × Fg) := ex416_middle_change_prod_chart (hg := hg) (hf := hf)
  let xi : PartialEquiv G G :=
    ((hg.equiv.toHomeomorph.toOpenPartialHomeomorph).toPartialEquiv.symm.trans rho).trans
      (hg.equiv.toHomeomorph.toOpenPartialHomeomorph).toPartialEquiv
  have hrho :
      ContDiffOn 𝕜 n rho (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).target) ∧
        ContDiffOn 𝕜 n rho.symm
          (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).source) := by
    -- The product-model straightening is exactly the promoted middle chart change.
    simpa [rho, ex416_middle_change_prod_chart] using
      ex416_middle_change_prod_contDiff (hg := hg) (hf := hf)
  constructor
  · -- Pull the source smoothness of `rho` back and forth across the linear chart `hg.equiv`.
    have hcomp :
        ContDiffOn 𝕜 n (fun p : F × Fg ↦ xi (hg.equiv p))
          (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).target) := by
      have hbase :
          ContDiffOn 𝕜 n (fun p : F × Fg ↦ hg.equiv (rho p))
            (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).target) :=
        hg.equiv.contDiff.comp_contDiffOn hrho.1
      refine hbase.congr ?_
      intro p hp
      simp [xi, rho, PartialEquiv.trans_apply]
    have hpre :
        hg.equiv ⁻¹' xi.source =
          Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).target := by
      ext p
      simp [xi, rho, ex416_middle_change_prod_chart, PartialEquiv.trans_source]
    have hcomp' : ContDiffOn 𝕜 n (xi ∘ hg.equiv) (hg.equiv ⁻¹' xi.source) := by
      simpa [Function.comp, hpre] using hcomp
    exact (hg.equiv.contDiffOn_comp_iff (f := xi) (s := xi.source)).1 hcomp'
  · -- The same conjugation argument gives smoothness of the inverse on the target.
    have hcomp :
        ContDiffOn 𝕜 n (fun p : F × Fg ↦ xi.symm (hg.equiv p))
          (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).source) := by
      have hbase :
          ContDiffOn 𝕜 n (fun p : F × Fg ↦ hg.equiv (rho.symm p))
            (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).source) :=
        hg.equiv.contDiff.comp_contDiffOn hrho.2
      refine hbase.congr ?_
      intro p hp
      simp [xi, rho, Function.comp, PartialEquiv.trans_apply]
    have hpre :
        hg.equiv ⁻¹' xi.target =
          Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).source := by
      ext p
      simp [xi, rho, ex416_middle_change_prod_chart, PartialEquiv.trans_target]
    have hcomp' : ContDiffOn 𝕜 n (xi.symm ∘ hg.equiv) (hg.equiv ⁻¹' xi.target) := by
      simpa [Function.comp, hpre] using hcomp
    exact (hg.equiv.contDiffOn_comp_iff (f := xi.symm) (s := xi.target)).1 hcomp'

/-- Helper for Exercise 4.16: a model-space open partial homeomorphism belongs to the
`C^n` structure groupoid once its whole source is locally covered by `C^n` structomorph charts. -/
theorem ex416_mem_contDiffGroupoid_of_local_structomorphOn_source
    {f : OpenPartialHomeomorph H'' H''}
    (hf : ChartedSpace.LiftPropOn
      ((contDiffGroupoid n K).IsLocalStructomorphWithinAt) f f.source) :
    f ∈ contDiffGroupoid n K := by
  refine (contDiffGroupoid n K).locality ?_
  intro x hx
  -- Read the local structomorphism witness in the model chart `chartAt H'' x = refl`.
  have hfx := hf x hx
  have hfx' := hfx
  simp only [ChartedSpace.liftPropWithinAt_iff', chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm] at hfx'
  obtain ⟨-, hfx_prop⟩ := hfx'
  have hfx_prop' : (contDiffGroupoid n K).IsLocalStructomorphWithinAt f f.source x := by
    simpa using hfx_prop
  rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    (G := contDiffGroupoid n K) (f := f)] at hfx_prop'
  obtain ⟨e, he, hsource, hEq, hxe⟩ := hfx_prop' hx
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  -- Restricting `f` to the neighborhood where it agrees with `e` lets `mem_of_eqOnSource` close.
  have hEq' : Set.EqOn f e (f.source ∩ e.source) := by
    intro y hy
    exact hEq hy.2
  have hrestr : f.restr e.source ≈ e.restr f.source := by
    exact OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEq'
  have hEqOnSource : f.restr e.source ≈ e := by
    simpa [OpenPartialHomeomorph.restr_eq_of_source_subset hsource] using hrestr
  exact (contDiffGroupoid n K).mem_of_eqOnSource he hEqOnSource

/-- Helper for Exercise 4.16: forgetting the inverse of a model-space partial diffeomorphism
produces an element of the `C^n` structure groupoid. -/
theorem ex416_model_partial_diffeomorph_mem_contDiffGroupoid
    {Φ : PartialDiffeomorph K K H'' H'' n} :
    Φ.toOpenPartialHomeomorph ∈ contDiffGroupoid n K := by
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid n K).IsLocalStructomorphWithinAt)
        Φ.toOpenPartialHomeomorph Φ.source := by
    -- The partial diffeomorphism is `C^n` on its source and inverse-target by definition.
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := K) (n := n) (f := Φ.toOpenPartialHomeomorph)).2
      ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩
  exact ex416_mem_contDiffGroupoid_of_local_structomorphOn_source (K := K) hΦ

/-- Helper for Exercise 4.16: writing a `K`-partial diffeomorphism in maximal-atlas charts
produces a codomain chart change in `contDiffGroupoid n K`. -/
theorem ex416_writtenIn_partial_diffeomorph_mem_contDiffGroupoid
    {P' : Type*} [TopologicalSpace P'] [ChartedSpace H'' P']
    [IsManifold K n P] [IsManifold K n P']
    {Φ : PartialDiffeomorph K K P P' n} {e : OpenPartialHomeomorph P H''}
    {c : OpenPartialHomeomorph P' H''}
    (he : e ∈ IsManifold.maximalAtlas K n P)
    (hc : c ∈ IsManifold.maximalAtlas K n P') :
    (e.symm.trans Φ.toOpenPartialHomeomorph).trans c ∈ contDiffGroupoid n K := by
  let f : OpenPartialHomeomorph H'' H'' := (e.symm.trans Φ.toOpenPartialHomeomorph).trans c
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid n K).IsLocalStructomorphWithinAt)
        Φ.toOpenPartialHomeomorph Φ.source := by
    -- The partial diffeomorphism is smooth in both directions on its own source and target.
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := K) (n := n) (f := Φ.toOpenPartialHomeomorph)).2
      ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩
  -- Transport the local structomorphism property through the chosen source and target charts.
  refine ex416_mem_contDiffGroupoid_of_local_structomorphOn_source (K := K) ?_
  intro y hy
  rw [ChartedSpace.liftPropWithinAt_iff']
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.refl_symm, Set.preimage_id_eq]
  refine ⟨f.continuousOn_toFun.continuousWithinAt hy, ?_⟩
  intro hyf
  have hy_chart :
      y ∈ e.target ∩ e.symm ⁻¹' (Φ.source ∩ Φ.toOpenPartialHomeomorph ⁻¹' c.source) := by
    have hyf' := hyf
    simp only [f, OpenPartialHomeomorph.trans_source, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hyf'
    rcases hyf' with ⟨⟨hy_target, hy_source⟩, hy_csource⟩
    exact ⟨hy_target, hy_source, hy_csource⟩
  have htransport :
      (contDiffGroupoid n K).IsLocalStructomorphWithinAt
        (c ∘ Φ.toOpenPartialHomeomorph ∘ e.symm)
        (e.symm ⁻¹' Φ.source) y := by
    exact StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid n K))
      he hc hΦ hy_chart
  rcases htransport hy_chart.2.1 with ⟨φ, hφ, hEq, hyφ⟩
  refine ⟨φ, hφ, ?_, hyφ⟩
  -- Restrict the transported witness from the larger preimage `e.symm ⁻¹' Φ.source`
  -- to the actual source of the written-in-chart map.
  intro z hz
  have hz_big : z ∈ (e.symm ⁻¹' Φ.source) ∩ φ.source := by
    refine ⟨?_, hz.2⟩
    have hz' := hz.1
    simp only [f, OpenPartialHomeomorph.trans_source, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hz'
    exact hz'.1.2
  simpa [f, OpenPartialHomeomorph.coe_trans, Function.comp_assoc] using hEq hz_big

/-- Helper for Exercise 4.16: the model-with-corners map `K` identifies `H''` with the closed
subtype `Set.range K`. This is the ambient transport used by the remaining codomain-chart step. -/
noncomputable def ex416_codomain_model_range_homeomorph :
    H'' ≃ₜ Set.range (K : H'' → G) :=
  K.isClosedEmbedding.isEmbedding.toHomeomorph

/-- Helper for Exercise 4.16: if a local chart change is first built on the transported range
subtype `Set.range K`, conjugating by the canonical homeomorphism `H'' ≃ₜ Set.range K` gives a
chart change on `H''` with the same ambient `K`-expression. -/
lemma ex416_transport_subtype_homeomorph_to_chart_change
    {xi : G → G} {y0 : H''}
    {chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G))}
    (hy0 : (⟨K y0, ⟨y0, rfl⟩⟩ : Set.range (K : H'' → G)) ∈ chiRange.source)
    (hEqRange :
      Set.EqOn
        (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi z.1) chiRange.source) :
    ∃ chi : OpenPartialHomeomorph H'' H'',
      y0 ∈ chi.source ∧
      Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
  let eK : H'' ≃ₜ Set.range (K : H'' → G) := ex416_codomain_model_range_homeomorph (K := K)
  let chi : OpenPartialHomeomorph H'' H'' :=
    (eK.toOpenPartialHomeomorph.trans chiRange).transHomeomorph eK.symm
  refine ⟨chi, ?_, ?_⟩
  · -- The transported source is exactly the pullback of `chiRange.source` along `eK`.
    simpa [chi, eK, OpenPartialHomeomorph.trans_source] using hy0
  · intro y hy
    have hyRange : eK y ∈ chiRange.source := by
      -- Reinterpret source membership on the ambient side as source membership for `chiRange`.
      simpa [chi, eK, OpenPartialHomeomorph.trans_source] using hy
    calc
      K (chi y) = ((chiRange (eK y) : Set.range (K : H'' → G)).1) := by
        -- Unfold the conjugation and then read off the ambient coordinate of the subtype point.
        exact congrArg Subtype.val (eK.apply_symm_apply (chiRange (eK y)))
      _ = xi (K y) := by
        -- The transported subtype chart was chosen to agree with the ambient map `xi`.
        simpa [eK] using hEqRange hyRange

/-- Helper for Exercise 4.16: once the subtype-level straightening on `Set.range K` has been
upgraded to a `K`-partial diffeomorphism in the transported singleton chart, writing it back in
`H''` gives the local codomain chart change needed in the composition proof. -/
lemma ex416_writtenIn_range_straightening_to_chart_change
    {xi : G → G} {y0 : H''}
    {chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G))}
    (hchiRange_mem :
      let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
        (ex416_codomain_model_range_homeomorph (K := K)).symm.toOpenPartialHomeomorph
      ((eRange.symm.trans chiRange).trans eRange) ∈ contDiffGroupoid n K)
    (hy0 : (⟨K y0, ⟨y0, rfl⟩⟩ : Set.range (K : H'' → G)) ∈ chiRange.source)
    (hEqRange :
      Set.EqOn
        (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi z.1) chiRange.source) :
    ∃ chi : OpenPartialHomeomorph H'' H'',
      chi ∈ contDiffGroupoid n K ∧
      y0 ∈ chi.source ∧
      Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
  let eK : H'' ≃ₜ Set.range (K : H'' → G) := ex416_codomain_model_range_homeomorph (K := K)
  let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
    eK.symm.toOpenPartialHomeomorph
  let chi : OpenPartialHomeomorph H'' H'' :=
    (eRange.symm.trans chiRange).trans eRange
  have hchi_mem : chi ∈ contDiffGroupoid n K := by
    -- The transported range chart change already comes with the required groupoid membership.
    simpa [chi, eRange] using hchiRange_mem
  refine ⟨chi, hchi_mem, ?_, ?_⟩
  · -- The transported source membership is exactly the subtype source membership for `chiRange`.
    simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_source] using hy0
  · intro y hy
    have hyRange : (eK y : Set.range (K : H'' → G)) ∈ chiRange.source := by
      -- Read source membership for `chi` back across the transported range chart.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_source] using hy
    have htransport :
        eK (chi y) = chiRange (eK y) := by
      -- Conjugating by the range homeomorphism turns `chi` back into the subtype chart change.
      calc
        eK (chi y)
            = eK (eRange (chiRange (eRange.symm y))) := by
                rfl
        _ = chiRange (eRange.symm y) := by
              simp [eRange, eK]
        _ = chiRange (eK y) := by
              rfl
    calc
      K (chi y) = ((chiRange (eK y) : Set.range (K : H'' → G)).1) := by
        simpa [eK] using congrArg Subtype.val htransport
      _ = xi (K y) := by
        simpa [eK] using hEqRange hyRange

/-- Helper for Exercise 4.16: a point in the source of an extended coordinate change already maps
into the target of the second extended chart. -/
lemma comp_extendCoordChange_image_mem_target {e e' : OpenPartialHomeomorph N H'} {u : F}
    (hu : u ∈ (J.extendCoordChange e e').source) :
    J.extendCoordChange e e' u ∈ (e'.extend J).target := by
  -- Unfold the source condition just far enough to see that the second extended chart is legal.
  have hu_chart_source : (e.extend J).symm u ∈ e'.source := by
    simpa [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] using hu.2
  have hu_chart : (e.extend J).symm u ∈ (e'.extend J).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hu_chart_source
  -- Evaluating the second extended chart on that source point lands in its target.
  simpa [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply] using
    (e'.extend J).map_source hu_chart

/-- Helper for Exercise 4.16: at the composition basepoint, the middle coordinate change sends the
first-factor chart value into the target of `hg`'s extended domain chart. -/
lemma ex416_codomain_straightening_basepoint_first_coord_target {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      v0 ∈ (hg.domChart.extend J).target := by
  intro θ u0 v0 htheta_source0
  -- The generic coordinate-change target lemma applies directly to the basepoint input.
  simpa [θ, v0] using
    comp_extendCoordChange_image_mem_target
      (J := J) (e := hf.codChart) (e' := hg.domChart) htheta_source0

/-- Helper for Exercise 4.16: the codomain slice determined by the basepoint of the middle chart
already lands in the target of `hg`'s extended codomain chart. -/
lemma ex416_codomain_straightening_basepoint_slice_target {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      hg.equiv (v0, (0 : Fg)) ∈ (hg.codChart.extend K).target := by
  intro θ u0 v0 htheta_source0
  have hv0_target : v0 ∈ (hg.domChart.extend J).target := by
    -- First place the middle-chart output inside `hg`'s extended domain chart target.
    simpa [θ, u0, v0] using
      ex416_codomain_straightening_basepoint_first_coord_target
        (hg := hg) (hf := hf) (domChart0 := domChart0) htheta_source0
  -- Then apply the codomain immersion normal form for `g` to that codomain slice.
  exact hg.target_subset_preimage_target hv0_target

/-- Helper for Exercise 4.16: the codomain basepoint of `g ∘ f` already lies in the ambient model
range `Set.range K`, so the `range K` transport can start from the actual codomain chart value. -/
lemma ex416_codomain_chart_basepoint_mem_model_range {x : M} {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x)) :
    (hg.codChart.extend K) (g (f x)) ∈ Set.range (K : H'' → G) := by
  -- First record that the codomain-chart basepoint lies in the extended-chart target.
  have hz0_target :
      (hg.codChart.extend K) (g (f x)) ∈ (hg.codChart.extend K).target := by
    have hgf_source_ext : g (f x) ∈ (hg.codChart.extend K).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hg.mem_codChart_source
    exact (hg.codChart.extend K).map_source hgf_source_ext
  -- Reinterpret target membership as coming from an actual point of `H''`.
  rw [OpenPartialHomeomorph.extend_target'] at hz0_target
  rcases hz0_target with ⟨y, -, hy⟩
  exact ⟨y, hy⟩

/-- Helper for Exercise 4.16: any codomain slice whose first coordinate lies in the currently
chosen domain-chart target of `g` already lies in the ambient model range `Set.range K`. -/
lemma ex416_codomain_slice_mem_model_range {x : M} {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    {v : F} (hv : v ∈ (hg.domChart.extend J).target) :
    hg.equiv (v, (0 : Fg)) ∈ Set.range (K : H'' → G) := by
  -- The immersion normal form sends the chosen chart target into the codomain-chart target.
  have htarget :
      hg.equiv (v, (0 : Fg)) ∈ (hg.codChart.extend K).target :=
    hg.target_subset_preimage_target hv
  -- Reinterpret codomain-chart target membership as membership in the image of `K`.
  rw [OpenPartialHomeomorph.extend_target'] at htarget
  rcases htarget with ⟨y, -, hy⟩
  exact ⟨y, hy⟩

/-- Helper for Exercise 4.16: the conjugated model straightening `xi` acts on codomain slices by
the inverse middle chart change on the first factor. -/
lemma ex416_codomain_straightening_model_apply_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {v : F} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    xi (hg.equiv (v, (0 : Fg))) = hg.equiv (θ.symm v, (0 : Fg)) := by
  -- Unfold the conjugation and cancel the linear equivalence against its inverse.
  simp [ex416_middle_change_prod_chart, PartialEquiv.trans_apply]

/-- Helper for Exercise 4.16: once the straightened first coordinate still lies in the codomain
domain-chart target of `g`, the conjugated model straightening preserves the ambient model range on
that codomain slice. -/
lemma ex416_codomain_straightening_model_mem_range_of_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {v : F}
    (hv : (J.extendCoordChange hf.codChart hg.domChart).symm v ∈ (hg.domChart.extend J).target) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    xi (hg.equiv (v, (0 : Fg))) ∈ Set.range (K : H'' → G) := by
  -- Rewrite `xi` on the codomain slice, then use the ambient range lemma for `g`.
  dsimp
  simpa [ex416_middle_change_prod_chart] using
    (ex416_codomain_slice_mem_model_range (hg := hg)
      (v := (J.extendCoordChange hf.codChart hg.domChart).symm v) hv)

/-- Helper for Exercise 4.16: once the raw codomain basepoint is rewritten as the codomain slice
`hg.equiv (v0, 0)`, the remaining explicit source/target data already shows that this basepoint
lies in the source of the conjugated model straightening and in the codomain extended-chart
target. -/
lemma ex416_codomain_straightening_basepoint_source_data {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) := ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    let z0 : G := (hg.codChart.extend K) (g (f x))
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      z0 = hg.equiv (v0, (0 : Fg)) →
      z0 ∈ xi.source ∧ z0 ∈ (hg.codChart.extend K).target := by
  intro θ rho eG xi u0 v0 z0 htheta_source0 hz0_eq
  have hv0_theta_target : v0 ∈ θ.target := by
    -- The middle coordinate change sends source points to its own target by definition.
    simpa [v0] using θ.map_source htheta_source0
  have hv0_target : v0 ∈ (hg.domChart.extend J).target := by
    -- The first coordinate of the raw codomain slice is exactly the image of the middle chart
    -- change, so the generic coordinate-change target lemma applies.
    simpa [v0, θ] using
      comp_extendCoordChange_image_mem_target
        (J := J) (e := hf.codChart) (e' := hg.domChart) htheta_source0
  have hv0_rho_source : (v0, (0 : Fg)) ∈ rho.source := by
    -- The product straightening `rho` is defined exactly on points whose first coordinate lies in
    -- the target of the middle chart change.
    simpa [v0, θ, rho, ex416_middle_change_prod_chart] using hv0_theta_target
  constructor
  · -- Rewriting the raw codomain basepoint as `hg.equiv (v0, 0)` identifies it with a point in
    -- the source of the conjugated straightening `xi`.
    simpa [hz0_eq, xi, rho, eG, ex416_middle_change_prod_chart, PartialEquiv.trans_source] using
      hv0_rho_source
  · -- The actual codomain chart value at `g (f x)` is automatically in the extended-chart target.
    have hgf_source_ext : g (f x) ∈ (hg.codChart.extend K).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hg.mem_codChart_source
    simpa [z0] using (hg.codChart.extend K).map_source hgf_source_ext

/-- Helper for Exercise 4.16: at the composition basepoint, preserving the ambient model range
under the transported model straightening is reduced to the concrete overlap condition that the
`hf`-chart coordinate already lies in `hg`'s extended domain-chart target. -/
lemma ex416_codomain_straightening_basepoint_range_reduction {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) := ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    let z0 : G := (hg.codChart.extend K) (g (f x))
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      z0 = hg.equiv (v0, (0 : Fg)) →
      hf.equiv (u0, (0 : Ff)) ∈ (hg.domChart.extend J).target →
      xi z0 ∈ Set.range (K : H'' → G) := by
  intro θ rho eG xi u0 v0 z0 htheta_source0 hz0_eq hmid_target
  have htheta_symm_v0 :
      θ.symm v0 = hf.equiv (u0, (0 : Ff)) := by
    -- The inverse middle coordinate change recovers the original `hf`-chart coordinate.
    simpa [v0] using θ.left_inv htheta_source0
  have hv0_target :
      θ.symm v0 ∈ (hg.domChart.extend J).target := by
    -- Rewrite the needed overlap condition into the slice coordinates used by `xi`.
    simpa [htheta_symm_v0] using hmid_target
  -- With the overlap condition stated in the correct chart, the slice-range lemma applies.
  rw [hz0_eq]
  simpa [v0, θ, rho, eG, xi] using
    ex416_codomain_straightening_model_mem_range_of_slice
      (hg := hg) (hf := hf) (v := v0) hv0_target

/-- Helper for Exercise 4.16: once a new codomain chart around `(g ∘ f) x` is chosen, continuity of
`g ∘ f` lets us restrict a source chart around `x` so the whole restricted source lands in that new
codomain-chart source. -/
lemma ex416_exists_restr_chart_into_codomain_source {x : M}
    (hcont : ContinuousAt (g ∘ f) x) {domChart0 : OpenPartialHomeomorph M H}
    (hx_domChart0 : x ∈ domChart0.source)
    (hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I n M)
    {codChart1 : OpenPartialHomeomorph P H''}
    (hgf_codChart1 : g (f x) ∈ codChart1.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ domChart0.source ∧ V ⊆ (g ∘ f) ⁻¹' codChart1.source ∧
      x ∈ (domChart0.restr V).source ∧
      domChart0.restr V ∈ IsManifold.maximalAtlas I n M := by
  -- Intersect the old source chart with the preimage of the new codomain-chart source.
  have hdom_nhds : domChart0.source ∈ 𝓝 x :=
    IsOpen.mem_nhds domChart0.open_source hx_domChart0
  have hcod_nhds : codChart1.source ∈ 𝓝 (g (f x)) :=
    IsOpen.mem_nhds codChart1.open_source hgf_codChart1
  have hpre_nhds : domChart0.source ∩ (g ∘ f) ⁻¹' codChart1.source ∈ 𝓝 x := by
    exact Filter.inter_mem hdom_nhds (hcont.preimage_mem_nhds hcod_nhds)
  obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp hpre_nhds
  refine ⟨V, hV_open, hxV, fun y hy ↦ (hV_sub hy).1, fun y hy ↦ (hV_sub hy).2, ?_, ?_⟩
  · -- The restricted chart still contains the base point.
    simpa [OpenPartialHomeomorph.restr_source, hV_open.interior_eq] using
      show x ∈ domChart0.source ∩ V from ⟨hx_domChart0, hxV⟩
  · -- Restricting a maximal-atlas chart to an open neighborhood stays in the maximal atlas.
    simpa using
      restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart0_mem hV_open

/-- Helper for Exercise 4.16: once the codomain-model straightening has been transported to a local
chart change `chi` on `H''`, postcomposing `hg.codChart` with `chi` gives the codomain chart
package consumed by the final restriction lemmas. -/
lemma ex416_transported_codomain_chart_package {x : M} {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    {xi : G → G}
    (hchi :
      ∃ chi : OpenPartialHomeomorph H'' H'',
        chi ∈ contDiffGroupoid n K ∧
        hg.codChart (g (f x)) ∈ chi.source ∧
        Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source) :
    ∃ codChart1 : OpenPartialHomeomorph P H'',
      g (f x) ∈ codChart1.source ∧
      codChart1 ∈ IsManifold.maximalAtlas K n P ∧
      Set.EqOn
        (fun p ↦ (codChart1.extend K) p)
        (fun p ↦ xi ((hg.codChart.extend K) p))
        codChart1.source := by
  rcases hchi with ⟨chi, hchi_mem, hchi_base, hchi_eq⟩
  let codChart1 : OpenPartialHomeomorph P H'' := hg.codChart.trans chi
  refine ⟨codChart1, ?_, ?_, ?_⟩
  · -- The transported codomain chart still contains the base point of `g ∘ f`.
    exact ⟨hg.mem_codChart_source, hchi_base⟩
  · -- Postcomposing with a smooth model-space chart change preserves maximal-atlas membership.
    exact trans_mem_maximalAtlas_of_mem_groupoid
      (he := hg.codChart_mem_maximalAtlas) hchi_mem
  · intro p hp
    -- Unfold the transported extended chart and rewrite the new codomain factor using `hchi_eq`.
    have hp_cod : p ∈ hg.codChart.source := hp.1
    have hp_chi : hg.codChart p ∈ chi.source := hp.2
    calc
      (codChart1.extend K) p = K (chi (hg.codChart p)) := by
        simp [codChart1, OpenPartialHomeomorph.extend_coe, Function.comp, hp_cod, hp_chi]
      _ = xi (K (hg.codChart p)) := hchi_eq hp_chi
      _ = xi ((hg.codChart.extend K) p) := by
        simp [OpenPartialHomeomorph.extend_coe, hp_cod]

/-- Helper for Exercise 4.16: once a transported codomain chart is known and its extended chart
agrees with the model-space straightening `xi` on the whole chart source, continuity of `g ∘ f`
provides the final source restriction needed by the composition proof. -/
lemma ex416_final_transport_from_chart_extend_eq {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    {domChart0 : OpenPartialHomeomorph M H}
    (hcont : ContinuousAt (g ∘ f) x)
    (hx_domChart0 : x ∈ domChart0.source)
    (hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I n M)
    {xi : G → G}
    {codChart1 : OpenPartialHomeomorph P H''}
    (hgf_codChart1 : g (f x) ∈ codChart1.source)
    (hcodChart1 :
      Set.EqOn
        (fun p ↦ (codChart1.extend K) p)
        (fun p ↦ xi ((hg.codChart.extend K) p))
        codChart1.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ domChart0.source ∧
      Set.EqOn
        (((codChart1.extend K) ∘ g ∘ f ∘ ((domChart0.restr V).extend I).symm))
        (fun u ↦ xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u))
        ((domChart0.restr V).extend I).target := by
  -- First shrink the source chart so the whole restricted neighborhood lands in `codChart1.source`.
  rcases ex416_exists_restr_chart_into_codomain_source
      (hcont := hcont) (domChart0 := domChart0) hx_domChart0 hdomChart0_mem hgf_codChart1 with
    ⟨V, hV_open, hxV, hV_dom, hV_cod, -, -⟩
  refine ⟨V, hV_open, hxV, hV_dom, ?_⟩
  intro u hu
  -- Read the restricted target point back to the source so the codomain-chart hypothesis applies.
  have hu_restr_source :
      ((domChart0.restr V).extend I).symm u ∈ (domChart0.restr V).source := by
    simpa [OpenPartialHomeomorph.extend_source] using
      ((domChart0.restr V).extend I).map_target hu
  have hu_mem_V :
      ((domChart0.restr V).extend I).symm u ∈ V := by
    have hu_restr_source' :
        ((domChart0.restr V).extend I).symm u ∈ domChart0.source ∩ V := by
      simpa [OpenPartialHomeomorph.restr_source, hV_open.interior_eq] using hu_restr_source
    exact hu_restr_source'.2
  have hgf_source :
      g (f (((domChart0.restr V).extend I).symm u)) ∈ codChart1.source :=
    hV_cod hu_mem_V
  have hu_symm_eq :
      ((domChart0.restr V).extend I).symm u = (domChart0.extend I).symm u := by
    -- The restricted extended-chart inverse agrees with the original one on the restricted target.
    exact ex416_restr_extend_symm_eq_of_openPartialHomeomorph
      (I := I) (e := domChart0) (U := V) hV_open hu
  -- Rewrite the new codomain chart using `hcodChart1`, then replace the restricted inverse.
  simpa [Function.comp, hu_symm_eq] using hcodChart1 hgf_source

/-- Helper for Exercise 4.16: once a transported codomain chart is available on a final restricted
source chart, the remaining written-in-charts argument is exactly `hxi_raw` plus the linear
reassociation `equivTot`. -/
lemma ex416_straightened_writtenInCharts_on_final_restr {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x)
    {domChart0 : OpenPartialHomeomorph M H}
    (hx_domChart0 : x ∈ domChart0.source)
    (hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I n M)
    {xi : G → G}
    (hxi_raw :
      Set.EqOn
        (fun u ↦ xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u))
        (fun u ↦ hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)))
        (domChart0.extend I).target)
    {codChart1 : OpenPartialHomeomorph P H''}
    (hgf_codChart1 : g (f x) ∈ codChart1.source)
    (hcodChart1_mem : codChart1 ∈ IsManifold.maximalAtlas K n P)
    {V : Set M} (hV_open : IsOpen V) (hxV : x ∈ V) (hV_dom : V ⊆ domChart0.source)
    (htransport :
      Set.EqOn
        (((codChart1.extend K) ∘ g ∘ f ∘ ((domChart0.restr V).extend I).symm))
        (fun u ↦ xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u))
        ((domChart0.restr V).extend I).target) :
    IsImmersionAtOfComplement (Ff × Fg) I K n (g ∘ f) x := by
  let assocEquiv : (E × (Ff × Fg)) ≃L[𝕜] ((E × Ff) × Fg) :=
    (LinearIsometryEquiv.prodAssoc 𝕜 E Ff Fg).symm.toContinuousLinearEquiv
  let equivTot : (E × (Ff × Fg)) ≃L[𝕜] G :=
    assocEquiv.trans ((hf.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 Fg)).trans hg.equiv)
  let domChart1 := domChart0.restr V
  have hx_domChart1 : x ∈ domChart1.source := by
    -- The final restriction still contains `x` by construction.
    simpa [domChart1, OpenPartialHomeomorph.restr_source, hV_open.interior_eq] using
      show x ∈ domChart0.source ∩ V from ⟨hx_domChart0, hxV⟩
  have hdomChart1_mem : domChart1 ∈ IsManifold.maximalAtlas I n M := by
    -- Restricting the source chart preserves maximal-atlas membership.
    simpa [domChart1] using
      restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart0_mem hV_open
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (hg.ex416_continuousAt.comp hf.ex416_continuousAt) equivTot domChart1 codChart1
    hx_domChart1 hgf_codChart1 hdomChart1_mem hcodChart1_mem ?_
  intro u hu
  have hu_domChart0 :
      u ∈ (domChart0.extend I).target := by
    -- The final restricted target still lies in the earlier restricted target from `hxi_raw`.
    simpa [domChart1] using
      ex416_restr_extend_target_mem_of_openPartialHomeomorph
        (I := I) (e := domChart0) (U := V) hV_open hu
  -- First transport the new codomain chart expression back to `xi`, then invoke `hxi_raw`.
  calc
    ((codChart1.extend K) ∘ g ∘ f ∘ (domChart1.extend I).symm) u
        = xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u) := by
            simpa [domChart1] using htransport hu
    _ = hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)) := hxi_raw hu_domChart0
    _ = equivTot (u, (0 : Ff × Fg)) := by
          simp [equivTot, assocEquiv]

/-- Helper for Exercise 4.16: rewriting `g` in the restricted source chart coming from `hf`
produces the raw middle-chart expression `hg.equiv (θ v, 0)`. -/
lemma ex416_aligned_source_change_raw {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x)
    {W : Set N} (hW_open : IsOpen W)
    (hW_sub : W ⊆ hf.codChart.source ∩ hg.domChart.source) :
    Set.EqOn
      (((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm))
      (fun v ↦ hg.equiv (J.extendCoordChange hf.codChart hg.domChart v, (0 : Fg)))
      ((hf.codChart.restr W).extend J).target := by
  intro v hv
  -- Read the restricted target point back to the actual source point in `W`.
  let y : N := ((hf.codChart.restr W).extend J).symm v
  have hy_restr_source : y ∈ (hf.codChart.restr W).source := by
    simpa [y, OpenPartialHomeomorph.extend_source] using
      ((hf.codChart.restr W).extend J).map_target hv
  have hy_sourceW : y ∈ hf.codChart.source ∩ W := by
    have hy_restr_source' := hy_restr_source
    rw [hf.codChart.restr_source' W hW_open] at hy_restr_source'
    simpa [y] using hy_restr_source'
  have hy_hg_source : y ∈ hg.domChart.source := (hW_sub hy_sourceW.2).2
  have hy_hg_source_ext : y ∈ (hg.domChart.extend J).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hy_hg_source
  have hy_restr_value :
      ((hf.codChart.restr W).extend J) y = v := by
    simpa [y] using ((hf.codChart.restr W).extend J).right_inv hv
  have hy_chart_value :
      (hf.codChart.extend J) y = v := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp, hy_restr_source, hy_sourceW.1] using
      hy_restr_value
  have hy_symm :
      (hf.codChart.extend J).symm v = y := by
    -- The restricted and unrestricted chart inverses agree on the restricted target.
    simpa [y] using
      (ex416_restr_extend_symm_eq_of_openPartialHomeomorph
        (I := J) (e := hf.codChart) (U := W) hW_open hv).symm
  have hv_theta :
      J.extendCoordChange hf.codChart hg.domChart v = (hg.domChart.extend J) y := by
    -- Rewrite the coordinate change back through the actual overlap point `y`.
    simpa [ModelWithCorners.extendCoordChange] using congrArg (hg.domChart.extend J) hy_symm
  calc
    ((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v
        = ((hg.codChart.extend K) ∘ g) y := by
            simp [Function.comp, y]
    _ = ((hg.codChart.extend K) ∘ g ∘ (hg.domChart.extend J).symm) ((hg.domChart.extend J) y) := by
          -- Insert `hg.domChart.extend` and its inverse at the actual overlap point.
          simpa [Function.comp] using congrArg ((hg.codChart.extend K) ∘ g)
            ((hg.domChart.extend J).left_inv hy_hg_source_ext).symm
    _ = hg.equiv ((hg.domChart.extend J) y, (0 : Fg)) := by
          -- `hg` already has the standard inclusion form in its own source chart.
          simpa [Function.comp] using hg.writtenInCharts ((hg.domChart.extend J).map_source hy_hg_source_ext)
    _ = hg.equiv (J.extendCoordChange hf.codChart hg.domChart v, (0 : Fg)) := by
          rw [hv_theta]

/-- Helper for Exercise 4.16: the conjugated model straightening `xi` already cancels the raw
middle-chart term on the restricted source chart coming from `hf`. -/
lemma ex416_aligned_codomain_straightening_on_restr {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x)
    {W : Set N} (hW_open : IsOpen W)
    (hW_sub : W ⊆ hf.codChart.source ∩ hg.domChart.source) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      ex416_middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    Set.EqOn
      (fun v ↦ xi (((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v))
      (fun v ↦ hg.equiv (v, (0 : Fg)))
      ((hf.codChart.restr W).extend J).target := by
  dsimp
  intro v hv
  let θ : PartialEquiv F F := J.extendCoordChange hf.codChart hg.domChart
  let rho : PartialEquiv (F × Fg) (F × Fg) := ex416_middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
  change
    xi (((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v) =
      hg.equiv (v, (0 : Fg))
  -- First rewrite `g` in the restricted source chart of `hf`.
  have hraw :
      ((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v =
        hg.equiv (θ v, (0 : Fg)) := by
    simpa [θ] using
      ex416_aligned_source_change_raw (hg := hg) (hf := hf) (W := W) hW_open hW_sub hv
  let y : N := ((hf.codChart.restr W).extend J).symm v
  have hy_restr_source : y ∈ (hf.codChart.restr W).source := by
    simpa [y, OpenPartialHomeomorph.extend_source] using
      ((hf.codChart.restr W).extend J).map_target hv
  have hy_sourceW : y ∈ hf.codChart.source ∩ W := by
    have hy_restr_source' := hy_restr_source
    rw [hf.codChart.restr_source' W hW_open] at hy_restr_source'
    simpa [y] using hy_restr_source'
  have hy_hg_source : y ∈ hg.domChart.source := (hW_sub hy_sourceW.2).2
  have hy_chart_value :
      (hf.codChart.extend J) y = v := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp, hy_restr_source, hy_sourceW.1] using
      ((hf.codChart.restr W).extend J).right_inv hv
  have hv_theta_source :
      v ∈ θ.source := by
    -- The actual overlap point `y` lies in both middle charts, so its `hf`-coordinate lies in
    -- the source of the middle coordinate change.
    rw [← OpenPartialHomeomorph.extend_image_source_inter (I := J)
      (f := hf.codChart) (f' := hg.domChart)]
    exact ⟨y, ⟨hy_sourceW.1, hy_hg_source⟩, hy_chart_value⟩
  -- After the source-membership bookkeeping, `xi` cancels `θ` on the first factor.
  calc
    xi (((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v)
        = xi (hg.equiv (θ v, (0 : Fg))) := by
            rw [hraw]
    _ = hg.equiv (θ.symm (θ v), (0 : Fg)) := by
          simpa [xi, rho, eG, θ, ex416_middle_change_prod_chart] using
            (ex416_codomain_straightening_model_apply_slice
              (hg := hg) (hf := hf) (v := θ v))
    _ = hg.equiv (v, (0 : Fg)) := by
          rw [(show θ.symm (θ v) = v from θ.left_inv hv_theta_source)]

/-- Helper for Exercise 4.16: align the source chart of `g` with the codomain chart of `hf`
before composing the two standard inclusion formulas. -/
lemma ex416_exists_aligned_codomain_chart_for_g {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) :
    ∃ W : Set N, IsOpen W ∧ f x ∈ W ∧ W ⊆ hf.codChart.source ∩ hg.domChart.source ∧
      ∃ codChart1 : OpenPartialHomeomorph P H'',
        g (f x) ∈ codChart1.source ∧
        codChart1 ∈ IsManifold.maximalAtlas K n P ∧
        Set.EqOn
          (((codChart1.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm))
          (fun v ↦ hg.equiv (v, (0 : Fg)))
          ((hf.codChart.restr W).extend J).target := by
  -- Route correction: the right structural step is to rewrite `g` using the source chart supplied
  -- by `hf`, then transport the resulting model-space straightening through `K`.
  let rho : PartialEquiv (F × Fg) (F × Fg) := ex416_middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
  have hxi_cont :
      ContDiffOn 𝕜 n xi xi.source ∧ ContDiffOn 𝕜 n xi.symm xi.target := by
    -- This is the analytic input for the remaining transport through `K`.
    simpa [xi, rho, eG] using
      ex416_codomain_straightening_model_contDiff (hg := hg) (hf := hf)
  have hchi :
      ∃ chi : OpenPartialHomeomorph H'' H'',
        chi ∈ contDiffGroupoid n K ∧
        hg.codChart (g (f x)) ∈ chi.source ∧
        Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
    let z0 : G := (hg.codChart.extend K) (g (f x))
    let z0Range : Set.range (K : H'' → G) :=
      ⟨z0, ex416_codomain_chart_basepoint_mem_model_range (hg := hg)⟩
    have hrange :
        ∃ chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)),
          let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
            (ex416_codomain_model_range_homeomorph (K := K)).symm.toOpenPartialHomeomorph
          ((eRange.symm.trans chiRange).trans eRange) ∈ contDiffGroupoid n K ∧
            z0Range ∈ chiRange.source ∧
            Set.EqOn
              (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
              (fun z ↦ xi z.1) chiRange.source := by
      -- TODO: construct the subtype-level straightening on `Set.range K` near `z0Range`
      -- directly in the subtype topology; its transported groupoid membership should then be
      -- obtained from the singleton-chart `PartialDiffeomorph` packaging.
      sorry
    rcases hrange with ⟨chiRange, hchiRange_mem, hz0Range, hEqRange⟩
    -- The remaining transport back to `H''` is now isolated in a reusable packaging lemma.
    exact ex416_writtenIn_range_straightening_to_chart_change
      (K := K) (n := n) (xi := xi) (y0 := hg.codChart (g (f x))) (chiRange := chiRange)
      hchiRange_mem
      (by simpa [z0, z0Range] using hz0Range)
      hEqRange
  rcases ex416_transported_codomain_chart_package (hg := hg) (xi := xi) hchi with
    ⟨codChart1, hgf_codChart1, hcodChart1_mem, hcodChart1_eq⟩
  have hfx_overlap :
      f x ∈ hf.codChart.source ∩ hg.domChart.source := by
    exact ⟨hf.mem_codChart_source, hg.mem_domChart_source⟩
  have hoverlap_nhds :
      hf.codChart.source ∩ hg.domChart.source ∈ 𝓝 (f x) := by
    exact IsOpen.mem_nhds (hf.codChart.open_source.inter hg.domChart.open_source) hfx_overlap
  have hcod_nhds : codChart1.source ∈ 𝓝 (g (f x)) :=
    IsOpen.mem_nhds codChart1.open_source hgf_codChart1
  have hpre_nhds :
      hf.codChart.source ∩ hg.domChart.source ∩ g ⁻¹' codChart1.source ∈ 𝓝 (f x) := by
    exact Filter.inter_mem hoverlap_nhds (hg.ex416_continuousAt.preimage_mem_nhds hcod_nhds)
  obtain ⟨W, hW_sub, hW_open, hfxW⟩ := mem_nhds_iff.mp hpre_nhds
  refine ⟨W, hW_open, hfxW, ?_, codChart1, hgf_codChart1, hcodChart1_mem, ?_⟩
  · intro y hy
    exact (hW_sub hy).1
  · have hxi_raw :
        Set.EqOn
          (fun v ↦ xi (((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v))
          (fun v ↦ hg.equiv (v, (0 : Fg)))
          ((hf.codChart.restr W).extend J).target := by
      -- The overlap rewrite for `g` plus the model-space straightening already gives the target
      -- normal form before transporting `xi` back through `K`.
      exact ex416_aligned_codomain_straightening_on_restr
        (hg := hg) (hf := hf) (W := W) hW_open (fun y hy ↦ (hW_sub hy).1)
    intro v hv
    let y : N := ((hf.codChart.restr W).extend J).symm v
    have hy_restr_source : y ∈ (hf.codChart.restr W).source := by
      simpa [y, OpenPartialHomeomorph.extend_source] using
        ((hf.codChart.restr W).extend J).map_target hv
    have hyW : y ∈ W := by
      have hy_pair : y ∈ hf.codChart.source ∩ W := by
        have hy_restr_source' := hy_restr_source
        rw [hf.codChart.restr_source' W hW_open] at hy_restr_source'
        simpa [y] using hy_restr_source'
      exact hy_pair.2
    have hgy_cod : g y ∈ codChart1.source := (hW_sub hyW).2
    -- The final aligned formula is obtained by first rewriting `codChart1` via `xi`, then using
    -- the already-proved `xi`-straightened expression.
    calc
      ((codChart1.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v
          = xi (((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v) := by
              simpa [Function.comp, y] using hcodChart1_eq hgy_cod
      _ = hg.equiv (v, (0 : Fg)) := hxi_raw hv

/-- Helper for Exercise 4.16: if `f` and `g` are immersions at compatible points with fixed
complements, then `g ∘ f` is an immersion at the source point with the product complement. -/
theorem ex416_comp {x : M} {Ff : Type*} [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff]
    {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K n g (f x))
    (hf : IsImmersionAtOfComplement Ff I J n f x) :
    IsImmersionAtOfComplement (Ff × Fg) I K n (g ∘ f) x := by
  -- Route correction: instead of transporting the old codomain straightening through `range K`,
  -- first rewrite `g` in the source chart coming from `hf`, then compose the two inclusion forms.
  have hcont : ContinuousAt (g ∘ f) x := hg.ex416_continuousAt.comp hf.ex416_continuousAt
  rcases ex416_exists_aligned_codomain_chart_for_g (hg := hg) (hf := hf) with
    ⟨W, hW_open, hfxW, hW_sub, codChart1, hgf_codChart1, hcodChart1_mem, haligned⟩
  have hdom_nhds : hf.domChart.source ∈ 𝓝 x :=
    IsOpen.mem_nhds hf.domChart.open_source hf.mem_domChart_source
  have hW_nhds : W ∈ 𝓝 (f x) :=
    IsOpen.mem_nhds hW_open hfxW
  have hpre_nhds : hf.domChart.source ∩ f ⁻¹' W ∈ 𝓝 x := by
    -- Restrict to a neighborhood where `hf` uses its chosen source chart and `f` lands in the
    -- aligned source chart for `g`.
    exact Filter.inter_mem hdom_nhds (hf.ex416_continuousAt.preimage_mem_nhds hW_nhds)
  obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp hpre_nhds
  have hV_dom : V ⊆ hf.domChart.source := fun y hy ↦ (hV_sub hy).1
  have hV_map : V ⊆ f ⁻¹' W := fun y hy ↦ (hV_sub hy).2
  let domChart0 := hf.domChart.restr V
  have hx_domChart0 : x ∈ domChart0.source := by
    -- The final restricted source chart still contains the base point.
    have hx_domChart0' : x ∈ hf.domChart.source ∩ interior V := by
      exact ⟨hf.mem_domChart_source, by simpa [hV_open.interior_eq] using hxV⟩
    simpa [domChart0, OpenPartialHomeomorph.restr] using hx_domChart0'
  have hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I n M := by
    -- Restricting the source chart preserves maximal-atlas membership.
    simpa [domChart0] using
      restr_mem_maximalAtlas (contDiffGroupoid n I) hf.domChart_mem_maximalAtlas hV_open
  let assocEquiv : (E × (Ff × Fg)) ≃L[𝕜] ((E × Ff) × Fg) :=
    (LinearIsometryEquiv.prodAssoc 𝕜 E Ff Fg).symm.toContinuousLinearEquiv
  let equivTot : (E × (Ff × Fg)) ≃L[𝕜] G :=
    assocEquiv.trans ((hf.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 Fg)).trans hg.equiv)
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    hcont equivTot domChart0 codChart1 hx_domChart0 hgf_codChart1 hdomChart0_mem hcodChart1_mem ?_
  intro u hu
  have hu_target : u ∈ (hf.domChart.extend I).target := by
    -- The final restricted target still lies in the original source-chart target of `hf`.
    simpa [domChart0] using ex416_restr_extend_target_mem (hf := hf) (U := V) hV_open hu
  have hu_symm_eq :
      (domChart0.extend I).symm u = (hf.domChart.extend I).symm u := by
    -- On the restricted target, the restricted inverse agrees with the original one.
    simpa [domChart0] using ex416_restr_extend_symm_eq (hf := hf) (U := V) hV_open hu
  have hu_dom_source :
      (domChart0.extend I).symm u ∈ domChart0.source := by
    simpa [OpenPartialHomeomorph.extend_source] using (domChart0.extend I).map_target hu
  have hu_dom_source' :
      (domChart0.extend I).symm u ∈ hf.domChart.source ∩ V := by
    simpa [domChart0, OpenPartialHomeomorph.restr_source, hV_open.interior_eq] using hu_dom_source
  have hfyW : f ((domChart0.extend I).symm u) ∈ W :=
    hV_map hu_dom_source'.2
  have hfy_hfsource :
      f ((domChart0.extend I).symm u) ∈ hf.codChart.source :=
    (hW_sub hfyW).1
  have hfy_restr_source :
      f ((domChart0.extend I).symm u) ∈ (hf.codChart.restr W).source := by
    rw [hf.codChart.restr_source' W hW_open]
    exact ⟨hfy_hfsource, hfyW⟩
  have hfy_restr_source_ext :
      f ((domChart0.extend I).symm u) ∈ ((hf.codChart.restr W).extend J).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hfy_restr_source
  have hrestr_eval :
      ((hf.codChart.restr W).extend J) (f ((domChart0.extend I).symm u)) =
        (hf.codChart.extend J) (f ((domChart0.extend I).symm u)) := by
    -- On points mapping into `W`, the restricted codomain chart agrees with the original chart.
    simp [OpenPartialHomeomorph.extend_coe, Function.comp, hfy_restr_source, hfy_hfsource]
  have hv_eq :
      hf.equiv (u, (0 : Ff)) =
        ((hf.codChart.restr W).extend J) (f ((domChart0.extend I).symm u)) := by
    -- Rewrite `hf` in the final restricted source chart, then replace the codomain chart by its
    -- restriction to `W`.
    calc
      hf.equiv (u, (0 : Ff))
          = (hf.codChart.extend J) (f ((hf.domChart.extend I).symm u)) := by
              simpa [Function.comp] using (hf.writtenInCharts hu_target).symm
      _ = (hf.codChart.extend J) (f ((domChart0.extend I).symm u)) := by
            rw [hu_symm_eq]
      _ = ((hf.codChart.restr W).extend J) (f ((domChart0.extend I).symm u)) := by
            rw [hrestr_eval]
  have hv_target :
      hf.equiv (u, (0 : Ff)) ∈ ((hf.codChart.restr W).extend J).target := by
    -- The aligned source chart for `g` sees the `hf`-coordinates as an actual chart value.
    have hv_target' :
        ((hf.codChart.restr W).extend J) (f ((domChart0.extend I).symm u)) ∈
          ((hf.codChart.restr W).extend J).target :=
      ((hf.codChart.restr W).extend J).map_source hfy_restr_source_ext
    exact hv_eq.symm ▸ hv_target'
  have hleft_inv :
      ((hf.codChart.restr W).extend J).symm (hf.equiv (u, (0 : Ff))) =
        f ((domChart0.extend I).symm u) := by
    -- Applying the restricted chart inverse to its own chart value recovers the actual point.
    calc
      ((hf.codChart.restr W).extend J).symm (hf.equiv (u, (0 : Ff)))
          = ((hf.codChart.restr W).extend J).symm
              (((hf.codChart.restr W).extend J) (f ((domChart0.extend I).symm u))) := by
                rw [hv_eq]
      _ = f ((domChart0.extend I).symm u) :=
            ((hf.codChart.restr W).extend J).left_inv hfy_restr_source_ext
  -- Compose the aligned chart formula for `g` with the written-in-charts identity for `hf`.
  calc
    ((codChart1.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u
        = ((codChart1.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm)
            (hf.equiv (u, (0 : Ff))) := by
              simpa [Function.comp] using
                congrArg ((codChart1.extend K) ∘ g) hleft_inv.symm
    _ = hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)) := haligned hv_target
    _ = equivTot (u, (0 : Ff × Fg)) := by
          simp [equivTot, assocEquiv]

end IsImmersionAtOfComplement

namespace IsImmersionAt

/-- Helper for Exercise 4.16: forgetting the explicit complement preserves the pointwise
continuity consequence of immersion. -/
lemma continuousAt {x : M} (h : IsImmersionAt I J n f x) :
    ContinuousAt f x :=
  IsImmersionAtOfComplement.ex416_continuousAt h.isImmersionAtOfComplement_complement

end IsImmersionAt

namespace IsImmersion

/-- Helper for Exercise 4.16: composition preserves immersions once the pointwise fixed-complement
normal forms are composed. -/
theorem ex416_comp (hg : IsImmersion J K n g) (hf : IsImmersion I J n f) :
    IsImmersion I K n (g ∘ f) := by
  -- Fix the global complements already supplied by the two immersion hypotheses.
  let hgf : IsImmersionOfComplement (hf.complement × hg.complement) I K n (g ∘ f) := by
    intro x
    -- At each point, compose the chosen local normal forms with the product complement.
    exact IsImmersionAtOfComplement.ex416_comp
      ((hg.isImmersionOfComplement_complement) (f x))
      ((hf.isImmersionOfComplement_complement) x)
  -- Then forget the explicit complement to recover the owner-level immersion statement.
  exact hgf.isImmersion

end IsImmersion

namespace IsSmoothEmbedding

/-- Helper for Exercise 4.16: once the immersion field of `g ∘ f` is known, the composition is a
smooth embedding by composing the topological embeddings. -/
lemma mk_comp_of_isImmersion
    (hgf : IsImmersion I K n (g ∘ f))
    (hg : IsSmoothEmbedding J K n g) (hf : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I K n (g ∘ f) := by
  -- Smooth embeddings split into an immersion field and a topological embedding field.
  refine ⟨hgf, ?_⟩
  -- The global embedding component is already closed under composition.
  exact hg.isEmbedding.comp hf.isEmbedding

/-- Exercise 4.16: the composition of two `C^n` smooth embeddings is again a smooth embedding. -/
theorem comp (hg : IsSmoothEmbedding J K n g) (hf : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I K n (g ∘ f) := by
  -- Reduce the goal to the single missing immersion-composition input.
  refine mk_comp_of_isImmersion ?_ hg hf
  -- The immersion field now follows from the fixed-complement composition helper above.
  simpa using Manifold.IsImmersion.ex416_comp hg.isImmersion hf.isImmersion

end IsSmoothEmbedding

end

end Manifold
