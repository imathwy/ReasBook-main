import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uF uG uH uH' uH'' uM uN uP

namespace Manifold

section Composition

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
variable {K : ModelWithCorners 𝕜 G H''}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
variable {f : M → N} {g : N → P}

namespace IsSmoothSubmersion

/-- Exercise 4.4 (1): the composition of two smooth submersions is again a smooth submersion. -/
-- Proof sketch: combine the smoothness parts by the chain rule, then compose the local smooth
-- sections furnished by the two submersion hypotheses near each point.
theorem comp (hg : IsSmoothSubmersion J K g) (hf : IsSmoothSubmersion I J f) :
    IsSmoothSubmersion I K (g ∘ f) := by
  -- Combine the smoothness fields, then compose the surjective derivatives pointwise.
  refine ⟨hg.contMDiff.comp hf.contMDiff, ?_⟩
  intro x
  have hmdiff_g : MDifferentiableAt J K g (f x) := by
    exact hg.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmdiff_f : MDifferentiableAt I J f x := by
    exact hf.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [mfderiv_comp x hmdiff_g hmdiff_f]
  simpa using (hg.surjective_mfderiv (f x)).comp (hf.surjective_mfderiv x)

end IsSmoothSubmersion

namespace IsImmersionAtOfComplement

/-- Helper for Exercise 4.4: postcomposing a chart already in the smooth maximal atlas with a
smooth model-space self-chart change stays in the same maximal atlas. -/
lemma trans_mem_maximalAtlas_of_mem_groupoid_infty
    {e : OpenPartialHomeomorph P H''}
    (he : e ∈ IsManifold.maximalAtlas K ∞ P)
    {chi : OpenPartialHomeomorph H'' H''}
    (hchi : chi ∈ contDiffGroupoid ∞ K) :
    e.trans chi ∈ IsManifold.maximalAtlas K ∞ P := by
  -- Membership in the maximal atlas is tested by compatibility with the original atlas.
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas K ∞ P := by
    exact IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid ∞ K := by
    -- The old transition from `e` to any atlas chart is already smooth.
    exact IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid ∞ K := by
    -- Likewise for the reverse transition.
    exact IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · -- The new left transition factors through `chi.symm` and the old transition from `e`.
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ∞ K).trans ((contDiffGroupoid ∞ K).symm hchi) hleft
  · -- The new right transition factors through the old transition followed by `chi`.
    have hright' : (e'.symm.trans e).trans chi ∈ contDiffGroupoid ∞ K := by
      exact (contDiffGroupoid ∞ K).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Helper for Exercise 4.4: an immersion at a point is continuous at that point, since in
compatible charts it agrees near the point with the continuous standard inclusion
`u ↦ (u, 0)`. -/
lemma continuousAt {x : M} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (h : IsImmersionAtOfComplement F' I J ∞ f x) :
    ContinuousAt f x := by
  -- Work on the source-chart neighborhood where the normal form for the immersion is valid.
  have hdomChart_source : h.domChart.source ∈ nhds x :=
    IsOpen.mem_nhds h.domChart.open_source h.mem_domChart_source
  have hsource : f ⁻¹' h.codChart.source ∈ nhds x :=
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
      ((h.codChart.extend J) ∘ f) =ᶠ[nhds x]
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
    -- The chart map itself is recovered from the extended chart by composing with `J.symm`.
    convert J.continuousAt_symm.comp hcont_extend using 1
    funext y
    simp [Function.comp]
  -- Translate continuity of the chart expression back to continuity of `f`.
  exact (h.codChart.continuousAt_iff_continuousAt_comp_left hsource).2 hcont_chart

/-- Helper for Exercise 4.4: once the middle chart of `g` is aligned with the codomain chart of
`f`, the pointwise immersion normal forms should compose to a normal form for `g ∘ f` with
product complement. -/
theorem comp_of_shared_middle_chart {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    (hshared : hg.domChart = hf.codChart) :
    IsImmersionAtOfComplement (Ff × Fg) I K ∞ (g ∘ f) x := by
  -- Combine pointwise continuity first so the constructor can ignore source-to-target bookkeeping.
  have hcont : ContinuousAt (g ∘ f) x := hg.continuousAt.comp hf.continuousAt
  let assocEquiv : (E × (Ff × Fg)) ≃L[𝕜] ((E × Ff) × Fg) :=
    (LinearIsometryEquiv.prodAssoc 𝕜 E Ff Fg).symm.toContinuousLinearEquiv
  let composedEquiv : (E × (Ff × Fg)) ≃L[𝕜] G :=
    assocEquiv.trans ((hf.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 Fg)).trans hg.equiv)
  refine IsImmersionAtOfComplement.mk_of_continuousAt hcont composedEquiv hf.domChart hg.codChart
    hf.mem_domChart_source hg.mem_codChart_source hf.domChart_mem_maximalAtlas
    hg.codChart_mem_maximalAtlas ?_
  intro u hu
  -- Rewrite `f` into the shared middle chart and then apply the normal form for `g`.
  have hu_source :
      (hf.domChart.extend I).symm u ∈ hf.domChart.source := by
    simpa [OpenPartialHomeomorph.extend_source] using (hf.domChart.extend I).map_target hu
  have hfu_source :
      f ((hf.domChart.extend I).symm u) ∈ hf.codChart.source :=
    hf.source_subset_preimage_source hu_source
  have hfu_extend_source :
      f ((hf.domChart.extend I).symm u) ∈ (hf.codChart.extend J).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hfu_source
  have hmid :
      f ((hf.domChart.extend I).symm u) =
        ((hg.domChart.extend J).symm) (hf.equiv (u, (0 : Ff))) := by
    calc
      f ((hf.domChart.extend I).symm u)
          = ((hf.codChart.extend J).symm)
              (((hf.codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u) := by
              rw [Function.comp_apply, Function.comp_apply]
              symm
              exact (hf.codChart.extend J).left_inv hfu_extend_source
      _ = ((hf.codChart.extend J).symm) (hf.equiv (u, (0 : Ff))) := by
            simpa [Function.comp] using
              congrArg ((hf.codChart.extend J).symm) (hf.writtenInCharts hu)
      _ = ((hg.domChart.extend J).symm) (hf.equiv (u, (0 : Ff))) := by
            simp [hshared]
  have hfu_target :
      hf.equiv (u, (0 : Ff)) ∈ (hg.domChart.extend J).target := by
    simpa [hshared] using hf.target_subset_preimage_target hu
  calc
    ((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u
        = ((hg.codChart.extend K) ∘ g ∘ (hg.domChart.extend J).symm)
            (hf.equiv (u, (0 : Ff))) := by
            rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply,
              Function.comp_apply, hmid]
    _ = hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)) := by
          simpa [Function.comp] using hg.writtenInCharts hfu_target
    _ = composedEquiv (u, (0 : Ff × Fg)) := by
          simp [composedEquiv, assocEquiv]

/-- Helper for Exercise 4.4: changing the codomain chart of an immersion witness rewrites the
extended-chart expression by the corresponding manifold coordinate change. -/
lemma change_codomain_chart_raw {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
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
  have hfu_extend_source :
      f ((hf.domChart.extend I).symm u) ∈ (hf.codChart.extend J).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hfu_source
  calc
    ((codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u
        = ((codChart.extend J) ∘ (hf.codChart.extend J).symm)
            (((hf.codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u) := by
            rw [Function.comp_apply, Function.comp_apply, Function.comp_apply]
            exact congrArg (codChart.extend J) ((hf.codChart.extend J).left_inv hfu_extend_source).symm
    _ = ((codChart.extend J) ∘ (hf.codChart.extend J).symm) (hf.equiv (u, (0 : Ff))) := by
          simpa [Function.comp] using
            congrArg (fun z ↦ ((codChart.extend J) ∘ (hf.codChart.extend J).symm) z)
              (hf.writtenInCharts hu)
    _ = J.extendCoordChange hf.codChart codChart (hf.equiv (u, (0 : Ff))) := by
          rfl

/-- Helper for Exercise 4.4: once the source point already lands in the middle chart chosen for
`g`, the composition can be rewritten in raw coordinates by inserting that middle chart and then
using the two written-in-charts identities. -/
theorem comp_raw_middle_change {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {u : E}
    (hu : u ∈ (hf.domChart.extend I).target)
    (hmid : f ((hf.domChart.extend I).symm u) ∈ hg.domChart.source) :
    ((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u =
      hg.equiv
        (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) := by
  have hchange :
      ((hg.domChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u =
        J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))) :=
    change_codomain_chart_raw (hf := hf) (codChart := hg.domChart) hu
  have hmid_target :
      J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))) ∈
        (hg.domChart.extend J).target := by
    have hmid_extend_source :
        f ((hf.domChart.extend I).symm u) ∈ (hg.domChart.extend J).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hmid
    -- Reinterpret the middle coordinate change as the extended middle chart applied to
    -- the actual point `f ((hf.domChart.extend I).symm u)`.
    rw [← hchange]
    exact (hg.domChart.extend J).map_source hmid_extend_source
  calc
    ((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u
        = ((hg.codChart.extend K) ∘ g ∘ (hg.domChart.extend J).symm)
            (((hg.domChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u) := by
            have hmid_extend_source :
                f ((hf.domChart.extend I).symm u) ∈ (hg.domChart.extend J).source := by
              simpa [OpenPartialHomeomorph.extend_source] using hmid
            -- Since the intermediate point lies in `hg.domChart.source`, insert
            -- `hg.domChart.extend` and its inverse before applying `g`.
            rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply,
              Function.comp_apply]
            exact congrArg ((hg.codChart.extend K) ∘ g)
              ((hg.domChart.extend J).left_inv hmid_extend_source).symm
    _ = ((hg.codChart.extend K) ∘ g ∘ (hg.domChart.extend J).symm)
          (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff)))) := by
          rw [hchange]
    _ = hg.equiv
          (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) := by
          simpa [Function.comp] using hg.writtenInCharts hmid_target

/-- Helper for Exercise 4.4: after restricting the source chart of `hf` to an open neighborhood
on which `f` lands in `hg.domChart.source`, the raw middle-change formula from
`comp_raw_middle_change` still holds on the restricted chart target. -/
theorem comp_raw_middle_change_on_restr {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {U : Set M} (hU_open : IsOpen U)
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
      simpa [OpenPartialHomeomorph.restr_source, hU_open.interior_eq] using hu_restr_source
    exact hu_restr_source'.1
  have hu_mid :
      f (((hf.domChart.restr U).extend I).symm u) ∈ hg.domChart.source :=
    hU_mid <| by
      have hu_restr_source' :
          ((hf.domChart.restr U).extend I).symm u ∈ hf.domChart.source ∩ U := by
        simpa [OpenPartialHomeomorph.restr_source, hU_open.interior_eq] using hu_restr_source
      exact hu_restr_source'.2
  -- The restricted extended chart agrees with the original one on this restricted target point.
  have hu_eq :
      (hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u) = u := by
    simpa [OpenPartialHomeomorph.extend_coe, Function.comp] using
      (((hf.domChart.restr U).extend I).right_inv hu)
  have hu_target :
      u ∈ (hf.domChart.extend I).target := by
    have hu_source_extend :
        ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hu_source
    have hu_target' :
        (hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u) ∈
          (hf.domChart.extend I).target :=
      (hf.domChart.extend I).map_source hu_source_extend
    exact hu_eq ▸ hu_target'
  have hu_symm_eq :
      ((hf.domChart.restr U).extend I).symm u = (hf.domChart.extend I).symm u := by
    -- Apply the original chart inverse to the shared chart value `u`.
    have hu_source_extend :
        ((hf.domChart.restr U).extend I).symm u ∈ (hf.domChart.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hu_source
    have hu_symm_eq' :
        (hf.domChart.extend I).symm
            ((hf.domChart.extend I) (((hf.domChart.restr U).extend I).symm u)) =
          ((hf.domChart.restr U).extend I).symm u :=
      (hf.domChart.extend I).left_inv hu_source_extend
    rwa [hu_eq] at hu_symm_eq'
  -- Route correction: the remaining composition formula is exactly the earlier raw lemma once the
  -- restricted inverse is rewritten back to the original inverse.
  calc
    ((hg.codChart.extend K) ∘ g ∘ f ∘ ((hf.domChart.restr U).extend I).symm) u
        = ((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u := by
            simpa [Function.comp] using congrArg (((hg.codChart.extend K) ∘ g ∘ f) ) hu_symm_eq
    _ = hg.equiv
          (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)) :=
      comp_raw_middle_change (hg := hg) (hf := hf) (hu := hu_target) hu_mid

/-- Helper for Exercise 4.4: for any local chart `e`, points in the target of the restricted
extended chart also lie in the target of the original extended chart. -/
lemma restr_extend_target_mem_of_openPartialHomeomorph
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

/-- Helper for Exercise 4.4: for any local chart `e`, the restricted extended-chart inverse agrees
with the original extended-chart inverse on the restricted target. -/
lemma restr_extend_symm_eq_of_openPartialHomeomorph
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

/-- Helper for Exercise 4.4: a point in the target of the restricted extended chart is also in the
target of the original extended chart. -/
lemma restr_extend_target_mem {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {U : Set M} (hU_open : IsOpen U) {u : E}
    (hu : u ∈ ((hf.domChart.restr U).extend I).target) :
    u ∈ (hf.domChart.extend I).target := by
  -- Specialize the generic restriction lemma to the immersion source chart.
  exact restr_extend_target_mem_of_openPartialHomeomorph
    (I := I) (e := hf.domChart) hU_open hu

/-- Helper for Exercise 4.4: on the target of a restricted extended chart, the restricted inverse
agrees with the original extended-chart inverse. -/
lemma restr_extend_symm_eq {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {U : Set M} (hU_open : IsOpen U) {u : E}
    (hu : u ∈ ((hf.domChart.restr U).extend I).target) :
    ((hf.domChart.restr U).extend I).symm u = (hf.domChart.extend I).symm u := by
  -- Specialize the generic inverse-comparison lemma to the immersion source chart.
  exact restr_extend_symm_eq_of_openPartialHomeomorph
    (I := I) (e := hf.domChart) hU_open hu

/-- Helper for Exercise 4.4: points coming from the restricted source chart still land in the
source of the middle coordinate change used to straighten the composition. -/
lemma immersion_coordinate_mem_extendCoordChange_source_of_restr_target {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {U : Set M} (hU_open : IsOpen U)
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
    restr_extend_target_mem (hf := hf) (U := U) hU_open hu
  have hu_symm_eq :
      ((hf.domChart.restr U).extend I).symm u = (hf.domChart.extend I).symm u :=
    restr_extend_symm_eq (hf := hf) (U := U) hU_open hu
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

/-- Helper for Exercise 4.4: on the restricted source-chart target used in the composition proof,
the raw middle-change expression already lies in the codomain extended-chart target. -/
lemma raw_middle_change_mem_codomain_target {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {U : Set M} (hU_open : IsOpen U)
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
  rw [comp_raw_middle_change_on_restr
    (hg := hg) (hf := hf) (U := U) hU_open hU_dom hU_mid hu] at htarget
  exact htarget

/-- Helper for Exercise 4.4: the inverse middle coordinate change straightens the first factor of
the raw product-model map arising in the composition proof. -/
lemma middle_change_prod_apply {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {z : F}
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

/-- Helper for Exercise 4.4: pairing a smooth first-coordinate map with the identity on the
second factor gives a smooth product map on the corresponding product source. -/
lemma contDiffOn_prod_map_snd {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    {s : Set F} {φ : F → F} (hφ : ContDiffOn 𝕜 ∞ φ s) :
    ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦ (φ p.1, p.2)) (Prod.fst ⁻¹' s) := by
  -- Smoothness on the product comes from composing the first-coordinate map with `Prod.fst`
  -- and pairing it with the unchanged second coordinate.
  have hfst :
      ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦ φ p.1) (Prod.fst ⁻¹' s) := by
    refine hφ.comp contDiff_fst.contDiffOn ?_
    intro p hp
    exact hp
  have hsnd :
      ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦ p.2) (Prod.fst ⁻¹' s) := by
    refine (contDiff_snd.contDiffOn : ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦ p.2) Set.univ).mono ?_
    intro p hp
    simp
  simpa using hfst.prodMk hsnd

/-- Helper for Exercise 4.4: the middle coordinate change and its inverse are smooth after being
promoted to the product-model maps that fix the complement factor. -/
lemma middle_change_prod_contDiff {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦ (θ.symm p.1, p.2)) (Prod.fst ⁻¹' θ.target) ∧
      ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦ (θ p.1, p.2)) (Prod.fst ⁻¹' θ.source) := by
  -- Combine smoothness of the middle coordinate change with the identity on the complement factor.
  dsimp
  constructor
  · exact contDiffOn_prod_map_snd
      (F := F) (Fg := Fg)
      (J.contDiffOn_extendCoordChange_symm
        hf.codChart_mem_maximalAtlas hg.domChart_mem_maximalAtlas)
  · exact contDiffOn_prod_map_snd
      (F := F) (Fg := Fg)
      (J.contDiffOn_extendCoordChange
        hf.codChart_mem_maximalAtlas hg.domChart_mem_maximalAtlas)

/-- Helper for Exercise 4.4: package the product-model straightening map as an explicit
`PartialEquiv` so later chart conjugations can compose it without re-expanding the product map. -/
noncomputable def middle_change_prod_chart {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) :
    PartialEquiv (F × Fg) (F × Fg) :=
  (J.extendCoordChange hf.codChart hg.domChart).symm.prod (PartialEquiv.refl Fg)

/-- Helper for Exercise 4.4: the packaged product straightening chart sends the raw middle term
to the standard product inclusion `(z, 0)`. -/
lemma middle_change_prod_chart_apply {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {z : F}
    (hz : z ∈ (J.extendCoordChange hf.codChart hg.domChart).source) :
    middle_change_prod_chart (hg := hg) (hf := hf)
      (J.extendCoordChange hf.codChart hg.domChart z, (0 : Fg)) = (z, 0) := by
  -- Unfold the packaged chart and apply the explicit first-factor straightening formula.
  simpa [middle_change_prod_chart] using
    middle_change_prod_apply (hg := hg) (hf := hf) (z := z) hz

/-- Helper for Exercise 4.4: conjugating the product straightening map by `hg.equiv` already
gives the codomain-model normal form on `G`; only the final transport through `K` remains. -/
lemma codomain_straightening_model_chart_apply {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {u : E}
    (hu : u ∈ (hf.domChart.extend I).target)
    (hmid : f ((hf.domChart.extend I).symm u) ∈ hg.domChart.source) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
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
  simpa [middle_change_prod_chart, PartialEquiv.trans_apply] using
    congrArg hg.equiv (middle_change_prod_apply (hg := hg) (hf := hf)
      (z := hf.equiv (u, (0 : Ff))) hz_source)

/-- Helper for Exercise 4.4: the conjugated model straightening map on `G` is smooth in both
directions on its natural source and target. -/
lemma codomain_straightening_model_contDiff {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G :=
      hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target := by
  dsimp
  have hrho :
      ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦
          ((J.extendCoordChange hf.codChart hg.domChart).symm p.1, p.2))
        (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).target) ∧
        ContDiffOn 𝕜 ∞ (fun p : F × Fg ↦
          (J.extendCoordChange hf.codChart hg.domChart p.1, p.2))
        (Prod.fst ⁻¹' (J.extendCoordChange hf.codChart hg.domChart).source) := by
    -- This is exactly the product-model smoothness package already proved for the middle chart
    -- change and its inverse.
    simpa using
      middle_change_prod_contDiff (hg := hg) (hf := hf)
  have heG : ContDiffOn 𝕜 ∞ hg.equiv Set.univ := by
    -- The codomain linear equivalence is globally smooth.
    simpa using hg.equiv.contDiff.contDiffOn
  have heGsymm : ContDiffOn 𝕜 ∞ hg.equiv.symm Set.univ := by
    -- The inverse linear equivalence is globally smooth as well.
    simpa using hg.equiv.symm.contDiff.contDiffOn
  constructor
  · -- Compose `eG.symm`, the product straightening, and `eG` in that order.
    have heGsymm' :
        ContDiffOn 𝕜 ∞ hg.equiv.symm
          (hg.equiv.symm ⁻¹' (middle_change_prod_chart (hg := hg) (hf := hf)).source) := by
      refine heGsymm.mono ?_
      intro z hz
      simp
    have hmid :
        ContDiffOn 𝕜 ∞
          (fun z : G ↦
            middle_change_prod_chart (hg := hg) (hf := hf) (hg.equiv.symm z))
          (hg.equiv.symm ⁻¹' (middle_change_prod_chart (hg := hg) (hf := hf)).source) := by
      refine hrho.1.comp heGsymm' ?_
      intro z hz
      simpa [middle_change_prod_chart] using hz
    have hcomp :
        ContDiffOn 𝕜 ∞
          (fun z : G ↦
            hg.equiv (middle_change_prod_chart (hg := hg) (hf := hf) (hg.equiv.symm z)))
          (hg.equiv.symm ⁻¹' (middle_change_prod_chart (hg := hg) (hf := hf)).source) := by
      refine heG.comp hmid ?_
      intro z hz
      simp
    simpa [middle_change_prod_chart, PartialEquiv.trans_apply, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Function.comp_assoc] using hcomp
  · -- The inverse composition swaps the two globally smooth linear pieces.
    have heGsymm' :
        ContDiffOn 𝕜 ∞ hg.equiv.symm
          (hg.equiv.symm ⁻¹' (middle_change_prod_chart (hg := hg) (hf := hf)).target) := by
      refine heGsymm.mono ?_
      intro z hz
      simp
    have hmid :
        ContDiffOn 𝕜 ∞
          (fun z : G ↦
            (middle_change_prod_chart (hg := hg) (hf := hf)).symm (hg.equiv.symm z))
          (hg.equiv.symm ⁻¹' (middle_change_prod_chart (hg := hg) (hf := hf)).target) := by
      refine hrho.2.comp heGsymm' ?_
      intro z hz
      simpa [middle_change_prod_chart] using hz
    have hcomp :
        ContDiffOn 𝕜 ∞
          (fun z : G ↦
            hg.equiv ((middle_change_prod_chart (hg := hg) (hf := hf)).symm (hg.equiv.symm z)))
          (hg.equiv.symm ⁻¹' (middle_change_prod_chart (hg := hg) (hf := hf)).target) := by
      refine heG.comp hmid ?_
      intro z hz
      simp
    simpa [middle_change_prod_chart, PartialEquiv.trans_apply, PartialEquiv.trans_target,
      PartialEquiv.symm_target, Function.comp_assoc] using hcomp

/-- Helper for Exercise 4.4: the model-with-corners map `K` identifies `H''` with the closed
subtype `Set.range K`. This is the ambient transport used by the remaining codomain-chart step. -/
noncomputable def codomain_model_range_homeomorph :
    H'' ≃ₜ Set.range (K : H'' → G) :=
  K.isClosedEmbedding.isEmbedding.toHomeomorph

/-- Helper for Exercise 4.4: a point in the source of an extended coordinate change already maps
into the target of the second extended chart. -/
lemma extendCoordChange_image_mem_target {e e' : OpenPartialHomeomorph N H'} {u : F}
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

/-- Helper for Exercise 4.4: the codomain basepoint of `g ∘ f` already lies in the ambient model
range `Set.range K`, so the `range K` transport can start from the actual codomain chart value. -/
lemma codomain_chart_basepoint_mem_model_range {x : M} {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x)) :
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

/-- Helper for Exercise 4.4: once the raw codomain basepoint is rewritten as the codomain slice
`hg.equiv (v0, 0)`, the explicit source/target data already shows that this basepoint lies in the
source of the conjugated model straightening and in the codomain extended-chart target. -/
lemma codomain_straightening_basepoint_source_data {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
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
      extendCoordChange_image_mem_target
        (J := J) (e := hf.codChart) (e' := hg.domChart) htheta_source0
  have hv0_rho_source : (v0, (0 : Fg)) ∈ rho.source := by
    -- The product straightening `rho` is defined exactly on points whose first coordinate lies in
    -- the target of the middle chart change.
    simpa [v0, θ, rho, middle_change_prod_chart] using hv0_theta_target
  constructor
  · -- Rewriting the raw codomain basepoint as `hg.equiv (v0, 0)` identifies it with a point in
    -- the source of the conjugated straightening `xi`.
    simpa [hz0_eq, xi, rho, eG, middle_change_prod_chart, PartialEquiv.trans_source] using
      hv0_rho_source
  · -- The actual codomain chart value at `g (f x)` is automatically in the extended-chart target.
    have hgf_source_ext : g (f x) ∈ (hg.codChart.extend K).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hg.mem_codChart_source
    simpa [z0] using (hg.codChart.extend K).map_source hgf_source_ext

/-- Helper for Exercise 4.4: at the composition basepoint, the middle coordinate change sends the
first-factor chart value into the target of `hg`'s extended domain chart. -/
lemma codomain_straightening_basepoint_first_coord_target {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      v0 ∈ (hg.domChart.extend J).target := by
  intro θ u0 v0 htheta_source0
  -- The generic coordinate-change target lemma applies directly to the basepoint input.
  simpa [θ, v0] using
    extendCoordChange_image_mem_target
      (J := J) (e := hf.codChart) (e' := hg.domChart) htheta_source0

/-- Helper for Exercise 4.4: the codomain slice determined by the basepoint of the middle chart
already lands in the target of `hg`'s extended codomain chart. -/
lemma codomain_straightening_basepoint_slice_target {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      hg.equiv (v0, (0 : Fg)) ∈ (hg.codChart.extend K).target := by
  intro θ u0 v0 htheta_source0
  have hv0_target : v0 ∈ (hg.domChart.extend J).target := by
    -- First place the middle-chart output inside `hg`'s extended domain chart target.
    simpa [θ, u0, v0] using
      codomain_straightening_basepoint_first_coord_target
        (hg := hg) (hf := hf) (domChart0 := domChart0) htheta_source0
  -- Then apply the codomain immersion normal form for `g` to that codomain slice.
  exact hg.target_subset_preimage_target hv0_target

/-- Helper for Exercise 4.4: every codomain slice `hg.equiv (v, 0)` with first coordinate in the
chosen domain-chart target of `g` already lies in the ambient model range `Set.range K`. -/
lemma codomain_slice_mem_model_range {x : M} {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
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

/-- Helper for Exercise 4.4: the conjugated model straightening `xi` acts on codomain slices by the
inverse middle chart change on the first factor. -/
lemma codomain_straightening_model_apply_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {v : F} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    xi (hg.equiv (v, (0 : Fg))) = hg.equiv (θ.symm v, (0 : Fg)) := by
  -- Unfold the conjugation and cancel the linear equivalence against its inverse.
  simp [middle_change_prod_chart, PartialEquiv.trans_apply]

/-- Helper for Exercise 4.4: the inverse conjugated model straightening `xi.symm` acts on
codomain slices by the forward middle chart change on the first factor. -/
lemma codomain_straightening_model_apply_slice_symm {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {w : F} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    xi.symm (hg.equiv (w, (0 : Fg))) = hg.equiv (θ w, (0 : Fg)) := by
  -- Unfold the inverse conjugation and cancel the linear equivalence in the reverse order.
  simp [middle_change_prod_chart, PartialEquiv.trans_apply]

/-- Helper for Exercise 4.4: if the forward middle coordinate change of a first-factor slice lies
in `hg`'s domain-chart target, then applying `xi.symm` to that codomain slice preserves the ambient
model range `Set.range K`. -/
lemma codomain_straightening_model_mem_range_of_slice_symm {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {w : F}
    (hw : J.extendCoordChange hf.codChart hg.domChart w ∈ (hg.domChart.extend J).target) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    xi.symm (hg.equiv (w, (0 : Fg))) ∈ Set.range (K : H'' → G) := by
  -- Rewrite `xi.symm` on the codomain slice, then invoke the ambient range lemma for `g`.
  dsimp
  simpa [middle_change_prod_chart] using
    (codomain_slice_mem_model_range (hg := hg)
      (v := J.extendCoordChange hf.codChart hg.domChart w) hw)

/-- Helper for Exercise 4.4: if the transported first coordinate still lies in
`(hg.domChart.extend J).target`, then the conjugated model straightening sends the corresponding
codomain slice into `hg`'s codomain extended-chart target. -/
lemma codomain_straightening_model_target_of_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {v : F}
    (hv : (J.extendCoordChange hf.codChart hg.domChart).symm v ∈ (hg.domChart.extend J).target) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    xi (hg.equiv (v, (0 : Fg))) ∈ (hg.codChart.extend K).target := by
  -- After unfolding the conjugated chart change, this is exactly the codomain target statement
  -- for `g` applied to the transported first coordinate.
  simpa [OpenPartialHomeomorph.extend_target, middle_change_prod_chart, PartialEquiv.trans_apply] using
    (hg.target_subset_preimage_target hv :
      hg.equiv ((J.extendCoordChange hf.codChart hg.domChart).symm v, (0 : Fg)) ∈
        (hg.codChart.extend K).target)

/-- Helper for Exercise 4.4: once the straightened first coordinate still lies in the codomain
domain-chart target of `g`, the conjugated model straightening preserves the ambient model range on
that codomain slice. -/
lemma codomain_straightening_model_mem_range_of_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {v : F}
    (hv : (J.extendCoordChange hf.codChart hg.domChart).symm v ∈ (hg.domChart.extend J).target) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    xi (hg.equiv (v, (0 : Fg))) ∈ Set.range (K : H'' → G) := by
  -- Rewrite `xi` on the codomain slice, then use the ambient range lemma for `g`.
  dsimp
  simpa [middle_change_prod_chart] using
    (codomain_slice_mem_model_range (hg := hg)
      (v := (J.extendCoordChange hf.codChart hg.domChart).symm v) hv)

/-- Helper for Exercise 4.4: at the composition basepoint, preserving the ambient model range
under the transported model straightening reduces to the concrete overlap condition that the
`hf`-chart coordinate already lies in `hg`'s extended domain-chart target. -/
lemma codomain_straightening_basepoint_range_reduction {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
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
    codomain_straightening_model_mem_range_of_slice
      (hg := hg) (hf := hf) (v := v0) hv0_target

/-- Helper for Exercise 4.4: evaluating the raw codomain chart identity at the composition
basepoint rewrites that basepoint as the explicit codomain slice used by the model straightening
construction. -/
lemma codomain_straightening_basepoint_raw_chart {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H}
    (hx_domChart0 : x ∈ domChart0.source)
    (hraw :
      Set.EqOn
        (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm))
        (fun u ↦
          hg.equiv
            (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (u, (0 : Ff))), (0 : Fg)))
        (domChart0.extend I).target)
    (htheta_source :
      ∀ ⦃u : E⦄, u ∈ (domChart0.extend I).target →
        hf.equiv (u, (0 : Ff)) ∈ (J.extendCoordChange hf.codChart hg.domChart).source) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    let z0 : G := (hg.codChart.extend K) (g (f x))
    z0 = hg.equiv (v0, (0 : Fg)) := by
  dsimp
  have hu0_target : (domChart0.extend I) x ∈ (domChart0.extend I).target := by
    have hx_source_ext : x ∈ (domChart0.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hx_domChart0
    exact (domChart0.extend I).map_source hx_source_ext
  have hraw0 := hraw hu0_target
  simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hx_domChart0] using hraw0

/-- Helper for Exercise 4.4: a neighborhood of a point inside `Set.range K` can be represented by
an ambient open set whose intersection with `Set.range K` stays inside the prescribed
within-range neighborhood. -/
lemma ambient_open_window_of_within_neighborhood {z : G} {A u : Set G}
    (hu : u ∈ nhdsWithin z A) :
    ∃ s : Set G, IsOpen s ∧ z ∈ s ∧ s ∩ A ⊆ u := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hu with ⟨v, hv_nhds, hv_sub⟩
  rcases mem_nhds_iff.1 hv_nhds with ⟨s, hs_sub, hs_open, hz_s⟩
  refine ⟨s, hs_open, hz_s, ?_⟩
  intro y hy
  exact hv_sub ⟨hs_sub hy.1, hy.2⟩

/-- Helper for Exercise 4.4: specialize `ambient_open_window_of_within_neighborhood` to the model
range `Set.range K`. -/
lemma ambient_open_windows_of_within_range_neighborhood {z : G} {u : Set G}
    (hu : u ∈ nhdsWithin z (Set.range (K : H'' → G))) :
    ∃ s : Set G, IsOpen s ∧ z ∈ s ∧ s ∩ Set.range (K : H'' → G) ⊆ u := by
  exact ambient_open_window_of_within_neighborhood (A := Set.range (K : H'' → G)) hu

/-- Helper for Exercise 4.4: a neighborhood within `A` is also a neighborhood within `S` once
`A` itself is already a neighborhood within `S`. -/
lemma mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin {z : G} {A S u : Set G}
    (hA : A ∈ nhdsWithin z S) (hu : u ∈ nhdsWithin z A) :
    u ∈ nhdsWithin z S := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hA hu ⊢
  rcases hA with ⟨s, hs_nhds, hs_sub⟩
  rcases hu with ⟨t, ht_nhds, ht_sub⟩
  refine ⟨s ∩ t, Filter.inter_mem hs_nhds ht_nhds, ?_⟩
  intro y hy
  have hyA : y ∈ A := hs_sub ⟨hy.1.1, hy.2⟩
  exact ht_sub ⟨hy.1.2, hyA⟩

/-- Helper for Exercise 4.4: if an ambient open set `v` meets `Set.range K` inside `u`, then the
smaller set `v ∩ u` is open in the subtype topology on `Set.range K`. -/
lemma subtype_open_of_ambient_open_inter_subset {v u : Set G}
    (hv_open : IsOpen v) (hv_sub : v ∩ Set.range (K : H'' → G) ⊆ u) :
    IsOpen (Subtype.val ⁻¹' (v ∩ u) : Set (Set.range (K : H'' → G))) := by
  -- On the closed subtype `Set.range K`, the extra intersection with `u` is redundant because
  -- points of `v ∩ Set.range K` were already chosen to land inside `u`.
  have hs_eq :
      (Subtype.val ⁻¹' (v ∩ u) : Set (Set.range (K : H'' → G))) =
        Subtype.val ⁻¹' v := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      have hx_u : x.1 ∈ u := hv_sub ⟨hx, x.2⟩
      exact ⟨hx, hx_u⟩
  rw [hs_eq]
  exact hv_open.preimage continuous_subtype_val

/-- Helper for Exercise 4.4: a within-range neighborhood contains a smaller window that is open
in the subtype topology on `Set.range K` and is still a neighborhood within the original set. -/
lemma subtype_open_window_of_within_range_neighborhood {z : G} {u : Set G}
    (hz_u : z ∈ u)
    (hu : u ∈ nhdsWithin z (Set.range (K : H'' → G))) :
    ∃ s : Set G,
      IsOpen (Subtype.val ⁻¹' s : Set (Set.range (K : H'' → G))) ∧
      z ∈ s ∧
      s ⊆ u ∧
      s ∈ nhdsWithin z u := by
  rcases ambient_open_windows_of_within_range_neighborhood (K := K) (z := z) (u := u) hu with
    ⟨v, hv_open, hz_v, hv_sub⟩
  let s : Set G := v ∩ u
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · -- On the closed subtype `Set.range K`, the smaller window `v ∩ u` agrees with the ambient
    -- open set `v`, because `v ∩ Set.range K` was already chosen inside `u`.
    simpa [s] using
      subtype_open_of_ambient_open_inter_subset (K := K) (v := v) (u := u) hv_open hv_sub
  · exact ⟨hz_v, hz_u⟩
  · intro y hy
    exact hy.2
  · -- The same ambient open witness `v` certifies that `s = v ∩ u` is a neighborhood within `u`.
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨v, IsOpen.mem_nhds hv_open hz_v, ?_⟩
    intro y hy
    simpa [s] using hy

/-- Helper for Exercise 4.4: the conjugated model straightening is continuous within the
`Set.range K` transport domains determined by its source and target. -/
lemma codomain_straightening_within_range_continuous
    {xi : PartialEquiv G G} {z : G}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    (hz_source : z ∈ xi.source) :
    ContinuousWithinAt xi (Set.range (K : H'' → G) ∩ xi.source) z ∧
      ContinuousWithinAt xi.symm (Set.range (K : H'' → G) ∩ xi.target) (xi z) := by
  constructor
  · -- Restrict the already-known continuity on `xi.source` to the smaller transport domain.
    have hcont : ContinuousWithinAt xi xi.source z :=
      hxi_cont.1.continuousOn.continuousWithinAt hz_source
    exact hcont.mono fun _ hy ↦ hy.2
  · -- The inverse map is handled in the same way on `xi.target`.
    have hxi_target : xi z ∈ xi.target := xi.map_source hz_source
    have hcont : ContinuousWithinAt xi.symm xi.target (xi z) :=
      hxi_cont.2.continuousOn.continuousWithinAt hxi_target
    exact hcont.mono fun _ hy ↦ hy.2

/-- Helper for Exercise 4.4: the target of an extended coordinate change is a neighborhood within
the model range at each of its points. -/
lemma extendCoordChange_target_mem_nhdsWithin {e e' : OpenPartialHomeomorph N H'} {u : F}
    (hu : u ∈ (J.extendCoordChange e e').target) :
    (J.extendCoordChange e e').target ∈ nhdsWithin u (Set.range (J : H' → F)) := by
  -- Reduce the target statement to the already-available source statement for the inverse chart
  -- change.
  simpa [ModelWithCorners.extendCoordChange_symm] using
    (J.extendCoordChange_source_mem_nhdsWithin (e := e') (e' := e) hu)

/-- Helper for Exercise 4.4: conjugating a chart change on `Set.range K` by the canonical
homeomorphism `H'' ≃ₜ Set.range K` gives a chart change on `H''` whose `K`-expression is the same
ambient map. -/
lemma transport_subtype_homeomorph_to_chart_change
    {xi : PartialEquiv G G} {y0 : H''} {s t : Set G}
    {chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G))}
    (hy0 : (⟨K y0, ⟨y0, rfl⟩⟩ : Set.range (K : H'' → G)) ∈ chiRange.source)
    (hEqRange :
      Set.EqOn
        (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi z.1) chiRange.source)
    (hEqRangeSymm :
      Set.EqOn
        (fun z ↦ ((chiRange.symm z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi.symm z.1) chiRange.target)
    (hsourceRange : Set.MapsTo Subtype.val chiRange.source s)
    (htargetRange : Set.MapsTo Subtype.val chiRange.target t) :
    ∃ chi : OpenPartialHomeomorph H'' H'',
      y0 ∈ chi.source ∧
      Set.MapsTo K chi.source s ∧
      Set.MapsTo K chi.target t ∧
      Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source ∧
      Set.EqOn (fun y ↦ K (chi.symm y)) (fun y ↦ xi.symm (K y)) chi.target := by
  let eK : H'' ≃ₜ Set.range (K : H'' → G) := codomain_model_range_homeomorph (K := K)
  let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
    eK.symm.toOpenPartialHomeomorph
  let chi : OpenPartialHomeomorph H'' H'' :=
    (eRange.symm.trans chiRange).trans eRange
  refine ⟨chi, ?_, ?_, ?_, ?_, ?_⟩
  · -- The transported source is just the pullback of `chiRange.source` along `eK`.
    simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_source] using hy0
  · intro y hy
    have hyRange : eK y ∈ chiRange.source := by
      -- Read the transported source back in the subtype picture.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_source] using hy
    simpa [eK] using hsourceRange hyRange
  · intro y hy
    have hyRange : eK y ∈ chiRange.target := by
      -- The transported target is likewise the pullback of `chiRange.target`.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_target] using hy
    simpa [eK] using htargetRange hyRange
  · intro y hy
    have hyRange : eK y ∈ chiRange.source := by
      -- Reinterpret source membership for the transported chart change on the subtype side.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_source] using hy
    have htransport :
        eK (chi y) = chiRange (eK y) := by
      -- Conjugating by `eK` turns the transported chart change back into `chiRange`.
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
        -- The ambient coordinate of `chi y` is exactly the subtype value of `chiRange (eK y)`.
        simpa [eK] using congrArg Subtype.val htransport
      _ = xi (K y) := by
        -- The subtype chart change was chosen to agree with the ambient map `xi`.
        simpa [eK] using hEqRange hyRange
  · intro y hy
    have hyRange : eK y ∈ chiRange.target := by
      -- Reinterpret transported target membership on the subtype side.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_target] using hy
    have htransport :
        eK (chi.symm y) = chiRange.symm (eK y) := by
      -- The same conjugation formula holds for the inverse transported chart change.
      calc
        eK (chi.symm y)
            = eK (eRange (chiRange.symm (eRange.symm y))) := by
                rfl
        _ = chiRange.symm (eRange.symm y) := by
              simp [eRange, eK]
        _ = chiRange.symm (eK y) := by
              rfl
    calc
      K (chi.symm y) = ((chiRange.symm (eK y) : Set.range (K : H'' → G)).1) := by
        -- The inverse ambient coordinate is read off from the inverse transported subtype map.
        simpa [eK] using congrArg Subtype.val htransport
      _ = xi.symm (K y) := by
        -- On the transported target, the inverse subtype chart matches `xi.symm`.
        simpa [eK] using hEqRangeSymm hyRange

/-- Helper for Exercise 4.4: smooth ambient windows in `G` induce a homeomorphism between the
corresponding open windows in the closed subtype `Set.range K`. -/
noncomputable def range_window_homeomorph
    {xi : PartialEquiv G G} {s t : Set G}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    (hs_source : s ⊆ xi.source) (ht_target : t ⊆ xi.target)
    (hmap : Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)))
    (hmap_symm :
      Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G))) :
    (Subtype.val ⁻¹' s : Set (Set.range (K : H'' → G))) ≃ₜ
      (Subtype.val ⁻¹' t : Set (Set.range (K : H'' → G))) := by
  let rangeK : Set G := Set.range (K : H'' → G)
  let sourceRange : Set (Set.range (K : H'' → G)) := Subtype.val ⁻¹' s
  let targetRange : Set (Set.range (K : H'' → G)) := Subtype.val ⁻¹' t
  let sourceToAmbient : sourceRange → ↥(s ∩ rangeK) :=
    fun z ↦ ⟨z.1.1, z.2, z.1.2⟩
  let targetToAmbient : targetRange → ↥(t ∩ rangeK) :=
    fun z ↦ ⟨z.1.1, z.2, z.1.2⟩
  have hsourceToAmbient_cont : Continuous sourceToAmbient := by
    -- The source subtype is just the intersection `s ∩ rangeK` written in two stages.
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      fun z ↦ ⟨z.2, z.1.2⟩
  have htargetToAmbient_cont : Continuous targetToAmbient := by
    -- The target subtype has the same two-stage subtype description.
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      fun z ↦ ⟨z.2, z.1.2⟩
  have hxi_on_range : ContinuousOn xi (s ∩ rangeK) := by
    -- Restrict the ambient `C^∞` map to the smaller window `s ∩ rangeK`.
    exact hxi_cont.1.continuousOn.mono fun z hz ↦ hs_source hz.1
  have hxi_symm_on_range : ContinuousOn xi.symm (t ∩ rangeK) := by
    -- The inverse ambient map is continuous on the target window as well.
    exact hxi_cont.2.continuousOn.mono fun z hz ↦ ht_target hz.1
  refine
    { toFun := fun z ↦
        ⟨⟨xi z.1.1, (hmap ⟨z.2, z.1.2⟩).2⟩, (hmap ⟨z.2, z.1.2⟩).1⟩
      invFun := fun z ↦
        ⟨⟨xi.symm z.1.1, (hmap_symm ⟨z.2, z.1.2⟩).2⟩, (hmap_symm ⟨z.2, z.1.2⟩).1⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    -- On the source window, `xi.symm` is a genuine inverse to `xi`.
    apply Subtype.ext
    apply Subtype.ext
    exact xi.left_inv (hs_source z.2)
  · intro z
    -- On the target window, the inverse relation is the opposite identity.
    apply Subtype.ext
    apply Subtype.ext
    exact xi.right_inv (ht_target z.2)
  · -- Route correction: rather than constructing a partial homeomorphism on `Set.range K`
    -- directly, first identify the source window with `s ∩ rangeK` and then compose with `xi`.
    have hcont :
        Continuous fun z : sourceRange ↦ xi z.1.1 := by
      exact hxi_on_range.restrict.comp hsourceToAmbient_cont
    exact (hcont.subtype_mk fun z ↦ (hmap ⟨z.2, z.1.2⟩).2).subtype_mk
      fun z ↦ (hmap ⟨z.2, z.1.2⟩).1
  · -- The inverse window map is handled by the same source-to-intersection conversion.
    have hcont :
        Continuous fun z : targetRange ↦ xi.symm z.1.1 := by
      exact hxi_symm_on_range.restrict.comp htargetToAmbient_cont
    exact (hcont.subtype_mk fun z ↦ (hmap_symm ⟨z.2, z.1.2⟩).2).subtype_mk
      fun z ↦ (hmap_symm ⟨z.2, z.1.2⟩).1

/-- Helper for Exercise 4.4: the subtype-window homeomorphism packages into an
`OpenPartialHomeomorph` on `Set.range K` whose ambient value is exactly `xi` on its source. -/
lemma range_window_homeomorph_to_partial_homeomorph_on_range
    {xi : PartialEquiv G G} {y0 : H''} {s t : Set G}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    (hs_open : IsOpen s) (ht_open : IsOpen t)
    (hy0s : K y0 ∈ s) (hxi_y0_t : xi (K y0) ∈ t)
    (hs_source : s ⊆ xi.source) (ht_target : t ⊆ xi.target)
    (hmap : Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)))
    (hmap_symm :
      Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G))) :
    ∃ chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)),
      (⟨K y0, ⟨y0, rfl⟩⟩ : Set.range (K : H'' → G)) ∈ chiRange.source ∧
      Set.MapsTo Subtype.val chiRange.source s ∧
      Set.MapsTo Subtype.val chiRange.target t ∧
      Set.EqOn
        (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi z.1) chiRange.source ∧
      Set.EqOn
        (fun z ↦ ((chiRange.symm z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi.symm z.1) chiRange.target := by
  let sourceRange : TopologicalSpace.Opens (Set.range (K : H'' → G)) :=
    ⟨Subtype.val ⁻¹' s, by
      simpa using hs_open.preimage continuous_subtype_val⟩
  let targetRange : TopologicalSpace.Opens (Set.range (K : H'' → G)) :=
    ⟨Subtype.val ⁻¹' t, by
      simpa using ht_open.preimage continuous_subtype_val⟩
  have hsource_nonempty : Nonempty sourceRange := by
    -- The basepoint witnesses that the source window in `range K` is nonempty.
    refine ⟨⟨⟨K y0, ⟨y0, rfl⟩⟩, hy0s⟩⟩
  have htarget_nonempty : Nonempty targetRange := by
    -- The image basepoint likewise witnesses nonemptiness of the target window.
    refine ⟨⟨⟨xi (K y0), (hmap ⟨hy0s, ⟨y0, rfl⟩⟩).2⟩, hxi_y0_t⟩⟩
  let hwin :
      sourceRange ≃ₜ targetRange :=
    range_window_homeomorph (K := K) (xi := xi) hxi_cont hs_source ht_target hmap hmap_symm
  let chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)) :=
    ((sourceRange.openPartialHomeomorphSubtypeCoe hsource_nonempty).symm.trans
      hwin.toOpenPartialHomeomorph).trans
      (targetRange.openPartialHomeomorphSubtypeCoe htarget_nonempty)
  refine ⟨chiRange, ?_, ?_, ?_, ?_, ?_⟩
  · -- The source of `chiRange` is exactly the pulled-back source window `Subtype.val ⁻¹' s`.
    simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
      using hy0s
  · intro z hz
    have hz_sourceRange : z ∈ sourceRange := by
      -- Source membership for `chiRange` is just source-window membership in the subtype.
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hz
    exact hz_sourceRange
  · intro z hz
    have hz_targetRange : z ∈ targetRange := by
      -- Target membership for `chiRange` is the transported target window in the subtype.
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_source,
        Homeomorph.toOpenPartialHomeomorph_target,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
        using hz
    exact hz_targetRange
  · intro z hz
    -- Read source membership back as `z.1 ∈ s`, then unfold the packaged homeomorphism.
    have hz_sourceRange : z ∈ sourceRange := by
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hz
    have hsource_symm :
        (sourceRange.openPartialHomeomorphSubtypeCoe hsource_nonempty).symm z =
          ⟨z, hz_sourceRange⟩ := by
      apply Subtype.ext
      simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
        (sourceRange.openPartialHomeomorphSubtypeCoe hsource_nonempty).right_inv
          (by
            simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using
              hz_sourceRange)
    -- The middle homeomorphism `hwin` was built so that its ambient value is `xi`.
    simp [chiRange, hwin, range_window_homeomorph, sourceRange, targetRange, hsource_symm]
  · intro z hz
    -- The inverse chart change on the target window is given by `xi.symm`.
    have hz_targetRange : z ∈ targetRange := by
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_source,
        Homeomorph.toOpenPartialHomeomorph_target,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
        using hz
    have htarget_symm :
        (targetRange.openPartialHomeomorphSubtypeCoe htarget_nonempty).symm z =
          ⟨z, hz_targetRange⟩ := by
      apply Subtype.ext
      simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
        (targetRange.openPartialHomeomorphSubtypeCoe htarget_nonempty).right_inv
          (by
            simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using
              hz_targetRange)
    simp [chiRange, hwin, range_window_homeomorph, sourceRange, targetRange, htarget_symm]

/-- Helper for Exercise 4.4: the same subtype-window packaging works when the source and target
windows are already given as open subsets of `Set.range K`, without requiring ambient openness in
`G`. -/
lemma range_window_homeomorph_to_partial_homeomorph_on_range_of_subtype_open
    {xi : PartialEquiv G G} {y0 : H''} {s t : Set G}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    (hs_open : IsOpen (Subtype.val ⁻¹' s : Set (Set.range (K : H'' → G))))
    (ht_open : IsOpen (Subtype.val ⁻¹' t : Set (Set.range (K : H'' → G))))
    (hy0s : K y0 ∈ s) (hxi_y0_t : xi (K y0) ∈ t)
    (hs_source : s ⊆ xi.source) (ht_target : t ⊆ xi.target)
    (hmap : Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)))
    (hmap_symm :
      Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G))) :
    ∃ chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)),
      (⟨K y0, ⟨y0, rfl⟩⟩ : Set.range (K : H'' → G)) ∈ chiRange.source ∧
      Set.MapsTo Subtype.val chiRange.source s ∧
      Set.MapsTo Subtype.val chiRange.target t ∧
      Set.EqOn
        (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi z.1) chiRange.source ∧
      Set.EqOn
        (fun z ↦ ((chiRange.symm z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi.symm z.1) chiRange.target := by
  let sourceRange : TopologicalSpace.Opens (Set.range (K : H'' → G)) :=
    ⟨Subtype.val ⁻¹' s, hs_open⟩
  let targetRange : TopologicalSpace.Opens (Set.range (K : H'' → G)) :=
    ⟨Subtype.val ⁻¹' t, ht_open⟩
  have hsource_nonempty : Nonempty sourceRange := by
    -- The basepoint witnesses that the source window in `range K` is nonempty.
    refine ⟨⟨⟨K y0, ⟨y0, rfl⟩⟩, hy0s⟩⟩
  have htarget_nonempty : Nonempty targetRange := by
    -- The image basepoint likewise witnesses nonemptiness of the target window.
    refine ⟨⟨⟨xi (K y0), (hmap ⟨hy0s, ⟨y0, rfl⟩⟩).2⟩, hxi_y0_t⟩⟩
  let hwin :
      sourceRange ≃ₜ targetRange :=
    range_window_homeomorph (K := K) (xi := xi) hxi_cont hs_source ht_target hmap hmap_symm
  let chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)) :=
    ((sourceRange.openPartialHomeomorphSubtypeCoe hsource_nonempty).symm.trans
      hwin.toOpenPartialHomeomorph).trans
      (targetRange.openPartialHomeomorphSubtypeCoe htarget_nonempty)
  refine ⟨chiRange, ?_, ?_, ?_, ?_, ?_⟩
  · -- The source of `chiRange` is exactly the pulled-back source window `Subtype.val ⁻¹' s`.
    simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
      using hy0s
  · intro z hz
    have hz_sourceRange : z ∈ sourceRange := by
      -- Source membership for `chiRange` is just source-window membership in the subtype.
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hz
    exact hz_sourceRange
  · intro z hz
    have hz_targetRange : z ∈ targetRange := by
      -- Target membership for `chiRange` is the transported target window in the subtype.
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_source,
        Homeomorph.toOpenPartialHomeomorph_target,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
        using hz
    exact hz_targetRange
  · intro z hz
    -- Read source membership back as `z.1 ∈ s`, then unfold the packaged homeomorphism.
    have hz_sourceRange : z ∈ sourceRange := by
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hz
    have hsource_symm :
        (sourceRange.openPartialHomeomorphSubtypeCoe hsource_nonempty).symm z =
          ⟨z, hz_sourceRange⟩ := by
      apply Subtype.ext
      simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
        (sourceRange.openPartialHomeomorphSubtypeCoe hsource_nonempty).right_inv
          (by
            simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using
              hz_sourceRange)
    -- The middle homeomorphism `hwin` was built so that its ambient value is `xi`.
    simp [chiRange, hwin, range_window_homeomorph, sourceRange, targetRange, hsource_symm]
  · intro z hz
    -- The inverse chart change on the target window is given by `xi.symm`.
    have hz_targetRange : z ∈ targetRange := by
      simpa [chiRange, sourceRange, targetRange, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_source,
        Homeomorph.toOpenPartialHomeomorph_target,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
        using hz
    have htarget_symm :
        (targetRange.openPartialHomeomorphSubtypeCoe htarget_nonempty).symm z =
          ⟨z, hz_targetRange⟩ := by
      apply Subtype.ext
      simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
        (targetRange.openPartialHomeomorphSubtypeCoe htarget_nonempty).right_inv
          (by
            simpa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using
              hz_targetRange)
    simp [chiRange, hwin, range_window_homeomorph, sourceRange, targetRange, htarget_symm]

/-- Helper for Exercise 4.4: if a transported chart change on `H''` agrees with a smooth ambient
partial equivalence through `K` in both directions, then the only remaining task is to package
those coordinate formulas as membership in the smooth structure groupoid. -/
lemma transported_chart_change_mem_contDiffGroupoid
    {xi : PartialEquiv G G} {chi : OpenPartialHomeomorph H'' H''} {s t : Set G}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    (hsource : Set.MapsTo K chi.source s) (htarget : Set.MapsTo K chi.target t)
    (hs_source : s ⊆ xi.source) (ht_target : t ⊆ xi.target)
    (hEqchi : Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source)
    (hEqchi_symm :
      Set.EqOn (fun y ↦ K (chi.symm y)) (fun y ↦ xi.symm (K y)) chi.target) :
    chi ∈ contDiffGroupoid ∞ K := by
  have hchi_cont : ContMDiffOn K K ∞ chi chi.source := by
    -- Rewrite smoothness on `H''` to smoothness of `K ∘ chi`, then replace that expression by
    -- the ambient model map `xi ∘ K` on the whole source of `chi`.
    rw [contMDiffOn_iff_target]
    refine ⟨chi.continuousOn_toFun, ?_⟩
    intro y
    have hxi_comp_K :
        ContMDiffOn K 𝓘(𝕜, G) ∞ (fun z : H'' ↦ xi (K z)) chi.source := by
      exact hxi_cont.1.contMDiffOn.comp (contMDiff_model (I := K)).contMDiffOn fun z hz ↦
        hs_source (hsource hz)
    have hK_chi :
        ContMDiffOn K 𝓘(𝕜, G) ∞ (fun z : H'' ↦ K (chi z)) chi.source := by
      refine hxi_comp_K.congr ?_
      intro z hz
      simpa [Function.comp] using hEqchi hz
    simpa [extChartAt, chartAt_self_eq, Function.comp_assoc] using hK_chi
  have hchi_symm_cont : ContMDiffOn K K ∞ chi.symm chi.target := by
    -- The inverse chart-change smoothness is the same argument applied to `xi.symm`.
    rw [contMDiffOn_iff_target]
    refine ⟨chi.continuousOn_invFun, ?_⟩
    intro y
    have hxi_symm_comp_K :
        ContMDiffOn K 𝓘(𝕜, G) ∞ (fun z : H'' ↦ xi.symm (K z)) chi.target := by
      exact hxi_cont.2.contMDiffOn.comp (contMDiff_model (I := K)).contMDiffOn fun z hz ↦
        ht_target (htarget hz)
    have hK_chi_symm :
        ContMDiffOn K 𝓘(𝕜, G) ∞ (fun z : H'' ↦ K (chi.symm z)) chi.target := by
      refine hxi_symm_comp_K.congr ?_
      intro z hz
      simpa [Function.comp] using hEqchi_symm hz
    simpa [extChartAt, chartAt_self_eq, Function.comp_assoc] using hK_chi_symm
  -- Package the forward and inverse smoothness data as a local structomorphism witness.
  have hchi_local :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt) chi chi.source := by
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := K) (n := ∞) (f := chi)).2
      ⟨hchi_cont, hchi_symm_cont⟩
  -- Close by the same locality argument used later for partial diffeomorphisms, but kept inline
  -- here to respect the current declaration order.
  refine (contDiffGroupoid ∞ K).locality ?_
  intro x hx
  have hfx := hchi_local x hx
  have hfx' := hfx
  simp only [ChartedSpace.liftPropWithinAt_iff', chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm] at hfx'
  obtain ⟨-, hfx_prop⟩ := hfx'
  have hfx_prop' : (contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt chi chi.source x := by
    simpa using hfx_prop
  rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    (G := contDiffGroupoid ∞ K) (f := chi)] at hfx_prop'
  obtain ⟨e, he, hsource', hEq, hxe⟩ := hfx_prop' hx
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  have hEq' : Set.EqOn chi e (chi.source ∩ e.source) := by
    intro y hy
    exact hEq hy.2
  have hrestr : chi.restr e.source ≈ e.restr chi.source := by
    exact OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEq'
  have hEqOnSource : chi.restr e.source ≈ e := by
    simpa [OpenPartialHomeomorph.restr_eq_of_source_subset hsource'] using hrestr
  exact (contDiffGroupoid ∞ K).mem_of_eqOnSource he hEqOnSource

/-- Helper for Exercise 4.4: once ambient open windows around a basepoint preserve
`Set.range K` under `xi` and `xi.symm`, they transport to a codomain chart change on `H''`
whose `K`-expression is exactly `xi`. -/
lemma range_windows_to_chart_change
    {xi : PartialEquiv G G} {y0 : H''}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    {s t : Set G} (hs_open : IsOpen s) (ht_open : IsOpen t)
    (hy0s : K y0 ∈ s) (hxi_y0_t : xi (K y0) ∈ t)
    (hs_source : s ⊆ xi.source) (ht_target : t ⊆ xi.target)
    (hmap : Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)))
    (hmap_symm :
      Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G))) :
    ∃ chi : OpenPartialHomeomorph H'' H'',
      chi ∈ contDiffGroupoid ∞ K ∧
      y0 ∈ chi.source ∧
      Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
  -- Route correction: the subtype-window homeomorphism `range_window_homeomorph` isolates the
  -- pure transport step on `Set.range K`; the remaining gap is to package that homeomorphism as
  -- an `OpenPartialHomeomorph` and then transport its smoothness through `K`.
  rcases
      range_window_homeomorph_to_partial_homeomorph_on_range
        (K := K) (xi := xi) (y0 := y0) hxi_cont hs_open ht_open hy0s hxi_y0_t
        hs_source ht_target hmap hmap_symm with
    ⟨chiRange, hy0Range, hsourceRange, htargetRange, hEqRange, hEqRangeSymm⟩
  rcases
      transport_subtype_homeomorph_to_chart_change
        (K := K) (xi := xi) (s := s) (t := t) (y0 := y0) hy0Range hEqRange hEqRangeSymm
        hsourceRange htargetRange with
    ⟨chi, hy0chi, hsource, htarget, hEqchi, hEqchi_symm⟩
  have hchi_mem : chi ∈ contDiffGroupoid ∞ K := by
    -- The remaining analytic bridge is isolated in `transported_chart_change_mem_contDiffGroupoid`.
    exact transported_chart_change_mem_contDiffGroupoid
      (K := K) (xi := xi) (chi := chi) (s := s) (t := t)
      hxi_cont hsource htarget hs_source ht_target hEqchi hEqchi_symm
  exact ⟨chi, hchi_mem, hy0chi, hEqchi⟩

/-- Helper for Exercise 4.4: the remaining codomain transport step for
`IsImmersionAtOfComplement.comp` is to package the codomain straightening `xi` into a local chart
change on `H''` at the basepoint `hg.codChart (g (f x))`, once the source-faithful subtype chart
change on `Set.range K` has already been constructed. -/
lemma codomain_straightening_chart_change_at_basepoint {x : M} {Fg : Type*}
    [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    {xi : PartialEquiv G G}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    (hchiRange :
      ∃ chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)),
        ((⟨(hg.codChart.extend K) (g (f x)),
            codomain_chart_basepoint_mem_model_range (hg := hg)⟩ :
            Set.range (K : H'' → G)) ∈ chiRange.source) ∧
        ∃ s t : Set G,
          Set.MapsTo Subtype.val chiRange.source s ∧
          Set.MapsTo Subtype.val chiRange.target t ∧
          s ⊆ xi.source ∧
          t ⊆ xi.target ∧
          Set.EqOn
            (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
            (fun z ↦ xi z.1) chiRange.source ∧
          Set.EqOn
            (fun z ↦ ((chiRange.symm z : Set.range (K : H'' → G)).1))
            (fun z ↦ xi.symm z.1) chiRange.target) :
    ∃ chi : OpenPartialHomeomorph H'' H'',
      chi ∈ contDiffGroupoid ∞ K ∧
      hg.codChart (g (f x)) ∈ chi.source ∧
      Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
  -- Route correction: the real closing step is purely transport. Once `chiRange` exists on
  -- `Set.range K`, the ambient chart change on `H''` follows from the generic transport lemmas.
  rcases hchiRange with
    ⟨chiRange, hz0Range, s, t, hsourceRange, htargetRange, hs_source, ht_target,
      hEqRange, hEqRangeSymm⟩
  rcases
      transport_subtype_homeomorph_to_chart_change
        (K := K) (xi := xi) (y0 := hg.codChart (g (f x))) (s := s) (t := t)
        (chiRange := chiRange)
        (by
          -- The ambient codomain chart value is the same point as the transported subtype basepoint.
          simpa [OpenPartialHomeomorph.extend_coe, hg.mem_codChart_source] using hz0Range)
        hEqRange hEqRangeSymm hsourceRange htargetRange with
    ⟨chi, hbase, hsource, htarget, hEqchi, hEqchi_symm⟩
  have hchi_mem : chi ∈ contDiffGroupoid ∞ K := by
    -- Smoothness is already isolated in `transported_chart_change_mem_contDiffGroupoid`.
    exact transported_chart_change_mem_contDiffGroupoid
      (K := K) (xi := xi) (chi := chi) (s := s) (t := t)
      hxi_cont hsource htarget hs_source ht_target hEqchi hEqchi_symm
  exact ⟨chi, hchi_mem, hbase, hEqchi⟩

/-- Helper for Exercise 4.4: once the restricted source chart still contains the basepoint, the
raw codomain basepoint already supplies the basic source/target data needed to start the final
`Set.range K` transport. -/
lemma codomain_straightening_basepoint_transport_data {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {domChart0 : OpenPartialHomeomorph M H} (hx_domChart0 : x ∈ domChart0.source) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    let z0 : G := (hg.codChart.extend K) (g (f x))
    (∀ ⦃u : E⦄, u ∈ (domChart0.extend I).target →
      hf.equiv (u, (0 : Ff)) ∈ θ.source) →
    z0 = hg.equiv (v0, (0 : Fg)) →
    u0 ∈ (domChart0.extend I).target ∧
      hf.equiv (u0, (0 : Ff)) ∈ θ.source ∧
      z0 ∈ xi.source ∧
      xi z0 ∈ xi.target := by
  intro θ rho eG xi u0 v0 z0 htheta_source hz0_eq
  have hu0_target : u0 ∈ (domChart0.extend I).target := by
    -- The basepoint stays in the target of the restricted extended chart because it lies in the
    -- restricted chart source.
    have hx_source_ext : x ∈ (domChart0.extend I).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hx_domChart0
    simpa [u0] using (domChart0.extend I).map_source hx_source_ext
  have htheta_source0 : hf.equiv (u0, (0 : Ff)) ∈ θ.source :=
    htheta_source hu0_target
  have hz0_source : z0 ∈ xi.source := by
    -- The explicit codomain-slice description of the basepoint places it in the source of `xi`.
    exact
      (codomain_straightening_basepoint_source_data
        (hg := hg) (hf := hf) (domChart0 := domChart0) htheta_source0 hz0_eq).1
  have hxi_z0_target : xi z0 ∈ xi.target := xi.map_source hz0_source
  exact ⟨hu0_target, htheta_source0, hz0_source, hxi_z0_target⟩

/-- Helper for Exercise 4.4: after rewriting the codomain basepoint as the explicit slice
`hg.equiv (v0, 0)`, the conjugated model straightening sends it back to the unstraightened slice
with first coordinate `hf.equiv (u0, 0)`. -/
lemma codomain_straightening_basepoint_image_eq {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    let z0 : G := (hg.codChart.extend K) (g (f x))
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      z0 = hg.equiv (v0, (0 : Fg)) →
      xi z0 = hg.equiv (hf.equiv (u0, (0 : Ff)), (0 : Fg)) := by
  intro θ rho eG xi u0 v0 z0 htheta_source0 hz0_eq
  have htheta_symm_v0 :
      θ.symm v0 = hf.equiv (u0, (0 : Ff)) := by
    -- The inverse middle coordinate change recovers the original `hf`-chart coordinate.
    simpa [v0] using θ.left_inv htheta_source0
  -- Route correction: rewrite `xi z0` once using the explicit codomain slice, then eliminate the
  -- remaining transport with the inverse-chart identity above.
  rw [hz0_eq]
  calc
    xi (hg.equiv (v0, (0 : Fg))) = hg.equiv (θ.symm v0, (0 : Fg)) := by
      simpa [θ, rho, eG, xi] using
        codomain_straightening_model_apply_slice
          (hg := hg) (hf := hf) (v := v0)
    _ = hg.equiv (hf.equiv (u0, (0 : Ff)), (0 : Fg)) := by
      rw [htheta_symm_v0]

/-- Helper for Exercise 4.4: on the source-side model range, the codomain straightening sends
points into the exact target-side locus where the inverse still lands in `Set.range K`. -/
lemma codomain_straightening_mapsTo_target_preserving_range
    {xi : PartialEquiv G G} :
    Set.MapsTo xi (Set.range (K : H'' → G) ∩ xi.source)
      (xi.target ∩ xi.symm ⁻¹' Set.range (K : H'' → G)) := by
  intro z hz
  constructor
  · -- Source points always map into the target of the partial equivalence.
    exact xi.map_source hz.2
  · -- On the source, the inverse recovers the original range point.
    change xi.symm (xi z) ∈ Set.range (K : H'' → G)
    simpa [xi.left_inv hz.2] using hz.1

/-- Helper for Exercise 4.4: on the exact target-side preserving-range locus, the inverse
straightening lands back in the source-side model range. -/
lemma codomain_straightening_symm_mapsTo_source_preserving_range
    {xi : PartialEquiv G G} :
    Set.MapsTo xi.symm
      (xi.target ∩ xi.symm ⁻¹' Set.range (K : H'' → G))
      (Set.range (K : H'' → G) ∩ xi.source) := by
  intro z hz
  constructor
  · -- Membership in the preserving-range locus records the needed range statement directly.
    exact hz.2
  · -- Target points map back into the source of the partial equivalence.
    exact xi.symm_mapsTo hz.1

/-- Helper for Exercise 4.4: a basepoint in the source-side model range is sent into the exact
target-side locus whose inverse still lies in `Set.range K`. -/
lemma codomain_straightening_basepoint_mem_preserving_range
    {xi : PartialEquiv G G} {z0 : G}
    (hz0_range : z0 ∈ Set.range (K : H'' → G)) (hz0_source : z0 ∈ xi.source) :
    xi z0 ∈ xi.target ∩ xi.symm ⁻¹' Set.range (K : H'' → G) := by
  -- This is exactly the basepoint case of the generic source-side range-preservation map.
  exact codomain_straightening_mapsTo_target_preserving_range (K := K) ⟨hz0_range, hz0_source⟩

/-- Helper for Exercise 4.4: the source-faithful codomain-slice witness set already lies in the
exact target-side preserving-range locus. -/
lemma codomain_straightening_target_slice_subset_preserving_range {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let C : Set G := (fun w : F ↦ hg.equiv (w, (0 : Fg))) '' θ.source
    let B : Set G := xi.target ∩ xi.symm ⁻¹' Set.range (K : H'' → G)
    C ⊆ B := by
  intro θ C B
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
    simpa [rho, eG] using hxi_def
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  constructor
  · -- Realize the target slice as the image under `xi` of the straightened slice at `θ w`.
    have hw_theta_target : θ w ∈ θ.target := θ.map_source hw
    have hslice_source : hg.equiv (θ w, (0 : Fg)) ∈ xi.source := by
      have hprod_source : (θ w, (0 : Fg)) ∈ rho.source := by
        simpa [θ, rho, middle_change_prod_chart] using hw_theta_target
      -- Route correction: prove target membership by exhibiting an explicit source point of `xi`.
      rw [hxi_eq]
      simpa [rho, eG, middle_change_prod_chart, PartialEquiv.trans_source] using hprod_source
    have hslice_image :
        xi (hg.equiv (θ w, (0 : Fg))) = hg.equiv (w, (0 : Fg)) := by
      have hslice_image_raw :
          xi (hg.equiv (θ w, (0 : Fg))) = hg.equiv (θ.symm (θ w), (0 : Fg)) := by
        rw [hxi_eq]
        simpa [θ, rho, eG] using
          codomain_straightening_model_apply_slice
            (hg := hg) (hf := hf) (v := θ w)
      simpa [θ.left_inv hw] using hslice_image_raw
    have hslice_target : xi (hg.equiv (θ w, (0 : Fg))) ∈ xi.target := xi.map_source hslice_source
    simpa [hslice_image] using hslice_target
  · -- On source-faithful slice points, `xi.symm` preserves the ambient model range.
    have hw_target : θ w ∈ (hg.domChart.extend J).target := by
      simpa [θ] using
        extendCoordChange_image_mem_target
          (J := J) (e := hf.codChart) (e' := hg.domChart) hw
    rw [hxi_eq]
    simpa [θ, rho, eG] using
      codomain_straightening_model_mem_range_of_slice_symm
        (hg := hg) (hf := hf) (w := w) hw_target

/-- Helper for Exercise 4.4: the codomain slice map `w ↦ hg.equiv (w, 0)` is an embedding. -/
lemma codomain_slice_map_isEmbedding {x : M} {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x)) :
    Topology.IsEmbedding (fun w : F ↦ hg.equiv (w, (0 : Fg))) := by
  -- The slice map is the standard product embedding followed by the linear homeomorphism
  -- attached to the immersion witness `hg`.
  simpa [Function.comp] using
    (hg.equiv.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (0 : Fg)))

/-- Helper for Exercise 4.4: the canonical target-side codomain slice
`ψ '' θ.target` is a neighborhood of the codomain basepoint within the full codomain-slice locus
`ψ '' (hg.domChart.extend J).target`. -/
lemma codomain_target_slice_image_mem_nhdsWithin {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let u0 : E := (domChart0.extend I) x
    let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
    let z0 : G := (hg.codChart.extend K) (g (f x))
    let R : Set G := ψ '' (hg.domChart.extend J).target
    let D : Set G := ψ '' θ.target
    hf.equiv (u0, (0 : Ff)) ∈ θ.source →
      z0 = ψ v0 →
      D ∈ nhdsWithin z0 R := by
  intro θ ψ u0 v0 z0 R D htheta_source0 hz0_eq
  have hψ_emb : Topology.IsEmbedding ψ := codomain_slice_map_isEmbedding (hg := hg)
  have hv0_target : v0 ∈ θ.target := θ.map_source htheta_source0
  have htheta_target :
      θ.target ∈ nhdsWithin v0 (Set.range (J : H' → F)) :=
    extendCoordChange_target_mem_nhdsWithin (J := J) hv0_target
  have htheta_sub_target : θ.target ⊆ (hg.domChart.extend J).target := by
    intro v hv
    -- Read a target point back through `θ.symm`, then reuse the generic target-membership lemma.
    have himage :
        θ (θ.symm v) ∈ (hg.domChart.extend J).target := by
      simpa [θ] using
        extendCoordChange_image_mem_target
          (J := J) (e := hf.codChart) (e' := hg.domChart) (θ.symm_mapsTo hv)
    simpa [θ.right_inv hv] using
      himage
  have hdomChart_target_sub_range :
      (hg.domChart.extend J).target ⊆ Set.range (J : H' → F) := by
    intro v hv
    rw [OpenPartialHomeomorph.extend_target'] at hv
    rcases hv with ⟨y, hy, rfl⟩
    exact ⟨y, rfl⟩
  have htheta_target_on_domChart :
      θ.target ∈ nhdsWithin v0 (hg.domChart.extend J).target := by
    -- The middle-chart target is already a neighborhood within the larger target of `hg`.
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at htheta_target ⊢
    rcases htheta_target with ⟨s, hs_nhds, hs_sub⟩
    refine ⟨s, hs_nhds, ?_⟩
    intro y hy
    exact hs_sub ⟨hy.1, hdomChart_target_sub_range hy.2⟩
  have hD_local :
      D ∈ nhdsWithin (ψ v0) R := by
    -- Push the neighborhood in `F` forward through the embedded codomain slice map.
    rw [← hψ_emb.map_nhdsWithin_eq ((hg.domChart.extend J).target) v0]
    exact Filter.image_mem_map htheta_target_on_domChart
  -- Rewrite the codomain basepoint as the explicit slice point `ψ v0`.
  simpa [R, D, hz0_eq] using hD_local

/-- Helper for Exercise 4.4: the source-side codomain slice `ψ '' θ.source` is a neighborhood of
the unstraightened basepoint inside the ambient source slice carrier `ψ '' Set.range J`. -/
lemma codomain_source_slice_image_mem_nhdsWithin {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) {domChart0 : OpenPartialHomeomorph M H} :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let u0 : E := (domChart0.extend I) x
    let w0 : F := hf.equiv (u0, (0 : Ff))
    let R : Set G := ψ '' Set.range (J : H' → F)
    let C : Set G := ψ '' θ.source
    w0 ∈ θ.source →
      C ∈ nhdsWithin (ψ w0) R := by
  intro θ ψ u0 w0 R C hw0_source
  have hψ_emb : Topology.IsEmbedding ψ := codomain_slice_map_isEmbedding (hg := hg)
  have htheta_source :
      θ.source ∈ nhdsWithin w0 (Set.range (J : H' → F)) :=
    J.extendCoordChange_source_mem_nhdsWithin hw0_source
  have hC_local :
      C ∈ nhdsWithin (ψ w0) R := by
    -- Push the source-side neighborhood in `F` forward through the embedded codomain slice map.
    rw [← hψ_emb.map_nhdsWithin_eq (Set.range (J : H' → F)) w0]
    exact Filter.image_mem_map htheta_source
  simpa [R, C] using hC_local

/-- Helper for Exercise 4.4: pulling the target-side slice witness back along `xi.symm` lands in
the original source-side slice witness. -/
lemma codomain_straightening_target_slice_preimage_subset_source_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let C : Set G := ψ '' θ.source
    let D : Set G := ψ '' θ.target
    let E : Set G := xi.target ∩ xi.symm ⁻¹' D
    E ⊆ C := by
  intro θ ψ C D E
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
    simpa [rho, eG] using hxi_def
  intro y hy
  rcases hy with ⟨hy_target, hyD⟩
  rcases hyD with ⟨v, hv, hsymm_y⟩
  refine ⟨θ.symm v, θ.symm_mapsTo hv, ?_⟩
  -- Rewrite `y` through the partial-equivalence inverse relation and then use the slice formula
  -- for `xi` on the target-side codomain slice `ψ v`.
  have hslice :
      xi (ψ v) = ψ (θ.symm v) := by
    rw [hxi_eq]
    simpa [θ, ψ, rho, eG] using
      codomain_straightening_model_apply_slice
        (hg := hg) (hf := hf) (v := v)
  calc
    ψ (θ.symm v) = xi (ψ v) := hslice.symm
    _ = xi (xi.symm y) := by rw [hsymm_y]
    _ = y := xi.right_inv hy_target

/-- Helper for Exercise 4.4: every target-side codomain slice `ψ v` with `v ∈ θ.target`
already lies in the transported model range and in the source of the conjugated straightening
`xi`. -/
lemma codomain_target_slice_subset_source_range {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let D : Set G := ψ '' θ.target
    D ⊆ Set.range (K : H'' → G) ∩ xi.source := by
  intro θ ψ D
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
    simpa [rho, eG] using hxi_def
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  constructor
  · -- First move the target-side first coordinate into `hg`'s chart target, then apply the
    -- codomain-slice range lemma.
    have hv_domChart_target : v ∈ (hg.domChart.extend J).target := by
      have himage :
          θ (θ.symm v) ∈ (hg.domChart.extend J).target := by
        simpa [θ] using
          extendCoordChange_image_mem_target
            (J := J) (e := hf.codChart) (e' := hg.domChart) (θ.symm_mapsTo hv)
      simpa [θ.right_inv hv] using himage
    exact codomain_slice_mem_model_range (hg := hg) hv_domChart_target
  · -- Reinterpret the codomain slice as a source point of the explicit conjugated straightening.
    have hprod_source : (v, (0 : Fg)) ∈ rho.source := by
      simpa [θ, rho, middle_change_prod_chart] using hv
    rw [hxi_eq]
    simpa [ψ, rho, eG, middle_change_prod_chart, PartialEquiv.trans_source] using hprod_source

/-- Helper for Exercise 4.4: on the target-side codomain slice `ψ '' θ.target`, the conjugated
straightening `xi` lands in the source-side codomain slice `ψ '' θ.source`. -/
lemma codomain_straightening_maps_target_slice_to_source_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let C : Set G := ψ '' θ.source
    let D : Set G := ψ '' θ.target
    Set.MapsTo xi D C := by
  intro θ ψ C D
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
    simpa [rho, eG] using hxi_def
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  refine ⟨θ.symm v, θ.symm_mapsTo hv, ?_⟩
  -- Rewrite `xi` on the target-side slice by the explicit first-coordinate straightening formula.
  rw [hxi_eq]
  simpa [θ, ψ, rho, eG] using
    codomain_straightening_model_apply_slice
      (hg := hg) (hf := hf) (v := v)

/-- Helper for Exercise 4.4: the source-side codomain slice is exactly the target-side preserving
window cut out by pulling `D` back along `xi.symm`. -/
lemma codomain_source_slice_subset_exact_target_window {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let C : Set G := ψ '' θ.source
    let D : Set G := ψ '' θ.target
    let E : Set G := xi.target ∩ xi.symm ⁻¹' D
    C ⊆ E := by
  intro θ ψ C D E
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
    simpa [rho, eG] using hxi_def
  have hC_target :
      C ⊆ xi.target := by
    -- The earlier preserving-range lemma already places every source-side slice point in
    -- `xi.target`.
    have hC_preserving :
        C ⊆ xi.target ∩ xi.symm ⁻¹' Set.range (K : H'' → G) := by
      simpa [θ, ψ, C] using
        codomain_straightening_target_slice_subset_preserving_range
          (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
    intro y hy
    exact (hC_preserving hy).1
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  constructor
  · -- Source-side slice points already lie in the target of `xi`.
    exact hC_target ⟨w, hw, rfl⟩
  · -- Applying `xi.symm` to the source-side slice recovers the target-side slice `ψ (θ w)`.
    refine ⟨θ w, θ.map_source hw, ?_⟩
    rw [hxi_eq]
    simpa [θ, ψ, rho, eG] using
      codomain_straightening_model_apply_slice_symm
        (hg := hg) (hf := hf) (w := w)

/-- Helper for Exercise 4.4: on the source-side codomain slice `ψ '' θ.source`, the inverse
straightening `xi.symm` lands back in the target-side codomain slice `ψ '' θ.target`. -/
lemma codomain_straightening_symm_maps_source_slice_to_target_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let C : Set G := ψ '' θ.source
    let D : Set G := ψ '' θ.target
    Set.MapsTo xi.symm C D := by
  intro θ ψ C D
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
    simpa [rho, eG] using hxi_def
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  refine ⟨θ w, θ.map_source hw, ?_⟩
  -- The inverse model straightening restores the forward middle coordinate change.
  rw [hxi_eq]
  simpa [θ, ψ, rho, eG] using
    codomain_straightening_model_apply_slice_symm
      (hg := hg) (hf := hf) (w := w)

/-- Helper for Exercise 4.4: on the range-preserving source transport domain
`Set.range K ∩ xi.source`, landing in the source-side codomain slice `C` is exactly the
target-side slice condition defining `D`. -/
lemma codomain_target_slice_eq_source_range_preimage_source_slice {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let θ := J.extendCoordChange hf.codChart hg.domChart
    let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
    let C : Set G := ψ '' θ.source
    let D : Set G := ψ '' θ.target
    let A : Set G := Set.range (K : H'' → G) ∩ xi.source
    A ∩ xi ⁻¹' C = D := by
  intro θ ψ C D A
  have hDsubA : D ⊆ A := by
    -- The target-side slice already lies in the range-preserving source transport domain.
    simpa [θ, ψ, D, A] using
      codomain_target_slice_subset_source_range
        (hg := hg) (hf := hf) (xi := xi) hxi_def
  have hCD_maps :
      Set.MapsTo xi D C ∧ Set.MapsTo xi.symm C D := by
    constructor
    · -- The forward straightening sends the target-side slice to the source-side slice.
      simpa [θ, ψ, C, D] using
        codomain_straightening_maps_target_slice_to_source_slice
          (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
    · -- The inverse straightening restores the target-side slice from the source-side slice.
      simpa [θ, ψ, C, D] using
        codomain_straightening_symm_maps_source_slice_to_target_slice
          (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
  ext y
  constructor
  · intro hy
    have hy_source : y ∈ xi.source := hy.1.2
    have hyD : xi.symm (xi y) ∈ D := hCD_maps.2 hy.2
    simpa [xi.left_inv hy_source] using hyD
  · intro hy
    exact ⟨hDsubA hy, hCD_maps.1 hy⟩

/-- Helper for Exercise 4.4: for the exact target window
`E = xi.target ∩ xi.symm ⁻¹' D`, the forward map sends `D` into `E` and the inverse map sends `E`
back into `D`. -/
lemma codomain_straightening_exact_target_window_maps
    {xi : PartialEquiv G G} {D : Set G}
    (hDsub_source_range : D ⊆ Set.range (K : H'' → G) ∩ xi.source) :
    let E : Set G := xi.target ∩ xi.symm ⁻¹' D
    Set.MapsTo xi D E ∧ Set.MapsTo xi.symm E D := by
  intro E
  constructor
  · -- Source points of `D` map into the exact target locus by the partial-equivalence laws.
    intro y hy
    constructor
    · exact xi.map_source (hDsub_source_range hy).2
    · change xi.symm (xi y) ∈ D
      simpa [xi.left_inv (hDsub_source_range hy).2] using hy
  · -- Membership in `E` records the inverse image statement directly.
    intro y hy
    exact hy.2

/-- Helper for Exercise 4.4: once a target window `t` has been chosen inside the exact target
window `E = xi.target ∩ xi.symm ⁻¹' D`, its concrete pullback `s = D ∩ xi ⁻¹' t` already has the
correct source/target and two-way `MapsTo` bookkeeping on `Set.range K`. -/
lemma source_target_window_maps_of_exact_target_window
    {xi : PartialEquiv G G} {D E t : Set G}
    (hDsub_source_range : D ⊆ Set.range (K : H'' → G) ∩ xi.source)
    (hE_eq : E = xi.target ∩ xi.symm ⁻¹' D)
    (ht_sub_E : t ⊆ E)
    (ht_sub_range : t ⊆ Set.range (K : H'' → G)) :
    let s : Set G := D ∩ xi ⁻¹' t
    s ⊆ xi.source ∧
      t ⊆ xi.target ∧
      Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)) ∧
      Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G)) := by
  intro s
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The pullback window stays in the source because its first factor already lies in `D`.
    intro y hy
    exact (hDsub_source_range hy.1).2
  · -- Every point of `t` lies in the exact target window, hence in `xi.target`.
    intro y hy
    rw [hE_eq] at ht_sub_E
    exact (ht_sub_E hy).1
  · -- Forward transport uses the concrete pullback definition of `s` and range preservation of `xi`.
    intro y hy
    rcases hy with ⟨hy_s, hy_range⟩
    -- Route correction: the old statement forgot to assume that the chosen target window already
    -- lies in `Set.range K`, so the previous proof only produced inverse-range preservation.
    exact ⟨hy_s.2, ht_sub_range hy_s.2⟩
  · -- Reverse transport reads `t ⊆ E` as the concrete inverse-image condition defining `D`.
    intro y hy
    rcases hy with ⟨hy_t, hy_range⟩
    have hyE : y ∈ E := ht_sub_E hy_t
    rw [hE_eq] at hyE
    have hyD : xi.symm y ∈ D := hyE.2
    have hy_target : y ∈ xi.target := hyE.1
    have hsymm_mem_t : xi (xi.symm y) ∈ t := by
      simpa [xi.right_inv hy_target] using hy_t
    refine ⟨⟨hyD, hsymm_mem_t⟩, ?_⟩
    exact (hDsub_source_range hyD).1

/-- Helper for Exercise 4.4: transporting the source and target of a local chart change on `H''`
through `K` gives neighborhoods within `Set.range K` of the corresponding ambient points. -/
lemma codomain_chart_change_images_mem_nhdsWithin_range
    {chi : OpenPartialHomeomorph H'' H''} {y0 : H''} (hy0 : y0 ∈ chi.source) :
    K '' chi.source ∈ nhdsWithin (K y0) (Set.range (K : H'' → G)) ∧
      K '' chi.target ∈ nhdsWithin (K (chi y0)) (Set.range (K : H'' → G)) := by
  constructor
  · -- The source of `chi` is open in `H''`, so its image under `K` is a within-range
    -- neighborhood of the basepoint in `Set.range K`.
    have hsource_nhds : chi.source ∈ nhds y0 :=
      IsOpen.mem_nhds chi.open_source hy0
    exact K.image_mem_nhdsWithin hsource_nhds
  · -- The same argument applies to the target after moving the basepoint through `chi`.
    have hy0_target : chi y0 ∈ chi.target := chi.map_source hy0
    have htarget_nhds : chi.target ∈ nhds (chi y0) :=
      IsOpen.mem_nhds chi.open_target hy0_target
    exact K.image_mem_nhdsWithin htarget_nhds

/-- Helper for Exercise 4.4: once the codomain-model straightening has been transported to a local
chart change `chi` on `H''`, postcomposing `hg.codChart` with `chi` gives the codomain chart
package consumed by the final restriction lemmas. -/
lemma transported_codomain_chart_package {x : M} {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    {xi : G → G}
    (hchi :
      ∃ chi : OpenPartialHomeomorph H'' H'',
        chi ∈ contDiffGroupoid ∞ K ∧
        hg.codChart (g (f x)) ∈ chi.source ∧
        Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source) :
    ∃ codChart1 : OpenPartialHomeomorph P H'',
      g (f x) ∈ codChart1.source ∧
      codChart1 ∈ IsManifold.maximalAtlas K ∞ P ∧
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
    exact trans_mem_maximalAtlas_of_mem_groupoid_infty
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

/-- Helper for Exercise 4.4: a model-space open partial homeomorphism belongs to the smooth
groupoid once its whole source is locally covered by smooth structomorph charts. -/
theorem mem_contDiffGroupoid_of_local_structomorphOn_source
    {f : OpenPartialHomeomorph H'' H''}
    (hf : ChartedSpace.LiftPropOn
      ((contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt) f f.source) :
    f ∈ contDiffGroupoid ∞ K := by
  refine (contDiffGroupoid ∞ K).locality ?_
  intro x hx
  -- The local structomorphism data gives a genuine groupoid element on a neighborhood of `x`.
  have hfx := hf x hx
  have hfx' := hfx
  simp only [ChartedSpace.liftPropWithinAt_iff', chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm] at hfx'
  obtain ⟨-, hfx_prop⟩ := hfx'
  have hfx_prop' : (contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt f f.source x := by
    simpa using hfx_prop
  rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    (G := contDiffGroupoid ∞ K) (f := f)] at hfx_prop'
  obtain ⟨e, he, hsource, hEq, hxe⟩ := hfx_prop' hx
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  -- Restricting `f` to the neighborhood where it agrees with `e` identifies the two
  -- open partial homeomorphisms.
  have hEq' : Set.EqOn f e (f.source ∩ e.source) := by
    intro y hy
    exact hEq hy.2
  have hrestr : f.restr e.source ≈ e.restr f.source := by
    exact OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEq'
  have hEqOnSource : f.restr e.source ≈ e := by
    simpa [OpenPartialHomeomorph.restr_eq_of_source_subset hsource] using hrestr
  exact (contDiffGroupoid ∞ K).mem_of_eqOnSource he hEqOnSource

/-- Helper for Exercise 4.4: forgetting the inverse of a model-space partial diffeomorphism
produces an element of the smooth structure groupoid. -/
theorem model_partial_diffeomorph_mem_contDiffGroupoid
    {Φ : PartialDiffeomorph K K H'' H'' ∞} :
    Φ.toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ K := by
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt)
        Φ.toOpenPartialHomeomorph Φ.source := by
    -- The partial diffeomorphism is smooth in both directions on its own source and target.
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := K) (n := ∞) (f := Φ.toOpenPartialHomeomorph)).2
      ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩
  exact mem_contDiffGroupoid_of_local_structomorphOn_source (K := K) hΦ

/-- Helper for Exercise 4.4: writing a manifold partial diffeomorphism in maximal-atlas charts
produces a smooth transition map on the model space. -/
theorem writtenIn_partial_diffeomorph_mem_contDiffGroupoid
    {P' : Type*} [TopologicalSpace P'] [ChartedSpace H'' P']
    [IsManifold K ∞ P] [IsManifold K ∞ P']
    {Φ : PartialDiffeomorph K K P P' ∞} {e : OpenPartialHomeomorph P H''}
    {c : OpenPartialHomeomorph P' H''}
    (he : e ∈ IsManifold.maximalAtlas K ∞ P)
    (hc : c ∈ IsManifold.maximalAtlas K ∞ P') :
    (e.symm.trans Φ.toOpenPartialHomeomorph).trans c ∈ contDiffGroupoid ∞ K := by
  let f : OpenPartialHomeomorph H'' H'' := (e.symm.trans Φ.toOpenPartialHomeomorph).trans c
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt)
        Φ.toOpenPartialHomeomorph Φ.source := by
    -- The partial diffeomorphism is smooth in both directions on its own source and target.
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := K) (n := ∞) (f := Φ.toOpenPartialHomeomorph)).2
      ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩
  -- Writing `Φ` in maximal-atlas charts transports its local structomorphism property to the
  -- model space, where `mem_contDiffGroupoid_of_local_structomorphOn_source` can close.
  refine mem_contDiffGroupoid_of_local_structomorphOn_source (K := K) ?_
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
      (contDiffGroupoid ∞ K).IsLocalStructomorphWithinAt
        (c ∘ Φ.toOpenPartialHomeomorph ∘ e.symm)
        (e.symm ⁻¹' Φ.source) y := by
    exact StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid ∞ K))
      he hc hΦ hy_chart
  rcases htransport hy_chart.2.1 with ⟨φ, hφ, hEq, hyφ⟩
  refine ⟨φ, hφ, ?_, hyφ⟩
  -- The source of the written-in-chart map is the usual chart-transport source, so the witness
  -- from the bigger set `e.symm ⁻¹' Φ.source` also works on the actual composite source.
  intro z hz
  have hz_big : z ∈ (e.symm ⁻¹' Φ.source) ∩ φ.source := by
    refine ⟨?_, hz.2⟩
    have hz' := hz.1
    simp only [f, OpenPartialHomeomorph.trans_source, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hz'
    exact hz'.1.2
  simpa [f, OpenPartialHomeomorph.coe_trans, Function.comp_assoc] using hEq hz_big

/-- Helper for Exercise 4.4: once a codomain straightening has been built directly on the
transported model subtype `Set.range K`, conjugating by `H'' ≃ₜ Set.range K` packages it into a
chart change on `H''`. -/
lemma writtenIn_range_straightening_to_chart_change
    {xi : G → G} {y0 : H''}
    {chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G))}
    (hchiRange_mem :
      let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
        (codomain_model_range_homeomorph (K := K)).symm.toOpenPartialHomeomorph
      ((eRange.symm.trans chiRange).trans eRange) ∈ contDiffGroupoid ∞ K)
    (hy0 : (⟨K y0, ⟨y0, rfl⟩⟩ : Set.range (K : H'' → G)) ∈ chiRange.source)
    (hEqRange :
      Set.EqOn
        (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
        (fun z ↦ xi z.1) chiRange.source) :
    ∃ chi : OpenPartialHomeomorph H'' H'',
      chi ∈ contDiffGroupoid ∞ K ∧
      y0 ∈ chi.source ∧
      Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
  let eK : H'' ≃ₜ Set.range (K : H'' → G) := codomain_model_range_homeomorph (K := K)
  let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
    eK.symm.toOpenPartialHomeomorph
  let chi : OpenPartialHomeomorph H'' H'' :=
    (eRange.symm.trans chiRange).trans eRange
  have hchi_mem : chi ∈ contDiffGroupoid ∞ K := by
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

/-- Helper for Exercise 4.4: once a new codomain chart around `(g ∘ f) x` is chosen, continuity of
`g ∘ f` lets us restrict a source chart around `x` so the whole restricted source lands in that new
codomain-chart source. -/
lemma exists_restr_chart_into_codomain_source {x : M}
    (hcont : ContinuousAt (g ∘ f) x) {domChart0 : OpenPartialHomeomorph M H}
    (hx_domChart0 : x ∈ domChart0.source)
    (hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I ∞ M)
    {codChart1 : OpenPartialHomeomorph P H''}
    (hgf_codChart1 : g (f x) ∈ codChart1.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ domChart0.source ∧ V ⊆ (g ∘ f) ⁻¹' codChart1.source ∧
      x ∈ (domChart0.restr V).source ∧
      domChart0.restr V ∈ IsManifold.maximalAtlas I ∞ M := by
  -- Intersect the old source chart with the preimage of the new codomain-chart source.
  have hdom_nhds : domChart0.source ∈ nhds x :=
    IsOpen.mem_nhds domChart0.open_source hx_domChart0
  have hcod_nhds : codChart1.source ∈ nhds (g (f x)) :=
    IsOpen.mem_nhds codChart1.open_source hgf_codChart1
  have hpre_nhds : domChart0.source ∩ (g ∘ f) ⁻¹' codChart1.source ∈ nhds x := by
    exact Filter.inter_mem hdom_nhds (hcont.preimage_mem_nhds hcod_nhds)
  obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp hpre_nhds
  refine ⟨V, hV_open, hxV, fun y hy ↦ (hV_sub hy).1, fun y hy ↦ (hV_sub hy).2, ?_, ?_⟩
  · -- The restricted chart still contains the base point.
    simpa [OpenPartialHomeomorph.restr_source, hV_open.interior_eq] using
      show x ∈ domChart0.source ∩ V from ⟨hx_domChart0, hxV⟩
  · -- Restricting a maximal-atlas chart to an open neighborhood stays in the maximal atlas.
    simpa using
      restr_mem_maximalAtlas (contDiffGroupoid ∞ I) hdomChart0_mem hV_open

/-- Helper for Exercise 4.4: once a transported codomain chart is known and its extended chart
agrees with the model-space straightening `xi` on the whole chart source, continuity of `g ∘ f`
provides the final source restriction needed by the composition proof. -/
lemma final_transport_from_chart_extend_eq {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    {domChart0 : OpenPartialHomeomorph M H}
    (hcont : ContinuousAt (g ∘ f) x)
    (hx_domChart0 : x ∈ domChart0.source)
    (hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I ∞ M)
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
  rcases exists_restr_chart_into_codomain_source
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
    exact restr_extend_symm_eq_of_openPartialHomeomorph
      (I := I) (e := domChart0) (U := V) hV_open hu
  -- Rewrite the new codomain chart using `hcodChart1`, then replace the restricted inverse.
  simpa [Function.comp, hu_symm_eq] using hcodChart1 hgf_source

/-- Helper for Exercise 4.4: once a transported codomain chart is available on a final restricted
source chart, the remaining written-in-charts argument is exactly `hxi_raw` plus the linear
reassociation `hequivTot`. -/
lemma straightened_writtenInCharts_on_final_restr {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {domChart0 : OpenPartialHomeomorph M H}
    (hx_domChart0 : x ∈ domChart0.source)
    (hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I ∞ M)
    {xi : G → G}
    (hxi_raw :
      Set.EqOn
        (fun u ↦ xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u))
        (fun u ↦ hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)))
        (domChart0.extend I).target)
    {codChart1 : OpenPartialHomeomorph P H''}
    (hgf_codChart1 : g (f x) ∈ codChart1.source)
    (hcodChart1_mem : codChart1 ∈ IsManifold.maximalAtlas K ∞ P)
    {V : Set M} (hV_open : IsOpen V) (hxV : x ∈ V) (hV_dom : V ⊆ domChart0.source)
    (htransport :
      Set.EqOn
        (((codChart1.extend K) ∘ g ∘ f ∘ ((domChart0.restr V).extend I).symm))
        (fun u ↦ xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u))
        ((domChart0.restr V).extend I).target) :
    IsImmersionAtOfComplement (Ff × Fg) I K ∞ (g ∘ f) x := by
  let assocEquiv : (E × (Ff × Fg)) ≃L[𝕜] ((E × Ff) × Fg) :=
    (LinearIsometryEquiv.prodAssoc 𝕜 E Ff Fg).symm.toContinuousLinearEquiv
  let equivTot : (E × (Ff × Fg)) ≃L[𝕜] G :=
    assocEquiv.trans ((hf.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 Fg)).trans hg.equiv)
  let domChart1 := domChart0.restr V
  have hx_domChart1 : x ∈ domChart1.source := by
    -- The final restriction still contains `x` by construction.
    simpa [domChart1, OpenPartialHomeomorph.restr_source, hV_open.interior_eq] using
      show x ∈ domChart0.source ∩ V from ⟨hx_domChart0, hxV⟩
  have hdomChart1_mem : domChart1 ∈ IsManifold.maximalAtlas I ∞ M := by
    -- Restricting the source chart preserves maximal-atlas membership.
    simpa [domChart1] using
      restr_mem_maximalAtlas (contDiffGroupoid ∞ I) hdomChart0_mem hV_open
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (hg.continuousAt.comp hf.continuousAt) equivTot domChart1 codChart1
    hx_domChart1 hgf_codChart1 hdomChart1_mem hcodChart1_mem ?_
  intro u hu
  have hu_domChart0 :
      u ∈ (domChart0.extend I).target := by
    -- The final restricted target still lies in the earlier restricted target from `hxi_raw`.
    simpa [domChart1] using
      restr_extend_target_mem_of_openPartialHomeomorph
        (I := I) (e := domChart0) (U := V) hV_open hu
  -- First transport the new codomain chart expression back to `xi`, then invoke `hxi_raw`.
  calc
    ((codChart1.extend K) ∘ g ∘ f ∘ (domChart1.extend I).symm) u
        = xi (((hg.codChart.extend K) ∘ g ∘ f ∘ (domChart0.extend I).symm) u) := by
            simpa [domChart1] using htransport hu
    _ = hg.equiv (hf.equiv (u, (0 : Ff)), (0 : Fg)) := hxi_raw hu_domChart0
    _ = equivTot (u, (0 : Ff × Fg)) := by
          simp [equivTot, assocEquiv]

/-- Helper for Exercise 4.4: rewriting `g` in the restricted source chart coming from `hf`
produces the raw middle-chart expression `hg.equiv (θ v, 0)`. -/
lemma aligned_source_change_raw {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
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
  have hy_symm :
      (hf.codChart.extend J).symm v = y := by
    -- The restricted and unrestricted chart inverses agree on the restricted target.
    simpa [y] using
      (restr_extend_symm_eq_of_openPartialHomeomorph
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

/-- Helper for Exercise 4.4: the conjugated model straightening `xi` already cancels the raw
middle-chart term on the restricted source chart coming from `hf`. -/
lemma aligned_codomain_straightening_on_restr {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg] (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {W : Set N} (hW_open : IsOpen W)
    (hW_sub : W ⊆ hf.codChart.source ∩ hg.domChart.source) :
    let rho : PartialEquiv (F × Fg) (F × Fg) :=
      middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
    Set.EqOn
      (fun v ↦ xi (((hg.codChart.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm) v))
      (fun v ↦ hg.equiv (v, (0 : Fg)))
      ((hf.codChart.restr W).extend J).target := by
  dsimp
  intro v hv
  let θ : PartialEquiv F F := J.extendCoordChange hf.codChart hg.domChart
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
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
      aligned_source_change_raw (hg := hg) (hf := hf) (W := W) hW_open hW_sub hv
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
          simpa [xi, rho, eG, θ, middle_change_prod_chart] using
            (codomain_straightening_model_apply_slice
              (hg := hg) (hf := hf) (v := θ v))
    _ = hg.equiv (v, (0 : Fg)) := by
          rw [(show θ.symm (θ v) = v from θ.left_inv hv_theta_source)]

/-- Helper for Exercise 4.4: the remaining geometric step is to build the codomain straightening
directly on `Set.range K`, using windows that are open in the subtype topology instead of forcing
them into ambient-open subsets of `G`. -/
lemma subtype_local_codomain_straightening_of_range_windows
    {xi : PartialEquiv G G} {y0 : H''}
    (hxi_cont : ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target)
    {s t : Set G}
    (hs_open : IsOpen (Subtype.val ⁻¹' s : Set (Set.range (K : H'' → G))))
    (ht_open : IsOpen (Subtype.val ⁻¹' t : Set (Set.range (K : H'' → G))))
    (hy0s : K y0 ∈ s) (hxi_y0_t : xi (K y0) ∈ t)
    (hs_source : s ⊆ xi.source) (ht_target : t ⊆ xi.target)
    (hmap : Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)))
    (hmap_symm :
      Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G))) :
    ∃ chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)),
      let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
        (codomain_model_range_homeomorph (K := K)).symm.toOpenPartialHomeomorph
      ((eRange.symm.trans chiRange).trans eRange) ∈ contDiffGroupoid ∞ K ∧
        (⟨K y0, ⟨y0, rfl⟩⟩ : Set.range (K : H'' → G)) ∈ chiRange.source ∧
        Set.EqOn
          (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
          (fun z ↦ xi z.1) chiRange.source := by
  -- Package the range-open windows into a subtype chart change first.
  rcases
      range_window_homeomorph_to_partial_homeomorph_on_range_of_subtype_open
        (K := K) (xi := xi) (y0 := y0) hxi_cont hs_open ht_open hy0s hxi_y0_t
        hs_source ht_target hmap hmap_symm with
    ⟨chiRange, hy0Range, hsourceRange, htargetRange, hEqRange, hEqRangeSymm⟩
  let eK : H'' ≃ₜ Set.range (K : H'' → G) := codomain_model_range_homeomorph (K := K)
  let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
    eK.symm.toOpenPartialHomeomorph
  let chi : OpenPartialHomeomorph H'' H'' :=
    (eRange.symm.trans chiRange).trans eRange
  have hsource : Set.MapsTo K chi.source s := by
    intro y hy
    have hyRange : eK y ∈ chiRange.source := by
      -- Read transported source membership back on the subtype side.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_source] using hy
    simpa [eK] using hsourceRange hyRange
  have htarget : Set.MapsTo K chi.target t := by
    intro y hy
    have hyRange : eK y ∈ chiRange.target := by
      -- The transported target is the pullback of the subtype target window.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_target] using hy
    simpa [eK] using htargetRange hyRange
  have hEqchi :
      Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
    intro y hy
    have hyRange : eK y ∈ chiRange.source := by
      -- Source membership for the transported chart is exactly source membership for `chiRange`.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_source] using hy
    have htransport :
        eK (chi y) = chiRange (eK y) := by
      -- Conjugating by the model-range homeomorphism recovers the subtype chart change.
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
  have hEqchi_symm :
      Set.EqOn (fun y ↦ K (chi.symm y)) (fun y ↦ xi.symm (K y)) chi.target := by
    intro y hy
    have hyRange : eK y ∈ chiRange.target := by
      -- The inverse transported target is likewise read in the subtype model.
      simpa [chi, eRange, eK, OpenPartialHomeomorph.trans_target] using hy
    have htransport :
        eK (chi.symm y) = chiRange.symm (eK y) := by
      -- The same conjugation identity holds for the inverse chart change.
      calc
        eK (chi.symm y)
            = eK (eRange (chiRange.symm (eRange.symm y))) := by
                rfl
        _ = chiRange.symm (eRange.symm y) := by
              simp [eRange, eK]
        _ = chiRange.symm (eK y) := by
              rfl
    calc
      K (chi.symm y) = ((chiRange.symm (eK y) : Set.range (K : H'' → G)).1) := by
        simpa [eK] using congrArg Subtype.val htransport
      _ = xi.symm (K y) := by
        simpa [eK] using hEqRangeSymm hyRange
  have hchi_mem : chi ∈ contDiffGroupoid ∞ K := by
    -- Once the transported chart change agrees with `xi` through `K`, smoothness is automatic.
    exact transported_chart_change_mem_contDiffGroupoid
      (K := K) (xi := xi) (chi := chi) (s := s) (t := t)
      hxi_cont hsource htarget hs_source ht_target hEqchi hEqchi_symm
  refine ⟨chiRange, ?_⟩
  -- The target statement records exactly the transported groupoid membership and source formula.
  dsimp
  exact ⟨by simpa [chi, eRange] using hchi_mem, hy0Range, hEqRange⟩

/-- Helper for Exercise 4.4: once the transported source and target-preserving domains of `xi`
are known to be open in `Set.range K`, the remaining range-window package is formal bookkeeping. -/
lemma codomain_straightening_full_range_windows {x : M} {Ff : Type*}
    [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg]
    [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G} {z0 : G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv)
    (hz0_range : z0 ∈ Set.range (K : H'' → G))
    (hz0_source : z0 ∈ xi.source) :
    ∃ s t : Set G,
      IsOpen (Subtype.val ⁻¹' s : Set (Set.range (K : H'' → G))) ∧
      IsOpen (Subtype.val ⁻¹' t : Set (Set.range (K : H'' → G))) ∧
      z0 ∈ s ∧ xi z0 ∈ t ∧
      s ⊆ xi.source ∧ t ⊆ xi.target ∧
      Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)) ∧
      Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G)) := by
  have hxi_cont :
      ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target := by
    -- The transported codomain straightening is already smooth on its natural source and target.
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
      simpa [rho, eG] using hxi_def
    rw [hxi_eq]
    simpa [rho, eG] using codomain_straightening_model_contDiff (hg := hg) (hf := hf)
  have hxi_z0_exact_target :
      xi z0 ∈ xi.target ∩ xi.symm ⁻¹' Set.range (K : H'' → G) := by
    -- The source-side basepoint already lands in the exact target-side preserving-range locus.
    exact
      codomain_straightening_basepoint_mem_preserving_range
        (K := K) (xi := xi) hz0_range hz0_source
  -- Route correction: abandon the codimension-`Fg` slice windows `C`, `D`, `E`. The remaining
  -- source-faithful route is to work with the full transported domains of `xi` on `Set.range K`.
  have hsource_nhds :
      xi.source ∈ nhdsWithin z0 (Set.range (K : H'' → G)) := by
    -- TODO: rewrite `xi.source` through `hxi_def` as the first-coordinate condition for
    -- `middle_change_prod_chart`, then pull back the within-range neighborhood `θ.target`
    -- along `z ↦ (hg.equiv.symm z).1` on `Set.range K`.
    sorry
  have hexact_target_nhds :
      (xi.target ∩ xi.symm ⁻¹' Set.range (K : H'' → G)) ∈
        nhdsWithin (xi z0) (Set.range (K : H'' → G)) := by
    -- TODO: after the full target domain is known to be a within-range neighborhood, restrict the
    -- inverse continuity of `xi.symm` to that target neighborhood and pull back `Set.range K`.
    -- This should produce the exact preserving-range locus needed for the final target window.
    sorry
  -- TODO: shrink `hsource_nhds` to a subtype-open source prewindow `u`, pull `u ∩ rangeK`
  -- back along `xi.symm` inside `hexact_target_nhds` to get a subtype-open target prewindow,
  -- then alternate one more source/target shrink so both `MapsTo` directions hold.
  sorry

/-- Helper for Exercise 4.4: the remaining geometric step is to build the codomain straightening
directly on `Set.range K` instead of forcing the slice witnesses into ambient-open subsets of
`G`. -/
lemma subtype_local_codomain_straightening {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x)
    {xi : PartialEquiv G G}
    (hxi_def :
      let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
      let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
      xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv) :
    let z0 : G := (hg.codChart.extend K) (g (f x))
    let z0Range : Set.range (K : H'' → G) :=
      ⟨z0, codomain_chart_basepoint_mem_model_range (hg := hg)⟩
    ∃ chiRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) (Set.range (K : H'' → G)),
      let eRange : OpenPartialHomeomorph (Set.range (K : H'' → G)) H'' :=
        (codomain_model_range_homeomorph (K := K)).symm.toOpenPartialHomeomorph
      ((eRange.symm.trans chiRange).trans eRange) ∈ contDiffGroupoid ∞ K ∧
        z0Range ∈ chiRange.source ∧
        Set.EqOn
          (fun z ↦ ((chiRange z : Set.range (K : H'' → G)).1))
          (fun z ↦ xi z.1) chiRange.source := by
  intro z0 z0Range
  let θ : PartialEquiv F F := J.extendCoordChange hf.codChart hg.domChart
  let ψ : F → G := fun w ↦ hg.equiv (w, (0 : Fg))
  let D : Set G := ψ '' θ.target
  let u0 : E := (hf.domChart.extend I) x
  let v0 : F := θ (hf.equiv (u0, (0 : Ff)))
  have hx_source_ext : x ∈ (hf.domChart.extend I).source := by
    -- The basepoint lies in the source of the extended source chart of `hf`.
    simpa [OpenPartialHomeomorph.extend_source] using hf.mem_domChart_source
  have hu0_target : u0 ∈ (hf.domChart.extend I).target := by
    -- The image of the basepoint under the extended source chart is a target point.
    simpa [u0] using (hf.domChart.extend I).map_source hx_source_ext
  have hu0_symm : (hf.domChart.extend I).symm u0 = x := by
    -- Evaluating the chart inverse at the chart value of `x` recovers `x`.
    simpa [u0] using (hf.domChart.extend I).left_inv hx_source_ext
  have htheta_source0 : hf.equiv (u0, (0 : Ff)) ∈ θ.source := by
    -- The basepoint lies in the overlap of the middle charts of `hf` and `hg`.
    have hz_image :
        (hf.codChart.extend J) (f x) ∈ θ.source := by
      rw [← OpenPartialHomeomorph.extend_image_source_inter (I := J)
        (f := hf.codChart) (f' := hg.domChart)]
      exact ⟨f x, ⟨hf.mem_codChart_source, hg.mem_domChart_source⟩, rfl⟩
    have hwritten0 :
        hf.equiv (u0, (0 : Ff)) = (hf.codChart.extend J) (f x) := by
      calc
        hf.equiv (u0, (0 : Ff))
            = (((hf.codChart.extend J) ∘ f ∘ (hf.domChart.extend I).symm) u0) := by
                symm
                exact hf.writtenInCharts hu0_target
        _ = (hf.codChart.extend J) (f ((hf.domChart.extend I).symm u0)) := by
              rfl
        _ = (hf.codChart.extend J) (f x) := by
              rw [hu0_symm]
    exact hwritten0 ▸ hz_image
  have hv0_target : v0 ∈ θ.target := by
    -- The middle coordinate change sends the basepoint slice to its target slice.
    simpa [v0] using θ.map_source htheta_source0
  have hz0_eq : z0 = ψ v0 := by
    -- Evaluate the raw written-in-charts identity for the composition at the basepoint.
    have hmid0 : f ((hf.domChart.extend I).symm u0) ∈ hg.domChart.source := by
      rw [hu0_symm]
      exact hg.mem_domChart_source
    calc
      z0 = (hg.codChart.extend K) (g (f x)) := rfl
      _ = (((hg.codChart.extend K) ∘ g ∘ f ∘ (hf.domChart.extend I).symm) u0) := by
            rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, hu0_symm]
      _ = hg.equiv (θ (hf.equiv (u0, (0 : Ff))), (0 : Fg)) := by
            exact comp_raw_middle_change (hg := hg) (hf := hf) (u := u0) (hu := hu0_target)
              hmid0
      _ = ψ v0 := by
            simp [ψ, v0]
  have hz0_mem_D : z0 ∈ D := by
    -- The codomain basepoint is one of the target-side codomain slices.
    exact ⟨v0, hv0_target, hz0_eq.symm⟩
  have hz0_source : z0 ∈ xi.source := by
    -- Rewriting the basepoint as the explicit codomain slice places it in `xi.source`.
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
      simpa [rho, eG] using hxi_def
    have hz0_source_data :
        z0 ∈ ((eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv).source := by
      exact
        (codomain_straightening_basepoint_source_data
          (hg := hg) (hf := hf) (domChart0 := hf.domChart) htheta_source0
          (by simpa [u0, v0, z0, ψ] using hz0_eq)).1
    rw [hxi_eq]
    exact hz0_source_data
  have hxi_z0_target : xi z0 ∈ xi.target := xi.map_source hz0_source
  have hDsub_source_range : D ⊆ Set.range (K : H'' → G) ∩ xi.source := by
    -- Every target-side codomain slice already lies in the transported model range and in
    -- `xi.source`.
    simpa [θ, ψ, D] using
      codomain_target_slice_subset_source_range
        (hg := hg) (hf := hf) (xi := xi) hxi_def
  have hxi_cont :
      ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target := by
    -- The ambient conjugated straightening is already known to be smooth in both directions.
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
      simpa [rho, eG] using hxi_def
    rw [hxi_eq]
    simpa [rho, eG] using codomain_straightening_model_contDiff (hg := hg) (hf := hf)
  have hxi_within_cont :
      ContinuousWithinAt xi (Set.range (K : H'' → G) ∩ xi.source) z0 ∧
        ContinuousWithinAt xi.symm (Set.range (K : H'' → G) ∩ xi.target) (xi z0) := by
    -- The ambient smoothness package restricts to continuity on the range-preserving domains.
    exact codomain_straightening_within_range_continuous
      (K := K) (xi := xi) hxi_cont hz0_source
  let C : Set G := ψ '' θ.source
  let E : Set G := xi.target ∩ xi.symm ⁻¹' D
  have hE_sub_C : E ⊆ C := by
    -- The exact target witness already sits inside the source-side codomain slice.
    simpa [θ, ψ, C, D, E] using
      codomain_straightening_target_slice_preimage_subset_source_slice
        (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
  have hC_sub_E : C ⊆ E := by
    -- The source-side codomain slice is exactly the target-side range-preserving window.
    simpa [θ, ψ, C, D, E] using
      codomain_source_slice_subset_exact_target_window
        (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
  have hC_eq_E : C = E := Set.Subset.antisymm hC_sub_E hE_sub_C
  have hCD_maps :
      Set.MapsTo xi D C ∧ Set.MapsTo xi.symm C D := by
    constructor
    · -- The forward straightening carries the target-side slice to the source-side slice.
      simpa [θ, ψ, C, D] using
        codomain_straightening_maps_target_slice_to_source_slice
          (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
    · -- The inverse straightening carries the source-side slice back to the target-side slice.
      simpa [θ, ψ, C, D] using
        codomain_straightening_symm_maps_source_slice_to_target_slice
          (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
  have hxi_z0_mem_C : xi z0 ∈ C := hCD_maps.1 hz0_mem_D
  have hC_sub_target : C ⊆ xi.target := by
    -- The exact target-side window description already records target membership for `C`.
    intro y hy
    exact (hC_sub_E hy).1
  have hD_eq_preimage :
      (Set.range (K : H'' → G) ∩ xi.source) ∩ xi ⁻¹' C = D := by
    -- On the range-preserving source domain, hitting the source-side slice `C` is exactly the
    -- target-side slice condition `D`.
    simpa [θ, ψ, C, D] using
      codomain_target_slice_eq_source_range_preimage_source_slice
        (K := K) (hg := hg) (hf := hf) (xi := xi) hxi_def
  have hC_sub_image_source_range :
      C ⊆ xi '' (Set.range (K : H'' → G) ∩ xi.source) := by
    -- Read each point of `C` back through `xi.symm`; the exact target-side description places
    -- that inverse point in `D`, hence in the source transport domain.
    intro y hy
    refine ⟨xi.symm y, hDsub_source_range ((hCD_maps.2 hy)), ?_⟩
    exact xi.right_inv (hC_sub_target hy)
  have hD_nhds_range :
      D ∈ nhdsWithin z0 (ψ '' (hg.domChart.extend J).target) := by
    -- Route correction: reuse the earlier target-side codomain-slice neighborhood exactly in the
    -- ambient carrier supplied by the codomain normal-form theorem.
    simpa [θ, ψ, D, z0, u0, v0] using
      (codomain_target_slice_image_mem_nhdsWithin
        (J := J) (K := K) (hg := hg) (hf := hf) (domChart0 := hf.domChart)
        htheta_source0 hz0_eq)
  have hxi_z0_eq_source_slice :
      xi z0 = ψ (hf.equiv (u0, (0 : Ff))) := by
    -- The conjugated codomain straightening sends the straightened basepoint back to the
    -- source-side slice basepoint.
    let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
    let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
    have hxi_eq : xi = (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv := by
      simpa [rho, eG] using hxi_def
    rw [hxi_eq]
    simpa [θ, ψ, z0, u0, v0, rho, eG] using
      (codomain_straightening_basepoint_image_eq
        (J := J) (K := K) (hg := hg) (hf := hf) (domChart0 := hf.domChart)
        htheta_source0 hz0_eq)
  have hC_nhds_slice_range :
      C ∈ nhdsWithin (xi z0) (ψ '' Set.range (J : H' → F)) := by
    -- The symmetric source-side slice is also a neighborhood, but only inside its own slice
    -- carrier. This is the exact frontier reached before transporting to `Set.range K`.
    simpa [θ, ψ, C, u0, hxi_z0_eq_source_slice] using
      (codomain_source_slice_image_mem_nhdsWithin
        (J := J) (K := K) (hg := hg) (hf := hf) (domChart0 := hf.domChart)
        htheta_source0)
  have hR_sub_range :
      ψ '' (hg.domChart.extend J).target ⊆ Set.range (K : H'' → G) := by
    -- Every codomain slice over the domain-chart target already lies in the ambient model range.
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact codomain_slice_mem_model_range (K := K) (hg := hg) hv
  have hwindow_package :
      ∃ s t : Set G,
        IsOpen (Subtype.val ⁻¹' s : Set (Set.range (K : H'' → G))) ∧
        IsOpen (Subtype.val ⁻¹' t : Set (Set.range (K : H'' → G))) ∧
        z0 ∈ s ∧ xi z0 ∈ t ∧
        s ⊆ xi.source ∧ t ⊆ xi.target ∧
        Set.MapsTo xi (s ∩ Set.range (K : H'' → G)) (t ∩ Set.range (K : H'' → G)) ∧
        Set.MapsTo xi.symm (t ∩ Set.range (K : H'' → G)) (s ∩ Set.range (K : H'' → G)) := by
    -- Route correction: use the full transported source and target-preserving domains of `xi`
    -- on `Set.range K`, not the old codimension-`Fg` slice windows `D`, `C`, and `E`.
    exact
      codomain_straightening_full_range_windows
        (K := K) (hg := hg) (hf := hf) (xi := xi) (z0 := z0) hxi_def z0Range.2 hz0_source
  rcases hwindow_package with
    ⟨s, t, hs_open, ht_open, hz0s, hxi_z0_t, hs_source, ht_target, hmap, hmap_symm⟩
  -- Once the range-preserving windows exist, the subtype-local chart change is already packaged.
  simpa [z0, z0Range, OpenPartialHomeomorph.extend_coe, hg.mem_codChart_source] using
    subtype_local_codomain_straightening_of_range_windows
      (K := K) (xi := xi) (y0 := hg.codChart (g (f x))) hxi_cont hs_open ht_open
      (by simpa [z0, OpenPartialHomeomorph.extend_coe, hg.mem_codChart_source] using hz0s)
      (by simpa [z0, OpenPartialHomeomorph.extend_coe, hg.mem_codChart_source] using hxi_z0_t)
      hs_source ht_target hmap hmap_symm

/-- Helper for Exercise 4.4: align the source chart of `g` with the codomain chart of `hf`
before transporting the codomain straightening back through `K`. -/
lemma exists_aligned_codomain_chart_for_g {x : M} {Ff : Type*} [NormedAddCommGroup Ff]
    [NormedSpace 𝕜 Ff] {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) :
    ∃ W : Set N, IsOpen W ∧ f x ∈ W ∧ W ⊆ hf.codChart.source ∩ hg.domChart.source ∧
      ∃ codChart1 : OpenPartialHomeomorph P H'',
        g (f x) ∈ codChart1.source ∧
        codChart1 ∈ IsManifold.maximalAtlas K ∞ P ∧
        Set.EqOn
          (((codChart1.extend K) ∘ g ∘ ((hf.codChart.restr W).extend J).symm))
          (fun v ↦ hg.equiv (v, (0 : Fg)))
          ((hf.codChart.restr W).extend J).target := by
  -- Route correction: the right structural step is to rewrite `g` using the source chart supplied
  -- by `hf`, then transport the resulting model-space straightening through `K`.
  let rho : PartialEquiv (F × Fg) (F × Fg) := middle_change_prod_chart (hg := hg) (hf := hf)
  let eG : OpenPartialHomeomorph (F × Fg) G := hg.equiv.toHomeomorph.toOpenPartialHomeomorph
  let xi : PartialEquiv G G := (eG.toPartialEquiv.symm.trans rho).trans eG.toPartialEquiv
  have hxi_cont :
      ContDiffOn 𝕜 ∞ xi xi.source ∧ ContDiffOn 𝕜 ∞ xi.symm xi.target := by
    -- This is the analytic input for the remaining transport through `K`.
    simpa [xi, rho, eG] using
      codomain_straightening_model_contDiff (hg := hg) (hf := hf)
  have hchi :
      ∃ chi : OpenPartialHomeomorph H'' H'',
        chi ∈ contDiffGroupoid ∞ K ∧
        hg.codChart (g (f x)) ∈ chi.source ∧
        Set.EqOn (fun y ↦ K (chi y)) (fun y ↦ xi (K y)) chi.source := by
    let z0 : G := (hg.codChart.extend K) (g (f x))
    let z0Range : Set.range (K : H'' → G) :=
      ⟨z0, codomain_chart_basepoint_mem_model_range (hg := hg)⟩
    rcases subtype_local_codomain_straightening
        (hg := hg) (hf := hf) (xi := xi) rfl with
      ⟨chiRange, hchiRange_mem, hz0Range, hEqRange⟩
    -- The remaining transport back to `H''` is now isolated in a reusable packaging lemma.
    exact writtenIn_range_straightening_to_chart_change
      (K := K) (xi := xi) (y0 := hg.codChart (g (f x))) (chiRange := chiRange)
      hchiRange_mem
      (by simpa [z0, z0Range] using hz0Range)
      hEqRange
  rcases transported_codomain_chart_package (hg := hg) (xi := xi) hchi with
    ⟨codChart1, hgf_codChart1, hcodChart1_mem, hcodChart1_eq⟩
  have hfx_overlap :
      f x ∈ hf.codChart.source ∩ hg.domChart.source := by
    exact ⟨hf.mem_codChart_source, hg.mem_domChart_source⟩
  have hoverlap_nhds :
      hf.codChart.source ∩ hg.domChart.source ∈ nhds (f x) := by
    exact IsOpen.mem_nhds (hf.codChart.open_source.inter hg.domChart.open_source) hfx_overlap
  have hcod_nhds : codChart1.source ∈ nhds (g (f x)) :=
    IsOpen.mem_nhds codChart1.open_source hgf_codChart1
  have hpre_nhds :
      hf.codChart.source ∩ hg.domChart.source ∩ g ⁻¹' codChart1.source ∈ nhds (f x) := by
    exact Filter.inter_mem hoverlap_nhds (hg.continuousAt.preimage_mem_nhds hcod_nhds)
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
      exact aligned_codomain_straightening_on_restr
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

/-- Helper for Exercise 4.4: once the middle chart of `g` is aligned with the codomain chart of
`f`, the pointwise immersion normal forms should compose to a normal form for `g ∘ f` with
product complement. -/
theorem comp {x : M} {Ff : Type*} [NormedAddCommGroup Ff] [NormedSpace 𝕜 Ff]
    {Fg : Type*} [NormedAddCommGroup Fg] [NormedSpace 𝕜 Fg]
    (hg : IsImmersionAtOfComplement Fg J K ∞ g (f x))
    (hf : IsImmersionAtOfComplement Ff I J ∞ f x) :
    IsImmersionAtOfComplement (Ff × Fg) I K ∞ (g ∘ f) x := by
  -- Route correction: instead of transporting the old codomain straightening through `range K`,
  -- first rewrite `g` in the source chart coming from `hf`, then compose the two inclusion forms.
  have hcont : ContinuousAt (g ∘ f) x := hg.continuousAt.comp hf.continuousAt
  rcases exists_aligned_codomain_chart_for_g (hg := hg) (hf := hf) with
    ⟨W, hW_open, hfxW, hW_sub, codChart1, hgf_codChart1, hcodChart1_mem, haligned⟩
  have hdom_nhds : hf.domChart.source ∈ nhds x :=
    IsOpen.mem_nhds hf.domChart.open_source hf.mem_domChart_source
  have hW_nhds : W ∈ nhds (f x) :=
    IsOpen.mem_nhds hW_open hfxW
  have hpre_nhds : hf.domChart.source ∩ f ⁻¹' W ∈ nhds x := by
    -- Restrict to a neighborhood where `hf` uses its chosen source chart and `f` lands in
    -- the aligned source chart for `g`.
    exact Filter.inter_mem hdom_nhds (hf.continuousAt.preimage_mem_nhds hW_nhds)
  obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp hpre_nhds
  have hV_dom : V ⊆ hf.domChart.source := fun y hy ↦ (hV_sub hy).1
  have hV_map : V ⊆ f ⁻¹' W := fun y hy ↦ (hV_sub hy).2
  let domChart0 := hf.domChart.restr V
  have hx_domChart0 : x ∈ domChart0.source := by
    -- The final restricted source chart still contains the base point.
    have hx_domChart0' : x ∈ hf.domChart.source ∩ interior V := by
      exact ⟨hf.mem_domChart_source, by simpa [hV_open.interior_eq] using hxV⟩
    simpa [domChart0, OpenPartialHomeomorph.restr] using hx_domChart0'
  have hdomChart0_mem : domChart0 ∈ IsManifold.maximalAtlas I ∞ M := by
    -- Restricting the source chart preserves maximal-atlas membership.
    simpa [domChart0] using
      restr_mem_maximalAtlas (contDiffGroupoid ∞ I) hf.domChart_mem_maximalAtlas hV_open
  let assocEquiv : (E × (Ff × Fg)) ≃L[𝕜] ((E × Ff) × Fg) :=
    (LinearIsometryEquiv.prodAssoc 𝕜 E Ff Fg).symm.toContinuousLinearEquiv
  let equivTot : (E × (Ff × Fg)) ≃L[𝕜] G :=
    assocEquiv.trans ((hf.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 Fg)).trans hg.equiv)
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    hcont equivTot domChart0 codChart1 hx_domChart0 hgf_codChart1 hdomChart0_mem hcodChart1_mem ?_
  intro u hu
  have hu_target : u ∈ (hf.domChart.extend I).target := by
    -- The final restricted target still lies in the original source-chart target of `hf`.
    simpa [domChart0] using restr_extend_target_mem (hf := hf) (U := V) hV_open hu
  have hu_symm_eq :
      (domChart0.extend I).symm u = (hf.domChart.extend I).symm u := by
    -- On the restricted target, the restricted inverse agrees with the original one.
    simpa [domChart0] using restr_extend_symm_eq (hf := hf) (U := V) hV_open hu
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

namespace IsImmersion

/-- Exercise 4.4 (2): the composition of two smooth immersions is again a smooth immersion. -/
-- Proof sketch: compose the local normal forms in charts for `f` and `g`; equivalently, compose
-- the complementary splittings appearing in the immersion data pointwise.
theorem comp (hg : IsImmersion J K ∞ g) (hf : IsImmersion I J ∞ f) :
    IsImmersion I K ∞ (g ∘ f) := by
  -- Fix the global complements already supplied by the two immersion hypotheses.
  have hgf : IsImmersionOfComplement (hf.complement × hg.complement) I K ∞ (g ∘ f) := by
    intro x
    -- Compose the chosen pointwise normal forms with the product complement.
    exact IsImmersionAtOfComplement.comp
      ((hg.isImmersionOfComplement_complement) (f x))
      ((hf.isImmersionOfComplement_complement) x)
  -- Forget the explicit complement to recover the ambient immersion statement.
  exact hgf.isImmersion

end IsImmersion

end Composition

section ConstantRank

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The rank of a smooth map between manifolds at a point, when the target model space is
finite-dimensional, is the dimension of the image of its manifold derivative there. -/
noncomputable def rankAt
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H') [hF : FiniteDimensional 𝕜 F]
    (f : M → N) (x : M) : ℕ :=
  let _ := hF
  Module.finrank 𝕜 ((mfderiv I J f x).range)

/-- A map between manifolds with finite-dimensional target model space has constant rank `r` if
its pointwise manifold rank is `r` at every point. -/
def HasConstantRank (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    [hF : FiniteDimensional 𝕜 F] (f : M → N) (r : ℕ) : Prop :=
  let _ := hF
  ∀ x : M, rankAt I J f x = r

namespace IsSmoothSubmersion

/-- A smooth submersion to a finite-dimensional target has constant rank equal to the dimension of
the target model space. -/
theorem hasConstantRank [hF : FiniteDimensional 𝕜 F] {f : M → N} (hf : IsSmoothSubmersion I J f) :
    HasConstantRank I J f (Module.finrank 𝕜 F) := by
  let _ := hF
  -- A submersion has full derivative range, so the pointwise rank is the full target dimension.
  intro x
  unfold rankAt
  dsimp
  rw [LinearMap.range_eq_top.2 (hf.surjective_mfderiv x), finrank_top]
  rfl

end IsSmoothSubmersion

/-- The standard parabola parametrization in `ℝ²`. -/
def parabola_map : ℝ → ℝ × ℝ :=
  fun t ↦ (t, t ^ 2)

/-- Helper for Exercise 4.4: the manifold derivative of the parabola map is injective at every
point. -/
theorem parabola_map_mfderiv_injective (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) parabola_map t) := by
  -- On model spaces, `mfderiv` is the ordinary derivative, whose first component is the identity.
  rw [mfderiv_eq_fderiv]
  have hpow :
      fderiv ℝ (fun x : ℝ ↦ x ^ (2 : ℕ)) t =
        ((2 : ℝ) * t) • ContinuousLinearMap.id ℝ ℝ := by
    simpa [pow_one, two_mul] using
      (fderiv_pow_ring 2 :
        fderiv ℝ (fun x : ℝ ↦ x ^ (2 : ℕ)) t =
          (2 • t ^ (2 - 1)) • ContinuousLinearMap.id ℝ ℝ)
  have hdiff_pow : DifferentiableAt ℝ (fun x : ℝ ↦ x ^ (2 : ℕ)) t := by
    exact differentiableAt_id.pow 2
  have hderiv :
      fderiv ℝ parabola_map t =
        (ContinuousLinearMap.id ℝ ℝ).prod (((2 : ℝ) * t) • ContinuousLinearMap.id ℝ ℝ) := by
    simpa [parabola_map, hpow, fderiv_id] using differentiableAt_id.fderiv_prodMk hdiff_pow
  rw [hderiv]
  intro v w h
  simpa using congrArg Prod.fst h

/-- Helper for Exercise 4.4: the square map on `ℝ` has rank `0` at the origin. -/
theorem square_map_rankAt_zero :
    rankAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ ↦ t ^ (2 : ℕ)) 0 = 0 := by
  -- The derivative at `0` is the zero linear map, so its range is trivial.
  unfold rankAt
  dsimp
  rw [mfderiv_eq_fderiv]
  have hzero : fderiv ℝ (fun t : ℝ ↦ t ^ (2 : ℕ)) 0 = 0 := by
    simpa using
      (fderiv_pow_ring 2 :
        fderiv ℝ (fun t : ℝ ↦ t ^ (2 : ℕ)) 0 =
          (2 • (0 : ℝ) ^ (2 - 1)) • ContinuousLinearMap.id ℝ ℝ)
  rw [hzero]
  change Module.finrank ℝ ((0 : ℝ →L[ℝ] ℝ).range) = 0
  simp

/-- Helper for Exercise 4.4: the square map on `ℝ` has rank `1` at `1`. -/
theorem square_map_rankAt_one :
    rankAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ ↦ t ^ (2 : ℕ)) 1 = 1 := by
  -- At `1`, the derivative is `2 • id`, which is injective on the one-dimensional source.
  unfold rankAt
  rw [mfderiv_eq_fderiv]
  have hone : fderiv ℝ (fun t : ℝ ↦ t ^ (2 : ℕ)) 1 =
      (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    simpa using
      (fderiv_pow_ring 2 :
        fderiv ℝ (fun t : ℝ ↦ t ^ (2 : ℕ)) 1 =
          (2 • (1 : ℝ) ^ (2 - 1)) • ContinuousLinearMap.id ℝ ℝ)
  rw [hone]
  have hinj : Function.Injective ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) := by
    intro v w h
    have hmul : (2 : ℝ) * v = (2 : ℝ) * w := by
      simpa using h
    linarith
  have hlin_inj : Function.Injective (((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).toLinearMap) := by
    simpa using hinj
  have hdim : Module.finrank ℝ (((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).range) =
      Module.finrank ℝ ℝ := by
    simpa using
      (LinearMap.finrank_range_of_inj
        (f := ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).toLinearMap) hlin_inj)
  simpa using hdim

/-- Exercise 4.4 (3): the parabola parametrization is a map of constant rank `1`. -/
-- Proof sketch: compute the derivative `(1, 2t)` and note that a linear map `ℝ → ℝ²` sending
-- `1` to a nonzero vector has one-dimensional range for every `t`.
theorem parabola_map_has_constant_rank :
    HasConstantRank 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) parabola_map 1 := by
  -- Each derivative is injective, so its image has the source dimension `1`.
  intro t
  unfold rankAt
  dsimp
  have hlin_inj :
      Function.Injective ((mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) parabola_map t).toLinearMap) := by
    simpa using parabola_map_mfderiv_injective t
  have hdim : Module.finrank ℝ
      ((mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) parabola_map t).range) =
      Module.finrank ℝ (TangentSpace 𝓘(ℝ) t) := by
    simpa using
      (LinearMap.finrank_range_of_inj
        (f := (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) parabola_map t).toLinearMap) hlin_inj)
  calc
    Module.finrank ℝ ((mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) parabola_map t).range) =
        Module.finrank ℝ (TangentSpace 𝓘(ℝ) t) := hdim
    _ = Module.finrank ℝ ℝ := by
      unfold TangentSpace
      rfl
    _ = 1 := by
      have hself : Module.finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ
      exact hself

/-- Exercise 4.4 (4): the second projection from `ℝ²` to `ℝ` is a map of constant rank `1`. -/
-- Proof sketch: the manifold derivative of `Prod.snd` is the continuous linear projection onto the
-- second factor, whose range is all of `ℝ`.
theorem snd_has_constant_rank :
    HasConstantRank 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) (Prod.snd : ℝ × ℝ → ℝ) 1 := by
  -- The derivative of `Prod.snd` is the linear projection onto the second coordinate.
  intro x
  unfold rankAt
  dsimp
  rw [mfderiv_eq_fderiv, fderiv_snd]
  have hsurj : Function.Surjective (LinearMap.snd ℝ ℝ ℝ) := by
    intro v
    exact ⟨(0, v), rfl⟩
  have htop : (ContinuousLinearMap.snd ℝ ℝ ℝ).range = (⊤ : Submodule ℝ ℝ) := by
    simpa using (LinearMap.range_eq_top.2 hsurj :
      (LinearMap.snd ℝ ℝ ℝ).range = (⊤ : Submodule ℝ ℝ))
  change Module.finrank ℝ ((ContinuousLinearMap.snd ℝ ℝ ℝ).range) = 1
  rw [htop, finrank_top]
  exact (CommSemiring.finrank_self ℝ : Module.finrank ℝ ℝ = 1)

/-- Exercise 4.4 (5): the composition of the parabola parametrization with the second projection is
not a map of constant rank. -/
-- Proof sketch: the composition is `t ↦ t^2`, whose derivative is `2t`; the derivative has rank
-- `0` at `t = 0` and rank `1` away from `0`, so no single constant rank works globally.
theorem parabola_snd_comp_not_constant_rank :
    ¬ ∃ r : ℕ, HasConstantRank 𝓘(ℝ) 𝓘(ℝ) ((Prod.snd : ℝ × ℝ → ℝ) ∘ parabola_map) r := by
  rintro ⟨r, hr⟩
  -- The composite is the square map, whose ranks at `0` and `1` are incompatible.
  have h0 : r = 0 := by
    calc
      r = rankAt 𝓘(ℝ) 𝓘(ℝ) (((Prod.snd : ℝ × ℝ → ℝ) ∘ parabola_map)) 0 := (hr 0).symm
      _ = rankAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ ↦ t ^ (2 : ℕ)) 0 := by rfl
      _ = 0 := square_map_rankAt_zero
  have h1 : r = 1 := by
    calc
      r = rankAt 𝓘(ℝ) 𝓘(ℝ) (((Prod.snd : ℝ × ℝ → ℝ) ∘ parabola_map)) 1 := (hr 1).symm
      _ = rankAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ ↦ t ^ (2 : ℕ)) 1 := by rfl
      _ = 1 := square_map_rankAt_one
  have : (0 : ℕ) = 1 := by
    rw [← h0, h1]
  norm_num at this

end ConstantRank

end Manifold
