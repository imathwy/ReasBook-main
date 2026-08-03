module

public import Topology_Munkres_2000.Book.Exercise_43_8.UniformTopology
public import Mathlib.Topology.MetricSpace.Basic

public section

universe u v

namespace UniformFun

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [UniformSpace Y]

/-- Helper for Exercise 43.8: joint evaluation on `UniformFun X Y` is continuous at a
continuous function and its point of continuity. -/
theorem continuousAt_eval₂ {f : UniformFun X Y} {x : X}
    (hf : ContinuousAt (UniformFun.toFun f) x) :
    ContinuousAt (fun p : UniformFun X Y × X ↦ UniformFun.toFun p.1 p.2) (f, x) := by
  -- Use one uniform entourage to control the function coordinate at every point.
  rw [ContinuousAt, nhds_eq_comap_uniformity, Filter.tendsto_comap_iff,
    ← lift'_comp_uniformity, Filter.tendsto_lift']
  intro U hU
  have hgen : {g | (f, g) ∈ UniformFun.gen X Y U} ∈ nhds f :=
    (UniformFun.hasBasis_nhds X Y f).mem_iff.mpr ⟨U, hU, subset_rfl⟩
  -- Continuity of `f` controls the point coordinate in the same entourage.
  filter_upwards [prod_mem_nhds hgen
    (hf (UniformSpace.ball_mem_nhds (UniformFun.toFun f x) hU))]
    with ⟨g, y⟩ ⟨hg, hy⟩ using ⟨UniformFun.toFun f y, hy, hg y⟩

end UniformFun

namespace ContinuousMap

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [MetricSpace Y]

/-- Exercise 43.8: The evaluation map `X × C(X, Y) → Y` is continuous when `C(X, Y)`
carries the uniform topology induced from all functions `X → Y`. -/
theorem continuousEvaluation_uniformTopology :
    Continuous (fun p : X × UniformTopologyContinuousMap X Y ↦ evaluation X Y p) := by
  -- Isolate transport from the named view to the public uniform-topology normal form.
  have htop :
      (inferInstance : TopologicalSpace (UniformTopologyContinuousMap X Y)) =
        TopologicalSpace.induced (fun f : C(X, Y) ↦ UniformFun.ofFun f)
          (UniformFun.topologicalSpace X Y) :=
    UniformTopologyContinuousMap.topologicalSpace_eq_uniformTopology.trans
      (ContinuousMap.uniformTopology_def X Y)
  have hprod :
      (inferInstance : TopologicalSpace (X × UniformTopologyContinuousMap X Y)) =
        @instTopologicalSpaceProd X (UniformTopologyContinuousMap X Y) inferInstance
          (TopologicalSpace.induced (fun f : C(X, Y) ↦ UniformFun.ofFun f)
            (UniformFun.topologicalSpace X Y)) :=
    congrArg
      (fun t ↦ @instTopologicalSpaceProd X (UniformTopologyContinuousMap X Y) inferInstance t)
      htop
  have hcontinuous :
      @Continuous (X × C(X, Y)) Y
        (@instTopologicalSpaceProd X C(X, Y) inferInstance
          (TopologicalSpace.induced (fun f : C(X, Y) ↦ UniformFun.ofFun f)
            (UniformFun.topologicalSpace X Y)))
        inferInstance (fun p ↦ evaluation X Y p) := by
    -- The topology is induced by the representation in `UniformFun`.
    letI : TopologicalSpace C(X, Y) :=
      TopologicalSpace.induced (fun f : C(X, Y) ↦ UniformFun.ofFun f)
        (UniformFun.topologicalSpace X Y)
    rw [continuous_iff_continuousAt]
    rintro ⟨x, f⟩
    -- Each represented continuous map satisfies the pointwise hypothesis for joint evaluation.
    have hf : ContinuousAt (UniformFun.toFun (UniformFun.ofFun f)) x := by
      simpa only [UniformFun.toFun_ofFun] using f.continuous.continuousAt
    have heval := UniformFun.continuousAt_eval₂ hf
    -- The induced topology makes the representation continuous on the product.
    have hpair :
        ContinuousAt (fun p : X × C(X, Y) ↦ (UniformFun.ofFun p.2, p.1)) (x, f) :=
      ((continuous_induced_dom.comp' continuous_snd).prodMk continuous_fst).continuousAt
    have hcomp := ContinuousAt.comp'
      (f := fun p : X × C(X, Y) ↦ (UniformFun.ofFun p.2, p.1)) heval hpair
    simpa only [evaluation, UniformFun.toFun_ofFun] using hcomp
  -- Transport the proved normal-form statement back to the named topology.
  have htransport :
      (@Continuous (X × UniformTopologyContinuousMap X Y) Y
          (inferInstance : TopologicalSpace (X × UniformTopologyContinuousMap X Y))
          inferInstance (fun p ↦ evaluation X Y p)) =
        (@Continuous (X × C(X, Y)) Y
          (@instTopologicalSpaceProd X C(X, Y) inferInstance
            (TopologicalSpace.induced (fun f : C(X, Y) ↦ UniformFun.ofFun f)
              (UniformFun.topologicalSpace X Y)))
          inferInstance (fun p ↦ evaluation X Y p)) :=
    congrArg
      (fun t ↦ @Continuous (X × UniformTopologyContinuousMap X Y) Y t inferInstance
        (fun p ↦ evaluation X Y p))
      hprod
  exact Eq.mpr htransport hcontinuous

end ContinuousMap
