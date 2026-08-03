module

public import Topology_Munkres_2000.Book.Proposition_21_3.UniformConvergence

public section

universe u

namespace UniformMetric

/-- Helper for Proposition 21.3: the canonical homeomorphism sends a raw function, viewed in
the uniform-metric function space, to the same function in `UniformFun`. -/
private lemma functionSpaceHomeomorph_ofFun {X : Type u} (h : X → ℝ) :
    functionSpaceHomeomorph X (FunctionSpace.ofFun h) = UniformFun.ofFun h := by
  -- Compare inverse images, whose values are given by the exported inverse computation rule.
  apply (functionSpaceHomeomorph X).symm.injective
  rw [(functionSpaceHomeomorph X).symm_apply_apply,
    functionSpaceHomeomorph_symm_apply, UniformFun.toFun_ofFun]

/-- Helper for Proposition 21.3: convergence of raw functions is preserved by the canonical
homeomorphism between the uniform-metric function space and `UniformFun`. -/
private lemma tendsto_functionSpace_iff_tendsto_uniformFun {X : Type u} {I : Type*}
    {l : Filter I} (F : I → X → ℝ) (g : X → ℝ) :
    Filter.Tendsto (fun i ↦ FunctionSpace.ofFun (F i)) l
        (nhds (FunctionSpace.ofFun g)) ↔
      Filter.Tendsto (fun i ↦ UniformFun.ofFun (F i)) l
        (nhds (UniformFun.ofFun g)) := by
  -- Transport the neighborhood limit through the inducing homeomorphism.
  rw [(functionSpaceHomeomorph X).isInducing.tendsto_nhds_iff]
  have mappedFamily :
      (⇑(functionSpaceHomeomorph X) ∘ fun i ↦ FunctionSpace.ofFun (F i)) =
        (fun i ↦ UniformFun.ofFun (F i)) := by
    funext i
    exact functionSpaceHomeomorph_ofFun (F i)
  rw [mappedFamily, functionSpaceHomeomorph_ofFun]

end UniformMetric

/-- Proposition 21.3: Uniform convergence of real-valued functions is equivalent to
convergence in the topology induced by the uniform metric. -/
theorem tendstoUniformly_iff_tendsto_uniformMetric {X : Type u}
    (f : ℕ → X → ℝ) (g : X → ℝ) :
    TendstoUniformly f g Filter.atTop ↔
      Filter.Tendsto (fun n ↦ UniformMetric.FunctionSpace.ofFun (f n)) Filter.atTop
        (nhds (UniformMetric.FunctionSpace.ofFun g)) := by
  -- First identify uniform convergence with convergence in mathlib's `UniformFun` model.
  calc
    TendstoUniformly f g Filter.atTop ↔
        Filter.Tendsto (fun n ↦ UniformFun.ofFun (f n)) Filter.atTop
          (nhds (UniformFun.ofFun g)) := by
      rw [UniformFun.tendsto_iff_tendstoUniformly]
      simp only [Function.comp_def, UniformFun.toFun_ofFun]
    -- Then transport that convergence back through the canonical homeomorphism.
    _ ↔ Filter.Tendsto (fun n ↦ UniformMetric.FunctionSpace.ofFun (f n)) Filter.atTop
          (nhds (UniformMetric.FunctionSpace.ofFun g)) :=
      (UniformMetric.tendsto_functionSpace_iff_tendsto_uniformFun f g).symm
