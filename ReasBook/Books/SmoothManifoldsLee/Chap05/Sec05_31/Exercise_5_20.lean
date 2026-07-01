import SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1

open Topology
open scoped Manifold

universe u𝕜 uE uH uM

namespace Manifold
namespace ImmersedSubmanifold

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}

/-- The inclusion of an immersed submanifold into the ambient manifold is continuous. -/
theorem continuous_inclusion (S : ImmersedSubmanifold I M) : Continuous S.inclusion := by
  rw [continuous_iff_continuousAt]
  intro x
  let h := S.inclusion_isImmersion.isImmersionAt x
  have hdomChart_source : h.domChart.source ∈ 𝓝 x :=
    IsOpen.mem_nhds h.domChart.open_source h.mem_domChart_source
  have hsource : S.inclusion ⁻¹' h.codChart.source ∈ 𝓝 x :=
    Filter.mem_of_superset hdomChart_source h.source_subset_preimage_source
  have hEqOn :
      Set.EqOn ((h.codChart.extend I) ∘ S.inclusion)
        (h.equiv ∘ fun y : S ↦
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement)))
        h.domChart.source := by
    intro y hy
    have hy_target :
        h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y ∈
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).target :=
      (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, OpenPartialHomeomorph.extend_coe, h.domChart.left_inv hy] using
      h.writtenInCharts hy_target
  have hEq :
      ((h.codChart.extend I) ∘ S.inclusion) =ᶠ[𝓝 x]
        h.equiv ∘ fun y : S ↦
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement)) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hcont_rhs :
      ContinuousAt
        (h.equiv ∘ fun y : S ↦
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement))) x := by
    have hcont_dom :
        ContinuousAt (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) x :=
      h.domChart.continuousAt_extend h.mem_domChart_source
    have hcont_pair :
        ContinuousAt
          (fun y : S ↦
            (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement))) x :=
      hcont_dom.prodMk continuousAt_const
    simpa [Function.comp] using ContinuousAt.comp h.equiv.continuousAt hcont_pair
  have hcont_extend : ContinuousAt ((h.codChart.extend I) ∘ S.inclusion) x :=
    hcont_rhs.congr hEq.symm
  have hcont_chart : ContinuousAt (h.codChart ∘ S.inclusion) x := by
    convert I.continuousAt_symm.comp hcont_extend using 1
    funext y
    simp [Function.comp]
  exact (h.codChart.continuousAt_iff_continuousAt_comp_left hsource).2 hcont_chart

/-- Exercise 5.20: the topology carried by an immersed submanifold is finer than the ambient
subspace topology pulled back along its inclusion map. -/
theorem givenTopology_le_subspaceTopology (S : ImmersedSubmanifold I M) :
    (inferInstance : TopologicalSpace S) ≤ TopologicalSpace.induced S.inclusion inferInstance :=
  S.continuous_inclusion.le_induced

/-- Exercise 5.20: the ambient subspace topology on the image of an immersed submanifold is finer
than the chosen topology exactly when the inclusion is an embedding. -/
theorem subspaceTopology_le_givenTopology_iff_isEmbedding (S : ImmersedSubmanifold I M) :
    TopologicalSpace.induced S.inclusion inferInstance ≤ (inferInstance : TopologicalSpace S) ↔
      IsEmbedding S.inclusion := by
  constructor
  · intro hle
    exact ⟨⟨le_antisymm S.givenTopology_le_subspaceTopology hle⟩, S.inclusion_injective⟩
  · intro hEmbedding
    rw [hEmbedding.eq_induced]

end

end ImmersedSubmanifold
end Manifold
