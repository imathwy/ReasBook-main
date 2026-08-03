module

public import Topology_Munkres_2000.Book.Exercise_38_11.Extension

public section

universe u v

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- Exercise 38.11. A continuous real-valued function on `X` extends continuously to a
compactification exactly when it has a limit along the embedded copy of `X` at every point. -/
theorem extends_iff_tendsto
    (C : Compactification.{u, v} X) (f : ContinuousMap X ℝ) :
    C.Extends f ↔
      ∀ y : C, ∃ r : ℝ, Filter.Tendsto f (Filter.comap C (nhds y)) (nhds r) := by
  rw [extends_iff]
  constructor
  · rintro ⟨g, hg⟩ y
    refine ⟨g y, ?_⟩
    have hC : Filter.Tendsto C (Filter.comap C (nhds y)) (nhds y) :=
      Filter.tendsto_comap
    have ht := Filter.Tendsto.comp (g.continuousAt y) hC
    rw [show g ∘ C = f from funext hg] at ht
    exact ht
  · intro hf
    exact ⟨continuousExtension C f hf, continuousExtension_apply C f hf⟩

end Compactification
