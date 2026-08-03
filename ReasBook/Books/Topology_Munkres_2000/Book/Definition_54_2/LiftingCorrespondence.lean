module

public import Mathlib.Topology.Homotopy.Lifting

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The lifting correspondence of a covering map at a chosen point of a fiber. -/
noncomputable def liftingCorrespondence {p : E → B} (hp : IsCoveringMap p) {b₀ : B}
    (e₀ : p ⁻¹' {b₀}) : FundamentalGroup B b₀ → p ⁻¹' {b₀} :=
  fun γ ↦ hp.monodromy γ e₀

end IsCoveringMap
