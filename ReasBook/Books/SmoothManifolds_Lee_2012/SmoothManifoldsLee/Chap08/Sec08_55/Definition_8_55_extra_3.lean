import Mathlib

open scoped Manifold ContDiff

section

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Semantic recall note: this item reuses the chapter's canonical owner
-- `IsLocalFrameOn I E ∞ e Set.univ` for a smooth global tangent-bundle frame.

/-- Definition 8.55-extra-3: a smooth manifold with or without boundary is `parallelizable` if it
admits a smooth global frame. -/
abbrev parallelizable (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Prop :=
  ∃ (ι : Type uE) (e : ι → (x : M) → TangentSpace I x), IsLocalFrameOn I E ∞ e Set.univ

namespace IsLocalFrameOn

/-- A smooth global frame on `M` makes `M` parallelizable. -/
theorem parallelizable {ι : Type uE} {e : ι → (x : M) → TangentSpace I x}
    (he : IsLocalFrameOn I E ∞ e Set.univ) : parallelizable I M :=
  ⟨ι, e, he⟩

end IsLocalFrameOn

end
