import Mathlib.Geometry.Manifold.IsManifold.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe u𝕜 uE uH uM

namespace OpenPartialHomeomorph

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M]

variable (I : ModelWithCorners 𝕜 E H) (e e' : OpenPartialHomeomorph M H)

/- Definition 1.2-extra-2 (core/canonical): smooth compatibility of two charts is the canonical
owner condition that the chart change `e.symm ≫ₕ e'` belongs to the smooth structure groupoid. -/
#check (e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I)

/-- In Lee's source wording, if the chart domains are disjoint then the chart change has empty
source, so the textbook "disjoint or smooth" condition is equivalent to direct membership in the
smooth structure groupoid. This is the source-facing bridge from Lee's formulation to the
canonical owner condition. -/
theorem mem_contDiffGroupoid_of_source_inter_eq_empty
    (I : ModelWithCorners 𝕜 E H) {e e' : OpenPartialHomeomorph M H}
    (h : e.source ∩ e'.source = ∅) :
    e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I := by
  apply ContDiffGroupoid.mem_of_source_eq_empty
  rw [trans_source'']
  simp [h]

/-- In Lee's source wording, if the chart domains are disjoint then the chart change has empty
source, so the textbook "disjoint or smooth" condition is equivalent to direct membership in the
smooth structure groupoid. This is the source-facing bridge from Lee's formulation to the
canonical owner condition. -/
theorem source_inter_eq_empty_or_mem_contDiffGroupoid_iff
    (I : ModelWithCorners 𝕜 E H) (e e' : OpenPartialHomeomorph M H) :
    e.source ∩ e'.source = ∅ ∨ e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I ↔
      e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I := by
  constructor
  · rintro (h | h)
    · exact mem_contDiffGroupoid_of_source_inter_eq_empty I h
    · exact h
  · exact Or.inr

end OpenPartialHomeomorph
