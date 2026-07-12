import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Definition III.4-extra-5: `o` is an isolated singularity of `f` if `f` is analytic on a
punctured neighborhood of `o`. Removability, poles, and essentiality are later refinements of
this source-facing notion, not part of the definition itself. -/
def HasIsolatedSingularityAt (f : 𝕜 → E) (o : 𝕜) : Prop :=
  ∀ᶠ z in 𝓝[≠] o, AnalyticAt 𝕜 f z

namespace HasIsolatedSingularityAt

/-- An isolated singularity is analytic at every nearby point away from its center. -/
theorem eventually_analyticAt {f : 𝕜 → E} {o : 𝕜} (hf : HasIsolatedSingularityAt f o) :
    ∀ᶠ z in 𝓝[≠] o, AnalyticAt 𝕜 f z :=
  hf

/-- Source-text reformulation: an isolated singularity is equivalently analyticity on some punctured
ball. -/
theorem iff_exists_analyticOnNhd_punctured_ball {f : 𝕜 → E} {o : 𝕜} :
    HasIsolatedSingularityAt f o ↔
      ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd 𝕜 f (Metric.ball o ρ \ {o}) := by
  constructor
  · intro hf
    rcases Metric.mem_nhdsWithin_iff.mp hf with ⟨ρ, hρ, hρanalytic⟩
    refine ⟨ρ, hρ, fun z hz ↦ hρanalytic ?_⟩
    simpa [Set.diff_eq, Set.mem_compl_iff] using hz
  · rintro ⟨ρ, hρ, hρanalytic⟩
    have hball : Metric.ball o ρ \ ({o} : Set 𝕜) ∈ 𝓝[≠] o := by
      rw [show Metric.ball o ρ \ ({o} : Set 𝕜) = Metric.ball o ρ ∩ ({o} : Set 𝕜)ᶜ by
        ext z
        simp [Set.diff_eq]]
      exact Metric.mem_nhdsWithin_iff.mpr ⟨ρ, hρ, subset_rfl⟩
    exact Filter.mem_of_superset hball hρanalytic

end HasIsolatedSingularityAt

end
