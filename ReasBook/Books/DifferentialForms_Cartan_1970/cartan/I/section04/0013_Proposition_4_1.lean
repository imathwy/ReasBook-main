import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {D K : Set 𝕜} {f : 𝕜 → E}

/- Proposition 4.1 is `source-facing`: the core owner is
`AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`, while discreteness and compact finiteness are
derived through `isDiscrete_of_codiscreteWithin` and
`IsCompact.finite_diff_of_mem_codiscreteWithin`. The openness hypothesis from the textbook is
redundant for these consequences, so the refined statements keep only connectedness. -/
/-- Proposition 4.1: if `f` is analytic on a connected set `D` and is not identically zero on
`D`, then the zero set of `f` in `D` is a discrete subset. -/
theorem analytic_zero_set_isDiscrete
    (hD_connected : IsConnected D) (hf : AnalyticOnNhd 𝕜 f D)
    (hf_nontrivial : ¬ Set.EqOn f 0 D) :
    IsDiscrete (D ∩ f ⁻¹' ({0} : Set E)) := by
  have hf_nontrivial' : ∃ x ∈ D, f x ≠ 0 := by
    simpa [Set.EqOn] using hf_nontrivial
  rcases hf_nontrivial' with ⟨x, hxD, hfx⟩
  simpa [Set.inter_comm] using
    (isDiscrete_of_codiscreteWithin
      (hf.preimage_zero_mem_codiscreteWithin hfx hxD hD_connected))

/-- A compact subset of the domain of a nonzero analytic function contains only finitely many
zeros. -/
theorem analytic_zero_set_finite_of_isCompact_subset
    (hK : IsCompact K) (hKD : K ⊆ D) (hD_connected : IsConnected D)
    (hf : AnalyticOnNhd 𝕜 f D) (hf_nontrivial : ¬ Set.EqOn f 0 D) :
    (K ∩ f ⁻¹' ({0} : Set E)).Finite := by
  have hf_nontrivial' : ∃ x ∈ D, f x ≠ 0 := by
    simpa [Set.EqOn] using hf_nontrivial
  rcases hf_nontrivial' with ⟨x, hxD, hfx⟩
  have hzero_codiscrete : f ⁻¹' ({0} : Set E)ᶜ ∈ Filter.codiscreteWithin D :=
    hf.preimage_zero_mem_codiscreteWithin hfx hxD hD_connected
  simpa [Set.diff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
    hK.finite_diff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hKD hzero_codiscrete)
