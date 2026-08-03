module

public import Mathlib.Topology.UnitInterval

public section

/-- Theorem 3.0.2. Maximum value theorem: a continuous real-valued function on
`Set.Icc a b` attains a maximum. -/
theorem maximumValueOnIcc {a b : ℝ} (hab : a ≤ b) (f : Set.Icc a b → ℝ)
    (hf : Continuous f) :
    ∃ c : Set.Icc a b, ∀ x : Set.Icc a b, f x ≤ f c := by
  have hne : (Set.univ : Set (Set.Icc a b)).Nonempty :=
    ⟨⟨a, le_rfl, hab⟩, Set.mem_univ _⟩
  obtain ⟨c, -, hc⟩ :=
    isCompact_univ.exists_isMaxOn hne hf.continuousOn
  exact ⟨c, fun x ↦ hc (Set.mem_univ x)⟩
