import Mathlib
noncomputable section
universe u
section
variable {G : Type u} [Group G]
example (g : G) (q : ℕ) (b : ℤ) : (g : G) ^ ((q : ℤ) * b) ∈ Subgroup.zpowers ((g : G) ^ q) := by
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨b, by rw [← zpow_natCast ((g:G)) q, ← zpow_mul]⟩
end
