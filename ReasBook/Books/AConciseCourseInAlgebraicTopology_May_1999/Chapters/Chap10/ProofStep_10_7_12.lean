import Mathlib.Topology.UnitInterval

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped unitInterval

-- Semantic recall via `lean_leansearch`: `exists_monotone_Icc_subset_open_cover_unitInterval`
-- is the canonical mathlib subdivision owner for separating two disjoint closed parts of `I`.

/-- ProofStep 10.7.12: if `C_A` and `C_B` are disjoint closed subsets of `I`, then a sufficiently
fine subdivision of `I` separates the portions controlled by `A` and by `B`.  In the canonical
mathlib API, such a subdivision is represented by a monotone breakpoint sequence `t : ℕ → I`
starting at `0`, eventually equal to `1`, with each subinterval `Icc (t n) (t (n + 1))` lying
entirely in `C_Aᶜ` or entirely in `C_Bᶜ`. -/
theorem unitInterval_subdivision_separates_disjoint_closed_parts
    {C_A C_B : Set I}
    (hA_closed : IsClosed C_A) (hB_closed : IsClosed C_B) (h_disjoint : Disjoint C_A C_B) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ m, ∀ n ≥ m, t n = 1) ∧
      ∀ n, Icc (t n) (t (n + 1)) ⊆ C_Aᶜ ∨ Icc (t n) (t (n + 1)) ⊆ C_Bᶜ := by
  let c : Bool → Set I := fun b ↦ cond b C_Bᶜ C_Aᶜ
  have hc_open : ∀ b, IsOpen (c b) := by
    intro b
    cases b
    · simp [c, cond, hA_closed.isOpen_compl]
    · simp [c, cond, hB_closed.isOpen_compl]
  have hc_cover : univ ⊆ ⋃ b, c b := by
    intro x _
    by_cases hxA : x ∈ C_A
    · have hxB : x ∉ C_B := by
        intro hxB
        exact h_disjoint.le_bot ⟨hxA, hxB⟩
      exact Set.mem_iUnion.mpr ⟨true, by simp [c, cond, hxB]⟩
    · exact Set.mem_iUnion.mpr ⟨false, by simp [c, cond, hxA]⟩
  obtain ⟨t, ht0, hmono, htop, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  refine ⟨t, ht0, hmono, htop, ?_⟩
  intro n
  simpa [c, cond] using hsub n
