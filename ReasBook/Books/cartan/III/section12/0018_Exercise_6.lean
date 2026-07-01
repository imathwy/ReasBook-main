import Mathlib

open Set
open scoped BigOperators

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the statement
-- surface was chosen by direct mathlib inspection of `frontier`, `closure`, and bounded-closure
-- compactness for subsets of `ℂ`.

-- Declarations for this item will be appended below by the statement pipeline.

/-- Exercise 6: for a bounded nonempty set `D ⊆ ℂ` and finitely many points `p i` in the plane,
the product of the distances from a point of `closure D` to the `p i` attains its maximum at a
point of `frontier D`. -/
theorem exists_mem_frontier_isMaxOn_prod_dist
    {ι : Type*} [Fintype ι] {D : Set ℂ} (p : ι → ℂ)
    (hD_bounded : Bornology.IsBounded D)
    (hD_nonempty : D.Nonempty) :
    ∃ z ∈ frontier D, IsMaxOn (fun w ↦ ∏ i, dist w (p i)) (closure D) z := by
  let f : ℂ → ℂ := fun z ↦ ∏ i, (z - p i)
  have hf : Differentiable ℂ f := by
    dsimp [f]
    fun_prop
  obtain ⟨z, hz, hmax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm
      hD_bounded
      hD_nonempty
      hf.diffContOnCl
  refine ⟨z, ?_, ?_⟩
  · exact hz
  · rw [isMaxOn_iff] at hmax ⊢
    intro w hw
    simpa [f, dist_eq_norm] using hmax w hw
