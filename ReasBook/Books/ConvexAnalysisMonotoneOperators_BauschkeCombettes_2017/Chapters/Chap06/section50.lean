import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_50 (from Chap06) -/
universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

open scoped Pointwise

omit [CompleteSpace 𝓗] in
/-- Corollary 6.50: the recession cone of a nonempty closed convex cone in a real Hilbert space
equals the cone itself. -/
theorem recessionCone_eq_self_of_nonempty_isClosed_convex_isCone {K : Set 𝓗}
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K) :
    rec K = K := by
  -- Route correction: in this workspace Proposition 6.49 exposes the source polar cone only
  -- through a private local definition, so we realize the same corollary through the equivalent
  -- additive characterization of a convex cone.
  have _hK_closed : IsClosed K := hK_closed
  have hK_smul : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K :=
    (Set.isCone_iff_nonneg_smul_mem.mp hK_cone)
  obtain ⟨x, hx⟩ := hK_nonempty
  have h0 : (0 : 𝓗) ∈ K := by
    -- A nonempty cone contains the origin by scaling any point by `0`.
    simpa using hK_smul x hx 0 le_rfl
  have hAdd : K + K ⊆ K := (Convex.isCone_iff_add_subset hK_convex h0).mp hK_cone
  -- Prove both inclusions: recession vectors preserve `K` under translation, and elements of a
  -- cone translate `K` into itself because the cone is additively closed.
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    rw [Set.mem_recessionCone_iff] at hy
    have hy0 : y + 0 ∈ ({y} : Set 𝓗) + K := by
      exact Set.mem_add.2 ⟨y, by simp, 0, h0, by simp⟩
    simpa using hy hy0
  · intro y hy
    rw [Set.mem_recessionCone_iff]
    intro z hz
    rcases Set.mem_add.1 hz with ⟨u, hu, v, hv, huv⟩
    have hu' : u = y := by
      simpa using hu
    subst u
    -- Additive closure of the cone sends `y + v` back to `K`.
    simpa [huv] using hAdd (Set.mem_add.2 ⟨y, hy, v, hv, rfl⟩)

end

end Set
