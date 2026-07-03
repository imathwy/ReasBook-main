import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uM uN

section

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

-- Proof sketch: each summand in the supremum is bounded by
-- `(LinearMap.range d ⊓ G p) ⊔ G (p + 1)`. Indeed, `Submodule.map d (F (p - r + 1))` is
-- contained in `LinearMap.range d` for every `r`, so
-- `G p ⊓ Submodule.map d (F (p - r + 1)) ≤ LinearMap.range d ⊓ G p`; then taking the supremum
-- over all `r` preserves the inequality.
/-- The supremum of the submodules `(G^p ∩ d(F^{p-r+1})) + G^{p+1}` is always contained in
`Im(d) ∩ G^p + G^{p+1}`. -/
theorem iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next
    (d : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (p : ℤ) :
    (⨆ r : ℕ, (G p ⊓ Submodule.map d (F (p - r + 1))) ⊔ G (p + 1)) ≤
      (LinearMap.range d ⊓ G p) ⊔ G (p + 1) := by
  refine iSup_le fun r ↦ sup_le ?_ le_sup_right
  refine (le_inf ?_ inf_le_left).trans le_sup_left
  exact inf_le_right.trans LinearMap.map_le_range

end
