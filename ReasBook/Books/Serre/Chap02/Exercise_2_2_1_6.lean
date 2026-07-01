import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

open Module.Dual

section

variable {k : Type u} [CommSemiring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/- The canonical contragredient action on the algebraic dual is `Representation.dual`. -/
recall dual

/- The primitive action formula for the canonical dual representation is
`Representation.dual_apply`. -/
recall dual_apply

/-- The canonical dual representation preserves evaluation against `ρ`. -/
theorem dual_preserves_eval (s : G) (x : V) (x' : Module.Dual k V) :
    ρ.dual s x' (ρ s x) = x' x := by
  simp [dual_apply, transpose_apply]

/-- Any representation on the dual space whose action preserves evaluation against `ρ` is the
canonical dual representation `ρ.dual`. -/
theorem eq_dual_of_preserves_eval {ρ' : Representation k G (Module.Dual k V)}
    (hρ' : ∀ (s : G) (x : V) (x' : Module.Dual k V), ρ' s x' (ρ s x) = x' x) :
    ρ' = ρ.dual := by
  ext s x' x
  simpa [dual_apply] using hρ' s (ρ s⁻¹ x) x'

/-- Exercise 2-2.1-6: there exists a unique contragredient representation on the dual space whose
action preserves the natural pairing with `ρ`. -/
theorem existsUnique_dual_representation :
    ∃! ρ' : Representation k G (Module.Dual k V),
      ∀ s x x', ρ' s x' (ρ s x) = x' x := by
  refine ⟨ρ.dual, ρ.dual_preserves_eval, ?_⟩
  · intro ρ' hρ'
    exact ρ.eq_dual_of_preserves_eval hρ'

end

end Representation
