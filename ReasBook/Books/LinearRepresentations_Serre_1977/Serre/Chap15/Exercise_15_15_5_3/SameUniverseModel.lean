import Mathlib

open scoped MonoidAlgebra

universe u v w

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Exercise 15-15.5-3: conjugating a representation through a finite basis preserves
the unit element. -/
private theorem finBasis_model_map_one
    (ρ : Representation k G V) :
    ((Module.finBasis k V).equivFun).conj (ρ 1) = 1 := by
  -- Conjugation carries the identity action to the identity endomorphism.
  calc
    ((Module.finBasis k V).equivFun).conj (ρ 1) =
        ((Module.finBasis k V).equivFun).conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id _

/-- Helper for Exercise 15-15.5-3: conjugating a representation through a finite basis preserves
multiplication. -/
private theorem finBasis_model_map_mul
    (ρ : Representation k G V) (g h : G) :
    ((Module.finBasis k V).equivFun).conj (ρ (g * h)) =
      (((Module.finBasis k V).equivFun).conj (ρ g)) *
        (((Module.finBasis k V).equivFun).conj (ρ h)) := by
  -- Conjugation is multiplicative, so the transported action is still a representation.
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 15-15.5-3: every finite-dimensional residue representation can be moved to
the same-universe coordinate model `Fin (finrank V) → k` without changing the representation up to
equivalence. -/
theorem exists_same_universe_finite_rep_model
    (ρ : Representation k G V) :
    ∃ ρW : Representation k G (Fin (Module.finrank k V) → k),
      Nonempty (ρW.Equiv ρ) := by
  let e := (Module.finBasis k V).equivFun
  let ρW : Representation k G (Fin (Module.finrank k V) → k) :=
    { toFun := fun g ↦ e.conj (ρ g)
      map_one' := by
        -- Conjugation carries the identity action to the identity matrix.
        simpa [e] using finBasis_model_map_one (ρ := ρ)
      map_mul' := by
        -- The transported action remains multiplicative after conjugation.
        intro g h
        simpa [e] using finBasis_model_map_mul (ρ := ρ) g h }
  refine ⟨ρW, ?_⟩
  refine ⟨Representation.Equiv.mk e.symm ?_⟩
  intro g
  -- The chosen basis equivalence intertwines the original action with its coordinate transport.
  ext x
  simp [ρW, e, LinearEquiv.conj_apply_apply]

end

end Representation
