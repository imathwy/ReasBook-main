import Mathlib

open scoped MonoidAlgebra

universe u v w

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Theorem 17-17.3-1: conjugating a representation through a finite basis preserves
the identity endomorphism. -/
private theorem finBasis_model_map_one_local
    (ρ : Representation k G V) :
    ((Module.finBasis k V).equivFun).conj (ρ 1) = 1 := by
  -- Conjugation carries the identity action to the identity matrix.
  calc
    ((Module.finBasis k V).equivFun).conj (ρ 1) =
        ((Module.finBasis k V).equivFun).conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id _

/-- Helper for Theorem 17-17.3-1: conjugating a representation through a finite basis preserves
multiplication of the action operators. -/
private theorem finBasis_model_map_mul_local
    (ρ : Representation k G V) (g h : G) :
    ((Module.finBasis k V).equivFun).conj (ρ (g * h)) =
      (((Module.finBasis k V).equivFun).conj (ρ g)) *
        (((Module.finBasis k V).equivFun).conj (ρ h)) := by
  -- Conjugation is multiplicative, so the transported action is still a representation.
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Theorem 17-17.3-1: every finite-dimensional residue representation can be moved to
the same-universe coordinate model `Fin (finrank V) → k` without changing the representation up to
equivalence, even when the group universe differs from the coefficient-field universe. -/
theorem exists_same_universe_finite_rep_model_local
    (ρ : Representation k G V) :
    ∃ ρW : Representation k G (Fin (Module.finrank k V) → k),
      Nonempty (ρW.Equiv ρ) := by
  let e := (Module.finBasis k V).equivFun
  let ρW : Representation k G (Fin (Module.finrank k V) → k) :=
    { toFun := fun g ↦ e.conj (ρ g)
      map_one' := by
        -- Conjugation carries the identity action to the coordinate identity operator.
        simpa [e] using finBasis_model_map_one_local (ρ := ρ)
      map_mul' := by
        intro g h
        -- The transported action remains multiplicative after conjugation.
        simpa [e] using finBasis_model_map_mul_local (ρ := ρ) g h }
  refine ⟨ρW, ?_⟩
  refine ⟨Representation.Equiv.mk e.symm ?_⟩
  intro g
  -- The chosen basis equivalence intertwines the original action with its coordinate transport.
  ext x
  simp [ρW, e, LinearEquiv.conj_apply_apply]

end

section

variable {A : Type u} [CommRing A]
variable {G : Type v} [Group G] [Finite G]
variable {H : Subgroup G}
variable {W0 : Type w} [AddCommGroup W0] [Module A W0]
variable [Module.Free A W0] [Module.Finite A W0]

/-- Helper for Theorem 17-17.3-1: after inducing a free finite `A[H]`-model, one can still move
the induced source to a same-universe coordinate carrier without changing the induced
representation up to equivalence. -/
theorem exists_same_universe_finite_free_induced_model_local
    (ρA_H : Representation A H W0) :
    ∃ (W_ind : Type u) (_ : AddCommGroup W_ind) (_ : Module A W_ind)
      (_ : Module.Free A W_ind) (_ : Module.Finite A W_ind)
      (ρA_ind : Representation A G W_ind),
        Nonempty (ρA_ind.Equiv (Representation.ind H.subtype ρA_H)) := by
  -- TODO: prove the native induced carrier is equivalent to a same-universe free finite
  -- coordinate model by the Chapter 7 representative-indexed induced model, then transport the
  -- action along that equivalence.
  sorry

end

end Representation
