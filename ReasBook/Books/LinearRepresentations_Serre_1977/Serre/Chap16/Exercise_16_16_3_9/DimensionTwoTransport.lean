import Mathlib

noncomputable section

namespace Representation

section SpecialLinear

variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]

/-- Helper for Exercise 16-16.3-9: a two-dimensional `𝔽_p`-space is finite-dimensional. -/
theorem finiteDimensional_of_finrank_eq_two
    (hV : Module.finrank (ZMod p) V = 2) : FiniteDimensional (ZMod p) V :=
  .of_finrank_pos <| by simp [hV]

/-- Helper for Exercise 16-16.3-9: a two-dimensional `𝔽_p`-space is linearly equivalent to the
standard plane `𝔽_p²`. -/
noncomputable def two_dimensional_linear_equiv_of_finrank_eq_two
    (hV : Module.finrank (ZMod p) V = 2) :
    V ≃ₗ[(ZMod p)] (Fin 2 → ZMod p) := by
  letI : FiniteDimensional (ZMod p) V := finiteDimensional_of_finrank_eq_two hV
  let eFin : Fin (Module.finrank (ZMod p) V) ≃ Fin 2 := by
    -- Reindex the chosen finite basis using the dimension hypothesis.
    simpa [hV] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) (ZMod p) V := (Module.finBasis (ZMod p) V).reindex eFin
  -- The resulting basis equivalence is the concrete identification with the standard plane.
  exact b.equivFun

/-- Helper for Exercise 16-16.3-9: a two-dimensional `𝔽_p`-space identifies `SL(V)` with the
standard matrix group `SL(2, 𝔽_p)`. -/
noncomputable def special_linear_group_matrix_equiv_of_finrank_eq_two
    (hV : Module.finrank (ZMod p) V = 2) :
    SpecialLinearGroup (ZMod p) V ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := by
  letI : FiniteDimensional (ZMod p) V := finiteDimensional_of_finrank_eq_two hV
  let eFin : Fin (Module.finrank (ZMod p) V) ≃ Fin 2 := by
    -- Reindex the canonical finite basis using the dimension hypothesis.
    simpa [hV] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) (ZMod p) V := (Module.finBasis (ZMod p) V).reindex eFin
  -- `toLin_equiv` is the standard transport from matrix `SL₂` to the abstract special linear
  -- group attached to the chosen basis.
  exact (Matrix.SpecialLinearGroup.toLin_equiv b).symm

end SpecialLinear

end Representation
