import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Proposition 1.4.32: A subspace `W` of a `K`-vector space `V` has finite codimension if and
only if it admits a finite-dimensional complementary subspace. -/
-- Proof sketch: If `V ⧸ W` is finite-dimensional, choose a complement `S` to `W`; the quotient
-- equivalence `W.quotientEquivOfIsCompl S hWS` transfers finite-dimensionality to `S`.
-- Conversely, if `S` is a finite-dimensional complement of `W`, the same equivalence transfers
-- finite-dimensionality from `S` to `V ⧸ W`.
theorem finiteDimensional_quotient_iff_exists_isCompl_finiteDimensional (W : Submodule K V) :
    FiniteDimensional K (V ⧸ W) ↔ ∃ S : Submodule K V, IsCompl W S ∧ FiniteDimensional K S := by
  constructor
  · intro h
    obtain ⟨S, hWS⟩ := W.exists_isCompl
    exact ⟨S, hWS, (W.quotientEquivOfIsCompl S hWS).finiteDimensional⟩
  · rintro ⟨S, hWS, hS⟩
    exact (W.quotientEquivOfIsCompl S hWS).symm.finiteDimensional

/-- A complement of a subspace has dimension equal to the quotient dimension. -/
-- Proof sketch: For complementary subspaces `W` and `S`, the canonical linear equivalence
-- `W.quotientEquivOfIsCompl S hWS : (V ⧸ W) ≃ₗ[K] S` identifies their dimensions, so taking
-- `Module.finrank` yields the stated equality.
theorem finrank_of_isCompl_eq_finrank_quotient (W S : Submodule K V) (hWS : IsCompl W S) :
    Module.finrank K S = Module.finrank K (V ⧸ W) := by
  simpa using (W.quotientEquivOfIsCompl S hWS).finrank_eq.symm

end
