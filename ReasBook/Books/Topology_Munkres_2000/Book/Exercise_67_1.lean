module

public import Mathlib.LinearAlgebra.DFinsupp

public section

universe u v

/-- Exercise 67.1. A family of additive subgroups is independent exactly when every finite
zero sum of elements from distinct indexed subgroups has all summands equal to zero.

Together with `(⨆ α, Gα α) = ⊤`, this characterizes when `G` is the internal direct sum of
the subgroups `Gα α`. -/
theorem iSupIndep_iff_finsetSum_eq_zero {G : Type u} [AddCommGroup G] {J : Type v}
    (Gα : J → AddSubgroup G) :
    iSupIndep Gα ↔
      ∀ (s : Finset J) (x : J → G),
        (∀ α ∈ s, x α ∈ Gα α) →
          (∑ α ∈ s, x α) = 0 →
            ∀ α ∈ s, x α = 0 := by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup G ≃o _)]
  exact iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero fun α ↦ (Gα α).toIntSubmodule
