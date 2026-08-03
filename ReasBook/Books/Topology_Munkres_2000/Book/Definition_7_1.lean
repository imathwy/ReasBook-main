module

public import Topology_Munkres_2000.Book.Definition_7_1.CountablyInfinite

public section

universe u

/- Definition 7.1 (1). A set is infinite exactly when it is not finite. -/
#check Set.Infinite

/- Definition 7.1 (2). A set is countably infinite when it admits a bijective
correspondence with the positive integers `ℕ+`. -/
#check Set.CountablyInfinite

namespace Set

/-- Definition 7.1. A set is countably infinite exactly when it is both countable and infinite. -/
theorem countablyInfinite_iff_countable_and_infinite {α : Type u} (A : Set α) :
    A.CountablyInfinite ↔ A.Countable ∧ A.Infinite := by
  constructor
  · intro h
    -- Transport the positive-integer indexing to a denumerability witness.
    have hEquiv : Nonempty (A ≃ ℕ+) :=
      h.nonemptyEquivPNat.map Equiv.symm
    have hDenumerable : Nonempty (Denumerable A) :=
      hEquiv.map fun e ↦ Denumerable.ofEquiv ℕ+ e
    -- Apply the canonical characterization of countable infinite subtypes.
    exact Set.countable_infinite_iff_nonempty_denumerable.mpr hDenumerable
  · intro h
    -- First obtain a denumerability witness for the subtype of the set.
    have hDenumerable : Nonempty (Denumerable A) :=
      Set.countable_infinite_iff_nonempty_denumerable.mp h
    -- Reindex the resulting equivalence with `ℕ` by the positive integers.
    exact hDenumerable.elim fun inst ↦
      Set.CountablyInfinite.ofEquiv
        ((@Denumerable.eqv A inst).trans Equiv.pnatEquivNat.symm)

end Set
