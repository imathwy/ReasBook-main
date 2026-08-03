module

public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

open Cardinal Ordinal

/-- Helper for Exercise 1.99.8: the well-ordered type of countable ordinals. -/
abbrev CountableOrdinal := Set.Iio (ω₁ : Ordinal)

namespace CountableOrdinal

/-- Helper for Exercise 1.99.8: the least countable ordinal. -/
def zero : CountableOrdinal := ⟨0, Ordinal.omega_pos 1⟩

/-- Helper for Exercise 1.99.8: a countable ordinal is canonically order-isomorphic
to its strict lower section. -/
noncomputable def orderIsoIio (α : CountableOrdinal) : α.1.ToType ≃o Set.Iio α :=
  Ordinal.ToType.mk.symm.trans
    { toFun := fun (β : Set.Iio α.1) ↦
        ⟨(⟨β.1, show β.1 < (ω₁ : Ordinal) from lt_trans β.2 α.2⟩ : CountableOrdinal), β.2⟩
      invFun := fun (β : Set.Iio α) ↦ ⟨β.1.1, β.2⟩
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
      map_rel_iff' := Iff.rfl }

@[simp]
theorem coe_zero : (zero : Ordinal) = 0 := rfl

/-- Helper for Exercise 1.99.8: an ordinal is countable exactly when its
cardinality is at most `ℵ₀`. -/
theorem mem_iff_card_le_aleph0 (α : Ordinal) :
    α ∈ Set.Iio (ω₁ : Ordinal) ↔ α.card ≤ ℵ₀ := by
  change α < ω₁ ↔ α.card ≤ ℵ₀
  rw [Cardinal.lt_omega_iff_card_lt, Cardinal.lt_aleph_one_iff]

/-- Helper for Exercise 1.99.8: `zero` is the least countable ordinal. -/
theorem zero_isLeast : IsLeast (Set.univ : Set CountableOrdinal) zero := by
  refine ⟨Set.mem_univ _, fun α _ ↦ ?_⟩
  exact (bot_le : (0 : Ordinal) ≤ α.1)

/-- Exercise 1.99.8: the well-ordered type of countable ordinals is uncountable. -/
instance instUncountable : Uncountable CountableOrdinal := by
  refine Cardinal.aleph0_lt_mk_iff.mp ?_
  -- Compute the cardinality of the initial segment below `ω₁`.
  rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega, Cardinal.aleph0_lt_lift]
  -- Finish with the defining strict growth from `ℵ₀` to `ℵ₁`.
  exact Cardinal.aleph0_lt_aleph_one

end CountableOrdinal

end
