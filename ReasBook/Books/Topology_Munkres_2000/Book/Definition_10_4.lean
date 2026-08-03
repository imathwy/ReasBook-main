module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace

public section

open scoped Ordinal

universe u

/-- Definition 10.4. A minimal uncountable well-order is uncountable, well founded,
and has countable strict initial sections. -/
class MinimalUncountableOrder (A : Type u) [LinearOrder A] : Prop extends
    WellFoundedLT A, Uncountable A where
  countable_Iio (a : A) : Countable (Set.Iio a)

namespace MinimalUncountableOrder

variable {A : Type u} [LinearOrder A] [MinimalUncountableOrder A]

/-- Every strict initial section of a minimal uncountable order is countable. -/
instance instCountableIio (a : A) : Countable (Set.Iio a) :=
  MinimalUncountableOrder.countable_Iio a

/-- The order type of a minimal uncountable well-order is the first
uncountable ordinal `ω₁`. -/
theorem typeLT_eq : typeLT A = ω₁ := by
  letI : IsWellOrder A (· < ·) :=
    { wf := wellFounded_lt
      trichotomous := fun a b hab hba ↦
        le_antisymm (le_of_not_gt hba) (le_of_not_gt hab) }
  apply le_antisymm
  · -- If `ω₁` occurred below the order type, its initial section would be uncountable.
    apply le_of_not_gt
    intro hAbove
    let a : A := Ordinal.enum (· < ·) ⟨ω₁, hAbove⟩
    have hTypein : Ordinal.typein (· < ·) a = ω₁ := by
      exact Ordinal.typein_enum (· < ·) hAbove
    have hCard : (Ordinal.typein (· < ·) a).card ≤ Cardinal.aleph0 := by
      rw [Ordinal.card_typein]
      exact Cardinal.mk_le_aleph0_iff.mpr
        (MinimalUncountableOrder.countable_Iio a)
    rw [hTypein, Ordinal.card_omega] at hCard
    exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hCard
  · -- A smaller order type would make the entire carrier countable.
    apply le_of_not_gt
    intro hBelow
    have hCard : Cardinal.mk A ≤ Cardinal.aleph0 := by
      apply Cardinal.lt_aleph_one_iff.mp
      rw [← Ordinal.card_type (r := (· < ·))]
      exact Cardinal.lt_omega_iff_card_lt.mp hBelow
    have hCountable : Countable A := Cardinal.mk_le_aleph0_iff.mp hCard
    exact not_countable_iff.mpr inferInstance hCountable

end MinimalUncountableOrder

namespace CountableOrdinal

/-- Helper for Definition 10.4: every strict initial section of the countable
ordinals is countable. -/
lemma countableIio (α : CountableOrdinal) : Countable (Set.Iio α) := by
  -- First express the cardinality of the ordinal's canonical type.
  have hCard : Cardinal.mk α.1.ToType ≤ Cardinal.aleph0 := by
    rw [Cardinal.mk_toType]
    exact (mem_iff_card_le_aleph0 α.1).mp α.2
  -- Then transport countability across the canonical order isomorphism.
  have hCountable : Countable α.1.ToType :=
    Cardinal.mk_le_aleph0_iff.mp hCard
  exact (orderIsoIio α).toEquiv.countable_iff.mp hCountable

end CountableOrdinal

/-- The open first-uncountable ordinal is the canonical minimal uncountable
well-order. -/
instance CountableOrdinal.instMinimalUncountableOrder :
    MinimalUncountableOrder (CountableOrdinal.{u}) where
  -- The parent properties are inferred; the helper supplies every section.
  countable_Iio := CountableOrdinal.countableIio
