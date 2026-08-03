module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Order.Compact

public section

open Set Ordinal

universe u

namespace OpenOmegaOne

/-- The canonical inclusion of the open first-uncountable ordinal omits exactly
the greatest point of the closed first-uncountable ordinal. -/
theorem range_toClosed :
    range (toClosed : OpenOmegaOne.{u} → ClosedOmegaOne.{u}) = {ClosedOmegaOne.omega}ᶜ := by
  ext x
  simp only [mem_range, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩ h
    have : (y : Ordinal) = ω₁ := by simpa using congrArg Subtype.val h
    exact (ne_of_lt y.property) this
  · intro hx
    have hlt : (x : Ordinal) < ω₁ := lt_of_le_of_ne x.property (by
      intro h
      apply hx
      apply Subtype.ext
      simpa using h)
    exact ⟨⟨x, hlt⟩, Subtype.ext rfl⟩

end OpenOmegaOne

namespace ClosedOmegaOne

/-- The closed first-uncountable ordinal is compact. -/
instance instCompactSpace : CompactSpace ClosedOmegaOne.{u} := by
  -- View the closed ordinal interval as a compact closed interval in `Ordinal`.
  change CompactSpace (Set.Iic (ω₁ : Ordinal.{u}))
  apply isCompact_iff_compactSpace.mp
  have h_interval :
      Set.Iic (ω₁ : Ordinal.{u}) = Set.Icc ⊥ ω₁ := by
    ext x
    simp only [Set.mem_Iic, Set.mem_Icc, bot_le, true_and]
  rw [h_interval]
  exact isCompact_Icc

end ClosedOmegaOne

/-- The canonical homeomorphism from the one-point compactification of the open
first-uncountable ordinal to the closed first-uncountable ordinal. -/
@[expose]
noncomputable def onePointOpenOmegaOneHomeomorphClosedOmegaOne :
    OnePoint OpenOmegaOne.{u} ≃ₜ ClosedOmegaOne.{u} :=
  OnePoint.equivOfIsEmbeddingOfRangeEq ClosedOmegaOne.omega OpenOmegaOne.toClosed
    OpenOmegaOne.isEmbedding_toClosed OpenOmegaOne.range_toClosed

@[simp]
theorem onePointOpenOmegaOneHomeomorphClosedOmegaOne_apply_coe (x : OpenOmegaOne.{u}) :
    onePointOpenOmegaOneHomeomorphClosedOmegaOne x = OpenOmegaOne.toClosed x := rfl

@[simp]
theorem onePointOpenOmegaOneHomeomorphClosedOmegaOne_apply_infty :
    onePointOpenOmegaOneHomeomorphClosedOmegaOne (OnePoint.infty : OnePoint OpenOmegaOne.{u}) =
      ClosedOmegaOne.omega := rfl
