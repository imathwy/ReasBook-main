module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Order.Compact

public section

open Set Ordinal

universe u

namespace OpenOmegaOne

/-- Helper for Exercise 29.7: the canonical inclusion of `OpenOmegaOne` omits exactly
`ClosedOmegaOne.omega`. -/
theorem range_toClosed_forOnePointCompactification :
    range (toClosed : OpenOmegaOne.{u} → ClosedOmegaOne.{u}) = {ClosedOmegaOne.omega}ᶜ := by
  ext x
  simp only [mem_range, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩ h
    have hy : (y : Ordinal) = ω₁ := by
      simpa using congrArg Subtype.val h
    exact (ne_of_lt y.property) hy
  · intro hx
    have hne : (x : Ordinal) ≠ ω₁ := by
      intro h
      apply hx
      apply Subtype.ext
      simpa using h
    have hlt : (x : Ordinal) < ω₁ := lt_of_le_of_ne x.property hne
    have h_toClosed : OpenOmegaOne.toClosed ⟨x, hlt⟩ = x := Subtype.ext rfl
    exact ⟨⟨x, hlt⟩, h_toClosed⟩

end OpenOmegaOne

namespace ClosedOmegaOne

/-- Helper for Exercise 29.7: the closed first-uncountable ordinal is compact. -/
instance instCompactSpaceForOnePointCompactification : CompactSpace ClosedOmegaOne.{u} := by
  -- Identify the closed ordinal interval with a compact order interval.
  change CompactSpace (Set.Iic (ω₁ : Ordinal.{u}))
  apply isCompact_iff_compactSpace.mp
  have h_interval : Set.Iic (ω₁ : Ordinal.{u}) = Set.Icc ⊥ ω₁ := by
    ext x
    simp only [Set.mem_Iic, Set.mem_Icc, bot_le, true_and]
  rw [h_interval]
  exact isCompact_Icc

end ClosedOmegaOne

/-- Exercise 29.7: The one-point compactification of `OpenOmegaOne` is homeomorphic
to the closed first-uncountable ordinal `S̄_Ω`. -/
noncomputable def onePointOpenOmegaOneHomeomorphClosedOmegaOne :
    OnePoint OpenOmegaOne.{u} ≃ₜ ClosedOmegaOne.{u} :=
  OnePoint.equivOfIsEmbeddingOfRangeEq ClosedOmegaOne.omega OpenOmegaOne.toClosed
    OpenOmegaOne.isEmbedding_toClosed OpenOmegaOne.range_toClosed_forOnePointCompactification
