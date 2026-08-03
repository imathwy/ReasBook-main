module

public import Topology_Munkres_2000.Book.Exercise_1_99_8.CountableOrdinal
public import Mathlib.SetTheory.Ordinal.Topology

public section

open Ordinal

/-- The open first-uncountable ordinal, modeling Munkres' `S_Ω`. -/
abbrev OpenOmegaOne := CountableOrdinal

/-- The closed first-uncountable ordinal, modeling Munkres' `S̄_Ω`. -/
abbrev ClosedOmegaOne := {o : Ordinal // o ≤ (ω₁ : Ordinal)}

/-- The greatest point `Ω` of `ClosedOmegaOne`. -/
@[expose]
noncomputable def ClosedOmegaOne.omega : ClosedOmegaOne :=
  ⟨ω₁, le_rfl⟩

@[simp]
theorem ClosedOmegaOne.coe_omega :
    (ClosedOmegaOne.omega : Ordinal) = ω₁ := rfl

/-- The canonical inclusion of `OpenOmegaOne` into `ClosedOmegaOne`. -/
@[expose]
def OpenOmegaOne.toClosed (o : OpenOmegaOne) : ClosedOmegaOne :=
  ⟨o, le_of_lt (show (o : Ordinal) < ω₁ from o.property)⟩

@[simp]
theorem OpenOmegaOne.coe_toClosed (o : OpenOmegaOne) :
    (OpenOmegaOne.toClosed o : Ordinal) = (o : Ordinal) := rfl

/-- The canonical inclusion of `OpenOmegaOne` into `ClosedOmegaOne` is a topological embedding. -/
theorem OpenOmegaOne.isEmbedding_toClosed :
    Topology.IsEmbedding (OpenOmegaOne.toClosed : OpenOmegaOne → ClosedOmegaOne) := by
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact Topology.IsEmbedding.subtypeVal

/-- The open first-uncountable ordinal contains the least ordinal. -/
instance OpenOmegaOne.instNonempty : Nonempty OpenOmegaOne :=
  ⟨CountableOrdinal.zero⟩
