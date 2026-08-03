module

public import Topology_Munkres_2000.Book.Notation_43_4.Quotient

public section

universe u

namespace CauchySequences

variable {X : Type u} [PseudoMetricSpace X]

/-- The constant Cauchy sequence with value `x`. -/
@[expose]
def constant (x : X) : X̃ :=
  ⟨fun _ : ℕ ↦ x, mem_cauchySequences.mpr (cauchySeq_const x)⟩

/-- A constant Cauchy sequence evaluates to its constant value. -/
@[simp]
theorem constant_apply (x : X) (n : ℕ) : (constant x).1 n = x := rfl

namespace Quotient

/-- The canonical inclusion into the quotient of Cauchy sequences. -/
@[expose]
def inclusion (x : X) : CauchySequences.Quotient X :=
  ⟦CauchySequences.constant x⟧

/-- The inclusion sends a point to the class of its constant Cauchy sequence. -/
@[simp]
theorem inclusion_apply (x : X) :
    inclusion x = ⟦CauchySequences.constant x⟧ := rfl

end Quotient

end CauchySequences

end
