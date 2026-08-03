module

public import Topology_Munkres_2000.Book.Definition_43_10.Equivalence
public import Mathlib.Data.Quot

public section

universe u

open scoped CauchySequences

namespace CauchySequences

variable {X : Type u} [PseudoMetricSpace X]

/-- Equivalence of Cauchy sequences is an equivalence relation. -/
theorem equivalentEquivalence : Equivalence (@Equivalent X _) where
  refl x := by
    rw [equivalent_iff]
    exact fun ε hε ↦ ⟨0, fun n _ ↦ by simpa using hε⟩
  symm {x y} h := by
    rw [equivalent_iff] at h ⊢
    exact fun ε hε ↦ by
      obtain ⟨N, hN⟩ := h ε hε
      exact ⟨N, fun n hn ↦ by simpa [dist_comm] using hN n hn⟩
  trans {x y z} hxy hyz := by
    rw [equivalent_iff] at hxy hyz ⊢
    intro ε hε
    obtain ⟨Nxy, hNxy⟩ := hxy (ε / 2) (half_pos hε)
    obtain ⟨Nyz, hNyz⟩ := hyz (ε / 2) (half_pos hε)
    refine ⟨max Nxy Nyz, fun n hn ↦ ?_⟩
    calc
      dist (x.1 n) (z.1 n) ≤ dist (x.1 n) (y.1 n) + dist (y.1 n) (z.1 n) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hNxy n (le_trans (le_max_left _ _) hn))
        (hNyz n (le_trans (le_max_right _ _) hn))
      _ = ε := add_halves ε

/-- The setoid of Cauchy sequences modulo pointwise-distance convergence to zero. -/
def setoid (X : Type u) [PseudoMetricSpace X] : Setoid X̃ where
  r := Equivalent
  iseqv := equivalentEquivalence

/-- The quotient setoid relation is Cauchy sequence equivalence. -/
theorem setoid_rel_iff_equivalent {x y : X̃} :
    (setoid X).r x y ↔ x ∼ y := Iff.rfl

/-- The type of equivalence classes of Cauchy sequences in `X`. -/
abbrev Quotient (X : Type u) [PseudoMetricSpace X] :=
  _root_.Quotient (setoid X)

namespace Quotient

/-- Two represented classes are equal exactly when their Cauchy sequences are equivalent. -/
theorem mk_eq_mk_iff {x y : X̃} :
    (⟦x⟧ : CauchySequences.Quotient X) = ⟦y⟧ ↔ x ∼ y := Quotient.eq

end Quotient

end CauchySequences

end
