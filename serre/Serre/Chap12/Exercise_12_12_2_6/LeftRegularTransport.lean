import Mathlib
import Serre.Chap02.Proposition_2_2_4_1
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents

noncomputable section

open scoped Representation

universe u v

namespace Representation

namespace Exercise_12_12_2_6

section FieldPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_left_regular_transport : Fintype G :=
  Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: scalar extension carries a finite-dimensional source
character to the coefficientwise image of that character in the algebraic closure. -/
private theorem scalarExtension_character_eq_map_algClosure_transport_local
    {K' : Type v} [Field K'] [CharZero K']
    (ρ : Rep K' G)
    [FiniteDimensional K' ρ] :
    (Representation.scalarExtension (k := AlgebraicClosure K') ρ.ρ).character =
      ((IsScalarTower.toAlgHom ℤ K' (AlgebraicClosure K')).compLeft G) ρ.ρ.character := by
  -- Reuse the generic scalar-extension character comparison already proved for this item.
  exact
    Representation.scalarExtension_character_eq_map_algClosure_local
      (G := G) (ρ := ρ)

/-- Helper for Exercise 12-12.2-6: after extending scalars from a stabilizer fixed field to the
algebraic closure, the left regular character is unchanged except for the coefficient map, so it
matches the algebraic-closure left regular character exactly. This isolates the character-level
half of the missing regular-model transport in a small checkable file. -/
theorem scalar_extension_left_regular_fixedField_character_eq_leftRegular_local
    {K' : Type v} [Field K'] [CharZero K']
    (H : Subgroup ((AlgebraicClosure K') ≃ₐ[K'] (AlgebraicClosure K'))) :
    (Representation.scalarExtension (k := AlgebraicClosure K')
        ((Rep.leftRegular (IntermediateField.fixedField H) G).ρ)).character =
      (Rep.leftRegular (AlgebraicClosure K') G).ρ.character := by
  let L := IntermediateField.fixedField H
  let ρL : Rep L G := Rep.leftRegular L G
  let ρAC : Rep (AlgebraicClosure K') G := Rep.leftRegular (AlgebraicClosure K') G
  ext g
  by_cases hg : g = 1
  · subst hg
    -- At the identity, both left regular characters are the cardinality of `G`.
    calc
      (Representation.scalarExtension (k := AlgebraicClosure K')
          ((Rep.leftRegular (IntermediateField.fixedField H) G).ρ)).character 1
          =
            algebraMap L (AlgebraicClosure K')
              (ρL.ρ.character 1) := by
                simpa using congrFun
                  (scalarExtension_character_eq_map_algClosure_transport_local
                    (G := G) (ρ := ρL)) 1
      _ =
            algebraMap L (AlgebraicClosure K')
              (Nat.card G) := by
                rw [Representation.leftRegular_character_one]
      _ = ρAC.ρ.character 1 := by
            simp [Representation.leftRegular_character_one]
  · -- Away from the identity, both left regular characters vanish.
    calc
      (Representation.scalarExtension (k := AlgebraicClosure K')
          ((Rep.leftRegular (IntermediateField.fixedField H) G).ρ)).character g
          =
            algebraMap L (AlgebraicClosure K')
              (ρL.ρ.character g) := by
                simpa using congrFun
                  (scalarExtension_character_eq_map_algClosure_transport_local
                    (G := G) (ρ := ρL)) g
      _ = 0 := by
            rw [Representation.leftRegular_character_eq_zero_of_ne_one hg]
            simp
      _ = ρAC.ρ.character g := by
            symm
            exact Representation.leftRegular_character_eq_zero_of_ne_one hg

end FieldPart

end Exercise_12_12_2_6

end Representation
