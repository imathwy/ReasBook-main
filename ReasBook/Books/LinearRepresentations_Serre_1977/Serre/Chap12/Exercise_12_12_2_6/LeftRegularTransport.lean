import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_4_1
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents

noncomputable section

open scoped Representation

universe u v w

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

/-- Helper for Exercise 12-12.2-6: scalar extension of the left regular representation along any
field extension `L → E` only changes coefficients of the character via the structure map.  This is
the generic, base-field-agnostic form of the regular-model transport: it specialises to the
stabilizer fixed field `L = IntermediateField.fixedField H` and the algebraic closure `E =
AlgebraicClosure K'` of the original ground field. -/
theorem scalar_extension_left_regular_character_eq_map_leftRegular_local
    {L : Type v} [Field L]
    {E : Type w} [Field E] [Algebra L E] :
    (Representation.scalarExtension (k := E)
        ((Rep.leftRegular L G).ρ)).character =
      fun g ↦ algebraMap L E ((Rep.leftRegular L G).ρ.character g) := by
  -- Trace commutes with base change, so the scalar-extension character is the coefficientwise
  -- image of the source left regular character.
  ext g
  exact LinearMap.trace_baseChange ((Rep.leftRegular L G).ρ g) E

/-- Helper for Exercise 12-12.2-6: after extending scalars along any field extension `L → E`, the
left regular character matches the target left regular character whenever `L` and `E` have the same
finite group `G`.  Specialised to `L = IntermediateField.fixedField H` and `E = AlgebraicClosure
K'`, this is the character-level half of the regular-model transport. -/
theorem scalar_extension_left_regular_character_eq_leftRegular_local
    {L : Type v} [Field L]
    {E : Type w} [Field E] [Algebra L E] :
    (Representation.scalarExtension (k := E)
        ((Rep.leftRegular L G).ρ)).character =
      (Rep.leftRegular E G).ρ.character := by
  ext g
  rw [scalar_extension_left_regular_character_eq_map_leftRegular_local (G := G) (L := L) (E := E)]
  simp only []
  by_cases hg : g = 1
  · subst hg
    -- At the identity, both left regular characters are the cardinality of `G`, and the structure
    -- map preserves that natural-number value.
    rw [Representation.leftRegular_character_one (k := L),
      Representation.leftRegular_character_one (k := E)]
    push_cast
    rfl
  · -- Away from the identity, both left regular characters vanish.
    rw [Representation.leftRegular_character_eq_zero_of_ne_one (k := L) hg,
      Representation.leftRegular_character_eq_zero_of_ne_one (k := E) hg, map_zero]

end FieldPart

end Exercise_12_12_2_6

end Representation
