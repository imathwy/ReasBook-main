import Mathlib
import Serre.RepresentationTheory.RealizableOver
import Serre.Chap18.Remark_18_18_6_1
import Serre.Chap18.Exercise_18_18_6_3.Shared
import Serre.Chap18.Exercise_18_18_6_3.SourceCharacters

noncomputable section

universe u v

namespace Representation

open AlternatingGroupFive

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Helper for Exercise 18-18.6-3: Serre's source route for the two degree-`2` Brauer slots of
`A₅` in characteristic `2`. The missing owner-level input is exactly that one gets a descended
irreducible degree-`2` `𝔽₄[A₅]`-module from the `χ₃` reductions, and that every irreducible
degree-`2` representation over an extension of `𝔽₄` is realizable over `𝔽₄`. -/
theorem a5_degree_two_source_route_over_f4 :
    (∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
        (ρ : Representation 𝔽₄ A5 W),
        ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2) ∧
      (∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
          {V : Type v} [AddCommGroup V] [Module K V]
          (ρ : Representation K A5 V) [ρ.IsIrreducible],
          Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ) := by
  -- Route correction: the blocker is not an ad hoc explicit matrix model. Serre's proof first
  -- identifies the two degree-`2` Brauer slots by reducing the ordinary degree-`3` rows
  -- `χ₂, χ₃`, then uses that those modular characters take values in `𝔽₄` on the `5`-cycle
  -- classes. Packaging that source-faithful argument here leaves the target file with only the
  -- formal descent and `SL₂(𝔽₄)` consequences.
  -- TODO for Exercise 18-18.6-3: the stabilized frontier is now explicit.
  -- 1. The p-regular/Brauer-label bridge and the algebraically closed classification side are now
  --    public in `SourceCharacters.lean`, via
  --    `alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels`,
  --    `a5_source_degree_two_character_function_phi_modTwo`,
  --    `a5_source_degree_two_character_function_psi_modTwo`, and
  --    `a5_irreducible_degree_two_occurs_in_brauer_labeled_family_modTwo`.
  -- 2. The remaining missing owner is source-faithful: construct actual simple degree-`2`
  --    `𝔽₄[A₅]` modules from the reductions of Serre's two ordinary degree-`3` rows.
  -- 3. Once those two owners exist, compare their scalar extensions with the algebraically
  --    closed Brauer-labeled degree-`2` slots and descend realizability by
  --    `Representation.isRealizableOver_of_equiv`.
  sorry

/-- Helper for Exercise 18-18.6-3: extract one descended irreducible degree-`2` `𝔽₄[A₅]`-slot
from the full source-faithful characteristic-`2` package. -/
theorem a5_degree_two_source_slot_exists_over_f4 :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
      (ρ : Representation 𝔽₄ A5 W),
      ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2 := by
  -- Reuse the existential component of the full Serre source package.
  have hroute :
      (∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
          (ρ : Representation 𝔽₄ A5 W),
          ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2) ∧
        (∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
            {V : Type u} [AddCommGroup V] [Module K V]
            (ρ : Representation K A5 V) [ρ.IsIrreducible],
            Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ) :=
    a5_degree_two_source_route_over_f4
  exact hroute.1

/-- Helper for Exercise 18-18.6-3: every irreducible degree-`2` representation of `A₅` over an
extension of `𝔽₄` is realizable over `𝔽₄`. -/
theorem a5_irreducible_degree_two_realizable_over_f4
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2) :
    Representation.IsRealizableOver 𝔽₄ ρ := by
  -- Reuse the realizability component of the same source-faithful package.
  exact a5_degree_two_source_route_over_f4.2 ρ hV

end Representation
