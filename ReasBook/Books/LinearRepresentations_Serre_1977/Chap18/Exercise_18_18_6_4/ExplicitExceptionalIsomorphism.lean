import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ProjectiveLinearGroupCardinality
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ExplicitWordTransportHom

noncomputable section

open scoped MatrixGroups

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-4: the lookup transport sends LinearRepresentations_Serre_1977's involution generator to the
distinguished projective involution. -/
theorem alternating_group_fin5_to_psl_lookup_generator_two :
    alternating_group_fin5_to_psl_lookup a5_generator_two = psl_generator_two := by
  native_decide

/-- Helper for Exercise 18-18.6-4: the chosen `SL₂(𝔽₅)` involution does not lie in the center. -/
theorem sl_generator_two_not_mem_center :
    sl_generator_two ∉ Subgroup.center (SL(2, ZMod 5)) := by
  native_decide

/-- Helper for Exercise 18-18.6-4: the distinguished projective involution is nontrivial. -/
theorem psl_generator_two_ne_one :
    psl_generator_two ≠ 1 := by
  native_decide

/-- Helper for Exercise 18-18.6-4: the indexed-word transport is bijective. -/
theorem alternating_group_fin5_to_psl_lookup_bijective :
    Function.Bijective alternating_group_fin5_to_psl_lookup := by
  letI : Fintype A5 := Fintype.ofFinite A5
  letI : Fintype (PSL(2, ZMod 5)) := Fintype.ofFinite (PSL(2, ZMod 5))
  have hker_bot : alternating_group_fin5_to_psl_hom.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top
        (H := alternating_group_fin5_to_psl_hom.ker)
        (inferInstance : alternating_group_fin5_to_psl_hom.ker.Normal) with hker | hker
    · exact hker
    · exfalso
      have hmem : a5_generator_two ∈ alternating_group_fin5_to_psl_hom.ker := by
        simp [hker]
      have hmap : alternating_group_fin5_to_psl_lookup a5_generator_two = 1 := by
        exact hmem
      exact psl_generator_two_ne_one <| by
        simpa [alternating_group_fin5_to_psl_lookup_generator_two] using hmap
  have hinj : Function.Injective alternating_group_fin5_to_psl_lookup :=
    (MonoidHom.ker_eq_bot_iff alternating_group_fin5_to_psl_hom).mp hker_bot
  have hcard : Fintype.card A5 = Fintype.card (PSL(2, ZMod 5)) := by
    simpa [Nat.card_eq_fintype_card] using
      alternating_group_fin5_card_eq_sixty.trans psl_two_zmod_five_card_eq_sixty.symm
  exact (Fintype.bijective_iff_injective_and_card alternating_group_fin5_to_psl_lookup).2
    ⟨hinj, hcard⟩
