import LinearRepresentations_Serre_1977.Serre.Chap10.Exercise_10_10_5_5.SupersolvableBridge
import LinearRepresentations_Serre_1977.Serre.Chap10.MonomialCharacter

noncomputable section

universe u

open scoped Representation SubgroupInduction

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev finiteGroupFintype : Fintype G := Fintype.ofFinite G
attribute [local instance] finiteGroupFintype

/-- A subgroup of a finite group is finite. -/
private noncomputable abbrev subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H
attribute [local instance] subgroupFintype

/-- Helper for irreducible_fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary:
once a representation is identified with the standard induced model attached to a
one-dimensional subrepresentation, its character is monomial. -/
private theorem isMonomialCharacter_of_equiv_induced_finrank_one_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V}
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hWfinrank : Module.finrank ℂ W.toSubmodule = 1)
    (eInd : ρ.Equiv ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ)) :
    IsMonomialCharacter ρ.character := by
  letI : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨α, hαchar⟩ :=
    exists_linear_character_of_fdRep_finrank_one (FDRep.of W.toRepresentation) hWfinrank
  have hWchar : W.toRepresentation.character = α.toRepresentation.character := by
    -- Rebundle the one-dimensional source representation as the character of a linear character.
    simpa using hαchar
  refine ⟨H, α, ?_⟩
  -- Compare `ρ` with the canonical induced model, then rewrite the inducing character.
  calc
    Ind[H](α.toRepresentation.character) = Ind[H](W.toRepresentation.character) := by
      rw [hWchar]
    _ = ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ).character := by
      simpa using
        (Subgroup.inducedClassFunction_eq_character_ind
          (H := H) (K := ℂ) (θ := W.toRepresentation))
    _ = ρ.character := by
      simpa using (Representation.char_iso eInd).symm

-- The following 32 helper declarations are the canonical declarations from
-- `Serre.Chap10.Theorem_10_10_5_2.InducedModelEquivalence` (transitively imported); they are
-- reused directly rather than kept as duplicate copies.  (`extensionLinearMapLocal`,
-- `extensionIntertwiningMapLocal`, `existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation`,
-- etc. also appear in `Serre.Chap08.Theorem_8_8_5_2`.)

/-- Helper for irreducible_fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary:
the character of a monomial finite-dimensional complex representation is a monomial character. -/
private theorem isMonomialCharacter_of_isMonomial_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (hρ : Representation.IsMonomial ρ) :
    IsMonomialCharacter ρ.character := by
  rcases hρ with ⟨H, W, hWfinrank, hWinduced⟩
  -- Route correction: avoid the conflicting Chapter `7` import path by rebuilding the induced
  -- model equivalence locally from the source-faithful Chapter `3` uniqueness argument.
  let eInd : ρ.Equiv ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ) :=
    equiv_induced_of_isInducedFromSubrepresentation_local ρ H W hWinduced
  -- Once the ambient representation is identified with the standard induced model, the character
  -- argument reduces to the already proved one-dimensional induced case.
  exact isMonomialCharacter_of_equiv_induced_finrank_one_local H W hWfinrank eInd

/-- Helper for Exercise 10-10.5-5: a monomial finite-dimensional complex representation has
character induced from a degree-`1` subgroup character, once the equality is bundled in
Serre's character ring. -/
private theorem fdRepCharacterRing_eq_characterRingInduction_of_character_eq_induced_linear
    (V : FDRep ℂ G) (H : Subgroup G) (α : H →* ℂˣ)
    (hchar : V.character = Ind[H](α.toRepresentation.character)) :
    fdRepCharacterRing V = Subgroup.characterRingInduction H α.toCharacterRing := by
  -- Compare the two bundled characters pointwise after unfolding the induced-character owner.
  apply Subtype.ext
  ext g
  simpa [fdRepCharacterRing, Subgroup.characterRingInduction_apply,
    MonoidHom.toCharacterRing_apply] using congrFun hchar g

/-- Helper for irreducible_fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary:
an explicit monomial-character witness rebundles to an equality in `R(G)`. -/
private theorem fdRepCharacterRing_eq_characterRingInduction_of_isMonomialCharacter
    (V : FDRep ℂ G) (hmono : Representation.IsMonomialCharacter V.character) :
    ∃ H : Subgroup G, ∃ α : H →* ℂˣ,
      fdRepCharacterRing V = Subgroup.characterRingInduction H α.toCharacterRing := by
  rcases hmono with ⟨H, α, hchar⟩
  refine ⟨H, α, ?_⟩
  -- The character-level witness already has the right subgroup and linear character; only the
  -- `R(G)` packaging remains.
  exact
    fdRepCharacterRing_eq_characterRingInduction_of_character_eq_induced_linear
      V H α hchar.symm

/-- Helper for Exercise 10-10.5-5: a monomial finite-dimensional complex representation has
character induced from a degree-`1` subgroup character. -/
theorem fdRepCharacterRing_eq_characterRingInduction_of_isMonomial
    (V : FDRep ℂ G) (hmono : Representation.IsMonomial V.ρ) :
    ∃ H : Subgroup G, ∃ α : H →* ℂˣ,
      fdRepCharacterRing V = Subgroup.characterRingInduction H α.toCharacterRing := by
  have hmonchar : Representation.IsMonomialCharacter V.character := by
    -- Reduce the representation-level monomial witness to the source-facing monomial-character
    -- owner using the local induced-model comparison constructed above.
    exact isMonomialCharacter_of_isMonomial_local (ρ := V.ρ) hmono
  exact fdRepCharacterRing_eq_characterRingInduction_of_isMonomialCharacter V hmonchar


end

end Representation
