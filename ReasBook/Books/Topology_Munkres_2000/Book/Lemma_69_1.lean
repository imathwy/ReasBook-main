module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

public section

universe u

/-- Lemma 69.1. A family in a group is a system of free generators if and only if
every assignment of its elements into any group extends uniquely to a homomorphism. -/
theorem existsFreeGroupBasis_iff_uniqueExtension {J G : Type u} [Group G] (a : J → G) :
    (∃ basis : FreeGroupBasis J G, ∀ α, basis α = a α) ↔
      ∀ {H : Type u} [Group H] (y : J → H), ∃! h : G →* H, ∀ α, h (a α) = y α := by
  constructor
  · rintro ⟨basis, h_basis⟩ H _ y
    refine ⟨basis.lift y, ?_, ?_⟩
    · intro α
      rw [← h_basis α]
      exact congr_fun (basis.lift.symm_apply_apply y) α
    · intro h h_apply
      apply basis.ext_hom
      intro α
      rw [h_basis α, h_apply α, ← h_basis α]
      exact (congr_fun (basis.lift.symm_apply_apply y) α).symm
  · intro h
    let basis := FreeGroupBasis.ofUniqueLift J a h
    refine ⟨basis, ?_⟩
    intro α
    change (FreeGroup.lift a) (FreeGroup.of α) = a α
    exact FreeGroup.lift_apply_of
