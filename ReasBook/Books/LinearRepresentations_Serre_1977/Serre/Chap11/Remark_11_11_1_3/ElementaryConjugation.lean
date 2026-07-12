import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1

-- Stable elementary-subgroup conjugation infrastructure extracted from Remark 11-11.1-3.

noncomputable section

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation TensorProduct

variable {G : Type} [Group G] [Finite G]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: elementary groups stay elementary under group isomorphisms. -/
private theorem isElementary_of_mulEquiv_local
    {H : Type*} [Group H] {J : Type*} [Group J]
    (e : H ≃* J) (hH : IsElementary H) :
    IsElementary J := by
  rcases hH with ⟨p, C, P, hCP⟩
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite P := hCP.finite_pGroup_factor
  letI : Finite J := Finite.of_equiv H e.toEquiv
  letI : IsCyclic C := hCP.cyclic
  refine ⟨p, C.map e.toMonoidHom, P.map e.toMonoidHom, ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finite.of_equiv P (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · let eC : C ≃* C.map e.toMonoidHom := Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
    exact isCyclic_of_surjective eC eC.surjective
  · have hcard : Nat.card (C.map e.toMonoidHom) = Nat.card C :=
      (Nat.card_congr (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).toEquiv).symm
    exact hcard ▸ hCP.coprime_card
  · exact hCP.isPGroup.of_equiv (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · intro c hc y hy
    rcases hc with ⟨c0, hc0, rfl⟩
    rcases hy with ⟨y0, hy0, rfl⟩
    simpa using congrArg e (hCP.centralizes hc0 y0 hy0)
  · have hcardC : Nat.card (C.map e.toMonoidHom) = Nat.card C :=
        (Nat.card_congr (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).toEquiv).symm
    have hcardP : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
        (Nat.card_congr (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective).toEquiv).symm
    have hcardJ : Nat.card H = Nat.card J := Nat.card_congr e.toEquiv
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · calc
        Nat.card (C.map e.toMonoidHom) * Nat.card (P.map e.toMonoidHom)
            = Nat.card C * Nat.card P := by rw [hcardC, hcardP]
        _ = Nat.card H := hCP.isComplement.card_mul
        _ = Nat.card J := hcardJ
    · rw [disjoint_iff, ← Subgroup.map_inf C P e.toMonoidHom e.injective,
        disjoint_iff.mp hCP.isComplement.disjoint, Subgroup.map_bot]

/-- Helper for Remark 11-11.1-3: the family of elementary subgroups is stable under conjugation.
-/
theorem elementary_mem_of_conj
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {H : Subgroup G} (hH : H ∈ X) (s : G) :
    (s •ᶜ H) ∈ X := by
  rw [hXelem]
  exact isElementary_of_mulEquiv_local ((MulAut.conj s).subgroupMap H) ((hXelem H).1 hH)

end CharacterizationOfCharacters

end Representation
