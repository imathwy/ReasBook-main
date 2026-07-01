import Serre.Chap13.Theorem_13_13_1_6

noncomputable section

namespace Representation

open scoped Pointwise Representation

section Exercise138RepresentativeSpan

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Exercise 13-13.1-17: conjugating a subgroup does not change its subgroup
permutation character. -/
theorem subgroupPermutationCharacter_eq_conj
    (H : Subgroup G) (g : ConjAct G) :
    (ℓ_{g • H}^G : G → ℚ) = (ℓ_{H}^G : G → ℚ) := by
  classical
  symm
  ext x
  have hcard : Nat.card ↥(g • H) = Nat.card H := by
    rw [Subgroup.pointwise_smul_def]
    exact Nat.card_congr
      (((MulAut.conj (ConjAct.ofConjAct g)).subgroupMap H).symm.toEquiv)
  rw [Subgroup.characterRingOverFieldInduction_apply,
    Subgroup.characterRingOverFieldInduction_apply]
  rw [Subgroup.inducedClassFunction, Subgroup.inducedClassFunction, hcard]
  let c : G := ConjAct.ofConjAct g
  let φ : G → ℚ := fun s ↦
    if hs : s⁻¹ * x * s ∈ H then
      (1 : H → ℚ) ⟨s⁻¹ * x * s, hs⟩
    else 0
  let ψ : G → ℚ := fun t ↦
    if ht : t⁻¹ * x * t ∈ g • H then
      (1 : (↥(g • H) → ℚ)) ⟨t⁻¹ * x * t, ht⟩
    else 0
  have hmem : ∀ s : G,
      ((s * c⁻¹)⁻¹ * x * (s * c⁻¹) ∈ g • H) ↔ s⁻¹ * x * s ∈ H := by
    intro s
    rw [Subgroup.pointwise_smul_def]
    constructor
    · rintro ⟨h, hhH, hh⟩
      have hh' : c * h * c⁻¹ = c * (s⁻¹ * x * s) * c⁻¹ := by
        simpa [c, ConjAct.smul_def, mul_assoc] using hh
      have hmul := congrArg (fun y : G ↦ c⁻¹ * y * c) hh'
      have hEq : h = s⁻¹ * x * s := by
        simpa [mul_assoc] using hmul
      simpa [hEq] using hhH
    · intro hs
      refine ⟨s⁻¹ * x * s, hs, ?_⟩
      simp [c, ConjAct.smul_def, mul_assoc]
  have hphi : ∑ s : G, φ s = ∑ t : G, ψ t := by
    exact
      Fintype.sum_bijective
        (fun s : G ↦ s * c⁻¹)
        (Group.mulRight_bijective c⁻¹)
        φ ψ
        (fun s ↦ by
          dsimp [φ, ψ]
          by_cases hs : s⁻¹ * x * s ∈ H
          · rw [if_pos hs, if_pos ((hmem s).2 hs)]
          · have ht : ¬ ((s * c⁻¹)⁻¹ * x * (s * c⁻¹) ∈ g • H) :=
              fun h ↦ hs ((hmem s).1 h)
            rw [if_neg hs, if_neg ht])
  simpa [φ, ψ] using congrArg ((Nat.card H : ℚ)⁻¹ * ·) hphi

/-- Helper for Exercise 13-13.1-17: conjugate subgroups have the same subgroup permutation
character. -/
theorem subgroupPermutationCharacter_eq_of_isConj
    {H K : Subgroup G} (hHK : H.IsConj K) :
    (ℓ_{H}^G : G → ℚ) = (ℓ_{K}^G : G → ℚ) := by
  rw [Subgroup.isConj_iff_orbitRel, MulAction.orbitRel_apply] at hHK
  rcases hHK with ⟨g, hg⟩
  calc
    (ℓ_{H}^G : G → ℚ) = (ℓ_{g • K}^G : G → ℚ) := by rw [← hg]
    _ = (ℓ_{K}^G : G → ℚ) := subgroupPermutationCharacter_eq_conj K g

/-- Helper for Exercise 13-13.1-17: the chosen representative family viewed in
`ℚ ⊗R[ℚ](G)`. -/
def representativeCyclicPermutationCharacter
    {d : ℕ} (C : Fin d → Subgroup G) (i : Fin d) :
    ℚ ⊗R[ℚ](G) :=
  ⟨(ℓ_{C i}^G : G → ℚ),
    mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
      ((ℓ_{C i}^G : R[ℚ](G)).property)⟩

/-- Helper for Exercise 13-13.1-17: the representative-family characters still span the full
rational character ring. -/
theorem top_le_span_representative_cyclic_permutation_characters
    (d : ℕ) (C : Fin d → Subgroup G)
    (hC_cyclic : ∀ i, IsCyclic (C i))
    (hC_surj :
      ∀ H : Subgroup G, IsCyclic H →
        ∃ i : Fin d, (C i).IsConj H) :
    (⊤ : Submodule ℚ (ℚ ⊗R[ℚ](G))) ≤
      Submodule.span ℚ (Set.range (representativeCyclicPermutationCharacter (G := G) C)) := by
  intro θ _
  let Sraw : Submodule ℚ (G → ℚ) :=
    Submodule.span ℚ
      (Set.range fun H : Subgroup.cyclicSubgroups G ↦ (ℓ_{H.1}^G : G → ℚ))
  let Srep : Submodule ℚ (ℚ ⊗R[ℚ](G)) :=
    Submodule.span ℚ (Set.range (representativeCyclicPermutationCharacter (G := G) C))
  have hraw :
      ((θ : ℚ ⊗R[ℚ](G)) : G → ℚ) ∈ Sraw := by
    have hspan :
        (ℚ ⊗R[ℚ](G) : Submodule ℚ (G → ℚ)) = Sraw := by
      simpa [Sraw] using
        (characterRingOverFieldScalarExtension_eq_span_cyclic_subgroupPermutationCharactersOverQ :
          (ℚ ⊗R[ℚ](G) : Submodule ℚ (G → ℚ)) =
            Submodule.span ℚ
              (Set.range fun H : Subgroup.cyclicSubgroups G ↦ (ℓ_{H.1}^G : G → ℚ)))
    exact hspan ▸ θ.property
  let ownerSubtype : (ℚ ⊗R[ℚ](G)) →ₗ[ℚ] (G → ℚ) := Submodule.subtype (ℚ ⊗R[ℚ](G))
  let T : Submodule ℚ (G → ℚ) := Submodule.map ownerSubtype Srep
  have hlift_raw_aux : ∀ f : G → ℚ, f ∈ Sraw → f ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨H, rfl⟩
        rcases hC_surj H.1 (Subgroup.mem_cyclicSubgroups.mp H.2) with ⟨i, hi⟩
        have hchar :
            (ℓ_{C i}^G : G → ℚ) = (ℓ_{H.1}^G : G → ℚ) := by
          exact subgroupPermutationCharacter_eq_of_isConj (G := G) hi
        refine Submodule.mem_map.mpr ?_
        refine ⟨representativeCyclicPermutationCharacter (G := G) C i, ?_, ?_⟩
        · exact Submodule.subset_span ⟨i, rfl⟩
        · simpa [ownerSubtype, representativeCyclicPermutationCharacter] using hchar
    | zero =>
        simpa [T] using (Submodule.zero_mem T)
    | add f g _ _ hf hg =>
        simpa [T] using Submodule.add_mem T hf hg
    | smul a f _ hf =>
        simpa [T] using Submodule.smul_mem T a hf
  have hlift_raw : ((θ : ℚ ⊗R[ℚ](G)) : G → ℚ) ∈ T := hlift_raw_aux _ hraw
  rcases Submodule.mem_map.mp hlift_raw with ⟨η, hη, hηeq⟩
  have hηθ : η = θ := by
    apply Subtype.ext
    simpa [ownerSubtype] using hηeq
  simpa [Srep, hηθ] using hη

end Exercise138RepresentativeSpan

end Representation
