import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_5
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Representation SubgroupInduction

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

/-- A subgroup of a finite group is finite. -/
local instance instFintypeSubgroup_t1111 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Theorem 11-11.1-1: every element of Brauer's subgroup `V[p](G)` detects
membership after multiplication by the class function `φ`. -/
lemma pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H)
    (p : Nat.Primes) {χ : R(G)} (hχ : χ ∈ V[p](G)) :
    ((χ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G := by
  classical
  let _ : DecidablePred (fun H : Subgroup G ↦ IsPElementary (p : ℕ) H) := Classical.decPred _
  -- Rewrite `V[p](G)` as the supremum of induction ranges from `p`-elementary subgroups.
  rw [Representation.pElementaryInducedCharacterSpan] at hχ
  simp_rw [Representation.artinInducedCharacterSubmodule] at hχ
  refine Submodule.iSup_induction
      (p := fun H :
        { H : Subgroup G |
          H ∈ Finset.filter (fun H : Subgroup G ↦ IsPElementary (p : ℕ) H) Finset.univ } ↦
        LinearMap.range (Representation.Subgroup.characterRingInduction H.1))
      (motive := fun ξ : R(G) ↦
        ((ξ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G)
      hχ ?_ ?_ ?_
  · intro H ξ hξ
    rcases H with ⟨H, hHmem⟩
    rcases hξ with ⟨η, rfl⟩
    have hH : IsPElementary (p : ℕ) H := by
      simpa using (Finset.mem_filter.mp hHmem).2
    have hη :
        ((η : R(H)) : H → ℂ) ∈ characterRingScalarExtension A H :=
      mem_characterRingScalarExtension_of_mem_characterRing _ η.property
    have hφH :
        (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H :=
      hres H ⟨p, hH⟩
    have hmul :
        ((η : R(H)) : H → ℂ) * (H.classFunctionRestriction φ : H → ℂ) ∈
          characterRingScalarExtension A H :=
      mul_mem_characterRingScalarExtension hη hφH
    have hind :
        Ind[H]((((η : R(H)) : H → ℂ) * (H.classFunctionRestriction φ : H → ℂ))) ∈
          characterRingScalarExtension A G :=
      induced_mem_characterRingScalarExtension_of_mem (A := A) H hmul
    -- The source proof's product-with-induction identity turns the generator into an induced
    -- subgroup product, which already lies in `A ⊗R(G)`.
    rw [Representation.Subgroup.characterRingInduction_apply,
      induced_mul_eq_induced_mul_classFunctionRestriction]
    exact hind
  · simpa using zero_mem (characterRingScalarExtension A G)
  · intro ξ η hξ hη
    simpa [add_mul] using (characterRingScalarExtension A G).add_mem hξ hη

-- Source/core/bridge triage:
-- * source-facing: this subgroup-detection theorem for Serre's `A ⊗ R(G)`.
-- * core/canonical owner: bundled complex class functions `classFunctionSubmodule ℂ G`, with the
--   chapter alias `classFunctionSubspace G`.
-- * bridge/view: `characterRingScalarExtension A G`, the realized scalar-extension submodule in
--   `G → ℂ`.
--
-- Primitive data are the bundled class function `φ` and the restriction-membership hypotheses on
-- elementary subgroups. The coercions from bundled class functions to raw functions are derived
-- API and should not dominate the public theorem surface.

-- Proof sketch: apply Theorem `10-10.5-1` to write the unit character of `G` as an integral
-- combination of characters induced from elementary subgroups. Multiplying by `φ` and using the
-- class-function induction formula rewrites `φ` as a sum of inductions of the canonical
-- restrictions `H.classFunctionRestriction φ`. Each restricted term lies in `A ⊗R(H)` by
-- hypothesis, so every induced summand lies in `A ⊗R(G)`, hence `φ` is the realization of a
-- global tensor character.
/-- Theorem 11-11.1-1: a complex-valued class function on the finite group `G`, packaged in the
canonical bundled owner `classFunctionSubmodule ℂ G` (equivalently `classFunctionSubspace G`), is
realized by an element of Serre's tensor character ring `A ⊗R(G)` if, for every elementary
subgroup `H ≤ G`, its canonical restriction to `H` belongs to the corresponding scalar extension
`A ⊗R(H)`. -/
theorem classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H) :
    ∃ χ : A ⊗R(G), (χ : G → ℂ) = (φ : G → ℂ) := by
  -- Route correction: use Brauer's theorem on `⨆ p, V[p](G) = ⊤`, then test each `V[p](G)`
  -- against multiplication by `φ` rather than trying to construct the finite sum explicitly.
  have hone :
      ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
    have hone' : (1 : R(G)) ∈ (⨆ p : Nat.Primes, V[p](G)) := by
      have hone_top : (1 : R(G)) ∈ (⊤ : Submodule ℤ (R(G))) := by
        simp
      rwa [← iSup_pElementaryInducedCharacterSpan_eq_top (G := G)] at hone_top
    -- Once `1` lies in the Brauer supremum, `iSup`-induction reduces the claim to one `V[p]`.
    refine Submodule.iSup_induction
        (p := fun p : Nat.Primes ↦ V[p](G))
        (motive := fun χ : R(G) ↦
          ((χ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G)
        hone' ?_ ?_ ?_
    · intro p χ hχ
      exact pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension
        (A := A) φ hres p hχ
    · simpa using zero_mem (characterRingScalarExtension A G)
    · intro χ ψ hχ hψ
      simpa [add_mul] using (characterRingScalarExtension A G).add_mem hχ hψ
  have hφ : (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
    rw [← one_character_mul_classFunction φ]
    exact hone
  -- Convert the realized-span membership back to an element of the tensor character ring owner.
  exact tensorCharacter_exists_of_mem_characterRingScalarExtension (A := A) hφ

/-- Companion bridge/view form of Theorem `11-11.1-1` in the realized span
`characterRingScalarExtension A G`. -/
theorem classFunction_mem_characterRingScalarExtension_of_restrict_mem_on_elementarySubgroups
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H) :
    (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
  rcases
      classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups φ hres with
    ⟨χ, hχ⟩
  exact hχ ▸ tensorCharacterRing_mem_characterRingScalarExtension χ

end CharacterizationOfCharacters

end Representation
