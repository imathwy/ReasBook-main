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
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Theorem 11-11.1-1: multiplying an induced class function by the ambient class
function `φ` is the same as inducing the product with the canonical restriction of `φ`. -/
lemma induced_mul_eq_induced_mul_classFunctionRestriction
    (H : Subgroup G) (ψ : H → ℂ) (φ : classFunctionSubmodule ℂ G) :
    Ind[H](ψ) * (φ : G → ℂ) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → ℂ) h) := by
  classical
  -- Compare both sides pointwise and replace the global value of `φ` by its conjugacy-invariant
  -- value on the subgroup element contributing to the induction summand.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hφ :
        (φ : G → ℂ) (s⁻¹ * x * s) = (φ : G → ℂ) x := by
      exact ((mem_classFunctionSubmodule_iff ℂ _).1 φ.2).eq_of_isConj <|
        isConj_iff.2 ⟨s, by group⟩
    have hφ' :
        (φ : G → ℂ) (s⁻¹ * (x * s)) = (φ : G → ℂ) x := by
      simpa [mul_assoc] using hφ
    simp [hs', hφ', mul_comm, mul_assoc]
  · simp [hs]

/-- Helper for Theorem 11-11.1-1: subgroup induction sends the realized scalar extension
`A ⊗ R(H)` into `A ⊗ R(G)`. -/
lemma induced_mem_characterRingScalarExtension_of_mem
    (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ characterRingScalarExtension A H) :
    Ind[H](f) ∈ characterRingScalarExtension A G := by
  -- Induct over the `A`-span defining `characterRingScalarExtension A H`.
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      exact mem_characterRingScalarExtension_of_mem_characterRing (A := A) (Ind[H](χ)) <|
        Subgroup.inducedClassFunction_mem_characterRing H ⟨χ, hχ⟩
  | zero =>
      have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      rw [hzero]
      exact (zero_mem (characterRingScalarExtension A G) :
        (0 : G → ℂ) ∈ characterRingScalarExtension A G)
  | add f g _ _ hf hg =>
      simpa [Subgroup.inducedClassFunction_map_add] using
        (characterRingScalarExtension A G).add_mem hf hg
  | smul a f _ hf =>
      simpa [Subgroup.inducedClassFunction_map_smul] using
        (characterRingScalarExtension A G).smul_mem a hf

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

/-- Helper for Theorem 11-11.1-1: every realized element of `characterRingScalarExtension A G`
comes from an actual tensor character in `A ⊗ R(G)`. -/
lemma tensorCharacter_exists_of_mem_characterRingScalarExtension
    {f : G → ℂ} (hf : f ∈ characterRingScalarExtension A G) :
    ∃ χ : A ⊗R(G), (χ : G → ℂ) = f := by
  let fχ : characterRingScalarExtension A G := ⟨f, hf⟩
  obtain ⟨χ, hχ⟩ := (R(G)).toSubmodule.surjective_tensorToSpan A fχ
  change A ⊗R(G) at χ
  change (R(G)).toSubmodule.tensorToSpan A χ = fχ at hχ
  -- Forget the subtype after the surjective realization map to recover the ambient function.
  refine ⟨χ, ?_⟩
  simpa [fχ] using congrArg ((↑) : characterRingScalarExtension A G → G → ℂ) hχ

/-- Helper for Theorem 11-11.1-1: the unit character acts trivially by pointwise multiplication on
class functions. -/
lemma one_character_mul_classFunction (φ : classFunctionSubmodule ℂ G) :
    ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) = (φ : G → ℂ) := by
  -- Evaluate pointwise: the unit character has constant value `1`.
  ext x
  simp

-- Source/core/bridge triage:
-- * source-facing: this subgroup-detection theorem for LinearRepresentations_Serre_1977's `A ⊗ R(G)`.
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
realized by an element of LinearRepresentations_Serre_1977's tensor character ring `A ⊗R(G)` if, for every elementary
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
