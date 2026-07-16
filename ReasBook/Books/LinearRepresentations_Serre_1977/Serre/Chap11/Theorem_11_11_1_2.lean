import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap09.Corollary_9_9_2_2
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Representation SubgroupInduction

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra ℚ A] [Algebra A ℂ] [IsScalarTower ℚ A ℂ]

/-- A subgroup of a finite group is finite. -/
private abbrev instFintypeTheorem111112Subgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H
attribute [local instance] instFintypeTheorem111112Subgroup

-- Source/core/bridge triage:
-- * source-facing: the cyclic-subgroup detection criterion for Serre's `A ⊗ R(G)`.
-- * core/canonical owner: bundled complex class functions `classFunctionSubmodule ℂ G`.
-- * bridge/view: `characterRingScalarExtension A G`, the realized scalar-extension submodule in
--   `G → ℂ`.
--
-- Primitive data are the bundled class function `φ` and the cyclic-subgroup restriction
-- hypotheses. The coercions to raw functions and the realized-span membership conclusion are
-- derived API.

-- Proof sketch: Artin's theorem expresses characters of `G` as rational linear combinations of
-- characters induced from cyclic subgroups. The restriction hypothesis makes every cyclic-induced
-- summand preserve `A ⊗R(G)` after multiplication by `φ`; applying this to the trivial character
-- shows that `φ` itself lies in the realized scalar extension.
/-- Helper for Theorem 11-11.1-2: multiplying by a cyclic-induced owner character preserves the
realized scalar extension once all cyclic restrictions of the class function are controlled. -/
lemma cyclic_owner_character_mul_classFunction_mem_characterRingScalarExtension
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsCyclic H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H)
    {χ : R(G)} (hχ : χ ∈ cyclicInducedCharacterSubmodule G) :
    ((χ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G := by
  classical
  -- Rewrite the owner as a supremum of cyclic induction ranges and check the claim on generators.
  rw [cyclicInducedCharacterSubmodule] at hχ
  simp_rw [Representation.artinInducedCharacterSubmodule] at hχ
  refine Submodule.iSup_induction
      (p := fun H : Subgroup.cyclicSubgroups G ↦ LinearMap.range H.1.characterRingInduction)
      (motive := fun ξ : R(G) ↦
        ((ξ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G)
      hχ ?_ ?_ ?_
  · intro H ξ hξ
    rcases hξ with ⟨η, rfl⟩
    have hη :
        ((η : R(H.1)) : H.1 → ℂ) ∈ characterRingScalarExtension A H.1 :=
      mem_characterRingScalarExtension_of_mem_characterRing _ η.property
    have hφH :
        (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ characterRingScalarExtension A H.1 :=
      hres H.1 ((Subgroup.mem_cyclicSubgroups).1 H.2)
    have hmul :
        ((η : R(H.1)) : H.1 → ℂ) * (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈
          characterRingScalarExtension A H.1 :=
      mul_mem_characterRingScalarExtension hη hφH
    -- The source proof's product-with-induction identity turns the generator into an induced
    -- subgroup product, which already lies in `A ⊗R(G)`.
    -- `characterRingInduction_apply` holds by `rfl`, so rewrite the induced product directly:
    -- the source proof's product-with-induction identity turns the generator into an induced
    -- subgroup product, which already lies in `A ⊗R(G)`.
    have key :
        Ind[H.1]((η : H.1 → ℂ)) * (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
      rw [induced_mul_eq_induced_mul_classFunctionRestriction]
      exact induced_mem_characterRingScalarExtension_of_mem (A := A) H.1 hmul
    exact key
  · simpa using zero_mem (characterRingScalarExtension A G)
  · intro ξ η hξ hη
    simpa [add_mul] using (characterRingScalarExtension A G).add_mem hξ hη

/-- Helper for Theorem 11-11.1-2: every element of the rational cyclic-induced span acts on the
class function `φ` by an element of the realized scalar extension. -/
lemma cyclic_span_mul_classFunction_mem_characterRingScalarExtension
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsCyclic H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H)
    {f : G → ℂ} (hf : f ∈ cyclicInducedCharacterSpan ℚ G) :
    f * (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
  classical
  rw [cyclicInducedCharacterSpan] at hf
  -- Extend the owner-level cyclic-induction step from generators to the full rational span.
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨χ, hχ, rfl⟩
      exact
        cyclic_owner_character_mul_classFunction_mem_characterRingScalarExtension
          (A := A) φ hres hχ
  | zero =>
      simpa using
        (zero_mem (characterRingScalarExtension A G) : (0 : G → ℂ) ∈ characterRingScalarExtension A G)
  | add f g _ _ hf hg =>
      simpa [add_mul] using (characterRingScalarExtension A G).add_mem hf hg
  | smul a f _ hf =>
      -- Rewrite the rational scalar as an `A`-scalar via `ℚ → A`.
      have hsmul :
          (algebraMap ℚ A a) • (f * (φ : G → ℂ)) ∈ characterRingScalarExtension A G :=
        (characterRingScalarExtension A G).smul_mem (algebraMap ℚ A a) hf
      simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using hsmul

/-- Owner-level lift form of Theorem `11-11.1-2` into Serre's tensor character ring `A ⊗R(G)`. -/
theorem classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_cyclicSubgroups
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsCyclic H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H) :
    ∃ χ : A ⊗R(G), (χ : G → ℂ) = (φ : G → ℂ) := by
  have hone_span :
      ((1 : R(G)) : G → ℂ) ∈ cyclicInducedCharacterSpan ℚ G := by
    -- Artin's theorem on cyclic subgroups places the trivial character in the rational cyclic span.
    have htriv :
        (FDRep.of (Representation.trivial ℂ G ℂ)).character = ((1 : R(G)) : G → ℂ) := by
      ext x
      change Representation.character (Representation.trivial ℂ G ℂ) x = 1
      simp [Representation.character, Representation.trivial]
    simpa [htriv] using
      (character_mem_ratSpan_inducedCharacter_from_cyclicSubgroups
        (V := FDRep.of (Representation.trivial ℂ G ℂ)))
  have hone_mul :
      ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) ∈ characterRingScalarExtension A G :=
    cyclic_span_mul_classFunction_mem_characterRingScalarExtension (A := A) φ hres hone_span
  have hφ : (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
    -- The unit character acts trivially, so the cyclic Artin span already contains `φ`.
    simpa [one_character_mul_classFunction φ] using hone_mul
  -- Convert the realized-span membership back to an element of the tensor character ring owner.
  exact tensorCharacter_exists_of_mem_characterRingScalarExtension (A := A) hφ

/-- Theorem 11-11.1-2: if `A` is a `ℚ`-algebra and the canonical restriction of the class
function `φ`, packaged in the canonical owner `classFunctionSubmodule ℂ G`, to every cyclic
subgroup `H ≤ G` lies in `A ⊗ R(H)`, then `φ` itself lies in `A ⊗ R(G)`, realized as
`characterRingScalarExtension A G`. -/
theorem classFunction_mem_characterRingScalarExtension_of_restrict_mem_on_cyclicSubgroups
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsCyclic H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H) :
    (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
  rcases classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_cyclicSubgroups φ hres with
    ⟨χ, hχ⟩
  simpa [hχ] using tensorCharacterRing_mem_characterRingScalarExtension χ

end CharacterizationOfCharacters

end Representation
