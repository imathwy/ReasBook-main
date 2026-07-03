import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_11_11_1_1 (from Chap11) -/
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

/-! ### Theorem_11_11_1_2 (from Chap11) -/
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
-- * source-facing: the cyclic-subgroup detection criterion for LinearRepresentations_Serre_1977's `A ⊗ R(G)`.
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
    rw [Subgroup.characterRingInduction_apply,
      induced_mul_eq_induced_mul_classFunctionRestriction]
    exact induced_mem_characterRingScalarExtension_of_mem (A := A) H.1 hmul
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

/-- Owner-level lift form of Theorem `11-11.1-2` into LinearRepresentations_Serre_1977's tensor character ring `A ⊗R(G)`. -/
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

/-! ### Theorem_11_11_1_4 (from Chap11) -/
open scoped BigOperators Representation SubgroupInduction

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

/-- Helper for Theorem 11-11.1-4: every subgroup of a finite group is finite. -/
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Theorem 11-11.1-4: elementary groups stay elementary under multiplication
equivalences. -/
private theorem isElementary_of_mulEquiv_local
    {H : Type*} [Group H] {J : Type*} [Group J]
    (e : H ≃* J) (hH : IsElementary H) :
    IsElementary J := by
  rcases hH with ⟨p, C, P, hCP⟩
  -- Transport the textbook `p`-elementary decomposition across the chosen equivalence.
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite P := hCP.finite_pGroup_factor
  letI : Finite J := Finite.of_equiv H e.toEquiv
  letI : IsCyclic C := hCP.cyclic
  refine ⟨p, C.map e.toMonoidHom, P.map e.toMonoidHom, ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finite.of_equiv P (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  · let eC : C ≃* C.map e.toMonoidHom :=
      Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
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

/-- Helper for Theorem 11-11.1-4: subgroups of elementary groups are elementary. -/
private theorem subgroup_isElementary_of_isElementary_local
    {H : Type*} [Group H] (K : Subgroup H) (hH : IsElementary H) :
    IsElementary K := by
  rcases hH with ⟨p, hpH⟩
  rcases hpH with ⟨C, P, hCP⟩
  letI : Fact (Nat.Prime p) := ⟨hCP.prime⟩
  letI : Finite H := (show IsPElementary p H from ⟨C, P, hCP⟩).finite
  letI : Finite K := Finite.of_injective ((↑) : K → H) Subtype.val_injective
  let C' : Subgroup K := (K ⊓ C).subgroupOf K
  let P' : Subgroup K := (K ⊓ P).subgroupOf K
  letI : Finite ↥C' := Finite.of_injective ((↑) : C' → K) Subtype.val_injective
  letI : Finite ↥P' := Finite.of_injective ((↑) : P' → K) Subtype.val_injective
  have hC'card : Nat.card ↥C' = Nat.card ↥(K ⊓ C) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).toEquiv
  -- Restrict the textbook `p`-elementary decomposition to the chosen subgroup `K`.
  refine ⟨p, C', P', ?_⟩
  refine ⟨hCP.prime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · letI : IsCyclic ↥C := hCP.cyclic
    letI : IsCyclic ↥(K ⊓ C) :=
      Subgroup.isCyclic_of_le (show K ⊓ C ≤ C from inf_le_right)
    exact
      isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ C ≤ K from inf_le_left)).symm.surjective
  · have hdiv : Nat.card ↥(K ⊓ C) ∣ Nat.card ↥C := by
      exact Subgroup.card_dvd_of_le (show K ⊓ C ≤ C from inf_le_right)
    rw [hC'card]
    exact hCP.coprime_card.of_dvd_right hdiv
  · have hPsub : IsPGroup p ↥((K ⊓ P).subgroupOf P) := by
      exact hCP.isPGroup.to_subgroup ((K ⊓ P).subgroupOf P)
    have hPinf_right : IsPGroup p ↥(K ⊓ P) := by
      exact hPsub.of_equiv
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ P ≤ P from inf_le_right))
    exact hPinf_right.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show K ⊓ P ≤ K from inf_le_left)).symm
  · intro c hc u hu
    have hcC : ((c : K) : H) ∈ C := by
      exact (show ((c : K) : H) ∈ K ⊓ C from hc).2
    have huP : ((u : K) : H) ∈ P := by
      exact (show ((u : K) : H) ∈ K ⊓ P from hu).2
    apply Subtype.ext
    simpa using hCP.centralizes hcC ((u : K) : H) huP
  · refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxC hxP
      have hxCG : ((x : K) : H) ∈ C := by
        exact (show ((x : K) : H) ∈ K ⊓ C from hxC).2
      have hxPG : ((x : K) : H) ∈ P := by
        exact (show ((x : K) : H) ∈ K ⊓ P from hxP).2
      have hxbot : ((x : K) : H) ∈ (⊥ : Subgroup H) := by
        have hbot : C ⊓ P = (⊥ : Subgroup H) := disjoint_iff.mp hCP.isComplement.disjoint
        exact hbot ▸ ⟨hxCG, hxPG⟩
      apply Subtype.ext
      simpa using hxbot
    · apply Set.eq_univ_iff_forall.2
      intro x
      let xr : K := pRegularComponent p x
      let xu : K := pUnipotentComponent p x
      have hdecomp : IsPComponentDecomposition p x xu xr := by
        simpa [xu, xr] using
          p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
      have hxrC : (xr : H) ∈ C := by
        have hxrReg : IsPRegular p (xr : H) := by
          simpa [IsPRegular, Subgroup.orderOf_mk, xr] using hdecomp.isPRegular
        change (xr : H) ∈ (C : Set H)
        rw [hCP.cyclic_factor_eq_setOf_isPRegular]
        exact hxrReg
      have hxuP : (xu : H) ∈ P := by
        have hxuElt : IsPElement p (xu : H) := by
          simpa [IsPElement, Subgroup.orderOf_mk, xu] using hdecomp.isPElement
        change (xu : H) ∈ (P : Set H)
        rw [hCP.p_group_factor_eq_setOf_isPElement]
        exact hxuElt
      have hxr_mem : xr ∈ C' := by
        change (xr : H) ∈ K ⊓ C
        exact ⟨xr.2, hxrC⟩
      have hxu_mem : xu ∈ P' := by
        change (xu : H) ∈ K ⊓ P
        exact ⟨xu.2, hxuP⟩
      refine ⟨xr, hxr_mem, xu, hxu_mem, ?_⟩
      calc
        xr * xu = xu * xr := by
          simpa using hdecomp.commute.symm
        _ = x := hdecomp.mul_eq

/-- Helper for Theorem 11-11.1-4: evaluating the irreducible-character basis expansion of a
bundled class function recovers its pointwise values. -/
private theorem classFunction_basis_expansion_apply_local
    {H : Type*} [Group H] [Finite H]
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (classFunctionSubmodule ℂ H))
    (x : classFunctionSubmodule ℂ H) (h : H) :
    (∑ j, ((b.repr x j) • b j : classFunctionSubmodule ℂ H)) h = x h := by
  -- Evaluate the standard basis expansion `b.sum_repr x = x` at the chosen group element.
  exact congrArg (fun z : classFunctionSubmodule ℂ H ↦ z h) (b.sum_repr x)

/-- Helper for Theorem 11-11.1-4: in the irreducible-character basis coming from a complete
family, each coordinate is the normalized pairing with the corresponding irreducible character. -/
private theorem repr_irreducible_character_basis_eq_pairing_local
    {H : Type}
    [Group H] [Finite H]
    {ι : Type*}
    (π : ι → FDRep ℂ H)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    [Fintype ι]
    (x : classFunctionSubmodule ℂ H) (i : ι) :
    (irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
        π hπ_pairwise hπ_complete).repr x i =
      Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let coordLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ b.repr y i
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro a y
        simp }
  let pairLinear : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦
        Representation.groupFunctionPairingOverField ℂ (y : H → ℂ) (π i).character
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_left
          (y : H → ℂ) (z : H → ℂ) (π i).character
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_left
          a (y : H → ℂ) (π i).character }
  have hmaps : coordLinear = pairLinear := by
    -- Compare the coordinate functional and the pairing functional on the irreducible basis.
    apply b.ext
    intro j
    have hcoord_j : coordLinear (b j) = if i = j then 1 else 0 := by
      simpa [eq_comm] using
        (show coordLinear (b j) = if j = i then 1 else 0 by
          simp [coordLinear, Module.Basis.repr_self, Finsupp.single_apply])
    have hpair_j : pairLinear (b j) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hself_iso : Nonempty (π i ≅ π i) := ⟨CategoryTheory.Iso.refl _⟩
        calc
          pairLinear (b i) =
              Representation.groupFunctionPairingOverField ℂ
                (π i).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 1 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hself_iso] using
              (FDRep.char_orthonormal (π i) (π i))
          _ = if i = i then 1 else 0 := by simp
      · have hji : j ≠ i := fun h ↦ hij h.symm
        letI : CategoryTheory.Simple (π j) := hπ_complete.isSimple j
        letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
        have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
        calc
          pairLinear (b j) =
              Representation.groupFunctionPairingOverField ℂ
                (π j).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 0 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hnot] using
              (FDRep.char_orthonormal (π j) (π i))
          _ = if i = j then 1 else 0 := by simp [hij]
    exact hcoord_j.trans hpair_j.symm
  -- Apply the equality of linear functionals to the chosen class function.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [coordLinear, pairLinear] using hmaps_apply

/-- Helper for Theorem 11-11.1-4: Frobenius reciprocity identifies the pairing of an induced
linear character with any bundled class function on the ambient subgroup. -/
private theorem groupFunctionPairing_induced_linearCharacter_eq_restriction
    {H : Type} [Group H] [Finite H]
    (K : Subgroup H) (α : K →* ℂˣ) (x : classFunctionSubmodule ℂ H) :
    ⟪Ind[K](α.toRepresentation.character), (x : H → ℂ)⟫ =
      ⟪α.toCharacterRing, Subgroup.classFunctionRestriction K x⟫ := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let _ : Fintype K := Fintype.ofFinite K
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let _ : NeZero (Nat.card K : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let _ : Invertible (Nat.card H : ℂ) := invertibleOfNonzero <| by
    simpa using (NeZero.ne (Nat.card H : ℂ))
  let _ : Invertible (Nat.card K : ℂ) := invertibleOfNonzero <| by
    simpa using (NeZero.ne (Nat.card K : ℂ))
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    FDRep.exists_complete_pairwise_nonisomorphic_simple_family (k := ℂ) (G := H)
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let inducedPairing : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ ⟪Ind[K](α.toRepresentation.character), (y : H → ℂ)⟫
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_right
          (Ind[K](α.toRepresentation.character)) (y : H → ℂ) (z : H → ℂ)
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_right
          a (Ind[K](α.toRepresentation.character)) (y : H → ℂ) }
  let restrictedPairing : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ ⟪α.toCharacterRing, Subgroup.classFunctionRestriction K y⟫
      map_add' := by
        intro y z
        simp [Representation.groupFunctionPairing_add_right]
      map_smul' := by
        intro a y
        simp [Representation.groupFunctionPairing_smul_right] }
  have hmaps : inducedPairing = restrictedPairing := by
    -- Compare the two linear functionals on the irreducible-character basis of `H`.
    apply b.ext
    intro i
    have hind :
        Ind[K](α.toRepresentation.character) =
          (Representation.ind K.subtype α.toRepresentation).character := by
      simpa using
        (Subgroup.inducedClassFunction_eq_character_ind (H := K) (θ := α.toRepresentation))
    have hrestrict :
        ((Subgroup.classFunctionRestriction K (b i) : classFunctionSubmodule ℂ K) : K → ℂ) =
          Representation.character ((π i).ρ.comp K.subtype) := by
      ext k
      simp [b, irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply,
        Subgroup.classFunctionRestriction_apply, FDRep.character, Representation.character]
    -- Frobenius reciprocity on characters gives the equality on each basis vector.
    calc
      inducedPairing (b i) =
          ⟪(Representation.ind K.subtype α.toRepresentation).character, (π i).character⟫ := by
            simp [inducedPairing, hind, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
      _ = ⟪α.toRepresentation.character, Representation.character ((π i).ρ.comp K.subtype)⟫ := by
            simpa using
              (groupFunctionPairing_character_comp_eq_character_ind_bridge
                (α := K.subtype) (E := (π i).ρ) (θ := α.toRepresentation)).symm
      _ = restrictedPairing (b i) := by
            simp [restrictedPairing, hrestrict]
  -- Apply the equality of linear functionals to the target class function.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [inducedPairing, restrictedPairing] using hmaps_apply

/-- Helper for Theorem 11-11.1-4: reindexing along `K ≃ K.map H.subtype` identifies the ambient
pairing with the nested restriction pairing. -/
private theorem mapped_linear_character_pairing_eq_nested_restriction
    (φ : classFunctionSubmodule ℂ G)
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    ⟪(Subgroup.mappedLinearCharacter H K χ).toCharacterRing,
        Subgroup.classFunctionRestriction (K.map H.subtype) φ⟫ =
      ⟪χ.toCharacterRing,
        Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ)⟫ := by
  classical
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  let nested : K → ℂ := fun y ↦
    (χ.toCharacterRing : K → ℂ) y *
      ((Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ) :
          classFunctionSubmodule ℂ K) : K → ℂ) y⁻¹
  let ambient : K.map H.subtype → ℂ := fun y ↦
    ((Subgroup.mappedLinearCharacter H K χ).toCharacterRing : K.map H.subtype → ℂ) y *
      ((Subgroup.classFunctionRestriction (K.map H.subtype) φ :
          classFunctionSubmodule ℂ (K.map H.subtype)) : K.map H.subtype → ℂ) y⁻¹
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
    Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have hcardNat : Nat.card (K.map H.subtype) = Nat.card K :=
    (Nat.card_congr e.toEquiv).symm
  have hcard : ((Nat.card (K.map H.subtype) : ℕ) : ℂ) = (Nat.card K : ℂ) := by
    exact_mod_cast hcardNat
  rw [hcard]
  -- Reindex the ambient average along the subgroup equivalence `K ≃ K.map H.subtype`.
  refine congrArg (fun z : ℂ ↦ (Nat.card K : ℂ)⁻¹ * z) ?_
  change (∑ t : K.map H.subtype, ambient t) = ∑ t : K, nested t
  exact (Fintype.sum_equiv e nested ambient (by
    intro y
    -- After transporting along `e`, both the mapped linear character and the nested restriction
    -- reduce to the original subgroup data.
    dsimp [nested, ambient]
    congr 1
    simp [e, Subgroup.mappedLinearCharacter])).symm

/-- Helper for Theorem 11-11.1-4: transporting a linear character from a subgroup of an
elementary subgroup to its image in the ambient group preserves the relevant pairing. -/
private theorem pairing_mem_range_on_nested_elementary_linear_character
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈ Set.range (algebraMap A ℂ))
    (H : Subgroup G) (hH : IsElementary H) (K : Subgroup H) (χ : K →* ℂˣ) :
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K (Subgroup.classFunctionRestriction H φ)⟫ ∈
      Set.range (algebraMap A ℂ) := by
  have hK : IsElementary K := subgroup_isElementary_of_isElementary_local K hH
  have hKmap : IsElementary (K.map H.subtype) :=
    isElementary_of_mulEquiv_local (K.equivMapOfInjective H.subtype H.subtype_injective) hK
  have hmap :=
    hpair (K.map H.subtype) hKmap (Subgroup.mappedLinearCharacter H K χ)
  -- Route correction: descend immediately by reindexing the ambient pairing on `K.map H.subtype`
  -- back to the original subgroup `K`.
  rw [← mapped_linear_character_pairing_eq_nested_restriction (φ := φ) H K χ]
  exact hmap

/-- Helper for Theorem 11-11.1-4: any monomial character on an elementary subgroup pairs against
the restricted class function in the image of `A`. -/
private theorem pairing_mem_range_of_mem_monomialCharacterSpan_on_elementary_restriction
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈ Set.range (algebraMap A ℂ))
    (H : Subgroup G) (hH : IsElementary H)
    {η : R(H)} (hη : η ∈ monomialCharacterSpan H) :
    ⟪(η : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ ∈ Set.range (algebraMap A ℂ) := by
  rw [monomialCharacterSpan] at hη
  -- Extend the degree-`1` pairing criterion to the full monomial span by linearity.
  induction hη using Submodule.span_induction with
  | mem ξ hξ =>
      rcases hξ with ⟨K, α, hα⟩
      -- The generator case is exactly Frobenius reciprocity followed by the nested descent.
      rw [← hα]
      rw [groupFunctionPairing_induced_linearCharacter_eq_restriction]
      exact pairing_mem_range_on_nested_elementary_linear_character (A := A) φ hpair H hH K α
  | zero =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | add ξ ζ _ _ hξ hζ =>
      rcases hξ with ⟨a, ha⟩
      rcases hζ with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simpa [Representation.groupFunctionPairing_add_left, ha, hb, map_add]
  | smul n ξ _ hξ =>
      rcases hξ with ⟨a, ha⟩
      refine ⟨(n : A) * a, ?_⟩
      have hsmul :
          ⟪((n : ℤ) • (ξ : H → ℂ)), Subgroup.classFunctionRestriction H φ⟫ =
            (n : ℂ) * ⟪(ξ : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ := by
        simpa using
          (Representation.groupFunctionPairing_smul_left
            (a := (n : ℂ)) (φ := (ξ : H → ℂ))
            (ψ := Subgroup.classFunctionRestriction H φ))
      change algebraMap A ℂ ((n : A) * a) =
        ⟪((n • ξ : R(H)) : H → ℂ), Subgroup.classFunctionRestriction H φ⟫
      calc
        algebraMap A ℂ ((n : A) * a) =
            (n : ℂ) * ⟪(ξ : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ := by
              simpa [ha, map_mul, mul_assoc]
        _ = ⟪((n : ℤ) • (ξ : H → ℂ)), Subgroup.classFunctionRestriction H φ⟫ := hsmul.symm
        _ = ⟪((n • ξ : R(H)) : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ := by
              rfl

/-- Helper for Theorem 11-11.1-4: if every degree-`1` pairing on every elementary subgroup lands
in the image of `A`, then each elementary restriction already belongs to the corresponding scalar
extension. -/
lemma elementary_restriction_mem_characterRingScalarExtension_of_pairing_mem_range
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈ Set.range (algebraMap A ℂ))
    (H : Subgroup G) (hH : IsElementary H) :
    (Subgroup.classFunctionRestriction H φ : H → ℂ) ∈ characterRingScalarExtension A H := by
  classical
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    FDRep.exists_complete_pairwise_nonisomorphic_simple_family (k := ℂ) (G := H)
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let x : classFunctionSubmodule ℂ H := Subgroup.classFunctionRestriction H φ
  have hsum :
      ((((∑ i, ((b.repr x i) • b i : classFunctionSubmodule ℂ H)) :
          classFunctionSubmodule ℂ H) : H → ℂ)) ∈ characterRingScalarExtension A H := by
    have hsum_fun :
        (∑ i, ((((b.repr x i) • b i : classFunctionSubmodule ℂ H) : H → ℂ))) ∈
          characterRingScalarExtension A H := by
      -- Expand `x` in the irreducible-character basis and show each coefficient comes from `A`.
      refine Submodule.sum_mem (characterRingScalarExtension A H) ?_
      intro i hi
      have hmono : fdRepCharacterRing (π i) ∈ monomialCharacterSpan H := by
        rw [monomialCharacterSpan_eq_top_of_isElementary hH]
        simp
      have hpairing :
          ⟪((fdRepCharacterRing (π i) : R(H)) : H → ℂ), (x : H → ℂ)⟫ ∈
            Set.range (algebraMap A ℂ) :=
        pairing_mem_range_of_mem_monomialCharacterSpan_on_elementary_restriction
          (A := A) φ hpair H hH hmono
      rcases hpairing with ⟨a, ha⟩
      have ha' : algebraMap A ℂ a =
          Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character := by
        simpa [fdRepCharacterRing, Representation.groupFunctionPairing_comm] using ha
      have hcoeff : b.repr x i = algebraMap A ℂ a := by
        calc
          b.repr x i =
              Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character :=
            repr_irreducible_character_basis_eq_pairing_local
              (π := π) hπ_pairwise hπ_complete x i
          _ = algebraMap A ℂ a := ha'.symm
      have hbase :
          (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) ∈ characterRingScalarExtension A H := by
        have hb :
            (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) =
              (((fdRepCharacterRing (π i) : R(H)) : H → ℂ)) := by
          ext h
          simp [b, irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
        rw [hb]
        exact mem_characterRingScalarExtension_of_mem_characterRing (A := A)
          (((fdRepCharacterRing (π i) : R(H)) : H → ℂ)) (fdRepCharacterRing (π i)).property
      have hterm :
          ((((b.repr x i) • b i : classFunctionSubmodule ℂ H) : H → ℂ)) =
            a • (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) := by
        ext h
        simp [hcoeff]
      rw [hterm]
      exact (characterRingScalarExtension A H).smul_mem a hbase
    have hsum_coe :
        (∑ i, ((((b.repr x i) • b i : classFunctionSubmodule ℂ H) : H → ℂ))) =
          ((((∑ i, ((b.repr x i) • b i : classFunctionSubmodule ℂ H)) :
              classFunctionSubmodule ℂ H) : H → ℂ)) := by
      ext h
      let eval_h : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
        { toFun := fun z ↦ z h
          map_add' := by
            intro y z
            rfl
          map_smul' := by
            intro a z
            rfl }
      simpa using
        (_root_.map_sum eval_h
          (fun j ↦ ((b.repr x j) • b j : classFunctionSubmodule ℂ H)) Finset.univ).symm
    -- Expand `x` in the irreducible-character basis and show each coefficient comes from `A`.
    exact hsum_coe.symm ▸ hsum_fun
  have hx :
      ((((∑ i, ((b.repr x i) • b i : classFunctionSubmodule ℂ H)) :
          classFunctionSubmodule ℂ H) : H → ℂ)) = (x : H → ℂ) := by
    exact congrArg (fun z : classFunctionSubmodule ℂ H ↦ (z : H → ℂ)) (b.sum_repr x)
  simpa [x] using hx ▸ hsum

/-- Helper for Theorem 11-11.1-4: multiplying an induced class function by the ambient class
function is the same as inducing the product with the subgroup restriction. -/
private theorem induced_mul_eq_induced_mul_classFunctionRestriction_local
    (H : Subgroup G) (ψ : H → ℂ) (φ : classFunctionSubmodule ℂ G) :
    Ind[H](ψ) * (φ : G → ℂ) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → ℂ) h) := by
  classical
  -- Compare both sides pointwise and replace the ambient value of `φ` by its conjugacy-invariant
  -- subgroup value on each induction summand.
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

/-- Helper for Theorem 11-11.1-4: subgroup induction sends realized scalar-extension elements
into the ambient scalar extension. -/
private theorem induced_mem_characterRingScalarExtension_of_mem_local
    (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ characterRingScalarExtension A H) :
    Ind[H](f) ∈ characterRingScalarExtension A G := by
  -- Induct over the defining `A`-span on `H`, reducing to honest induced characters.
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      exact mem_characterRingScalarExtension_of_mem_characterRing (A := A) (Ind[H](χ)) <|
        Subgroup.inducedClassFunction_mem_characterRing H ⟨χ, hχ⟩
  | zero =>
      have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      rw [hzero]
      exact
        (zero_mem (characterRingScalarExtension A G) :
          (0 : G → ℂ) ∈ characterRingScalarExtension A G)
  | add f g _ _ hf hg =>
      simpa [Subgroup.inducedClassFunction_map_add] using
        (characterRingScalarExtension A G).add_mem hf hg
  | smul a f _ hf =>
      simpa [Subgroup.inducedClassFunction_map_smul] using
        (characterRingScalarExtension A G).smul_mem a hf

/-- Helper for Theorem 11-11.1-4: every realized scalar-extension element comes from an actual
tensor character. -/
private theorem tensorCharacter_exists_of_mem_characterRingScalarExtension_local
    {f : G → ℂ} (hf : f ∈ characterRingScalarExtension A G) :
    ∃ χ : A ⊗R(G), (χ : G → ℂ) = f := by
  let fχ : characterRingScalarExtension A G := ⟨f, hf⟩
  obtain ⟨χ, hχ⟩ := (R(G)).toSubmodule.surjective_tensorToSpan A fχ
  change A ⊗R(G) at χ
  change (R(G)).toSubmodule.tensorToSpan A χ = fχ at hχ
  -- Forget the subtype after surjectivity of the realization map.
  refine ⟨χ, ?_⟩
  simpa [fχ] using congrArg ((↑) : characterRingScalarExtension A G → G → ℂ) hχ

/-- Helper for Theorem 11-11.1-4: the unit character acts trivially on class functions by
pointwise multiplication. -/
private theorem one_character_mul_classFunction_local (φ : classFunctionSubmodule ℂ G) :
    ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) = (φ : G → ℂ) := by
  -- Evaluate pointwise: the unit character has constant value `1`.
  ext x
  simp

/-- Helper for Theorem 11-11.1-4: every element of Brauer's subgroup `V[p](G)` detects realized
scalar-extension membership after multiplication by the ambient class function. -/
private theorem pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension
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
      mem_characterRingScalarExtension_of_mem_characterRing (A := A) _ η.property
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
      induced_mem_characterRingScalarExtension_of_mem_local (A := A) H hmul
    -- The source proof turns a Brauer generator into the corresponding subgroup-induced product.
    rw [Representation.Subgroup.characterRingInduction_apply,
      induced_mul_eq_induced_mul_classFunctionRestriction_local]
    exact hind
  · simpa using zero_mem (characterRingScalarExtension A G)
  · intro ξ η hξ hη
    simpa [add_mul] using (characterRingScalarExtension A G).add_mem hξ hη

/-- Helper for Theorem 11-11.1-4: realized scalar-extension membership on every elementary
subgroup lifts the ambient class function into LinearRepresentations_Serre_1977's tensor character ring. -/
private theorem classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups_local
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H) :
    ∃ χ : A ⊗R(G), (χ : G → ℂ) = (φ : G → ℂ) := by
  -- Route correction: rebuild the Chapter `11.1` Brauer descent locally from Theorem `10-10.5-2`
  -- so this item no longer depends on the broken compiled artifact for `11-11.1-1`.
  have hone :
      ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
    have hone' : (1 : R(G)) ∈ (⨆ p : Nat.Primes, V[p](G)) := by
      simpa using character_mem_iSup_pElementaryInducedCharacterSpan (G := G) (1 : R(G))
    -- Once the unit character lies in Brauer's supremum, `iSup`-induction reduces the claim to
    -- one subgroup family `V[p](G)`.
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
    rw [← one_character_mul_classFunction_local φ]
    exact hone
  -- Convert realized-span membership back to an actual tensor character.
  exact tensorCharacter_exists_of_mem_characterRingScalarExtension_local (A := A) hφ

/-- Theorem 11-11.1-4: if the canonical restriction of a bundled class function `φ` to every
elementary subgroup pairs with each degree-`1` character to a value in the image of `A`, then `φ`
belongs to LinearRepresentations_Serre_1977's tensor character ring `A ⊗R(G)`. -/
theorem classFunction_lifts_to_tensorCharacterRing_of_pairing_mem_range_on_elementary_linearCharacters
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
        ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈ Set.range (algebraMap A ℂ)) :
    ∃ ψ : A ⊗R(G), (ψ : G → ℂ) = φ := by
  simpa using
    classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups_local
      (A := A) φ
      (fun H hH ↦
        elementary_restriction_mem_characterRingScalarExtension_of_pairing_mem_range
          (A := A) φ hpair H hH)

/-- Companion bridge/view form of Theorem `11-11.1-4` in the realized span
`characterRingScalarExtension A G`. -/
theorem mem_characterRingScalarExtension_of_pairing_mem_range_on_elementary_linearCharacters
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
        ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈ Set.range (algebraMap A ℂ)) :
    (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
  rcases
      classFunction_lifts_to_tensorCharacterRing_of_pairing_mem_range_on_elementary_linearCharacters
        (A := A) φ hpair with
    ⟨ψ, hψ⟩
  simpa [hψ] using tensorCharacterRing_mem_characterRingScalarExtension ψ

end CharacterizationOfCharacters

end Representation

/-! ### Corollary_11_11_2_4 (from Chap11) -/
noncomputable section

universe u

namespace Representation

section FrobeniusTheorem

variable {G : Type u} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: the divisibility of the cardinality of the `n`th-power fiber over `c`.
-- * core/canonical owner: `ConjClasses.pow`, the project owner for passing to `n`th powers on
--   conjugacy classes.
-- * bridge/view: evaluate `normalizedConjugacyClassNthRootCharacterSum_isIntegral` on the trivial
--   representation, whose character identifies the source sum with that cardinality.

-- Proof sketch: apply
-- `normalizedConjugacyClassNthRootCharacterSum_isIntegral` to the trivial complex
-- representation of `G`. The resulting algebraic integer is the rational number obtained by
-- dividing the cardinality of `{x : G | x ^ n ∈ c}` by `Nat.gcd (orderOf g) n`, so it must in
-- fact be an integer; equivalently, that cardinality is divisible by `Nat.gcd (orderOf g) n`.
omit [Finite G] in
/-- Helper for Corollary 11-11.2-4: an element lands in the carrier of `c` after taking an
`n`th power exactly when its conjugacy class maps to `c` under `ConjClasses.pow`. -/
lemma pow_mem_carrier_iff_pow_mk_eq
    (n : ℕ+) (c : ConjClasses G) (x : G) :
    x ^ (n : ℕ) ∈ c.carrier ↔ ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c := by
  -- This is the direct interface translation between the source statement and the core owner.
  simp [ConjClasses.pow_mk, ConjClasses.mem_carrier_iff_mk_eq]

/-- Helper for Corollary 11-11.2-4: the `n`th-root character sum for the trivial representation
counts the elements whose `n`th-power conjugacy class is `c`. -/
lemma conjugacyClassNthRootCharacterSum_trivial_eq_card_roots
    (n : ℕ+) (c : ConjClasses G) :
    conjugacyClassNthRootCharacterSum n c (trivial ℂ G ℂ) =
      Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c} := by
  classical
  -- Rewrite the filtered character sum as a filtered cardinality.
  rw [conjugacyClassNthRootCharacterSum, Nat.card_eq_fintype_card]
  rw [Fintype.card_of_subtype
    (Finset.univ.filter fun x : G ↦ x ^ (n : ℕ) ∈ c.carrier)]
  · -- The trivial character contributes `1`, so only the root condition remains.
    simp [Representation.character, Representation.trivial, pow_mem_carrier_iff_pow_mk_eq]
  · intro x
    simp [pow_mem_carrier_iff_pow_mk_eq]

/-- Helper for Corollary 11-11.2-4: if the quotient `(m : ℂ) / d` is integral over `ℤ`, then
the denominator `d` divides `m`. -/
lemma nat_dvd_of_isIntegral_natCast_div_local {m d : ℕ} (hd : d ≠ 0)
    (h : IsIntegral ℤ ((m : ℂ) / d)) :
    d ∣ m := by
  let q : ℚ := m / d
  have hq : IsIntegral ℤ q := by
    -- Descend integrality from the complex scalar to the rational quotient itself.
    have hqC : IsIntegral ℤ (q : ℂ) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqC
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    -- Integer-valued rationals have denominator `1`.
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m d hd).mp <| by
    simpa [q] using hden

/-- Corollary 11-11.2-4: for a conjugacy class `c` and a representative `g ∈ c`, the number of
elements `x ∈ G` whose `n`th-power conjugacy class is `c` is a multiple of
`Nat.gcd (orderOf g) n`; equivalently, the number of `x` such that `x ^ n ∈ c` is such a
multiple. -/
theorem gcd_orderOf_dvd_card_nth_pow_mem_conj_class
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    Nat.gcd (orderOf (g : G)) (n : ℕ) ∣
      Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c} := by
  classical
  have hgcd_ne_zero : Nat.gcd (orderOf (g : G)) (n : ℕ) ≠ 0 := by
    exact Nat.gcd_ne_zero_right n.ne_zero
  have h_integral :
      IsIntegral ℤ
        ((Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c} : ℂ) /
          Nat.gcd (orderOf (g : G)) (n : ℕ)) := by
    -- Evaluate the source theorem on the trivial representation, so the normalized sum becomes
    -- the normalized cardinality of the `n`th-power fiber.
    simpa [div_eq_mul_inv, conjugacyClassNthRootCharacterSum_trivial_eq_card_roots,
      mul_comm, mul_left_comm, mul_assoc] using
      normalizedConjugacyClassNthRootCharacterSum_isIntegral n c g (trivial ℂ G ℂ)
  -- Clear the denominator using the standard rational-integrality criterion.
  exact nat_dvd_of_isIntegral_natCast_div_local
    (m := Nat.card {x : G // ConjClasses.pow (n : ℕ) (ConjClasses.mk x) = c})
    (d := Nat.gcd (orderOf (g : G)) (n : ℕ))
    hgcd_ne_zero h_integral

end FrobeniusTheorem

end Representation

/-! ### Corollary_11_11_2_5 (from Chap11) -/
noncomputable section

universe u

namespace Representation

section FrobeniusTheorem

open scoped Representation

variable (G : Type u) [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: `dvd_card_pow_eq_one`, matching LinearRepresentations_Serre_1977's textbook corollary.
-- * core/canonical: divisibility of the `n`th-root fiber of `1` by `Nat.gcd (Nat.card G) n`.
-- * bridge/view: specialize the core statement along `Nat.gcd_eq_right` when `n ∣ Nat.card G`.
--
-- Sampled owner declarations in this domain:
-- * `ConjClasses.indicatorClassFunctionSubmodule`
-- * `Representation.frobenius_weighted_adamsOperator_lifts_to_tensorCharacterRing`
-- * `Representation.frobenius_weighted_adamsOperator_mem_characterRingScalarExtension`
-- * `Representation.weighted_adamsOperator_conjClassIndicator_mem_characterRingScalarExtension`
--
-- Primitive data: the unit conjugacy-class indicator and the source-facing `n`th-root fiber
-- `{x : G // x ^ n = 1}`.
-- Derived API: the textbook divisibility statement under the extra hypothesis `n ∣ Nat.card G`.

/-- The weighted Adams transform of the unit conjugacy-class indicator belongs to LinearRepresentations_Serre_1977's
integral character ring `R(G)`. This owner-level character statement is the canonical Chapter 11
input for the divisibility theorems in this file. -/
theorem weighted_adamsOperator_unitClassIndicator_mem_characterRing
    (n : ℕ+) :
    (fun x ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((ConjClasses.mk (1 : G)).indicator) x)) ∈
      R(G) := by
  let η : G → ℂ := fun x ↦
    algebraMap ℤ ℂ (Ψ^n((ConjClasses.mk (1 : G)).indicator) x)
  have hη_scalar : η ∈ characterRingScalarExtension ℤ G := by
    -- Route correction: for the unit conjugacy class, the Chapter `11.11.2.2` weighted owner
    -- already collapses pointwise to the ordinary Adams transform.
    let ω : G → ℂ := fun x ↦
      algebraMap ℤ ℂ
        ((((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((ConjClasses.mk (1 : G)).indicator) x)
    have hω : ω ∈ characterRingScalarExtension ℤ G := by
      -- Important correction: Theorem 23 is not available with `(A := ℤ)`.
      -- LinearRepresentations_Serre_1977's `A` is generated by the `|G|`-th roots of unity; the weighted indicator must first
      -- be constructed over that cyclotomic coefficient ring and then descended integrally to `ℤ`.
      sorry
    have hω_eq : ω = η := by
      funext x
      by_cases hx : x ^ (n : ℕ) = 1
      · have hx_dvd : orderOf x ∣ (n : ℕ) := orderOf_dvd_of_pow_eq_one hx
        have hmem : x ^ (n : ℕ) ∈ (ConjClasses.mk (1 : G)).carrier := by
          exact ConjClasses.mem_carrier_iff_mk_eq.2 <| by
            simpa [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] using hx
        -- On the support, the Frobenius weight is `1` because `orderOf x ∣ n`.
        simp only [ω, η]
        simp [Representation.adamsOperator, ConjClasses.indicator, hmem,
          Nat.gcd_eq_left hx_dvd, Nat.div_self (orderOf_pos x)]
      · have hnotmem : x ^ (n : ℕ) ∉ (ConjClasses.mk (1 : G)).carrier := by
          intro hmem
          exact hx <| by
            simpa [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] using
              (ConjClasses.mem_carrier_iff_mk_eq.1 hmem)
        -- Off the support, both the weighted and unweighted owners vanish.
        simp only [ω, η]
        simp [Representation.adamsOperator, ConjClasses.indicator, hnotmem]
    simpa [hω_eq] using hω
  have hη_mem : η ∈ R(G) := by
    have hspan : characterRingScalarExtension ℤ G = (R(G)).toSubmodule := by
      -- Over `ℤ`, the realized scalar-extension span is exactly the integral character ring.
      rw [characterRingScalarExtension]
      exact Submodule.span_eq ((R(G)).toSubmodule : Submodule ℤ (G → ℂ))
    simpa [η, hspan] using hη_scalar
  let k : ℤ := (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ)
  let ηR : R(G) := ⟨η, hη_mem⟩
  -- The target owner is the global integer scalar multiple of the unweighted unit Adams owner.
  simpa [ηR, η, k, Pi.smul_apply, zsmul_eq_mul, mul_assoc] using
    (k • ηR).property

/-- Helper for Corollary 11-11.2-5: pairing the weighted unit-class owner with the trivial
character computes the normalized cardinality of the `n`th-root fiber of `1`. -/
lemma weighted_unit_class_pairing_eq_card_pow_eq_one_div_gcd
    (n : ℕ+) :
    ⟪
      (fun x ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
            Ψ^n((ConjClasses.mk (1 : G)).indicator) x)),
      (trivial ℂ G ℂ).character
    ⟫ =
      ((Nat.card {x : G // x ^ (n : ℕ) = 1} : ℂ) / Nat.gcd (Nat.card G) (n : ℕ)) := by
  classical
  let d : ℕ := Nat.gcd (Nat.card G) (n : ℕ)
  let m : ℕ := Nat.card {x : G // x ^ (n : ℕ) = 1}
  have hdvd : d ∣ Nat.card G := Nat.gcd_dvd_left (Nat.card G) (n : ℕ)
  have hd_ne_zero : (d : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
  have hterm :
      ∀ x : G,
        algebraMap ℤ ℂ
            ((((Nat.card G / d) : ℕ) : ℤ) *
              Ψ^n((ConjClasses.mk (1 : G)).indicator) x) =
          if x ^ (n : ℕ) = 1 then ((Nat.card G / d : ℕ) : ℂ) else 0 := by
    intro x
    -- Reduce the unit-class indicator to the concrete equation `x ^ n = 1`.
    by_cases hx : x ^ (n : ℕ) = 1
    · have hmem : x ^ (n : ℕ) ∈ (ConjClasses.mk (1 : G)).carrier := by
        exact ConjClasses.mem_carrier_iff_mk_eq.2 <| by
          simpa [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] using hx
      rw [if_pos hx, Representation.adamsOperator]
      rw [ConjClasses.indicator, Set.indicator_of_mem hmem]
      simp only [Pi.one_apply, mul_one]
      calc
        (((Nat.card G : ℤ) / d : ℤ) : ℂ) = (Nat.card G : ℂ) / d := by
          exact Int.cast_div_ofNat_charZero (k := ℂ) hdvd
        _ = ((Nat.card G / d : ℕ) : ℂ) := by
          exact (Nat.cast_div hdvd hd_ne_zero).symm
    · have hnotmem : x ^ (n : ℕ) ∉ (ConjClasses.mk (1 : G)).carrier := by
        intro hmem
        exact hx <| by
          simpa [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] using
            (ConjClasses.mem_carrier_iff_mk_eq.1 hmem)
      rw [if_neg hx, Representation.adamsOperator]
      rw [ConjClasses.indicator, Set.indicator_apply]
      simp [hnotmem]
  have hsum :
      ∑ x : G,
          algebraMap ℤ ℂ
            ((((Nat.card G / d) : ℕ) : ℤ) *
              Ψ^n((ConjClasses.mk (1 : G)).indicator) x) =
        ((Nat.card G / d : ℕ) : ℂ) * m := by
    -- After the pointwise rewrite, the sum is a constant times the root count.
    simp_rw [hterm]
    calc
      ∑ x : G, (if x ^ (n : ℕ) = 1 then ((Nat.card G / d : ℕ) : ℂ) else 0)
          = ∑ x : G, ((Nat.card G / d : ℕ) : ℂ) * (if x ^ (n : ℕ) = 1 then (1 : ℂ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              by_cases hx : x ^ (n : ℕ) = 1 <;> simp [hx]
      _ = ((Nat.card G / d : ℕ) : ℂ) *
            ∑ x : G, (if x ^ (n : ℕ) = 1 then (1 : ℂ) else 0) := by
              rw [← Finset.mul_sum]
      _ = ((Nat.card G / d : ℕ) : ℂ) * m := by
              have hroot_count :
                  ∑ x : G, (if x ^ (n : ℕ) = 1 then (1 : ℂ) else 0) = m := by
                rw [show m = (Nat.card {x : G // x ^ (n : ℕ) = 1}) by rfl]
                rw [Nat.card_eq_fintype_card]
                rw [Fintype.card_of_subtype (Finset.univ.filter fun x : G ↦ x ^ (n : ℕ) = 1)]
                · simp
                · intro x
                  simp
              rw [hroot_count]
  -- Rewrite the normalized pairing as the displayed quotient and cancel the `|G|` factor.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have htriv : ∀ x : G, (trivial ℂ G ℂ).character x⁻¹ = 1 := by
    intro x
    simp [Representation.character, Representation.trivial]
  simp_rw [htriv]
  simp only [mul_one]
  rw [hsum]
  rw [Nat.cast_div hdvd]
  field_simp [hd_ne_zero]
  · ring
  · exact hd_ne_zero

/-- Core/canonical Frobenius divisibility statement for the unit class: the number of elements
`x ∈ G` such that `x ^ n = 1` is divisible by `Nat.gcd (Nat.card G) n`. -/
theorem gcd_groupOrder_dvd_card_pow_eq_one
    (n : ℕ) :
    Nat.gcd (Nat.card G) n ∣ Nat.card {x : G // x ^ n = 1} := by
  classical
  -- Split off the degenerate `n = 0` case, where the root fiber is the whole group.
  cases n with
  | zero =>
      simp
  | succ k =>
      let npos : ℕ+ := ⟨k + 1, Nat.succ_pos _⟩
      let η : R(G) :=
        ⟨
          (fun x ↦
            algebraMap ℤ ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (npos : ℕ)) : ℕ) : ℤ) *
                Ψ^npos((ConjClasses.mk (1 : G)).indicator) x)),
          weighted_adamsOperator_unitClassIndicator_mem_characterRing G npos
        ⟩
      have hpair_integral :
          IsIntegral ℤ ⟪(η : G → ℂ), (trivial ℂ G ℂ).character⟫ := by
        -- Pairing a virtual character with a genuine character stays integral.
        simpa [η] using
          characterRing_pairing_isIntegral_with_rep_character
            (G := G) (V := ℂ) η (trivial ℂ G ℂ)
      have hpair_eq :
          ⟪(η : G → ℂ), (trivial ℂ G ℂ).character⟫ =
            ((Nat.card {x : G // x ^ Nat.succ k = 1} : ℂ) /
              Nat.gcd (Nat.card G) (Nat.succ k)) := by
        -- The owner pairing is exactly the normalized root count.
        simpa [η, npos] using
          weighted_unit_class_pairing_eq_card_pow_eq_one_div_gcd (G := G) npos
      have hgcd_ne_zero : Nat.gcd (Nat.card G) (Nat.succ k) ≠ 0 := by
        exact Nat.gcd_ne_zero_right (Nat.succ_ne_zero _)
      rw [hpair_eq] at hpair_integral
      exact nat_dvd_of_isIntegral_natCast_div
        (m := Nat.card {x : G // x ^ Nat.succ k = 1})
        (n := Nat.gcd (Nat.card G) (Nat.succ k))
        hgcd_ne_zero hpair_integral

/-- Corollary 11-11.2-5: if `n` divides the order of the finite group `G`, then the number of
elements `x ∈ G` such that `x ^ n = 1` is divisible by `n`. -/
theorem dvd_card_pow_eq_one
    (n : ℕ) (hdiv : n ∣ Nat.card G) :
    n ∣ Nat.card {x : G // x ^ n = 1} := by
  have hdiv' : n ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using hdiv
  simpa [Nat.card_eq_fintype_card, Nat.gcd_eq_right hdiv'] using
    gcd_groupOrder_dvd_card_pow_eq_one G n

end FrobeniusTheorem

end Representation
