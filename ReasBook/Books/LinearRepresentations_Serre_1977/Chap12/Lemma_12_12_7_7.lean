import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_1
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2.SeparatorSupport

noncomputable section

universe u v w

namespace Representation

section

open scoped Representation TensorProduct
open PrimeSpectrum

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K]
variable [IsDomain A] [IsFractionRing A K]

local instance instFintypeLemma121277Group : Fintype G := Fintype.ofFinite G

local notation "ΓK" => Γ[K](G)

/-- Helper for Lemma 12-12.7-7: the mixed-universe version of LinearRepresentations_Serre_1977's fixed-`p` subgroup
`V_{K,p} ≤ R_K(G)`, written directly to avoid the public notation's universe mismatch for an
intermediate field `K ⊆ L`. -/
abbrev gammaPElementaryInducedCharacterSpan_local (p : ℕ) : Submodule ℤ R[K](G) :=
  let _ : DecidablePred (fun H : Subgroup G ↦ Subgroup.IsGammaPElementary ΓK p H) :=
    Classical.decPred _
  inducedCharacterSubmoduleOverField K
    (Finset.univ.filter fun H : Subgroup G ↦ Subgroup.IsGammaPElementary ΓK p H)

/-- Helper for Lemma 12-12.7-7: the canonical realization of the mixed-universe scalar extension
`A ⊗ V_{K,p}` as a `K`-valued class function on `G`. -/
abbrev tensorGammaPElementaryInducedCharacterToFunction_local (p : ℕ) :
    TensorProduct ℤ A (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p) →ₗ[A] G → K :=
  ((((R[K](G)).toSubmodule.subtype).comp
      (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p).subtype)).liftBaseChange A

omit [IsDomain A] [IsFractionRing A K] in
/-- Lemma 12-12.7-7: there exist an element of LinearRepresentations_Serre_1977's scalar-extended owner `A ⊗ V_{K,p}` and an
`A`-valued function realizing it coefficientwise for the genuine arithmetic subgroup
`Γ_K = Γ[K](G)` attached to the intermediate field `K ⊆ L` in the cyclotomic setting, whose value
at every element of `G` is nonzero modulo every prime ideal of `A` in the canonical zero locus of
`pA`. -/
theorem
    exists_auxiliary_function_mem_gammaPImageScalarExtension_nonzero_mod_primeIdealsOverPrime
    (p : ℕ) [Fact p.Prime]
    [Finite (A ⧸ Ideal.span {(p : A)})] :
    ∃ χ : TensorProduct ℤ A
        (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p),
      ∃ φ : G → A,
      ((algebraMap A K) ∘ φ) =
        tensorGammaPElementaryInducedCharacterToFunction_local
          (K := K) (G := G) (A := A) p χ ∧
      ∀ x (P : PrimeSpectrum A), P ∈ zeroLocus (Ideal.span {(p : A)} : Set A) →
        φ x ∉ P.asIdeal := by
  classical
  obtain ⟨m, hcop, hm_mem⟩ :=
    exists_coprime_scalar_smul_mem_gammaPElementaryInducedCharacterSpan
      (G := G) (L := L) (K := K) ⟨p, Fact.out⟩
  have hmem :
      m • (1 : R[K](G)) ∈
        gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p := by
    simpa using hm_mem (1 : R[K](G))
  let χ :
      TensorProduct ℤ A (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p) :=
    (1 : A) ⊗ₜ[ℤ]
      (⟨m • (1 : R[K](G)), hmem⟩ :
        gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p)
  let φ : G → A := fun _ ↦ (m : A)
  refine ⟨χ, φ, ?_, ?_⟩
  · ext x
    simpa [χ, φ, tensorGammaPElementaryInducedCharacterToFunction_local] using
      congrFun
        (LinearMap.liftBaseChange_one_tmul (A := A)
          ((((R[K](G)).toSubmodule.subtype).comp
            (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p).subtype))
          (⟨m • (1 : R[K](G)), hmem⟩ :
            gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p)) x
  · intro x P hP
    have hPspan : Ideal.span {(p : A)} ≤ P.asIdeal := by
      simpa [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hP
    simpa [φ] using
      nat_cast_not_mem_primeIdealOverPrime_of_coprime (A := A) p m hcop P hPspan

end

end Representation
