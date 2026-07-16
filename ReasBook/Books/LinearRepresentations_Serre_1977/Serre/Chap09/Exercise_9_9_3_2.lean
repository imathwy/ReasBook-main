import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_3_1
import LinearRepresentations_Serre_1977.Serre.Chap09.Theorem_9_9_2_1
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1

open scoped BigOperators Pointwise Representation SubgroupInduction TensorProduct

noncomputable section

namespace Subgroup

section

variable {G : Type} [Group G] [Finite G]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- A finite group carries the canonical `Fintype` structure used throughout the tensor
presentation. -/
local instance instFintypeExercise9932 : Fintype G :=
  Fintype.ofFinite G

/-- Subgroups of a finite group are finite. -/
local instance instFintypeSubgroupExercise9932 (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- The source of Exercise 9-9.3-2 is the family of rationalized character rings indexed by `X`.
-/
abbrev artinCharacterPresentationSource (X : Finset (Subgroup G)) :=
  (H : X) → ℚ ⊗[ℤ] R(H.1)

/-- Helper for Exercise 9-9.3-2: realize `ℚ ⊗ R(H)` as the corresponding scalar-extended
character subspace on `H`. -/
abbrev tensorCharacterRealization (H : Type) [Group H] [Finite H] :
    ℚ ⊗[ℤ] R(H) ≃ₗ[ℚ] Representation.characterRingScalarExtension ℚ H :=
  (R(H)).toSubmodule.tensorEquivSpan ℚ

/-- Helper for Exercise 9-9.3-2: a local tensor character yields a bundled class function. -/
def tensorCharacterToClassFunction (H : Type) [Group H] [Finite H] :
    ℚ ⊗[ℤ] R(H) →ₗ[ℚ] classFunctionSubspace H :=
  { toFun := fun χ =>
      ⟨((tensorCharacterRealization H χ : Representation.characterRingScalarExtension ℚ H) :
          H → ℂ),
        (mem_classFunctionSubspace_iff _).2 <|
          Representation.isClassFunction_of_mem_characterRingScalarExtension
            ((tensorCharacterRealization H χ).2)⟩
    map_add' := by
      intro χ ψ
      ext h
      simp [tensorCharacterRealization]
    map_smul' := by
      intro a χ
      ext h
      simp [tensorCharacterRealization] }

/-- Helper for Exercise 9-9.3-2: evaluating the bundled realization recovers the underlying
complex-valued tensor character. -/
@[simp] theorem tensorCharacterToClassFunction_apply
    (H : Type) [Group H] [Finite H] (χ : ℚ ⊗[ℤ] R(H)) (h : H) :
    (tensorCharacterToClassFunction H χ : H → ℂ) h =
      ((tensorCharacterRealization H χ :
        Representation.characterRingScalarExtension ℚ H) : H → ℂ) h :=
  rfl

/-- Helper for Exercise 9-9.3-2: the bundled realization is injective. -/
theorem tensorCharacterToClassFunction_injective
    (H : Type) [Group H] [Finite H] :
    Function.Injective (tensorCharacterToClassFunction H) := by
  intro χ ψ hχψ
  apply (tensorCharacterRealization H).injective
  ext h
  simpa [tensorCharacterToClassFunction_apply] using
    congrArg (fun f : classFunctionSubspace H ↦ (f : H → ℂ) h) hχψ

/-- Helper for Exercise 9-9.3-2: realize each tensor-character coordinate as a class-function
coordinate in the source of Exercise `9-9.3-1`. -/
def artinCharacterSourceToInductionSource (X : Finset (Subgroup G)) :
    artinCharacterPresentationSource X →ₗ[ℚ] artinInductionSource X where
  toFun ξ := fun H ↦ tensorCharacterToClassFunction H.1 (ξ H)
  map_add' := by
    intro ξ η
    ext H h
    simp [tensorCharacterToClassFunction]
  map_smul' := by
    intro a ξ
    ext H h
    simp [tensorCharacterToClassFunction]

/-- Helper for Exercise 9-9.3-2: the Artin induction sum of a tensor family always lands in the
global scalar-extended character ring. -/
theorem artinCharacterInduction_mem_characterRingScalarExtension
    (X : Finset (Subgroup G)) (ξ : artinCharacterPresentationSource X) :
    (artinInductionMap X (artinCharacterSourceToInductionSource X ξ) : G → ℂ) ∈
      Representation.characterRingScalarExtension ℚ G := by
  -- Each summand comes from inducing a local scalar-extended character, so the whole finite sum
  -- stays inside the global scalar extension.
  have hsum :
      ((artinInductionMap X (artinCharacterSourceToInductionSource X ξ) :
          classFunctionSubspace G) : G → ℂ) =
        ∑ H : X, Ind[H.1]((artinCharacterSourceToInductionSource X ξ H : H.1 → ℂ)) := by
    ext g
    simp [artinInductionMap_apply]
  rw [hsum]
  refine Submodule.sum_mem _ ?_
  intro H hH
  simpa [tensorCharacterToClassFunction_apply] using
    (Representation.induced_mem_characterRingScalarExtension_of_mem (A := ℚ) H.1
      ((tensorCharacterRealization H.1 (ξ H)).2))

/-- Helper for Exercise 9-9.3-2: the total tensor-character presentation map is the transported
Artin-induction map from Exercise `9-9.3-1`. -/
def artinCharacterPresentationMap (X : Finset (Subgroup G)) :
    artinCharacterPresentationSource X →ₗ[ℚ] ℚ ⊗[ℤ] R(G) :=
  ((tensorCharacterRealization G).symm.toLinearMap).comp <|
    LinearMap.codRestrict (Representation.characterRingScalarExtension ℚ G)
      ((((classFunctionSubspace G).subtype.restrictScalars ℚ).comp (artinInductionMap X)).comp
        (artinCharacterSourceToInductionSource X))
      (artinCharacterInduction_mem_characterRingScalarExtension X)

/-- Helper for Exercise 9-9.3-2: realizing the total tensor-character presentation map recovers
the Artin-induction map on the transported class-function source. -/
@[simp] theorem tensorCharacterToClassFunction_artinCharacterPresentationMap
    (X : Finset (Subgroup G)) (ξ : artinCharacterPresentationSource X) :
    tensorCharacterToClassFunction G (artinCharacterPresentationMap X ξ) =
      artinInductionMap X (artinCharacterSourceToInductionSource X ξ) := by
  ext g
  simp [artinCharacterPresentationMap, tensorCharacterToClassFunction]

/-- Helper for Exercise 9-9.3-2: the relation submodule is the pullback of the Artin-induction
relations from Exercise `9-9.3-1` along the coordinatewise tensor realization. -/
def artinCharacterPresentationRelations (X : Finset (Subgroup G)) :
    Submodule ℚ (artinCharacterPresentationSource X) :=
  Submodule.comap (artinCharacterSourceToInductionSource X) (artinInductionRelations X)

/-- Helper for Exercise 9-9.3-2: the transported tensor relations are exactly the kernel of the
total tensor presentation map. -/
theorem artinCharacterPresentationRelations_eq_ker
    (X : Finset (Subgroup G))
    (hsubgroups : ∀ {H H' : Subgroup G}, H ∈ X → H' ≤ H → H' ∈ X)
    (hconj : ∀ {H : Subgroup G}, H ∈ X → ∀ s : G, (s •ᶜ H) ∈ X)
    (hcover : is_conjugacy_cover X) :
    (artinCharacterPresentationMap X).ker = artinCharacterPresentationRelations X := by
  ext ξ
  constructor
  · intro hξ
    change artinCharacterSourceToInductionSource X ξ ∈ artinInductionRelations X
    have hzero :
        artinInductionMap X (artinCharacterSourceToInductionSource X ξ) = 0 := by
      have hmap := congrArg (tensorCharacterToClassFunction G) hξ
      simpa using hmap
    have hker :
        artinCharacterSourceToInductionSource X ξ ∈ (artinInductionMap X).ker := by
      simpa [LinearMap.mem_ker] using hzero
    simpa [artinInductionMap_ker_eq_artinInductionRelations X hsubgroups hconj hcover,
      artinCharacterPresentationRelations]
      using hker
  · intro hξ
    have hker :
        artinCharacterSourceToInductionSource X ξ ∈ (artinInductionMap X).ker := by
      simpa [artinInductionMap_ker_eq_artinInductionRelations X hsubgroups hconj hcover,
        artinCharacterPresentationRelations]
        using hξ
    have hzero :
        artinInductionMap X (artinCharacterSourceToInductionSource X ξ) = 0 := by
      simpa [LinearMap.mem_ker] using hker
    apply (tensorCharacterToClassFunction_injective G)
    simpa using hzero

/-- Exercise 9-9.3-2: the kernel of the tensor-character presentation map is contained in the
transported Artin relations. -/
theorem artinCharacterPresentationMap_ker_le_artinCharacterPresentationRelations
    (X : Finset (Subgroup G))
    (hsubgroups : ∀ {H H' : Subgroup G}, H ∈ X → H' ≤ H → H' ∈ X)
    (hconj : ∀ {H : Subgroup G}, H ∈ X → ∀ s : G, (s •ᶜ H) ∈ X)
    (hcover : is_conjugacy_cover X) :
    (artinCharacterPresentationMap X).ker ≤ artinCharacterPresentationRelations X := by
  exact le_of_eq
    (artinCharacterPresentationRelations_eq_ker X hsubgroups hconj hcover)

/-- Helper for Exercise 9-9.3-2: the total tensor-character presentation map is surjective under
the conjugacy-cover hypothesis. -/
theorem artinCharacterPresentationMap_surjective
    (X : Finset (Subgroup G)) (hcover : is_conjugacy_cover X) :
    Function.Surjective (artinCharacterPresentationMap X) := by
  intro χ
  have hχmem :
      ((χ : ℚ ⊗[ℤ] R(G)) : G → ℂ) ∈ Representation.artinInducedCharacterSpan (G := G) X := by
    have hspan :
        Representation.characterRingScalarExtension ℚ G =
          Representation.artinInducedCharacterSpan (G := G) X :=
      (is_conjugacy_cover_iff_characterRingScalarExtension_eq_span_induced
        (G := G) X).1 hcover
    simpa [hspan] using ((tensorCharacterRealization G χ).2 :
      (χ : G → ℂ) ∈ Representation.characterRingScalarExtension ℚ G)
  rcases
      Representation.exists_multiple_eq_sum_characterRingInduction_of_mem_artinInducedCharacterSpan
        hχmem with
    ⟨d, ξ, hξ⟩
  let η : artinCharacterPresentationSource X := fun H ↦ ((d : ℚ)⁻¹) ⊗ₜ[ℤ] ξ H
  refine ⟨η, ?_⟩
  apply (tensorCharacterToClassFunction_injective G)
  ext g
  have hd_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast d.ne_zero
  have hξg :
      ∑ H : X, Ind[H.1]((ξ H : H.1 → ℂ)) g =
        (d : ℂ) * (χ : G → ℂ) g := by
    simpa [Subgroup.characterRingInduction_apply, smul_eq_mul] using (congrFun hξ g).symm
  calc
    (tensorCharacterToClassFunction G (artinCharacterPresentationMap X η) : G → ℂ) g
        = ∑ H : X, Ind[H.1]((artinCharacterSourceToInductionSource X η H : H.1 → ℂ)) g := by
            simp [artinInductionMap_apply]
    _ = ∑ H : X, (d : ℂ)⁻¹ * Ind[H.1]((ξ H : H.1 → ℂ)) g := by
          refine Finset.sum_congr rfl ?_
          intro H hH
          have hterm :
              (artinCharacterSourceToInductionSource X η H : H.1 → ℂ) =
                (d : ℂ)⁻¹ • (ξ H : H.1 → ℂ) := by
            ext x
            have htmul :
                (((tensorCharacterRealization H.1) (((d : ℚ)⁻¹) ⊗ₜ[ℤ] ξ H) :
                    Representation.characterRingScalarExtension ℚ H.1) : H.1 → ℂ) =
                  ((d : ℚ)⁻¹) • (ξ H : H.1 → ℂ) := by
              simpa [tensorCharacterRealization] using
                (Submodule.tensorEquivSpan_apply_tmul (A := ℚ)
                  (p := Subalgebra.toSubmodule R[ℂ](H.1)) ((d : ℚ)⁻¹) (ξ H))
            simpa [artinCharacterSourceToInductionSource, η, tensorCharacterToClassFunction,
              Algebra.smul_def] using
              congrArg (fun f : H.1 → ℂ => f x) htmul
          rw [hterm, Subgroup.inducedClassFunction_map_smul]
          simp [smul_eq_mul]
    _ = (d : ℂ)⁻¹ * ∑ H : X, Ind[H.1]((ξ H : H.1 → ℂ)) g := by
          simp [Finset.mul_sum]
    _ = (d : ℂ)⁻¹ * ((d : ℂ) * (χ : G → ℂ) g) := by rw [hξg]
    _ = (χ : G → ℂ) g := by
          rw [← mul_assoc, inv_mul_cancel₀ hd_ne, one_mul]

/-- Helper for Exercise 9-9.3-2: quotienting the subgroup-indexed tensor-character source by the
transported Artin relations presents the rationalized character ring `ℚ ⊗ R(G)`. -/
def artinPresentationTensorCharacterRing
    (X : Finset (Subgroup G))
    (hsubgroups : ∀ {H H' : Subgroup G}, H ∈ X → H' ≤ H → H' ∈ X)
    (hconj : ∀ {H : Subgroup G}, H ∈ X → ∀ s : G, (s •ᶜ H) ∈ X)
    (hcover : is_conjugacy_cover X) :
    (artinCharacterPresentationSource X ⧸ artinCharacterPresentationRelations X) ≃ₗ[ℚ]
      ℚ ⊗[ℤ] R(G) := by
  exact
    (Submodule.quotEquivOfEq (artinCharacterPresentationRelations X)
      ((artinCharacterPresentationMap X).ker)
      (artinCharacterPresentationRelations_eq_ker X hsubgroups hconj hcover).symm).trans <|
      LinearMap.quotKerEquivOfSurjective _ (artinCharacterPresentationMap_surjective X hcover)

/-- Helper for Exercise 9-9.3-2: the quotient presentation sends a source class to the induced
tensor character represented by that family. -/
@[simp] theorem artinPresentationTensorCharacterRing_apply_mk
    (X : Finset (Subgroup G))
    (hsubgroups : ∀ {H H' : Subgroup G}, H ∈ X → H' ≤ H → H' ∈ X)
    (hconj : ∀ {H : Subgroup G}, H ∈ X → ∀ s : G, (s •ᶜ H) ∈ X)
    (hcover : is_conjugacy_cover X)
    (ξ : artinCharacterPresentationSource X) :
    artinPresentationTensorCharacterRing X hsubgroups hconj hcover (Submodule.Quotient.mk ξ) =
      artinCharacterPresentationMap X ξ := by
  simp [artinPresentationTensorCharacterRing, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Helper for Exercise 9-9.3-2: in realized form, the same quotient presents
`Representation.characterRingScalarExtension ℚ G`. -/
def artinPresentationCharacterRingScalarExtension
    (X : Finset (Subgroup G))
    (hsubgroups : ∀ {H H' : Subgroup G}, H ∈ X → H' ≤ H → H' ∈ X)
    (hconj : ∀ {H : Subgroup G}, H ∈ X → ∀ s : G, (s •ᶜ H) ∈ X)
    (hcover : is_conjugacy_cover X) :
    (artinCharacterPresentationSource X ⧸ artinCharacterPresentationRelations X) ≃ₗ[ℚ]
      Representation.characterRingScalarExtension ℚ G := by
  exact
    (artinPresentationTensorCharacterRing X hsubgroups hconj hcover).trans
      (tensorCharacterRealization G)

/-- Helper for Exercise 9-9.3-2: in the realized presentation, a source class maps to the
corresponding point of `Representation.characterRingScalarExtension ℚ G`. -/
@[simp] theorem artinPresentationCharacterRingScalarExtension_apply_mk
    (X : Finset (Subgroup G))
    (hsubgroups : ∀ {H H' : Subgroup G}, H ∈ X → H' ≤ H → H' ∈ X)
    (hconj : ∀ {H : Subgroup G}, H ∈ X → ∀ s : G, (s •ᶜ H) ∈ X)
    (hcover : is_conjugacy_cover X)
    (ξ : artinCharacterPresentationSource X) :
    artinPresentationCharacterRingScalarExtension X hsubgroups hconj hcover
        (Submodule.Quotient.mk ξ) =
      tensorCharacterRealization G (artinCharacterPresentationMap X ξ) := by
  simp [artinPresentationCharacterRingScalarExtension,
    artinPresentationTensorCharacterRing_apply_mk]

end

end Subgroup
