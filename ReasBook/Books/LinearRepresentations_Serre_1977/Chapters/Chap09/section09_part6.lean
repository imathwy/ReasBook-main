import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_9_9_3_2 (from Chap09) -/
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

/-! ### Exercise_9_9_4_3 (from Chap09) -/
open scoped BigOperators Representation SubgroupInduction
open Representation

noncomputable section

namespace Subgroup

section

variable {G : Type} [Group G] [Finite G]

/-- Helper for Exercise 9-9.4-3: the finite family of cyclic subgroups of a finite group. -/
abbrev cyclicSubgroups (G : Type) [Group G] [Finite G] : Finset (Subgroup G) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  exact Finset.univ.filter fun H : Subgroup G ↦ IsCyclic H

/-- Helper for Exercise 9-9.4-3: membership in `cyclicSubgroups G` is exactly cyclicity. -/
@[simp] theorem mem_cyclicSubgroups {H : Subgroup G} :
    H ∈ cyclicSubgroups G ↔ IsCyclic H := by
  classical
  simp [cyclicSubgroups]

end

end Subgroup

namespace Representation

section

variable {K : Type} [Zero K] [NatCast K]
variable (A : Type) [Group A] [Finite A]

open Classical in
/-- Helper for Exercise 9-9.4-3: LinearRepresentations_Serre_1977's auxiliary function `θ_A`, supported on the generators of
`A` and equal to `|A|` on each generator. -/
def cyclicGroupTheta : A → K :=
  fun a ↦ if Subgroup.zpowers a = (⊤ : Subgroup A) then Nat.card A else 0

scoped[Representation] notation:max "θ[" A "]" => cyclicGroupTheta A

end

end Representation

section

variable {G : Type} [Group G]

/-- Helper for Exercise 9-9.4-3: an element of a subgroup generates that subgroup internally
exactly when its ambient cyclic subgroup is the whole subgroup. -/
lemma subgroup_zpowers_eq_top_iff (H : Subgroup G) (a : H) :
    Subgroup.zpowers a = ⊤ ↔ Subgroup.zpowers (a : G) = H := by
  -- Map the internal cyclic subgroup along the subtype map to compare it with the ambient one.
  rw [← Subgroup.map_subtype_inj]
  rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, H.range_subtype]
  simp

end

section

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Semifield K]

attribute [local instance] Fintype.ofFinite

/-- Helper for Exercise 9-9.4-3: the induction scalar attached to `orderOf x` is absorbed by
`|G|`. -/
lemma natCard_mul_inv_orderOf_mul_orderOf (x : G) :
    (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) = (Nat.card G : K) := by
  -- Rewrite `|G|` as a multiple of `orderOf x`, then split according to whether that cast
  -- vanishes in `K`.
  obtain ⟨m, hm⟩ := orderOf_dvd_natCard x
  have hcard : (Nat.card G : K) = (orderOf x : K) * (m : K) := by
    simpa [Nat.cast_mul] using congrArg (fun n : ℕ => (n : K)) hm
  by_cases hx : (orderOf x : K) = 0
  · rw [hcard]
    simp [hx]
  · calc
      (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K))
          = ((orderOf x : K) * (m : K)) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
              rw [hcard]
      _ = ((orderOf x : K) * (orderOf x : K)⁻¹) * ((m : K) * (orderOf x : K)) := by
            ac_rfl
      _ = (m : K) * (orderOf x : K) := by
            simp [hx]
      _ = (orderOf x : K) * (m : K) := by
            ac_rfl
      _ = (Nat.card G : K) := by
            rw [hcard]

/-- Helper for Exercise 9-9.4-3: the cyclic-subgroup sum of the auxiliary functions `θ[H]`
recovers the constant function with value `|G|`. -/
theorem sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one :
    ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) = (Nat.card G : K) • (1 : G → K) := by
  classical
  ext x
  simp [Pi.smul_apply, Nat.card_eq_fintype_card]
  let F : Subgroup G → G → K := fun H y ↦
    if Subgroup.zpowers (y⁻¹ * x * y) = H then ((Nat.card H : K)⁻¹ * (Nat.card H : K)) else 0
  have hInd (H : Subgroup G) : Ind[H](θ[H]) x = ∑ y : G, F H y := by
    -- Unfold the induced class function and rewrite the `θ[H]` value using whether the conjugate
    -- generates `H`.
    change ((Nat.card H : K)⁻¹) *
        Finset.univ.sum (fun y : G =>
          if hy : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy⟩ else 0) = _
    rw [Finset.mul_sum]
    change Finset.univ.sum (fun y : G =>
        ((Nat.card H : K)⁻¹) *
          (if hy : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy⟩ else 0)) = _
    refine Finset.sum_congr rfl ?_
    intro y hyuniv
    by_cases hgen : Subgroup.zpowers (y⁻¹ * x * y) = H
    · have hy : y⁻¹ * x * y ∈ H := by
        rw [← hgen]
        exact Subgroup.mem_zpowers _
      have hleft :
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
            = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := by
        simp [hy]
      have htheta : (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = (Nat.card H : K) := by
        simp [Representation.cyclicGroupTheta, subgroup_zpowers_eq_top_iff, hgen]
      calc
        ((Nat.card H : K)⁻¹) *
            (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
            = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := hleft
        _ = ((Nat.card H : K)⁻¹) * (Nat.card H : K) := by
              exact congrArg (fun z : K => ((Nat.card H : K)⁻¹) * z) htheta
        _ = F H y := by
              dsimp [F]
              rw [if_pos hgen]
    · by_cases hy : y⁻¹ * x * y ∈ H
      · have hleft :
            ((Nat.card H : K)⁻¹) *
                (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
              = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := by
          simp [hy]
        have htheta : (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = 0 := by
          simp [Representation.cyclicGroupTheta, subgroup_zpowers_eq_top_iff, hgen]
        have hmul : ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = 0 := by
          simpa using congrArg (fun z : K => ((Nat.card H : K)⁻¹) * z) htheta
        calc
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
              = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := hleft
          _ = 0 := hmul
          _ = F H y := by
                dsimp [F]
                rw [if_neg hgen]
      · have hleft :
            ((Nat.card H : K)⁻¹) *
                (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0) = 0 := by
          simp [hy]
        calc
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0) = 0 := hleft
          _ = F H y := by
                dsimp [F]
                rw [if_neg hgen]
  have hCollapse (a : G) :
      ((Subgroup.cyclicSubgroups G).sum fun H ↦ F H a) =
        ((Nat.card (Subgroup.zpowers (a⁻¹ * x * a)) : K)⁻¹ *
          (Nat.card (Subgroup.zpowers (a⁻¹ * x * a)) : K)) := by
    -- Only the subgroup generated by `a⁻¹ * x * a` contributes to the subgroup sum.
    have ha : Subgroup.zpowers (a⁻¹ * x * a) ∈ Subgroup.cyclicSubgroups G := by
      simpa using (Subgroup.mem_cyclicSubgroups :
        Subgroup.zpowers (a⁻¹ * x * a) ∈ Subgroup.cyclicSubgroups G ↔
          IsCyclic (Subgroup.zpowers (a⁻¹ * x * a))).2 inferInstance
    dsimp [F]
    rw [Finset.sum_eq_single (Subgroup.zpowers (a⁻¹ * x * a))]
    · simp
    · intro H hH hne
      have hne' : Subgroup.zpowers (a⁻¹ * x * a) ≠ H := by
        simpa [eq_comm] using hne
      simp [hne']
    · intro hnot
      exact False.elim (hnot ha)
  -- Swap the subgroup sum with the ambient group sum and collapse the unique contributing term.
  calc
    ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) x
        = (Subgroup.cyclicSubgroups G).sum fun H ↦ ∑ y : G, F H y := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            exact hInd H
    _ = (Subgroup.cyclicSubgroups G).sum fun H ↦ Finset.univ.sum (F H) := by
          rfl
    _ = Finset.univ.sum fun y : G ↦ (Subgroup.cyclicSubgroups G).sum fun H ↦ F H y := by
          rw [Finset.sum_comm]
    _ = ∑ y : G,
          ((Nat.card (Subgroup.zpowers (y⁻¹ * x * y)) : K)⁻¹ *
            (Nat.card (Subgroup.zpowers (y⁻¹ * x * y)) : K)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simpa using hCollapse y
    _ = ∑ y : G, (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Nat.card_zpowers]
          have horder : orderOf (y⁻¹ * x * y) = orderOf x := by
            simpa using ((SemiconjBy.conj_mk y⁻¹ x).orderOf_eq y⁻¹).symm
          rw [horder]
    _ = (Fintype.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          simp
    _ = (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          rw [Nat.card_eq_fintype_card]
    _ = (Nat.card G : K) := by
          simpa using natCard_mul_inv_orderOf_mul_orderOf (K := K) x
    _ = (Fintype.card G : K) := by
          rw [Nat.card_eq_fintype_card]

end

namespace Representation

section

variable (A : Type) [Group A] [Finite A]

attribute [local instance] Fintype.ofFinite

/-- Helper for Exercise 9-9.4-3: a proper subgroup of a finite group has strictly smaller
cardinality. -/
private lemma subgroup_natCard_lt_of_ne_top {B : Type} [Group B] [Finite B] (H : Subgroup B)
    (hH : H ≠ ⊤) : Nat.card H < Nat.card B := by
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype H := Fintype.ofFinite H
  -- A proper subgroup omits some ambient element, so the inclusion on carriers is not surjective.
  have hex : ∃ x : B, x ∉ H := by
    by_cases hforall : ∀ x : B, x ∈ H
    · exact False.elim (hH (by
        ext x
        simp [hforall x]))
    · exact not_forall.mp hforall
  rcases hex with ⟨x, hx⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using (Fintype.card_subtype_lt (p := fun y : B ↦ y ∈ H) hx)

/-- Helper for Exercise 9-9.4-3: on the top subgroup, the subgroup version of `θ` agrees with
the ambient one after forgetting the trivial membership proof. -/
private lemma top_cyclicGroupTheta_eq {B : Type} [Group B] [Finite B] :
    (fun g : B ↦ ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩)) =
      (θ[B] : B → ℂ) := by
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype (⊤ : Subgroup B) := Fintype.ofFinite _
  ext g
  have hsub :
      Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup B)) = ⊤ ↔
        Subgroup.zpowers g = (⊤ : Subgroup B) := by
    -- Compare the internal cyclic subgroup with its image in the ambient group.
    rw [← Subgroup.map_subtype_inj]
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, (⊤ : Subgroup B).range_subtype]
    simp
  by_cases hg : Subgroup.zpowers g = (⊤ : Subgroup B)
  · have hg' : Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup B)) = ⊤ := hsub.mpr hg
    simp [Representation.cyclicGroupTheta, hg, hg', Nat.card_eq_fintype_card]
  · have hg' : Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup B)) ≠ ⊤ := by
      intro h
      exact hg (hsub.mp h)
    simp [Representation.cyclicGroupTheta, hg, hg']

/-- Helper for Exercise 9-9.4-3: in a finite commutative group, the `H = ⊤` summand in LinearRepresentations_Serre_1977's
induction formula is exactly the original auxiliary function `θ`. -/
private lemma top_induced_cyclicGroupTheta_eq {B : Type} [CommGroup B] [Finite B] :
    Ind[(⊤ : Subgroup B)]((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ)) = (θ[B] : B → ℂ) := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  have hcardF : (Fintype.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard : (Nat.card B : ℂ) ≠ 0 := by
    simpa [Nat.card_eq_fintype_card] using hcardF
  ext g
  -- In a commutative group every conjugate of `g` is `g`, so the induction sum is constant.
  calc
    Ind[(⊤ : Subgroup B)]((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ)) g
        = ((Nat.card (⊤ : Subgroup B) : ℂ)⁻¹) *
            ∑ s : B,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup B) then
                ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            rfl
    _ = (Nat.card B : ℂ)⁻¹ *
            ∑ s : B,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup B) then
                ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            simp [Nat.card_eq_fintype_card]
    _ = (Nat.card B : ℂ)⁻¹ *
            ∑ _s : B, ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩) := by
            refine congrArg ((Nat.card B : ℂ)⁻¹ * ·) ?_
            refine Fintype.sum_congr
              (fun s : B ↦
                if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup B) then
                  ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
                else 0)
              (fun _s : B ↦ ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩))
              ?_
            intro s
            have hs : s⁻¹ * g * s = g := by
              calc
                s⁻¹ * g * s = s⁻¹ * s * g := by
                  ac_rfl
                _ = g := by
                  simp
            have hsub :
                (⟨s⁻¹ * g * s, by simp⟩ : (⊤ : Subgroup B)) = ⟨g, by simp⟩ := by
              apply Subtype.ext
              simp [hs]
            simp [hs, hsub]
    _ = (Nat.card B : ℂ)⁻¹ *
          ((Nat.card B : ℂ) * ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩)) := by
          simp [Finset.sum_const, Nat.card_eq_fintype_card, nsmul_eq_mul]
    _ = (((Nat.card B : ℂ)⁻¹ * (Nat.card B : ℂ)) *
          ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩)) := by
          rw [mul_assoc]
    _ = ((θ[(⊤ : Subgroup B)] : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩) := by
          rw [inv_mul_cancel₀ hcard, one_mul]
    _ = (θ[B] : B → ℂ) g := by
          simpa using congrFun (top_cyclicGroupTheta_eq (B := B)) g

/-- Helper for Exercise 9-9.4-3: if `A` is cyclic, then LinearRepresentations_Serre_1977's auxiliary function `θ[A]`
belongs to the character ring `R(A)`. -/
theorem cyclicGroupTheta_mem_characterRing [IsCyclic A] :
    θ[A] ∈ R(A) := by
  classical
  let _ : CommGroup A := IsCyclic.commGroup
  let P : ℕ → Prop := fun n ↦
    ∀ (G : Type) (_ : Group G) (_ : Finite G) (_ : IsCyclic G),
      Nat.card G = n → θ[G] ∈ R(G)
  have hstrong : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    intro G _ _ _ hGcard
    let _ : CommGroup G := IsCyclic.commGroup
    let _ : Fintype G := Fintype.ofFinite G
    let S : Finset (Subgroup G) := Subgroup.cyclicSubgroups G
    have htop : (⊤ : Subgroup G) ∈ S := by
      simpa [S] using (Subgroup.mem_cyclicSubgroups.2 inferInstance :
        (⊤ : Subgroup G) ∈ Subgroup.cyclicSubgroups G)
    -- Split the cyclic-subgroup sum into the top subgroup and the proper cyclic subgroups.
    have hsplit :
        Finset.sum S (fun H ↦ Ind[H]((θ[H] : H → ℂ))) =
          Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ)) +
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) := by
      rw [← Finset.insert_erase htop]
      simp
    have hsum :
        Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ)) +
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) =
          (Nat.card G : ℂ) • (1 : G → ℂ) := by
      exact hsplit.symm.trans (sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ))
    -- The proper subgroup terms lie in `R(G)` by strong induction and induction on character
    -- rings over `ℂ`.
    have hproper :
        Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) ∈ R(G) := by
      refine (R(G)).sum_mem ?_
      intro H hH
      have hHne : H ≠ ⊤ := (Finset.mem_erase.mp hH).1
      have hthetaH : θ[H] ∈ R(H) := by
        have hlt : Nat.card H < n := by
          rw [← hGcard]
          exact subgroup_natCard_lt_of_ne_top H hHne
        simpa using ih (Nat.card H) hlt H inferInstance inferInstance inferInstance rfl
      exact Subgroup.inducedClassFunction_mem_characterRingOverField (K := ℂ) H ⟨(θ[H] : H → ℂ), hthetaH⟩
    -- The constant term is an integral multiple of the trivial character, hence lies in `R(G)`.
    have hconst : (Nat.card G : ℂ) • (1 : G → ℂ) ∈ R(G) := by
      convert ((((Fintype.card G : ℤ) • (1 : R(G))) : R(G)) : R(G)).property using 1
      ext g
      simp [Nat.card_eq_fintype_card, zsmul_eq_mul]
    -- Route correction: rewrite the cyclic-subgroup identity as
    -- `θ[G] = |G| • 1 - (proper subgroup sum)` and then use closure of `R(G)` under subtraction.
    have htheta_eq :
        (θ[G] : G → ℂ) =
          (Nat.card G : ℂ) • (1 : G → ℂ) -
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) := by
      rw [← top_induced_cyclicGroupTheta_eq (B := G)]
      exact eq_sub_iff_add_eq.2 hsum
    exact htheta_eq.symm ▸ (R(G)).sub_mem hconst hproper
  have hA : P (Nat.card A) := hstrong (Nat.card A)
  simpa using hA A inferInstance inferInstance inferInstance rfl

/-- LinearRepresentations_Serre_1977's auxiliary character candidate `λ_A = φ(|A|) r_A - θ_A` on a finite group `A`. -/
def cyclicGroupLambda : A → ℂ :=
  ((Nat.totient (Nat.card A) : ℂ)) • (leftRegular ℂ A).character - θ[A]

scoped[Representation] notation:max "λ[" A "]" => cyclicGroupLambda A

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's auxiliary class function `λ[A]`.
-- * core/canonical: the integral character ring owner `R(A)`.
-- * bridge/view: realization of `λ[A]` as an actual finite-dimensional character in `FDRep ℂ A`
--   and its induced sum over cyclic subgroups.

/-- Helper for Exercise 9-9.4-3: the pairing is additive across a finite sum in its left
argument. -/
private lemma groupFunctionPairing_finset_sum_left {ι : Type*} (s : Finset ι) (f : ι → A → ℂ)
    (ψ : A → ℂ) :
    Representation.groupFunctionPairingOverField ℂ (Finset.sum s fun i ↦ f i) ψ =
      Finset.sum s fun i ↦ Representation.groupFunctionPairingOverField ℂ (f i) ψ := by
  classical
  -- Peel off one summand at a time and use additivity of the pairing on the left.
  refine Finset.induction_on s ?_ ?_
  · simp [Representation.groupFunctionPairingOverField]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Representation.groupFunctionPairing_add_left, ih]

/-- Helper for Exercise 9-9.4-3: the trivial class function has self-pairing `1`. -/
private lemma groupFunctionPairing_one_one_eq_one :
    ⟪(1 : A → ℂ), (1 : A → ℂ)⟫ = 1 := by
  -- Rewrite the pairing as the average of the constant function `1`.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  simp [Nat.card_eq_fintype_card]

/-- Helper for Exercise 9-9.4-3: the regular character has pairing `1` with the unit character. -/
private lemma leftRegular_character_pairing_one_eq_one :
    ⟪((leftRegular ℂ A).character : A → ℂ), (1 : A → ℂ)⟫ = 1 := by
  -- Only the identity contributes to the regular-character average.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  simp only [Pi.one_apply, mul_one]
  calc
    (Nat.card A : ℂ)⁻¹ * ∑ t : A, (leftRegular ℂ A).character t
        = (Nat.card A : ℂ)⁻¹ * (Nat.card A : ℂ) := by
            rw [Finset.sum_eq_single 1]
            · simp [Representation.leftRegular_character_one]
            · intro t _ hne
              have hne' : t ≠ 1 := by
                simpa using hne
              simp [Representation.leftRegular_character_eq_zero_of_ne_one hne']
            · simp
    _ = 1 := by
          field_simp [Nat.cast_ne_zero]

/-- Helper for Exercise 9-9.4-3: in a finite cyclic group, generating the whole group is
equivalent to having order `|A|`. -/
private lemma zpowers_eq_top_iff_orderOf_eq_natCard [IsCyclic A] (a : A) :
    Subgroup.zpowers a = (⊤ : Subgroup A) ↔ orderOf a = Nat.card A := by
  constructor
  · intro ha
    exact orderOf_eq_card_of_zpowers_eq_top ha
  · intro ha
    -- In a finite cyclic group, equality of subgroup cardinalities forces equality with `⊤`.
    exact (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers a)).mp <| by
      rw [Nat.card_zpowers, ha]

/-- Helper for Exercise 9-9.4-3: summing `θ[A]` over a finite cyclic group counts all generators,
so the total is `|A| * φ(|A|)`. -/
private lemma cyclicGroupTheta_sum_eq_card_mul_totient [IsCyclic A] :
    ∑ a : A, (θ[A] : A → ℂ) a = (Nat.card A : ℂ) * Nat.totient (Nat.card A) := by
  classical
  let S : Finset A := Finset.univ.filter fun a : A ↦ orderOf a = Nat.card A
  -- Rewrite `θ[A]` as the constant `|A|` on the generator set and `0` elsewhere.
  calc
    ∑ a : A, (θ[A] : A → ℂ) a
        = ∑ a : A, if orderOf a = Nat.card A then (Nat.card A : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [Representation.cyclicGroupTheta, zpowers_eq_top_iff_orderOf_eq_natCard]
    _ = Finset.sum S fun _a ↦ (Nat.card A : ℂ) := by
          rw [Finset.sum_ite]
          simp [S]
    _ = (S.card : ℂ) * (Nat.card A : ℂ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = (Nat.totient (Nat.card A) : ℂ) * (Nat.card A : ℂ) := by
          congr 1
          simpa [S, Nat.card_eq_fintype_card] using
            (IsCyclic.card_orderOf_eq_totient (α := A) (dvd_rfl : Fintype.card A ∣ Fintype.card A))
    _ = (Nat.card A : ℂ) * Nat.totient (Nat.card A) := by
          ring

/-- Helper for Exercise 9-9.4-3: the auxiliary function `θ[A]` pairs with the unit character as
the number of generators of the cyclic group `A`. -/
private lemma cyclicGroupTheta_pairing_one_eq_totient [IsCyclic A] :
    ⟪(θ[A] : A → ℂ), (1 : A → ℂ)⟫ = Nat.totient (Nat.card A) := by
  have hcard : (Nat.card A : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  -- Rewrite the pairing as the average of `θ[A]` and substitute the generator count.
  calc
    ⟪(θ[A] : A → ℂ), (1 : A → ℂ)⟫
        = (Nat.card A : ℂ)⁻¹ * ∑ a : A, (θ[A] : A → ℂ) a := by
            rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
            simp
    _ = (Nat.card A : ℂ)⁻¹ * ((Nat.card A : ℂ) * Nat.totient (Nat.card A)) := by
          rw [cyclicGroupTheta_sum_eq_card_mul_totient (A := A)]
    _ = Nat.totient (Nat.card A) := by
          rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

-- Proof sketch: evaluate the pairing directly from the definition of `cyclicGroupLambda A`,
-- use the explicit values of the regular character and of `θ[A]`, and count the
-- generators of the cyclic group by `Nat.totient (Nat.card A)`.
/-- Exercise 9-9.4-3 (1): if `A` is cyclic, LinearRepresentations_Serre_1977's auxiliary character candidate `λ_A` is
orthogonal to the unit character. -/
theorem cyclicGroupLambda_pairing_one_eq_zero [IsCyclic A] :
    ⟪λ[A], 1⟫ = 0 := by
  -- Expand LinearRepresentations_Serre_1977's definition of `λ[A]` and evaluate each pairing separately.
  calc
    ⟪λ[A], 1⟫
        =
          Representation.groupFunctionPairingOverField ℂ
            (((Nat.totient (Nat.card A) : ℂ) • ((leftRegular ℂ A).character : A → ℂ)) +
              ((-1 : ℂ) • (θ[A] : A → ℂ)))
            (1 : A → ℂ) := by
            simp [Representation.cyclicGroupLambda, sub_eq_add_neg]
    _ = Representation.groupFunctionPairingOverField ℂ
            (((Nat.totient (Nat.card A) : ℂ) • ((leftRegular ℂ A).character : A → ℂ)))
            (1 : A → ℂ) +
          Representation.groupFunctionPairingOverField ℂ (((-1 : ℂ) • (θ[A] : A → ℂ)))
            (1 : A → ℂ) := by
            rw [Representation.groupFunctionPairing_add_left]
    _ = (Nat.totient (Nat.card A) : ℂ) *
          Representation.groupFunctionPairingOverField ℂ
            (((leftRegular ℂ A).character : A → ℂ))
            (1 : A → ℂ) +
          (-1 : ℂ) *
            Representation.groupFunctionPairingOverField ℂ
              ((θ[A] : A → ℂ))
              (1 : A → ℂ) := by
            rw [Representation.groupFunctionPairing_smul_left,
              Representation.groupFunctionPairing_smul_left]
    _ = (Nat.totient (Nat.card A) : ℂ) + (-1 : ℂ) * Nat.totient (Nat.card A) := by
          simp [leftRegular_character_pairing_one_eq_one, cyclicGroupTheta_pairing_one_eq_totient]
    _ = 0 := by
          simp

-- Proof sketch: `θ[A]` already lies in the owner `R(A)` by Proposition `9-9.4-2`. The regular
-- character term is itself a genuine character, so it also lies in `R(A)`, and the character ring
-- is closed under additive combinations inside the ambient function space.
/-- If `A` is cyclic, LinearRepresentations_Serre_1977's auxiliary character candidate `λ_A` belongs to the character ring
`R(A)`. This is the canonical owner-level bridge from the source-facing function `λ_A` to the
chapter's character-ring API. -/
theorem cyclicGroupLambda_mem_characterRing [IsCyclic A] :
    λ[A] ∈ R(A) := by
  have hreg : (leftRegular ℂ A).character ∈ R(A) := by
    simpa using
      Representation.rep_character_mem_characterRingOverField
        (K := ℂ) (G := A) (Rep.of (leftRegular ℂ A))
  refine (R(A)).sub_mem ?_ (cyclicGroupTheta_mem_characterRing A)
  simpa [Pi.smul_apply, zsmul_eq_mul] using
    (R(A)).toSubmodule.smul_mem (Nat.totient (Nat.card A) : ℤ) hreg

/-- Helper for Exercise 9-9.4-3: `λ[A]` is the complexification of an explicit real-valued
function that is nonpositive away from the identity. -/
private lemma cyclicGroupLambda_real_model [IsCyclic A] :
    ∃ φ : A → ℝ, Complex.ofReal ∘ φ = λ[A] ∧ ∀ a : A, a ≠ 1 → φ a ≤ 0 := by
  classical
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq (Subgroup A) := Classical.decEq (Subgroup A)
  let φ : A → ℝ := fun a ↦
    (Nat.totient (Nat.card A) : ℝ) * (if a = 1 then (Nat.card A : ℝ) else 0) -
      (if Subgroup.zpowers a = (⊤ : Subgroup A) then (Nat.card A : ℝ) else 0)
  refine ⟨φ, ?_, ?_⟩
  · -- Compare the explicit real model with LinearRepresentations_Serre_1977's complex-valued formula pointwise.
    ext a
    by_cases ha : a = 1
    · subst ha
      by_cases htop : (⊥ : Subgroup A) = ⊤
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, htop]
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, htop]
    · by_cases hgen : Subgroup.zpowers a = (⊤ : Subgroup A)
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, Representation.leftRegular_character_eq_zero_of_ne_one ha, ha, hgen]
      · simp [Function.comp, Representation.cyclicGroupLambda, Representation.cyclicGroupTheta,
          φ, Representation.leftRegular_character_eq_zero_of_ne_one ha, ha, hgen]
  · intro a ha
    -- Away from the identity the regular-character term vanishes, leaving a nonpositive value.
    by_cases hgen : Subgroup.zpowers a = (⊤ : Subgroup A)
    · simp [φ, ha, hgen]
    · simp [φ, ha, hgen]

-- Proof sketch: apply Exercise `9-9.1-1` to the source-facing function `λ[A]`, using the
-- canonical owner theorem `cyclicGroupLambda_mem_characterRing`, the pairing identity above, and
-- the sign condition away from the identity to obtain a finite-dimensional realization directly in
-- `FDRep ℂ A`.
/-- Exercise 9-9.4-3 (2): if `A` is cyclic, the auxiliary function `λ_A` is the character of a
finite-dimensional complex representation of `A`. -/
theorem cyclicGroupLambda_is_character [IsCyclic A] :
    ∃ V : FDRep ℂ A, V.character = λ[A] := by
  obtain ⟨φ, hφ, hneg⟩ := cyclicGroupLambda_real_model (A := A)
  -- Apply Exercise `9-9.1-1` to the explicit real model of `λ[A]`.
  have hpair : ⟪Complex.ofReal ∘ φ, (1 : A → ℂ)⟫ = 0 := by
    simpa [hφ] using cyclicGroupLambda_pairing_one_eq_zero (A := A)
  have hR : Complex.ofReal ∘ φ ∈ R(A) := by
    simpa [hφ] using cyclicGroupLambda_mem_characterRing (A := A)
  simpa [hφ] using
    exists_fdRep_character_eq_of_mem_characterRing_of_pairing_one_eq_zero_of_nonpos_off_identity
      (G := A) (φ := φ) hpair hneg hR

end

end Representation

section

variable {G : Type} [Group G] [Finite G]

attribute [local instance] Fintype.ofFinite

/-- Helper for Exercise 9-9.4-3: pairing an induced class function with the unit character does
not change the average. -/
private lemma groupFunctionPairing_inducedClassFunction_one_eq (H : Subgroup G) (χ : H → ℂ) :
    ⟪Ind[H](χ), (1 : G → ℂ)⟫ = ⟪χ, (1 : H → ℂ)⟫ := by
  classical
  have hcardG : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  have hsub_sum :
      (∑ y : G, (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))) = ∑ h : H, χ h := by
    calc
      ∑ y : G, (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))
          = ∑ y : G, if y ∈ H then (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ)) else (0 : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              by_cases hmem : y ∈ H <;> simp [hmem]
      _ = Finset.sum (Finset.univ.filter fun y : G ↦ y ∈ H)
            (fun y ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ)) := by
              simpa using
                (Finset.sum_filter
                  (s := Finset.univ)
                  (p := fun y : G ↦ y ∈ H)
                  (f := fun y : G ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))).symm
      _ = ∑ h : H, χ h := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := Finset.univ)
                (p := fun y : G ↦ y ∈ H)
                (f := fun y : G ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))).symm
  have hinner (s : G) :
      ∑ x : G,
        (if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ)) =
          ∑ h : H, χ h := by
    let e : G ≃ G :=
      { toFun := fun x ↦ s⁻¹ * x * s
        invFun := fun y ↦ s * y * s⁻¹
        left_inv := by
          intro x
          simp [mul_assoc]
        right_inv := by
          intro y
          simp [mul_assoc] }
    -- Reindex by conjugation, then collapse the ambient sum to the subgroup carrier.
    calc
      ∑ x : G,
          (if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ))
          = ∑ y : G, (if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ)) := by
              simpa [e] using
                Fintype.sum_equiv e
                  (fun x : G ↦ if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ))
                  (fun y : G ↦ if hy : y ∈ H then χ ⟨y, hy⟩ else (0 : ℂ))
                  (fun x ↦ by rfl)
      _ = ∑ h : H, χ h := hsub_sum
  let F : G → G → ℂ := fun x s ↦
    ((Nat.card H : ℂ)⁻¹) *
      (if hs : s⁻¹ * x * s ∈ H then χ ⟨s⁻¹ * x * s, hs⟩ else (0 : ℂ))
  have hF (x : G) : Ind[H](χ) x = ∑ s : G, F x s := by
    simp [Subgroup.inducedClassFunction, F, Finset.mul_sum]
  have hFsum (s : G) : ∑ x : G, F x s = ((Nat.card H : ℂ)⁻¹) * ∑ h : H, χ h := by
    dsimp [F]
    rw [← Finset.mul_sum, hinner s]
  -- Expand the two pairings as normalized sums and use the conjugation reindexing above.
  calc
    ⟪Ind[H](χ), (1 : G → ℂ)⟫
        = (Nat.card G : ℂ)⁻¹ * ∑ x : G, Ind[H](χ) x := by
            rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
            simp
    _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, ∑ s : G, F x s := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [hF x]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ s : G, ∑ x : G, F x s := by
          rw [Finset.sum_comm]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ s : G, ((Nat.card H : ℂ)⁻¹) * ∑ h : H, χ h := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s hs
          simpa using hFsum s
    _ = (Nat.card G : ℂ)⁻¹ *
          ((Nat.card G : ℂ) * (((Nat.card H : ℂ)⁻¹) * ∑ h : H, χ h)) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ h : H, χ h := by
          rw [← mul_assoc, inv_mul_cancel₀ hcardG, one_mul]
    _ = ⟪χ, (1 : H → ℂ)⟫ := by
          letI hFintype : Fintype H := H.instFintypeSubtypeMemOfDecidablePred
          rw [Representation.groupFunctionPairingOverField]
          simp only [Pi.one_apply, mul_one]
          have hsum_inv : ∑ h : H, χ h = ∑ x : H, χ x⁻¹ := by
            simpa using
              (Fintype.sum_equiv (Equiv.inv H)
                (fun x : H ↦ χ x)
                (fun x : H ↦ χ x⁻¹)
                (fun x ↦ by simp))
          rw [Nat.card_eq_fintype_card, hsum_inv]
          have hcard_inst :
              (@Fintype.card H hFintype) = (@Fintype.card H instFintypeGGroupFunctionPairingOwner) := by
            exact
              @Fintype.card_congr H H hFintype instFintypeGGroupFunctionPairingOwner (Equiv.refl H)
          have hsum_inst :
              (@Finset.univ H hFintype).sum (fun x : H ↦ χ x⁻¹) =
                (@Finset.univ H instFintypeGGroupFunctionPairingOwner).sum
                  (fun x : H ↦ χ x⁻¹) := by
            exact
              @Fintype.sum_equiv H H ℂ hFintype instFintypeGGroupFunctionPairingOwner inferInstance
                (Equiv.refl H)
                (fun x : H ↦ χ x⁻¹)
                (fun x : H ↦ χ x⁻¹)
                (fun x ↦ by rfl)
          rw [hcard_inst, hsum_inst]

/-- Helper for Exercise 9-9.4-3: summing scalar multiples of a fixed class function factors out
that class function. -/
private lemma finset_sum_smul_const {ι : Type*} (s : Finset ι) (a : ι → ℂ) (χ : G → ℂ) :
    Finset.sum s (fun i ↦ a i • χ) = (Finset.sum s fun i ↦ a i) • χ := by
  classical
  -- Build the sum one term at a time and factor out the common class function.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, add_smul]

/-- Helper for Exercise 9-9.4-3: evaluating an induced class function at the identity multiplies
the subgroup value at `1` by the subgroup index. -/
private lemma inducedClassFunction_one_eq_index_mul_value (H : Subgroup G) (χ : H → ℂ) :
    Ind[H](χ) 1 = (H.index : ℂ) * χ 1 := by
  -- TODO: evaluate the induction formula at the identity, where every summand is `χ 1`, and use
  -- `|G| = |H| * [G : H]`.
  classical
  have h1H : (1 : G) ∈ H := by
    simp
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hcard : (Nat.card G : ℂ) = (Nat.card H : ℂ) * H.index := by
    exact_mod_cast H.card_mul_index.symm
  have hsum :
      ∑ s : G,
        (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) =
          (Nat.card G : ℂ) * χ 1 := by
    have hχ1 : χ ⟨1, h1H⟩ = χ 1 := rfl
    -- Every summand at the identity is the same subgroup value `χ 1`.
    calc
      ∑ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0)
          = ∑ _s : G, χ 1 := by
              have hterm :
                  ∀ s : G,
                    (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) =
                      χ 1 := by
                    intro s
                    have hs : s⁻¹ * (1 : G) * s ∈ H := by
                      simpa using h1H
                    simp [hs, hχ1]
              simpa using
                (Fintype.sum_congr
                  (f := fun s : G ↦
                    if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0)
                  (g := fun _s : G ↦ χ 1)
                  hterm)
      _ = (Nat.card G : ℂ) * χ 1 := by
            simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  -- Substitute the constant identity-value sum into the induction formula.
  calc
    Ind[H](χ) 1
        = ((Nat.card H : ℂ)⁻¹) *
            ∑ s : G,
              (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) := by
            simp [Subgroup.inducedClassFunction]
    _ = ((Nat.card H : ℂ)⁻¹) * ((Nat.card G : ℂ) * χ 1) := by
          rw [hsum]
    _ = ((Nat.card H : ℂ)⁻¹) * (((Nat.card H : ℂ) * H.index) * χ 1) := by
          rw [hcard]
    _ = (H.index : ℂ) * χ 1 := by
          field_simp [hcardH]

/-- Helper for Exercise 9-9.4-3: inducing the regular character from a subgroup recovers the
ambient regular character. -/
private lemma induced_leftRegular_character_eq (H : Subgroup G) :
    Ind[H](((leftRegular ℂ H).character : H → ℂ)) = (leftRegular ℂ G).character := by
  classical
  ext x
  by_cases hx : x = 1
  · -- At the identity, induction multiplies the subgroup value by the subgroup index.
    subst hx
    calc
      Ind[H](((leftRegular ℂ H).character : H → ℂ)) 1
          = (H.index : ℂ) * (leftRegular ℂ H).character 1 := by
              rw [inducedClassFunction_one_eq_index_mul_value]
      _ = (H.index : ℂ) * (Nat.card H : ℂ) := by
            simp
      _ = (Nat.card G : ℂ) := by
            have hcard' : (Nat.card H : ℂ) * H.index = (Nat.card G : ℂ) := by
              exact_mod_cast H.card_mul_index
            simpa [mul_comm] using hcard'
      _ = (leftRegular ℂ G).character 1 := by
            simp
  · -- Away from the identity, each induced summand evaluates the subgroup regular character away
    -- from `1`, so every term vanishes.
    have hsum :
        ∑ s : G,
          (if hs : s⁻¹ * x * s ∈ H then
            ((leftRegular ℂ H).character : H → ℂ) ⟨s⁻¹ * x * s, hs⟩
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro s hs
      by_cases hsx : s⁻¹ * x * s ∈ H
      · have hconj_ne : s⁻¹ * x * s ≠ 1 := by
          intro h1
          apply hx
          calc
            x = s * (s⁻¹ * x * s) * s⁻¹ := by
                  simp [mul_assoc]
            _ = 1 := by
                  simp [h1]
        have hsub_ne : (⟨s⁻¹ * x * s, hsx⟩ : H) ≠ 1 := by
          intro hsub
          apply hconj_ne
          exact congrArg Subtype.val hsub
        have hreg0 :
            ((leftRegular ℂ H).character : H → ℂ) ⟨s⁻¹ * x * s, hsx⟩ = 0 :=
          Representation.leftRegular_character_eq_zero_of_ne_one hsub_ne
        simpa [hsx] using hreg0
      · simpa [hsx]
    calc
      Ind[H](((leftRegular ℂ H).character : H → ℂ)) x
          = ((Nat.card H : ℂ)⁻¹) *
              ∑ s : G,
                (if hs : s⁻¹ * x * s ∈ H then
                  ((leftRegular ℂ H).character : H → ℂ) ⟨s⁻¹ * x * s, hs⟩
                else 0) := by
              simp [Subgroup.inducedClassFunction]
      _ = 0 := by
            rw [hsum]
            simp
      _ = (leftRegular ℂ G).character x := by
            symm
            exact Representation.leftRegular_character_eq_zero_of_ne_one hx

/-- Helper for Exercise 9-9.4-3: the sum of the generator counts of the cyclic subgroups of `G`
is `|G|`. -/
private lemma sum_totient_natCard_cyclicSubgroups_eq_natCard :
    ∑ H ∈ Subgroup.cyclicSubgroups G, Nat.totient (Nat.card H) = Nat.card G := by
  have hpair_rhs :
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫ = Nat.card G := by
    -- Pair LinearRepresentations_Serre_1977's cyclic `θ`-identity with the unit character on the right.
    calc
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫
          = ⟪(Nat.card G : ℂ) • (1 : G → ℂ), (1 : G → ℂ)⟫ := by
              rw [sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ)]
      _ = (Nat.card G : ℂ) * ⟪(1 : G → ℂ), (1 : G → ℂ)⟫ := by
            rw [Representation.groupFunctionPairing_smul_left]
      _ = Nat.card G := by
            simp [groupFunctionPairing_one_one_eq_one]
  have hpair_lhs :
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫ =
        (∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ)) := by
    -- Distribute the pairing across the finite subgroup sum and evaluate each cyclic contribution.
    calc
      ⟪(∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫
          = ∑ H ∈ Subgroup.cyclicSubgroups G,
              ⟪(Ind[H](θ[H]) : G → ℂ), (1 : G → ℂ)⟫ := by
              simpa using
                groupFunctionPairing_finset_sum_left (A := G) (s := Subgroup.cyclicSubgroups G)
                  (f := fun H ↦ (Ind[H](θ[H]) : G → ℂ)) (ψ := (1 : G → ℂ))
      _ = ∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            haveI : IsCyclic H := (Subgroup.mem_cyclicSubgroups.mp hH)
            rw [groupFunctionPairing_inducedClassFunction_one_eq,
              cyclicGroupTheta_pairing_one_eq_totient]
  have hcomplex :
      (∑ H ∈ Subgroup.cyclicSubgroups G, Nat.totient (Nat.card H) : ℂ) = Nat.card G := by
    exact hpair_lhs.symm.trans hpair_rhs
  exact_mod_cast hcomplex

-- Proof sketch: expand `cyclicGroupLambda` inside the sum over cyclic subgroups. Proposition
-- `9-9.4-1` identifies the total contribution of the `θ_A` terms, while Proposition `7-7.2-1`
-- and the regular-character computation identify the total contribution of the regular terms with
-- `|G| • (leftRegular ℂ G).character`. Internally, each cyclic summand can be routed through the
-- canonical character-ring induction owner, but the public statement remains the source-facing
-- equality of class functions.
/-- Exercise 9-9.4-3 (3): summing the induced auxiliary characters `Ind_A^G(λ_A)` over the cyclic
subgroups `A ≤ G` gives `|G| (r_G - 1)`, written in Lean with the regular character
`(leftRegular ℂ G).character`. -/
theorem sum_induced_cyclicGroupLambda_eq_groupOrder_smul_regular_character_sub_one :
    ∑ H ∈ Subgroup.cyclicSubgroups G,
        Ind[H](λ[H]) =
      (Nat.card G : ℂ) • ((leftRegular ℂ G).character - 1) := by
  -- Expand each cyclic summand, rewrite the induced regular character, and then collect the
  -- common regular and `θ` contributions.
  calc
    ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](λ[H])
        = ∑ H ∈ Subgroup.cyclicSubgroups G,
            ((Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character - Ind[H](θ[H])) := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            haveI : IsCyclic H := (Subgroup.mem_cyclicSubgroups.mp hH)
            calc
              Ind[H](λ[H])
                  = Ind[H](((Nat.totient (Nat.card H) : ℂ) •
                        ((leftRegular ℂ H).character : H → ℂ)) +
                      ((-1 : ℂ) • (θ[H] : H → ℂ))) := by
                          simp [Representation.cyclicGroupLambda, sub_eq_add_neg]
              _ = (Nat.totient (Nat.card H) : ℂ) • Ind[H](((leftRegular ℂ H).character : H → ℂ)) +
                    (-1 : ℂ) • Ind[H](θ[H]) := by
                        rw [Subgroup.inducedClassFunction_map_add,
                          Subgroup.inducedClassFunction_map_smul,
                          Subgroup.inducedClassFunction_map_smul]
              _ = (Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character +
                    (-1 : ℂ) • Ind[H](θ[H]) := by
                        rw [induced_leftRegular_character_eq]
              _ = (Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character - Ind[H](θ[H]) := by
                        simp [sub_eq_add_neg]
    _ = (∑ H ∈ Subgroup.cyclicSubgroups G,
            (Nat.totient (Nat.card H) : ℂ) • (leftRegular ℂ G).character) -
          ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) := by
            rw [Finset.sum_sub_distrib]
    _ = ((∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ)) •
            (leftRegular ℂ G).character) -
          ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) := by
            simp [finset_sum_smul_const]
    _ = (Nat.card G : ℂ) • (leftRegular ℂ G).character -
          (Nat.card G : ℂ) • (1 : G → ℂ) := by
            have htot :
                (∑ H ∈ Subgroup.cyclicSubgroups G, (Nat.totient (Nat.card H) : ℂ)) =
                  (Nat.card G : ℂ) := by
              exact_mod_cast sum_totient_natCard_cyclicSubgroups_eq_natCard (G := G)
            rw [htot, sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ)]
    _ = (Nat.card G : ℂ) • ((leftRegular ℂ G).character - 1) := by
          rw [smul_sub]

end

/-! ### Proposition_9_9_4_1 (from Chap09) -/
open scoped BigOperators Representation SubgroupInduction
open Representation

noncomputable section

universe u v

namespace Representation

section

variable {K : Type v} [Zero K] [NatCast K]
variable (A : Type u) [Group A] [Finite A]

open Classical in
/-- LinearRepresentations_Serre_1977's auxiliary function `θ_A` on a finite group `A`, supported on the generators of `A`
and equal to `|A|` on each generator. -/
def cyclicGroupTheta : A → K :=
  fun a ↦ if Subgroup.zpowers a = (⊤ : Subgroup A) then Nat.card A else 0

scoped[Representation] notation:max "θ[" A "]" => cyclicGroupTheta A

end

section

variable {K : Type v} [Zero K] [NatCast K]
variable {A : Type u} [Group A]

-- Proof sketch: unfold `cyclicGroupTheta`; the defining `if` reduces to the first branch under the
-- assumption that `a` generates the whole group `A`.
/-- A generator of `A` is sent by `cyclicGroupTheta A` to the order of `A`. -/
@[simp] theorem cyclicGroupTheta_apply_of_zpowers_eq_top [Finite A]
    (a : A) (ha : Subgroup.zpowers a = (⊤ : Subgroup A)) :
    θ[A] a = Nat.card A := by
  simp [cyclicGroupTheta, ha]

-- Proof sketch: unfold `cyclicGroupTheta`; the defining `if` reduces to the second branch when
-- `a` does not generate the whole group `A`.
/-- A nongenerator of `A` is sent by `cyclicGroupTheta A` to `0`. -/
@[simp] theorem cyclicGroupTheta_apply_of_zpowers_ne_top [Finite A]
    (a : A) (ha : Subgroup.zpowers a ≠ (⊤ : Subgroup A)) :
    θ[A] a = 0 := by
  simp [cyclicGroupTheta, ha]

end

end Representation

section

variable {G : Type u} [Group G]

/-- Helper for Proposition 9-9.4-1: an element of a subgroup generates that subgroup internally
exactly when its ambient cyclic subgroup is the whole subgroup. -/
lemma subgroup_zpowers_eq_top_iff (H : Subgroup G) (a : H) :
    Subgroup.zpowers a = ⊤ ↔ Subgroup.zpowers (a : G) = H := by
  -- Map the internal cyclic subgroup along the subtype map to compare it with the ambient one.
  rw [← Subgroup.map_subtype_inj]
  rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, H.range_subtype]
  simp

end

section

variable {G : Type u} [Group G] [Finite G]
variable {K : Type v} [Semifield K]

private local instance : Fintype G := Fintype.ofFinite G

-- Proof sketch: rewrite `|G|` as a multiple of `orderOf x`, then split according to whether that
-- order vanishes after casting to `K`.
/-- Helper for Proposition 9-9.4-1: the induction scalar attached to `orderOf x` is absorbed by
`|G|`. -/
lemma natCard_mul_inv_orderOf_mul_orderOf (x : G) :
    (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) = (Nat.card G : K) := by
  -- Rewrite `|G|` as a multiple of `orderOf x`, then split on whether that cast is zero.
  obtain ⟨m, hm⟩ := orderOf_dvd_natCard x
  have hcard : (Nat.card G : K) = (orderOf x : K) * (m : K) := by
    simpa [Nat.cast_mul] using congrArg (fun n : ℕ => (n : K)) hm
  by_cases hx : (orderOf x : K) = 0
  · rw [hcard]
    simp [hx]
  · calc
      (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K))
          = ((orderOf x : K) * (m : K)) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
              rw [hcard]
      _ = ((orderOf x : K) * (orderOf x : K)⁻¹) * ((m : K) * (orderOf x : K)) := by
            ac_rfl
      _ = (m : K) * (orderOf x : K) := by
            simp [hx]
      _ = (orderOf x : K) * (m : K) := by
            ac_rfl
      _ = (Nat.card G : K) := by
            rw [hcard]

-- Proof sketch: evaluate both sides at `x : G`, expand `Ind[A](θ[A])` using the
-- induction formula, and sum over the canonical finite family `Subgroup.cyclicSubgroups G`. For
-- each `y : G`, the conjugate `y * x * y⁻¹` generates a unique cyclic subgroup of `G`, so exactly
-- one summand contributes `1`, giving the constant value `|G|`.
/-- Proposition 9-9.4-1: for a finite group `G`, the sum over all cyclic subgroups `A ≤ G` of the
induced functions `Ind_A^G(θ_A)` is the constant function with value `|G|`. -/
theorem sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one :
    ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) = (Nat.card G : K) • (1 : G → K) := by
  classical
  ext x
  simp [Pi.smul_apply, Nat.card_eq_fintype_card]
  let F : Subgroup G → G → K := fun H y ↦
    if Subgroup.zpowers (y⁻¹ * x * y) = H then ((Nat.card H : K)⁻¹ * (Nat.card H : K)) else 0
  -- Expand each induced summand into the subgroup generated by the conjugate `y⁻¹ * x * y`.
  have hInd (H : Subgroup G) : Ind[H](θ[H]) x = ∑ y : G, F H y := by
    change ((Nat.card H : K)⁻¹) *
        Finset.univ.sum (fun y : G =>
          if hy : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy⟩ else 0) = _
    rw [Finset.mul_sum]
    change Finset.univ.sum (fun y : G =>
        ((Nat.card H : K)⁻¹) *
          (if hy : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy⟩ else 0)) = _
    refine Finset.sum_congr rfl ?_
    intro y hyuniv
    by_cases hgen : Subgroup.zpowers (y⁻¹ * x * y) = H
    · have hy : y⁻¹ * x * y ∈ H := by
        rw [← hgen]
        exact Subgroup.mem_zpowers _
      have hleft :
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
            = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := by
        simp [hy]
      have htheta : (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = (Nat.card H : K) := by
        simp [Representation.cyclicGroupTheta, subgroup_zpowers_eq_top_iff, hgen]
      calc
        ((Nat.card H : K)⁻¹) *
            (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
            = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := hleft
        _ = ((Nat.card H : K)⁻¹) * (Nat.card H : K) := by
              exact congrArg (fun z : K => ((Nat.card H : K)⁻¹) * z) htheta
        _ = F H y := by
              dsimp [F]
              rw [if_pos hgen]
    · by_cases hy : y⁻¹ * x * y ∈ H
      · have hleft :
            ((Nat.card H : K)⁻¹) *
                (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
              = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := by
          simp [hy]
        have htheta : (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = 0 := by
          simp [Representation.cyclicGroupTheta, subgroup_zpowers_eq_top_iff, hgen]
        have hmul : ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = 0 := by
          simpa using congrArg (fun z : K => ((Nat.card H : K)⁻¹) * z) htheta
        calc
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0)
              = ((Nat.card H : K)⁻¹) * (θ[H] : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := hleft
          _ = 0 := hmul
          _ = F H y := by
                dsimp [F]
                rw [if_neg hgen]
      · have hleft :
            ((Nat.card H : K)⁻¹) *
                (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0) = 0 := by
          simp [hy]
        calc
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then θ[H] ⟨y⁻¹ * x * y, hy'⟩ else 0) = 0 := hleft
          _ = F H y := by
                dsimp [F]
                rw [if_neg hgen]
  -- For each conjugate, exactly one cyclic subgroup contributes to the subgroup sum.
  have hCollapse (a : G) :
      ((Subgroup.cyclicSubgroups G).sum fun H ↦ F H a) =
        ((Nat.card (Subgroup.zpowers (a⁻¹ * x * a)) : K)⁻¹ *
          (Nat.card (Subgroup.zpowers (a⁻¹ * x * a)) : K)) := by
    have ha : Subgroup.zpowers (a⁻¹ * x * a) ∈ Subgroup.cyclicSubgroups G :=
      Subgroup.mem_cyclicSubgroups.2 inferInstance
    dsimp [F]
    rw [Finset.sum_eq_single (Subgroup.zpowers (a⁻¹ * x * a))]
    · simp
    · intro H hH hne
      have hne' : Subgroup.zpowers (a⁻¹ * x * a) ≠ H := by
        simpa [eq_comm] using hne
      simp [hne']
    · intro hnot
      exact False.elim (hnot ha)
  -- Swap the two finite sums, collapse the inner indicator sum, and rewrite subgroup orders as
  -- `orderOf x`.
  calc
    ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) x
        = (Subgroup.cyclicSubgroups G).sum fun H ↦ ∑ y : G, F H y := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            exact hInd H
    _ = (Subgroup.cyclicSubgroups G).sum fun H ↦ Finset.univ.sum (F H) := by
          rfl
    _ = Finset.univ.sum fun y : G ↦ (Subgroup.cyclicSubgroups G).sum fun H ↦ F H y := by
          rw [Finset.sum_comm]
    _ = ∑ y : G,
          ((Nat.card (Subgroup.zpowers (y⁻¹ * x * y)) : K)⁻¹ *
            (Nat.card (Subgroup.zpowers (y⁻¹ * x * y)) : K)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simpa using hCollapse y
    _ = ∑ y : G, (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Nat.card_zpowers]
          have horder : orderOf (y⁻¹ * x * y) = orderOf x := by
            simpa using ((SemiconjBy.conj_mk y⁻¹ x).orderOf_eq y⁻¹).symm
          rw [horder]
    _ = (Fintype.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          simp
    _ = (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          rw [Nat.card_eq_fintype_card]
    _ = (Nat.card G : K) := by
          simpa using natCard_mul_inv_orderOf_mul_orderOf (K := K) x
    _ = (Fintype.card G : K) := by
          rw [Nat.card_eq_fintype_card]

end
