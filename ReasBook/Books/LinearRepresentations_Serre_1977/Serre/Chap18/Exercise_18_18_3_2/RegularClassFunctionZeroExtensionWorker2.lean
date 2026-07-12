import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibility

/-!
Zero-extension API for the Exercise 18.4 route.

This file packages the already established regular-restriction image theorem in the form needed
for the zero-on-singular argument: a regular row satisfying Serre's centralizer-`p`-part value
condition is represented by an element of `A ⊗R[K](G)` whose underlying full class function is
exactly the zero-extension of that row.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section RegularClassFunctionZeroExtensionWorker2

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

/-- A row on the `p`-regular classes satisfying the regular-value divisibility lattice has a full
representative in `A ⊗R[K](G)`.  The representative can be chosen in the projective-character
submodule, vanishes on the `p`-singular locus, and is pointwise Serre's zero-extension of the row.

This is the zero-extension form of the Exercise 18.4/Lemma 10.3.8 route: once the regular values
are in the image lattice, no separate singular data are needed. -/
theorem exists_projectiveCharacter_zeroExtension_of_mem_regularValueDivisibilitySubmodule
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    {f : PRegularConjClass G p → K}
    (hf :
      f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ = f ∧
          (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
            ∀ g : G,
              (Φ : G → K) g =
                if hg : IsPRegular p g then
                  f (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
                else
                  0 := by
  have hmap :
      f ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω] using hf
  rcases Submodule.mem_map.1 hmap with ⟨Φ, hΦ, hΦres⟩
  have hres :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ = f := by
    simpa [regularRestrictionLinearMap] using hΦres
  have hzero :
      ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0 :=
    projectiveCharacterSubmodule_zero_on_pSingular
      (p := p) (A := A) (K := K) (G := G) hΦ
  refine ⟨Φ, hΦ, hres, hzero, ?_⟩
  intro g
  by_cases hg : IsPRegular p g
  · rw [dif_pos hg]
    have hvalue :=
      congrFun hres (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
    simpa [regularRestriction_ofSubtype] using hvalue
  · rw [dif_neg hg]
    exact hzero g hg

/-- Direct membership form: a regular row in the centralizer-`p`-part divisibility lattice has
Serre zero-extension in the scalar-extended ordinary character lattice `A ⊗R[K](G)`. -/
theorem regularClassFunctionExtension_mem_characterRingOverFieldAlgebraScalarExtension_of_mem_regularValueDivisibilitySubmodule
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    {f : PRegularConjClass G p → K}
    (hf :
      f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    regularClassFunctionExtension (G := G) (p := p) f ∈ A ⊗R[K](G) := by
  rcases
      exists_projectiveCharacter_zeroExtension_of_mem_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hω hf with
    ⟨Φ, _hΦ, _hres, _hzero, hΦext⟩
  have hfun : (Φ : G → K) = regularClassFunctionExtension (G := G) (p := p) f := by
    funext g
    by_cases hg : IsPRegular p g
    · rw [regularClassFunctionExtension, dif_pos hg]
      have hvalue := hΦext g
      rw [dif_pos hg] at hvalue
      exact hvalue
    · rw [regularClassFunctionExtension, dif_neg hg]
      have hvalue := hΦext g
      rw [dif_neg hg] at hvalue
      exact hvalue
  rw [← hfun]
  exact Φ.2

/-- Large-field form of
`exists_projectiveCharacter_zeroExtension_of_mem_regularValueDivisibilitySubmodule`. -/
theorem exists_projectiveCharacter_zeroExtension_of_mem_regularValueDivisibilitySubmodule_of_enoughRoots
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {f : PRegularConjClass G p → K}
    (hf :
      f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ = f ∧
          (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
            ∀ g : G,
              (Φ : G → K) g =
                if hg : IsPRegular p g then
                  f (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
                else
                  0 := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    exists_projectiveCharacter_zeroExtension_of_mem_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω hf

/-- Large-field direct membership form for Serre's zero-extension. -/
theorem regularClassFunctionExtension_mem_characterRingOverFieldAlgebraScalarExtension_of_mem_regularValueDivisibilitySubmodule_of_enoughRoots
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {f : PRegularConjClass G p → K}
    (hf :
      f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    regularClassFunctionExtension (G := G) (p := p) f ∈ A ⊗R[K](G) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    regularClassFunctionExtension_mem_characterRingOverFieldAlgebraScalarExtension_of_mem_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω hf

/-- `A`-valued source version: if the scalar-cast regular row satisfies the centralizer-`p`-part
divisibility lattice, then its zero-extension is represented by a projective character in
`A ⊗R[K](G)`. -/
theorem exists_projectiveCharacter_zeroExtension_algebraMap_of_mem_regularValueDivisibilitySubmodule
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    {f : PRegularConjClass G p → A}
    (hf :
      (fun c : PRegularConjClass G p => algebraMap A K (f c)) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          (fun c : PRegularConjClass G p => algebraMap A K (f c)) ∧
          (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
            ∀ g : G,
              (Φ : G → K) g =
                if hg : IsPRegular p g then
                  algebraMap A K (f (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩))
                else
                  0 :=
  exists_projectiveCharacter_zeroExtension_of_mem_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G) hω hf

/-- Pointwise support/value constructor for the regular row.  This is often the most convenient
input shape when feeding the zero-extension route from `fullMixedModelRegularValueSourceStatement`
workers. -/
theorem exists_projectiveCharacter_zeroExtension_algebraMap_of_forall_regularValue
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    {f : PRegularConjClass G p → A}
    (hvalue :
      ∀ c : PRegularConjClass G p,
        ∃ a : A,
          algebraMap A K (f c) =
            algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a)) :
    ∃ Φ : A ⊗R[K](G),
      Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
          (fun c : PRegularConjClass G p => algebraMap A K (f c)) ∧
          (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
            ∀ g : G,
              (Φ : G → K) g =
                if hg : IsPRegular p g then
                  algebraMap A K (f (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩))
                else
                  0 := by
  refine
    exists_projectiveCharacter_zeroExtension_algebraMap_of_mem_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω ?_
  exact
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)
      (fun c : PRegularConjClass G p => algebraMap A K (f c))).2 hvalue

/-- Direct membership version for an `A`-valued regular row supplied with the pointwise
centralizer-`p`-part divisibility witness. -/
theorem regularClassFunctionExtension_algebraMap_mem_characterRingOverFieldAlgebraScalarExtension_of_forall_regularValue
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    {f : PRegularConjClass G p → A}
    (hvalue :
      ∀ c : PRegularConjClass G p,
        ∃ a : A,
          algebraMap A K (f c) =
            algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a)) :
    regularClassFunctionExtension
        (G := G) (p := p)
        (fun c : PRegularConjClass G p => algebraMap A K (f c)) ∈
      A ⊗R[K](G) := by
  refine
    regularClassFunctionExtension_mem_characterRingOverFieldAlgebraScalarExtension_of_mem_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω ?_
  exact
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)
      (fun c : PRegularConjClass G p => algebraMap A K (f c))).2 hvalue

end RegularClassFunctionZeroExtensionWorker2

end Representation
