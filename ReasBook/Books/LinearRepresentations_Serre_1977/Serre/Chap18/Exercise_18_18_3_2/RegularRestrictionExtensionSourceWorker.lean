import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibility

/-!
Source-side API between full class functions and their regular restrictions.

This file only packages the formal zero-extension/restriction interface used in Serre 18.5(a):
regular values live on `PRegularConjClass G p`, while the support condition is a statement about
the full function on `G`.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PlainRegularExtension

variable {p : ℕ}
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]

/-- Serre's zero-extension from regular conjugacy classes to all elements of `G`. -/
abbrev regularExtension (f : PRegularConjClass G p → K) : G → K :=
  regularClassFunctionExtension (G := G) (p := p) f

@[simp] theorem regularExtension_apply (f : PRegularConjClass G p → K) (g : G) :
    regularExtension (G := G) (p := p) f g =
      if hg : IsPRegular p g then
        f (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
      else
        0 := by
  rfl

/-- On a `p`-regular representative, `regularExtension` recovers the original regular value. -/
@[simp] theorem regularExtension_ofSubtype
    (f : PRegularConjClass G p → K) (s : {g : G // IsPRegular p g}) :
    regularExtension (G := G) (p := p) f s.1 =
      f (PRegularConjClass.ofSubtype (G := G) p s) := by
  simpa [regularExtension] using
    regularClassFunctionExtension_ofSubtype (G := G) (p := p) f s

/-- `regularExtension` is zero on the `p`-singular locus. -/
@[simp] theorem regularExtension_eq_zero_of_not_isPRegular
    (f : PRegularConjClass G p → K) {g : G} (hg : ¬ IsPRegular p g) :
    regularExtension (G := G) (p := p) f g = 0 := by
  simpa [regularExtension] using
    regularClassFunctionExtension_eq_zero_of_not_isPRegular (G := G) (p := p) f hg

/-- `regularExtension` is zero on every `p`-singular element. -/
theorem regularExtension_zero_on_pSingular
    (f : PRegularConjClass G p → K) :
    ∀ g : G, ¬ IsPRegular p g → regularExtension (G := G) (p := p) f g = 0 := by
  intro g hg
  exact regularExtension_eq_zero_of_not_isPRegular (G := G) (p := p) f hg

/-- `regularExtension` is a class function on `G`. -/
theorem regularExtension_isClassFunction
    (f : PRegularConjClass G p → K) :
    _root_.IsClassFunction (regularExtension (G := G) (p := p) f) := by
  simpa [regularExtension] using
    regularClassFunctionExtension_isClassFunction (G := G) (p := p) f

/-- Descending `regularExtension` back to regular conjugacy classes recovers the source function. -/
@[simp] theorem pRegularLift_regularExtension
    (f : PRegularConjClass G p → K) :
    IsClassFunction.pRegularLift
        (G := G) (p := p) (regularExtension_isClassFunction (G := G) (p := p) f) =
      f := by
  simpa [regularExtension] using
    pRegularLift_regularClassFunctionExtension (G := G) (p := p) f

/-- A class function with a fixed regular lift is zero off the regular locus exactly when it is
Serre's zero-extension of that lift. -/
theorem zero_on_pSingular_iff_eq_regularExtension_of_pRegularLift
    {F : G → K} (hF : _root_.IsClassFunction F)
    (f : PRegularConjClass G p → K)
    (hres : IsClassFunction.pRegularLift (G := G) (p := p) hF = f) :
    (∀ g : G, ¬ IsPRegular p g → F g = 0) ↔
      F = regularExtension (G := G) (p := p) f := by
  constructor
  · intro hzero
    funext g
    by_cases hg : IsPRegular p g
    · have hvalue :=
        congrFun hres (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
      rw [regularExtension_apply, dif_pos hg]
      simpa using hvalue
    · simp [regularExtension, regularClassFunctionExtension, hg, hzero g hg]
  · intro hFext g hg
    rw [hFext]
    exact regularExtension_eq_zero_of_not_isPRegular (G := G) (p := p) f hg

end PlainRegularExtension

section RegularRestrictionAPI

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

@[simp] theorem regularRestrictionLinearMap_apply
    (Φ : A ⊗R[K](G)) :
    regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G) Φ =
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ := by
  rfl

/-- Evaluating the linear-map form of regular restriction on a chosen representative. -/
@[simp] theorem regularRestrictionLinearMap_apply_ofSubtype
    (Φ : A ⊗R[K](G)) (g : G) (hg : IsPRegular p g) :
    (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G) Φ)
        (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩) =
      (Φ : G → K) g := by
  simpa [regularRestrictionLinearMap] using
    regularRestriction_ofSubtype (p := p) (A := A) (K := K) (G := G) Φ g hg

/-- Equality with a regular row is equivalent to equality on every `p`-regular element upstairs. -/
theorem regularRestriction_eq_iff_forall_pRegular_value_eq
    (Φ : A ⊗R[K](G)) (f : PRegularConjClass G p → K) :
    regularRestriction (p := p) (A := A) (K := K) (G := G) Φ = f ↔
      ∀ g : G, ∀ hg : IsPRegular p g,
        (Φ : G → K) g =
          f (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩) := by
  constructor
  · intro hres g hg
    have hvalue :=
      congrFun hres (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
    simpa [regularRestriction_ofSubtype] using hvalue
  · intro hvalue
    funext c
    let s := PRegularConjClass.representative (G := G) (p := p) c
    have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
      apply Subtype.ext
      simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
    calc
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ c =
          regularRestriction (p := p) (A := A) (K := K) (G := G) Φ
            (PRegularConjClass.ofSubtype (G := G) p s) := by
            rw [hs]
      _ = (Φ : G → K) s.1 := by
            simpa using
              regularRestriction_ofSubtype
                (p := p) (A := A) (K := K) (G := G) Φ s.1 s.2
      _ = f (PRegularConjClass.ofSubtype (G := G) p s) :=
            hvalue s.1 s.2
      _ = f c := by
            rw [hs]

/-- Two full class functions have the same regular restriction exactly when they agree on all
`p`-regular elements. -/
theorem regularRestriction_eq_regularRestriction_iff_forall_pRegular_value_eq
    (Φ Ψ : A ⊗R[K](G)) :
    regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ ↔
      ∀ g : G, ∀ hg : IsPRegular p g,
        (Φ : G → K) g = (Ψ : G → K) g := by
  constructor
  · intro hres g hg
    have hvalue :=
      congrFun hres (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
    simpa [regularRestriction_ofSubtype] using hvalue
  · intro hvalue
    funext c
    let s := PRegularConjClass.representative (G := G) (p := p) c
    have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
      apply Subtype.ext
      simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
    rw [← hs]
    simpa [regularRestriction_ofSubtype] using hvalue s.1 s.2

/-- If two full class functions vanish on the `p`-singular locus, their regular restrictions
determine equality on all of `G`. -/
theorem eq_of_regularRestriction_eq_of_zero_on_pSingular
    {Φ Ψ : A ⊗R[K](G)}
    (hΦzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0)
    (hΨzero : ∀ g : G, ¬ IsPRegular p g → (Ψ : G → K) g = 0)
    (hres :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ) :
    Φ = Ψ := by
  apply Subtype.ext
  funext g
  by_cases hg : IsPRegular p g
  · exact
      (regularRestriction_eq_regularRestriction_iff_forall_pRegular_value_eq
        (p := p) (A := A) (K := K) (G := G) Φ Ψ).1 hres g hg
  · rw [hΦzero g hg, hΨzero g hg]

/-- On the zero-on-`p`-singular subspace, regular restriction is an equality test. -/
theorem eq_iff_regularRestriction_eq_of_zero_on_pSingular
    {Φ Ψ : A ⊗R[K](G)}
    (hΦzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0)
    (hΨzero : ∀ g : G, ¬ IsPRegular p g → (Ψ : G → K) g = 0) :
    Φ = Ψ ↔
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ := by
  constructor
  · intro h
    rw [h]
  · exact
      eq_of_regularRestriction_eq_of_zero_on_pSingular
        (p := p) (A := A) (K := K) (G := G) hΦzero hΨzero

/-- A full class function is zero off the regular locus exactly when it is the zero-extension of
its regular restriction. -/
theorem zero_on_pSingular_iff_eq_regularExtension_regularRestriction
    (Φ : A ⊗R[K](G)) :
    (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ↔
      (Φ : G → K) =
        regularExtension (G := G) (p := p)
          (regularRestriction (p := p) (A := A) (K := K) (G := G) Φ) := by
  constructor
  · intro hzero
    funext g
    by_cases hg : IsPRegular p g
    · simp [regularExtension, regularClassFunctionExtension, hg, regularRestriction_ofSubtype]
    · simp [regularExtension, regularClassFunctionExtension, hg, hzero g hg]
  · intro hΦ g hg
    rw [hΦ]
    exact
      regularExtension_eq_zero_of_not_isPRegular
        (G := G) (p := p)
        (regularRestriction (p := p) (A := A) (K := K) (G := G) Φ) hg

/-- The restricted divisibility lattice, evaluated as a statement about full `g`-values. -/
theorem regularRestriction_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value
    (Φ : A ⊗R[K](G)) :
    regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ↔
      ∀ g : G, IsPRegular p g →
        ∃ a : A, (Φ : G → K) g =
          algebraMap A K ((centralizerPPart p g : A) * a) := by
  constructor
  · intro hmem g hg
    rcases
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G)
          (regularRestriction (p := p) (A := A) (K := K) (G := G) Φ)).1 hmem
          (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩) with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [regularRestriction_ofSubtype, ConjClasses.centralizerPPart_mk] using ha
  · intro hvalue
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (regularRestriction (p := p) (A := A) (K := K) (G := G) Φ)).2 ?_
    intro c
    let s := PRegularConjClass.representative (G := G) (p := p) c
    have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
      apply Subtype.ext
      simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
    rcases hvalue s.1 s.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ c =
          regularRestriction (p := p) (A := A) (K := K) (G := G) Φ
            (PRegularConjClass.ofSubtype (G := G) p s) := by
            rw [hs]
      _ = (Φ : G → K) s.1 := by
            simpa using
              regularRestriction_ofSubtype
                (p := p) (A := A) (K := K) (G := G) Φ s.1 s.2
      _ = algebraMap A K ((centralizerPPart p s.1 : A) * a) := ha
      _ = algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a) := by
            have hmk : ConjClasses.mk s.1 = c.1 := by
              simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
            rw [← hmk, ConjClasses.centralizerPPart_mk]

/-- The same divisibility condition for Serre's zero-extension of a restricted row. -/
theorem regularExtension_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value
    (f : PRegularConjClass G p → K) :
    f ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ↔
      ∀ g : G, IsPRegular p g →
        ∃ a : A, regularExtension (G := G) (p := p) f g =
          algebraMap A K ((centralizerPPart p g : A) * a) := by
  constructor
  · intro hmem g hg
    rcases
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G) f).1 hmem
          (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩) with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [regularExtension_apply, dif_pos hg]
    simpa [ConjClasses.centralizerPPart_mk] using ha
  · intro hvalue
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) f).2 ?_
    intro c
    let s := PRegularConjClass.representative (G := G) (p := p) c
    have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
      apply Subtype.ext
      simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
    rcases hvalue s.1 s.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      f c = f (PRegularConjClass.ofSubtype (G := G) p s) := by
            rw [hs]
      _ = regularExtension (G := G) (p := p) f s.1 := by
            simpa using
              (regularExtension_ofSubtype (G := G) (p := p) f s).symm
      _ = algebraMap A K ((centralizerPPart p s.1 : A) * a) := ha
      _ = algebraMap A K ((ConjClasses.centralizerPPart p c.1 : A) * a) := by
            have hmk : ConjClasses.mk s.1 = c.1 := by
              simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
            rw [← hmk, ConjClasses.centralizerPPart_mk]

section ProjectiveCharacterCriterionFullValues

variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Serre 18.5(a) in full-value form: projective-character membership is equivalent to vanishing
on `p`-singular elements and centralizer-`p`-part divisibility at every regular element. -/
theorem mem_projectiveCharacterSubmodule_iff_zero_on_pSingular_and_forall_pRegular_value
    (Φ : A ⊗R[K](G)) :
    Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ↔
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        ∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g =
            algebraMap A K ((centralizerPPart p g : A) * a) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  constructor
  · intro hΦ
    have hrestricted :=
      (mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regularRestriction_mem
        (p := p) (A := A) (K := K) (G := G) hω Φ).1 hΦ
    exact
      ⟨hrestricted.1,
        (regularRestriction_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value
          (p := p) (A := A) (K := K) (G := G) Φ).1 hrestricted.2⟩
  · rintro ⟨hzero, hvalue⟩
    exact
      (mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regularRestriction_mem
        (p := p) (A := A) (K := K) (G := G) hω Φ).2
        ⟨hzero,
          (regularRestriction_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value
            (p := p) (A := A) (K := K) (G := G) Φ).2 hvalue⟩

/-- Constructor form of the full-value Serre 18.5(a) criterion. -/
theorem mem_projectiveCharacterSubmodule_of_zero_on_pSingular_and_forall_pRegular_value
    {Φ : A ⊗R[K](G)}
    (hzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0)
    (hvalue :
      ∀ g : G, IsPRegular p g →
        ∃ a : A, (Φ : G → K) g =
          algebraMap A K ((centralizerPPart p g : A) * a)) :
    Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) :=
  (mem_projectiveCharacterSubmodule_iff_zero_on_pSingular_and_forall_pRegular_value
    (p := p) (A := A) (K := K) (G := G) Φ).2 ⟨hzero, hvalue⟩

end ProjectiveCharacterCriterionFullValues

end RegularRestrictionAPI

end Representation
