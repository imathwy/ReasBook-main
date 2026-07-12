import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibility

/-!
Source-side support/value API for Serre Exercise 18.5(a).

The declarations in this file keep the right-hand side of Serre's statement as a condition on
the original full class function `Φ : A ⊗R[K](G)`: vanishing on the `p`-singular locus and
centralizer-`p`-part divisibility on the `p`-regular locus.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section Serre18_5ASupportValueCriterionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Fact p.Prime] in
/-- Two full scalar-extended class functions have the same regular restriction exactly when they
agree on every `p`-regular element of `G`. -/
theorem regularRestriction_eq_regularRestriction_iff_forall_pRegular_value_eq_serre18_5a
    (Φ Ψ : A ⊗R[K](G)) :
    regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ ↔
      ∀ g : G, IsPRegular p g → (Φ : G → K) g = (Ψ : G → K) g := by
  constructor
  · intro h g hg
    have hvalue :=
      congrFun h (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
    simpa [regularRestriction_ofSubtype] using hvalue
  · intro h
    ext c
    let s := PRegularConjClass.representative (G := G) (p := p) c
    have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
      apply Subtype.ext
      simp [s]
    rw [← hs]
    rw [regularRestriction_ofSubtype (p := p) (A := A) (K := K) (G := G) Φ s.1 s.2,
      regularRestriction_ofSubtype (p := p) (A := A) (K := K) (G := G) Ψ s.1 s.2]
    exact h s.1 s.2

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- If two full class functions vanish on the `p`-singular locus, equality of their regular
restrictions upgrades to equality as elements of `A ⊗R[K](G)`. -/
theorem eq_of_regularRestriction_eq_of_zero_on_pSingular_serre18_5a
    {Φ Ψ : A ⊗R[K](G)}
    (hΦzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0)
    (hΨzero : ∀ g : G, ¬ IsPRegular p g → (Ψ : G → K) g = 0)
    (hreg :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ) :
    Φ = Ψ := by
  have hΦext :=
    (regular_restriction_zero_extension_iff (p := p) (A := A) (K := K) (G := G) Φ).1 hΦzero
  have hΨext :=
    (regular_restriction_zero_extension_iff (p := p) (A := A) (K := K) (G := G) Ψ).1 hΨzero
  apply Subtype.ext
  funext g
  rw [hΦext g, hΨext g]
  by_cases hg : IsPRegular p g
  · rw [dif_pos hg, dif_pos hg]
    exact congrFun hreg (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
  · simp [hg]

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Serre's pointwise regular-value divisibility condition is exactly membership of the regular
restriction in the coordinatewise centralizer-`p`-part lattice. -/
theorem regularRestriction_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value_serre18_5a
    (Φ : A ⊗R[K](G)) :
    regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ↔
      ∀ g : G, IsPRegular p g →
        ∃ a : A, (Φ : G → K) g =
          algebraMap A K ((centralizerPPart p g : A) * a) := by
  constructor
  · intro hreg g hg
    rcases
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G)
          (regularRestriction (p := p) (A := A) (K := K) (G := G) Φ)).1 hreg
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
      simp [s]
    rcases hvalue s.1 s.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← hs]
    simpa [regularRestriction_ofSubtype, ConjClasses.centralizerPPart_mk] using ha

/-- Serre 18.5(a), non-circular source-side direction: a full scalar-extended class function
whose source-side support and value conditions satisfy the right-hand side belongs to the
projective-character submodule.  The only representation-theoretic input is the existing
Exercise `18.4` regular-restriction image theorem. -/
theorem mem_projectiveCharacterSubmodule_of_serre18_5a_rhs
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    {Φ : A ⊗R[K](G)}
    (hzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0)
    (hvalue :
      ∀ g : G, IsPRegular p g →
        ∃ a : A, (Φ : G → K) g =
          algebraMap A K ((centralizerPPart p g : A) * a)) :
    Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) := by
  have hreg :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    (regularRestriction_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value_serre18_5a
      (p := p) (A := A) (K := K) (G := G) Φ).2 hvalue
  have hmap :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω] using hreg
  rcases Submodule.mem_map.1 hmap with ⟨Ψ, hΨ, hΨreg⟩
  have hΨzero :
      ∀ g : G, ¬ IsPRegular p g → (Ψ : G → K) g = 0 :=
    projectiveCharacterSubmodule_zero_on_pSingular
      (p := p) (A := A) (K := K) (G := G) hΨ
  have hregEq :
      regularRestriction (p := p) (A := A) (K := K) (G := G) Φ =
        regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ := by
    simpa [regularRestrictionLinearMap] using hΨreg.symm
  have hΦΨ : Φ = Ψ :=
    eq_of_regularRestriction_eq_of_zero_on_pSingular_serre18_5a
      (p := p) (A := A) (K := K) (G := G) hzero hΨzero hregEq
  simpa [hΦΨ] using hΨ

/-- Serre 18.5(a) as a source-facing support/value criterion, with an explicit primitive-root
hypothesis matching the Chapter `16` image theorem used upstream. -/
theorem mem_projectiveCharacterSubmodule_iff_serre18_5a_rhs
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (Φ : A ⊗R[K](G)) :
    Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ↔
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        ∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g =
            algebraMap A K ((centralizerPPart p g : A) * a) := by
  constructor
  · intro hΦ
    have hzero :
        ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0 :=
      projectiveCharacterSubmodule_zero_on_pSingular
        (p := p) (A := A) (K := K) (G := G) hΦ
    have hmap :
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
          Submodule.map
            (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
            (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
      ⟨Φ, hΦ, rfl⟩
    have hreg :
        regularRestriction (p := p) (A := A) (K := K) (G := G) Φ ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
      simpa [projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hω] using hmap
    exact
      ⟨hzero,
        (regularRestriction_mem_regularValueDivisibilitySubmodule_iff_forall_pRegular_value_serre18_5a
          (p := p) (A := A) (K := K) (G := G) Φ).1 hreg⟩
  · rintro ⟨hzero, hvalue⟩
    exact
      mem_projectiveCharacterSubmodule_of_serre18_5a_rhs
        (p := p) (A := A) (K := K) (G := G) hω hzero hvalue

/-- The same non-circular direction in the standard large-field regime of Chapter `18`, where
primitive roots of the required orders are obtained from `HasEnoughRootsOfUnity`. -/
theorem mem_projectiveCharacterSubmodule_of_serre18_5a_rhs_of_enoughRoots
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {Φ : A ⊗R[K](G)}
    (hzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0)
    (hvalue :
      ∀ g : G, IsPRegular p g →
        ∃ a : A, (Φ : G → K) g =
          algebraMap A K ((centralizerPPart p g : A) * a)) :
    Φ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    mem_projectiveCharacterSubmodule_of_serre18_5a_rhs
      (p := p) (A := A) (K := K) (G := G) hω hzero hvalue

/-- Source-facing Serre 18.5(a) criterion in the standard large-field regime. -/
theorem mem_projectiveCharacterSubmodule_iff_serre18_5a_rhs_of_enoughRoots
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
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
  exact
    mem_projectiveCharacterSubmodule_iff_serre18_5a_rhs
      (p := p) (A := A) (K := K) (G := G) hω Φ

end Serre18_5ASupportValueCriterionWorker

end Representation
