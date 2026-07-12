import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProductBasisImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CanonicalSourceProductImageEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance canonicalSourceProductImageEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductImageEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal source-quotient representative statement for the canonical source-product image.

This is the source-side version of mutual image containment: every canonical Cartan source class
is congruent modulo the canonical source span to some cast integer function, and conversely every
cast integer function is congruent to some virtual modular character. -/
def canonicalVirtualModularCartanProductImageSourceCongruences : Prop :=
  (∀ x : R₀[IsLocalRing.ResidueField A](G),
      ∃ g : PRegularConjClass G p → ℤ,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G)) ∧
    (∀ g : PRegularConjClass G p → ℤ,
      ∃ x : R₀[IsLocalRing.ResidueField A](G),
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G))

/-- Source-congruence endpoint: the minimal source-quotient representative statement implies the
canonical source-product image is exactly the coordinatewise integer image. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_source_congruences
    (hsource :
      canonicalVirtualModularCartanProductImageSourceCongruences
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hsource with ⟨hforward, hreverse⟩
  refine
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_integerRepresentatives
      (p := p) (A := A) (K := K) (G := G) ?_ ?_
  · intro x
    rcases hforward x with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have hg' :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G) := by
      have hneg :=
        (canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G)).neg_mem hg
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    exact
      (regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
        (p := p) (A := A) (K := K) (G := G) g x hg').symm
  · intro g
    rcases hreverse g with ⟨x, hx⟩
    exact
      ⟨x,
        regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
          (p := p) (A := A) (K := K) (G := G) g x hx⟩

/-- Endpoint in the preferred split form: the forward half is the existing regular-value
congruence, while the reverse half only asks for an existential source congruence for each
integer function. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_source_congruence
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
              canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_integerRepresentatives
      (p := p) (A := A) (K := K) (G := G)
      (canonicalVirtualModularCartanProduct_forwardRepresentative_of_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hforward) ?_
  intro g
  rcases hreverse g with ⟨x, hx⟩
  exact
    ⟨x,
      regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
        (p := p) (A := A) (K := K) (G := G) g x hx⟩

/-- Endpoint from the global regular-value congruence alone.

The forward representative is the fixed integer coordinate function. The reverse representative is
obtained formally by applying the same congruence to the virtual character with prescribed
regular-class coordinates and then negating the congruence. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_source_congruence
      (p := p) (A := A) (K := K) (G := G) hforward ?_
  intro g
  let x : R₀[IsLocalRing.ResidueField A](G) :=
    (regularClassCoordinateAddEquiv
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).symm g
  refine ⟨x, ?_⟩
  have hxcoord :
      regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x = g := by
    simp [x]
  have hxD :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [hxcoord] using hforward x
  have hxneg :=
    (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)).neg_mem hxD
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hxneg

/-- Point-mass reverse source congruence. This is weaker than asking for the fixed witness
`[π c]₀`: each integer point mass may use any residue-side virtual character representative. -/
def canonicalVirtualModularCartanProductReversePointSourceCongruence : Prop :=
  ∀ c : PRegularConjClass G p,
    ∃ x : R₀[IsLocalRing.ResidueField A](G),
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
          canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G)

/-- A global regular-value congruence gives the reverse point-source witnesses by choosing the
virtual modular character whose regular-coordinate vector is the requested point mass. -/
theorem canonicalVirtualModularCartanProductReversePointSourceCongruence_of_regularValue_congruence
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductReversePointSourceCongruence
      (p := p) (A := A) (K := K) (G := G) := by
  intro c
  let x : R₀[IsLocalRing.ResidueField A](G) :=
    (regularClassCoordinateAddEquiv
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).symm
      (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  refine ⟨x, ?_⟩
  have hxcoord :
      regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x =
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
    simp [x]
  have hxD :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [hxcoord] using hforward x
  have hxneg :=
    (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)).neg_mem hxD
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hxneg

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Point-mass reverse source congruences generate the reverse source congruence for every
integer regular-class function, using the corresponding integral linear combination of the
point-mass witnesses. -/
theorem canonicalVirtualModularCartanProduct_reverseSourceCongruence_of_reverse_point_source_congruence
    (hpoint :
      canonicalVirtualModularCartanProductReversePointSourceCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ g : PRegularConjClass G p → ℤ,
      ∃ x : R₀[IsLocalRing.ResidueField A](G),
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
          virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G) := by
  classical
  choose x hx using hpoint
  let χ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let S : Submodule A (PRegularConjClass G p → K) :=
    canonicalVirtualModularCartanRangeASpan
      (p := p) (A := A) (K := K) (G := G)
  intro g
  refine ⟨∑ c : PRegularConjClass G p, g c • x c, ?_⟩
  have hcast_expand :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) g =
        ∑ c : PRegularConjClass G p,
          g c •
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
    ext d
    simp [regularIntegerFunctionCast, Pi.single_apply]
  have hχ_expand :
      χ (∑ c : PRegularConjClass G p, g c • x c) =
        ∑ c : PRegularConjClass G p, g c • χ (x c) := by
    calc
      χ (∑ c : PRegularConjClass G p, g c • x c) =
          ∑ c : PRegularConjClass G p, χ (g c • x c) := by
            rw [map_sum]
      _ = ∑ c : PRegularConjClass G p, g c • χ (x c) := by
            refine Finset.sum_congr rfl ?_
            intro c _hc
            rw [map_zsmul]
  have hdiff :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
          χ (∑ c : PRegularConjClass G p, g c • x c) =
        ∑ c : PRegularConjClass G p,
          g c •
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
              χ (x c)) := by
    rw [hcast_expand, hχ_expand]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    rw [zsmul_sub]
  rw [hdiff]
  refine Submodule.sum_mem S ?_
  intro c _hc
  exact S.toAddSubgroup.zsmul_mem (by simpa [S, χ] using hx c) (g c)

/-- The source-congruence form of the non-fixed point-mass route. The forward half may use the
canonical coordinate representative, while the reverse half only requires arbitrary point-mass
witnesses and then sums them. -/
theorem canonicalVirtualModularCartanProductImageSourceCongruences_of_regularValue_congruence_and_reverse_point_source_congruence
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hpoint :
      canonicalVirtualModularCartanProductReversePointSourceCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageSourceCongruences
      (p := p) (A := A) (K := K) (G := G) := by
  refine ⟨?_, ?_⟩
  · intro x
    refine
      ⟨regularClassCoordinateAddEquiv
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) x, ?_⟩
    simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hforward x
  · exact
      canonicalVirtualModularCartanProduct_reverseSourceCongruence_of_reverse_point_source_congruence
        (p := p) (A := A) (K := K) (G := G) hpoint

/-- Same endpoint with the reverse side reduced only to point masses and arbitrary witnesses. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_point_source_congruence
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hpoint :
      canonicalVirtualModularCartanProductReversePointSourceCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_source_congruences
      (p := p) (A := A) (K := K) (G := G)
      (canonicalVirtualModularCartanProductImageSourceCongruences_of_regularValue_congruence_and_reverse_point_source_congruence
        (p := p) (A := A) (K := K) (G := G) hforward hpoint)

/-- Forward-from-basis, reverse-from-existential-source-congruence endpoint.

This is the requested non-fixed-witness variant of the existing basis-congruence route. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_basis_congruence_and_reverse_point_source_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ c : PRegularConjClass G p,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) [π c]₀ -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hpoint :
      canonicalVirtualModularCartanProductReversePointSourceCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_point_source_congruence
      (p := p) (A := A) (K := K) (G := G) ?_ hpoint
  exact
    canonicalVirtualModularCartanProduct_regularValueCongruence_of_basis_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis

end CanonicalSourceProductImageEndpoint

end Representation
