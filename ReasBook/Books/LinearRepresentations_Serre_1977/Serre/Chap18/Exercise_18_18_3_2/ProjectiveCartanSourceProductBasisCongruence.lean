import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProductBasisImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSourceProductBasisCongruence

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanSourceProductBasisCongruenceFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSourceProductBasisCongruenceDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The requested basis-vector congruence is exactly the inverse-Brauer-coordinate congruence for
the corresponding standard integer point mass.

This is the smallest formal reduction of the remaining gap: the existing readback theorem gives
that the Brauer coordinates of the virtual modular character of `[π c]₀` are `Pi.single c 1`;
closing the original congruence is therefore equivalent to proving that applying the inverse
Brauer-coordinate equivalence to that point mass changes it only by Serre's divisibility lattice.
-/
theorem projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p) :
    (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      ((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) := by
  let χ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let T : (PRegularConjClass G p → K) ≃ₗ[A] (PRegularConjClass G p → K) :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let e : PRegularConjClass G p → K :=
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
      (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  have hTχ : T (χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G))) = e := by
    simpa [T, χ, e, hπ_coord c, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap]
      using
        projectiveCartanASpanBrauerRepr_virtualModularCharacter
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G))
  have hχ : χ ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) = T.symm e := by
    rw [← hTχ]
    simp [T]
  simp [χ, T, e, hχ]

/-- Canonical-span version of the same reduction. This form exposes the exact place where
`canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule` applies. -/
theorem projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_canonical
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p) :
    (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      ((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)) := by
  rw [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G)]
  exact
    projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c

/-- Equivalent fixed-coordinate form of the inverse-Brauer point-mass congruence.

Applying the Brauer-coordinate equivalence transports Serre's divisibility lattice to the
Cartan-coordinate `A`-span. Thus the remaining basis-vector congruence can be checked before
applying `T.symm`, as the congruence
`e_c - T e_c ∈ span(projectiveCartanCoordinateCast.range)`.
-/
theorem brauerInverse_single_congruence_iff_brauerRepr_single_cartanSpan_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p) :
    ((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
        (projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) := by
  let E := PRegularConjClass G p → K
  let D : Submodule A E :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let S : Submodule A E :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set E)
  let T : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let e : E :=
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
      (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  have hTD : Submodule.map (T : E →ₗ[A] E) D = S := by
    simpa [D, S, T, E, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hSD : Submodule.map (T.symm : E →ₗ[A] E) S = D :=
    (Submodule.map_symm_eq_iff T).mpr hTD
  constructor
  · intro hDmem
    have hmap :
        T (T.symm e - e) ∈ Submodule.map (T : E →ₗ[A] E) D := by
      exact ⟨T.symm e - e, by simpa [D, T, E, e] using hDmem, rfl⟩
    have hS : T (T.symm e - e) ∈ S := by
      simpa [hTD] using hmap
    simpa [S, T, E, e, map_sub] using hS
  · intro hSmem
    have hmap :
        T.symm (e - T e) ∈ Submodule.map (T.symm : E →ₗ[A] E) S := by
      exact ⟨e - T e, by simpa [S, T, E, e] using hSmem, rfl⟩
    have hD : T.symm (e - T e) ∈ D := by
      simpa [hSD] using hmap
    simpa [D, T, E, e, map_sub] using hD

/-- Adapter: an explicit proof of the inverse-Brauer point-mass congruences closes the requested
basis-vector source congruence. -/
theorem projectiveCartanSourceProductBasisCongruence_of_brauerInverse_single_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcompat :
      ∀ c : PRegularConjClass G p,
        (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ c : PRegularConjClass G p,
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro c
  exact
    (projectiveCartanSourceProductBasisCongruence_iff_brauerInverse_single_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).2
      (hcompat c)

/-- Adapter from the fixed-coordinate Cartan-span congruence to the requested basis-vector source
congruence.

This is the smallest Cartan-side statement needed by the current API: for each standard point
mass `e_c`, the Brauer-coordinate map itself must be congruent to the identity modulo the
Cartan-coordinate `A`-span.
-/
theorem projectiveCartanSourceProductBasisCongruence_of_brauerRepr_single_cartanSpan_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcartan :
      ∀ c : PRegularConjClass G p,
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K))) :
    ∀ c : PRegularConjClass G p,
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  refine
    projectiveCartanSourceProductBasisCongruence_of_brauerInverse_single_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_
  intro c
  exact
    (brauerInverse_single_congruence_iff_brauerRepr_single_cartanSpan_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord c).2
      (hcartan c)

end ProjectiveCartanSourceProductBasisCongruence

end Representation
