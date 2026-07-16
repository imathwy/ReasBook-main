import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointwiseResidualWorker

/-!
Explicit source-side normalization for the residual `p`-primary divisibility route.

The lemmas in this file keep the Serre `18.5(a)` input in its coordinatewise divisibility
form.  A pointwise regular-value equality

```
  row d = algebraMap A K ((centralizerPPart p d.1 : A) * a)
```

is converted directly into the pure `A`-valued residual

```
  bA c d - delta_cd - z(d) * repr(indicator d⁻¹) c = z(d) * a'
```

by subtracting the visible centralizer-`p`-part multiple.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ExplicitResidualPPrimaryDivisibilityWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance explicitResidualPPrimaryDivisibilityWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance explicitResidualPPrimaryDivisibilityWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Single-coordinate normalization from regular-value divisibility to the explicit A-side
residual.

This is the small algebraic step needed after Serre `18.5(a)` gives the pointwise divisibility
of the coordinate-normalized modular-character row.  No Cartan range, cokernel, or determinant
endpoint is used. -/
theorem coordinateNormalizedBrauerBasis_explicitResidual_of_pointwiseRegularValueDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (hsource :
      ∃ a : A,
        FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  classical
  rcases hsource with ⟨a, ha⟩
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G)
        (inversePRegularConjClass (p := p) d)) c)
  refine ⟨a - coeff, ?_⟩
  apply IsFractionRing.injective A K
  have hbasis :=
    congrFun
      (canonicalDVRBrauerBasis_algebraMap_apply_eq_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G)
        π hπ_pairwise hπ_complete c) d
  calc
    algebraMap A K
        (bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) * coeff)
        =
      (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * coeff) := by
          simp [bA, coeff, regularIntegerFunctionCast, hbasis, map_sub, map_mul]
    _ =
        algebraMap A K
          ((ConjClasses.centralizerPPart p d.1 : A) * (a - coeff)) := by
          rw [ha]
          rw [← map_sub, mul_sub]

section RegularValueRows

variable [CharZero K]

/-- Row-membership version of
`coordinateNormalizedBrauerBasis_explicitResidual_of_pointwiseRegularValueDivisibility`.

This packages the usual `regularValueDivisibilitySubmodule` API: membership gives the
pointwise witness, and the preceding lemma subtracts the visible residual multiple. -/
theorem coordinateNormalizedBrauerBasis_explicitResidual_of_regularValueRowMem
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (hrow :
      (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G)
        (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))).1
        hrow d with
    ⟨a, ha⟩
  exact
    coordinateNormalizedBrauerBasis_explicitResidual_of_pointwiseRegularValueDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord c d ⟨a, by simpa using ha⟩

/-- Fixed-family closure: if every coordinate-normalized modular-character row is in Serre's
regular-value divisibility lattice, then the explicit residual is divisible by the attached
centralizer `p`-part at every coordinate. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_regularValueRows_explicit
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrows :
      ∀ c : PRegularConjClass G p,
        (FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro c d
  exact
    coordinateNormalizedBrauerBasis_explicitResidual_of_regularValueRowMem
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord c d (hrows c)

/-- Source-faithful regular-value congruence supplies the fixed-family explicit residual by the
pointwise normalization above. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_regularValueCongruence_explicit
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  refine
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_regularValueRows_explicit
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord ?_
  intro c
  have hrow := hregular ([π c]₀ : R₀[k](G))
  simpa [hπ_coord c, virtualModularCharacterOnPRegularConjClass_class] using hrow

end RegularValueRows

end ExplicitResidualPPrimaryDivisibilityWorker

end Representation
