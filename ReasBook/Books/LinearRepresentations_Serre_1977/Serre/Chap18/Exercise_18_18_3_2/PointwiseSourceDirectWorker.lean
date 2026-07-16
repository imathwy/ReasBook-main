import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointwiseSourceDivisibilityWorker

/-!
Worker H direct source-side bridges for the pointwise divisibility input.

The main local condition isolated here is exactly the fixed row membership requested by the
source route: each coordinate-normalized Brauer row differs from its integer point mass by an
element of Serre's regular-value divisibility lattice.  From that condition, worker F's bridge
gives the pointwise source divisibility statement without using Cartan range, cokernel, or
product endpoints.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PointwiseSourceDirectWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance pointwiseSourceDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointwiseSourceDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed row membership requested by the source-side proof route. -/
def regularValueCongruenceSourceFaithfulFixedRowMembership : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p),
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[k](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The global regular-value congruence specializes immediately to the fixed point-mass row
membership for every coordinate-normalized Brauer family. -/
theorem fixedRowMembership_of_regularValueCongruenceSourceFaithfulStatement
    (hglobal :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulFixedRowMembership
      (p := p) (A := A) (K := K) (G := G) := by
  intro π _hπ_simple hπ_coord c
  have hrow := hglobal ([π c]₀ : R₀[k](G))
  simpa [hπ_coord c] using hrow

/-- Serre `18.5(a)` in projective-character lattice form gives the requested fixed-row
membership directly.

This is the source-side provider: the row difference is first known as the regular restriction
of a projective character, then `projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule`
rewrites that whole projective-character lattice to Serre's regular-value divisibility lattice. -/
theorem fixedRowMembership_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulFixedRowMembership
      (p := p) (A := A) (K := K) (G := G) := by
  intro π _hπ_simple hπ_coord c
  have hrow := hlattice ([π c]₀ : R₀[k](G))
  simpa [hπ_coord c,
    projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hrow

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed row membership is exactly the input needed by worker F's pointwise bridge. -/
theorem pointwiseSourceDivisibility_of_fixedRowMembership
    (hrow :
      regularValueCongruenceSourceFaithfulFixedRowMembership
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) :=
  pointwiseSourceDivisibility_of_pointwiseRegularValueRowMem
    (p := p) (A := A) (K := K) (G := G)
    hrow

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Direct specialization from the global source-faithful regular-value congruence to the
pointwise source divisibility target. -/
theorem pointwiseSourceDivisibility_of_regularValueCongruenceSourceFaithfulStatement
    (hglobal :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) :=
  pointwiseSourceDivisibility_of_fixedRowMembership
    (p := p) (A := A) (K := K) (G := G)
    (fixedRowMembership_of_regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) hglobal)

/-- The canonical Brauer-basis readback input gives the fixed row membership directly through
the regular-value congruence adapter. -/
theorem fixedRowMembership_of_brauerBasisReadbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulFixedRowMembership
      (p := p) (A := A) (K := K) (G := G) :=
  fixedRowMembership_of_regularValueCongruenceSourceFaithfulStatement
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hread)

/-- Source-side readback input closes the requested pointwise source divisibility, without
routing through the final Cartan range or product statements. -/
theorem pointwiseSourceDivisibility_of_brauerBasisReadbackInput_direct
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulPointwiseSourceDivisibilityProof
      (p := p) (A := A) (K := K) (G := G) :=
  pointwiseSourceDivisibility_of_fixedRowMembership
    (p := p) (A := A) (K := K) (G := G)
    (fixedRowMembership_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G) hread)

end PointwiseSourceDirectWorker

end Representation
