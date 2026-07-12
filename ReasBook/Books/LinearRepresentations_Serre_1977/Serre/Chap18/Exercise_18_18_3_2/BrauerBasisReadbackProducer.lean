import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisReadbackProducer

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

local instance brauerBasisReadbackProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisReadbackProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The `A`-valued canonical Brauer-basis readback is equivalent to the already isolated
field-valued point-mass coordinate divisibility condition for the same coordinate-normalized
simple family.

This is only a producer adapter: it does not assert the point-mass divisibility itself.  It
packages the two existing readback APIs into the exact form needed by
`regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput`. -/
theorem brauerBasisFixedCoordinateReadbackDivisibility_iff_pointMassCoordinateDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) π hπ_simple hπ_coord) ↔
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_simple hπ_coord
  constructor
  · intro hread c d
    have hrow :
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π c]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv (p := p) (G := G) ([π c]₀ : R₀[k](G))) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
      exact
        ((fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete).2 hread) c
    rcases
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G) _).1 hrow d with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [virtualModularCharacterOnPRegularConjClass_class,
      regularIntegerFunctionCast, hπ_coord c] using ha
  · intro hpoint
    refine
      (fixedCoordinateRowCongruence_iff_brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete).1 ?_
    intro c
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) _).2 ?_
    intro d
    rcases hpoint c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [virtualModularCharacterOnPRegularConjClass_class,
      regularIntegerFunctionCast, hπ_coord c] using ha

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A fixed coordinate-normalized point-mass divisibility proof produces the local
Brauer-basis readback input requested by the source-faithful endpoint. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassCoordinateDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hpoint :
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (brauerBasisFixedCoordinateReadbackDivisibility_iff_pointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hpoint

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The existential point-mass coordinate blocker is equivalent to the local
Brauer-basis readback input.  This records the exact remaining producer obligation without adding
any placeholder theorem. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPointMassCoordinateDivisibility :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · rintro ⟨π, hπ_simple, hπ_coord, hread⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (brauerBasisFixedCoordinateReadbackDivisibility_iff_pointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hread
  · rintro ⟨π, hπ_simple, hπ_coord, hpoint⟩
    exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hpoint

end BrauerBasisReadbackProducer

end Representation
