import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerResidualMatrixClosureFinal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerResidualSourceValuationWorker

/-!
Source-side providers for the visible fixed-coordinate Brauer readback divisibility.

The route is the Serre `18.5(a)` route already isolated upstream: the projective-character
lattice congruence gives the A-valued pairing residual for every coordinate-normalized Brauer
family, and `BrauerResidualMatrixClosureFinal` identifies that residual with the visible
fixed-coordinate readback condition.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerReadbackDivisibilitySourceWorker

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

local instance brauerReadbackDivisibilitySourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReadbackDivisibilitySourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The pure A-side pairing residual is exactly enough to give visible readback.

This names the forward direction of
`coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback` so downstream
files can use it without unfolding the equivalence. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_pairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hresidual :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hresidual

/-- Serre `18.5(a)` in projective-character lattice form gives visible readback for any fixed
coordinate-normalized Brauer family.

The source theorem supplies the pairing residual by choosing projective envelopes and applying
Exercise `18.4`/orthogonality; the final step is the local A-side equivalence above. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_projectiveCharacter_lattice
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_pairingResidual
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    (coordinateNormalizedBrauerBasisPairingResidualDivisibility_forall_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice
      π hπ_simple hπ_coord)

/-- Universal fixed-family version of the source provider from the projective-character lattice
congruence. -/
theorem coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_forall_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ (π : PRegularConjClass G p → FDRep k G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro π hπ_simple hπ_coord
  exact
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hlattice

end BrauerReadbackDivisibilitySourceWorker

section FullMixedBrauerReadbackDivisibilitySourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerReadbackDivisibilitySourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerReadbackDivisibilitySourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-characteristic visible-readback provider from the source-side projective-character
lattice congruence, retaining the `∀ π` fixed-family shape. -/
theorem fullMixedModelCoordinateNormalizedBrauerBasisVisibleReadbackDivisibility_of_projectiveCharacter_lattice
    (hlattice :
      fullMixedModelProjectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (k := k) (G := G)) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent G)]
      [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
      IsLocalRing.ResidueField A ≃+* k →
        ∀ (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
          (hπ_simple : ∀ c, Simple (π c))
          (hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
          coordinateNormalizedBrauerBasisVisibleReadbackDivisibility
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    coordinateNormalizedBrauerBasisVisibleReadbackDivisibility_forall_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

end FullMixedBrauerReadbackDivisibilitySourceWorker

end Representation
