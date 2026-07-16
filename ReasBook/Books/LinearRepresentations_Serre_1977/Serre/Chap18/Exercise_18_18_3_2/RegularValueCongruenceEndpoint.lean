import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReprPointMassCongruence

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section RegularValueCongruenceEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance regularValueCongruenceEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularValueCongruenceEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Forward regular-value congruence from the source-side point-mass congruences for one
coordinate-normalized Brauer family.

This is the forward half needed by the canonical source product: once every normalized simple
class has virtual modular character congruent to the matching integer point mass modulo Serre's
regular-value divisibility lattice, finite `ℤ`-linear expansion in the normalized simple basis gives
the congruence for every virtual modular character. -/
theorem regularValueCongruence_of_brauerPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsource :
      brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    ∀ x : R₀[IsLocalRing.ResidueField A](G),
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProduct_regularValueCongruence_of_basis_congruence
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (by
      intro c
      simpa [brauerPointMassSourceCongruence] using hsource c)

/-- Forward regular-value congruence from the existence of one coordinate-normalized Brauer family
satisfying the source-side point-mass congruences.

The coordinate-normalized family itself is already available in the local API; the genuinely
mathematical remaining input is the source congruence for its basis vectors. -/
theorem regularValueCongruence_of_exists_brauerPointMassSourceCongruence
    (hsource :
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ hπ_simple : ∀ c, Simple (π c),
          ∃ hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)
                  ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
              brauerPointMassSourceCongruence
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    ∀ x : R₀[IsLocalRing.ResidueField A](G),
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  rcases hsource with ⟨π, hπ_simple, hπ_coord, hbasis⟩
  exact
    regularValueCongruence_of_brauerPointMassSourceCongruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis

end RegularValueCongruenceEndpoint

end Representation
