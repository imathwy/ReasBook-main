import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReprPointMassCongruence

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerReprPointMassEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerReprPointMassEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReprPointMassEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The point-mass product identity needed to turn Serre 18.5(b)'s source product into the
fixed-coordinate quotient identity.

This is the exact product-side form of the remaining gap: the canonical source-product map must
send the simple class whose fixed Brauer coordinate is `Pi.single c 1` to the corresponding
coordinatewise integer point mass. -/
def brauerPointMassCanonicalProductIdentity
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) =
      cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range
          ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)))

/-- The product identity is exactly the source-side point-mass congruence. -/
theorem brauerPointMassCanonicalProductIdentity_iff_source_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerPointMassCanonicalProductIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  let χ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  constructor
  · intro hprod c
    let E :=
      canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
    let f : PRegularConjClass G p → ℤ :=
      Pi.single c (1 : ℤ)
    let x : R₀[IsLocalRing.ResidueField A](G) :=
      ([π c]₀ : R₀[IsLocalRing.ResidueField A](G))
    have hE :
        E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (χ x)) =
          E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
      calc
        E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (χ x))
            =
          cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) := by
              exact (cartanCokernelToCanonicalVirtualModularCartanProduct_mk
                (p := p) (A := A) (K := K) (G := G) x).symm
        _ =
          regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk'
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) := by
              simpa [brauerPointMassCanonicalProductIdentity, f, x] using (hprod c).symm
        _ =
          E
            (Submodule.Quotient.mk
              (p := canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G))
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
              exact
                (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_mk_regularIntegerFunctionCast
                    (p := p) (A := A) (K := K) (G := G) f).symm
    have hquot :=
      E.injective hE
    have hsource :
        χ x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G) := by
      exact
        (Submodule.Quotient.eq
          (canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))).mp hquot
    simpa [brauerPointMassSourceCongruence, χ, x, f,
      canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G)] using hsource
  · intro hsource c
    let f : PRegularConjClass G p → ℤ :=
      Pi.single c (1 : ℤ)
    let x : R₀[IsLocalRing.ResidueField A](G) :=
      ([π c]₀ : R₀[IsLocalRing.ResidueField A](G))
    have hcanonical :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f -
          χ x ∈
            canonicalVirtualModularCartanRangeASpan
              (p := p) (A := A) (K := K) (G := G) := by
      have hD :
          χ x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              regularValueDivisibilitySubmodule
                (p := p) (A := A) (K := K) (G := G) := by
        simpa [brauerPointMassSourceCongruence, χ, x, f] using hsource c
      have hneg :=
        (regularValueDivisibilitySubmodule
          (p := p) (A := A) (K := K) (G := G)).neg_mem hD
      simpa [χ, x, f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
          (p := p) (A := A) (K := K) (G := G)] using hneg
    exact
      regularIntegerDiagonalQuotientToIntegerImageProduct_eq_canonicalVirtualModularCartanProduct_of_source_congruence
          (p := p) (A := A) (K := K) (G := G) f x hcanonical

/-- The point-mass product identity closes the exact quotient identity reported for the
fixed-coordinate Brauer map. -/
theorem brauerReprPointMassQuotientIdentity_of_canonicalProductIdentity
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hprod :
      brauerPointMassCanonicalProductIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerReprPointMassQuotientIdentity
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  have hsource :
      brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :=
    (brauerPointMassCanonicalProductIdentity_iff_source_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hprod
  have hcartan :=
    (brauerPointMassSourceCongruence_iff_brauerRepr_pointMass_cartanSpan_congruence
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hsource
  exact
    (brauerRepr_pointMass_cartanSpan_congruence_iff_quotient_identity
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hcartan

/-- The reported quotient identity is equivalent to the point-mass product identity above. -/
theorem brauerReprPointMassQuotientIdentity_iff_canonicalProductIdentity
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerReprPointMassQuotientIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      brauerPointMassCanonicalProductIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hquot
    have hcartan :=
      (brauerRepr_pointMass_cartanSpan_congruence_iff_quotient_identity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hquot
    have hsource :
        brauerPointMassSourceCongruence
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :=
      (brauerPointMassSourceCongruence_iff_brauerRepr_pointMass_cartanSpan_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hcartan
    exact
      (brauerPointMassCanonicalProductIdentity_iff_source_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hsource
  · exact
      brauerReprPointMassQuotientIdentity_of_canonicalProductIdentity
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

end BrauerReprPointMassEndpoint

end Representation
