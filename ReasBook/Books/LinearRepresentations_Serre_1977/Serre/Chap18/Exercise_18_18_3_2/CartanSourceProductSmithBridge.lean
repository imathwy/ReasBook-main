import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSmith
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSaturation
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSpanStability
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProduct
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegralQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanSourceProductSmithBridge

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local instance cartanSourceProductSmithBridgeFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanSourceProductSmithBridgeDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Source-product/Smith bridge once the remaining integer lattice descent is supplied as the
fixed-coordinate Cartan `A`-span equality.  The proof intentionally factors through the cokernel
product and `existsCartanRangeCoordinateEquiv_of_cokernelProduct`, rather than diagonalizing a
fixed Cartan matrix. -/
theorem cartanCokernelProduct_of_projectiveCartanCoordinate_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq
    (p := p) (A := A) (K := K) (G := G) hspan

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- The Smith endpoint of the source-product route, assuming exactly the missing integral
descent from the Cartan coordinate `A`-span to Serre's regular divisibility lattice. -/
theorem existsCartanRangeCoordinateEquiv_of_projectiveCartanCoordinate_span_eq_via_cokernelProduct
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_cokernelProduct
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCokernelProduct_of_projectiveCartanCoordinate_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)

/-- Equivalent source-side formulation of the remaining descent: the Brauer-coordinate change of
basis used to compare projective characters with fixed regular-class coordinates must preserve
Serre's coordinatewise divisibility lattice. -/
theorem cartanCokernelProduct_of_brauerRepr_regularValueDivisibility_stable
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hstable :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  exact
    cartanCokernelProduct_of_projectiveCartanCoordinate_span_eq
      (p := p) (A := A) (K := K) (G := G)
      (projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_brauerRepr_stable
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hstable)

/-- Smith endpoint from the Brauer-stability form of the missing source-product descent. -/
theorem existsCartanRangeCoordinateEquiv_of_brauerRepr_regularValueDivisibility_stable
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hstable :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_cokernelProduct
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCokernelProduct_of_brauerRepr_regularValueDivisibility_stable
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hstable)

end CartanSourceProductSmithBridge

end Representation
