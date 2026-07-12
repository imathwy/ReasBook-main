import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanFormalRangeSourceProductTransport
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeSourceCongruenceTransport

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeSourceCongruenceTransportFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeSourceCongruenceTransportDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Final transport adapter specialized to the canonical source-congruence endpoint.

This is the maximally source-faithful split of the remaining Serre 18.5(b) input: for each full
mixed-characteristic model, it is enough to prove the two source-quotient congruences between
virtual modular characters and integer regular-class functions. No fixed Cartan column or fixed
point-mass witness is chosen here. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceCongruences
    (hsource :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          canonicalVirtualModularCartanProductImageSourceCongruences
            (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_source_congruences
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

include p in
/-- Final transport adapter with the source-congruence endpoint split into the forward
regular-value congruence and the reverse source congruence.

The forward half says actual virtual modular character values have the intended integer
representatives modulo Serre's divisibility lattice. The reverse half says each integer
regular-class function has some virtual modular representative modulo the canonical Cartan source
span. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_forwardAndReverseSource
    (hforward :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∀ x : R₀[IsLocalRing.ResidueField A](G),
            virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
                regularValueDivisibilitySubmodule
                  (p := p) (A := A) (K := K) (G := G))
    (hreverse :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∀ g : PRegularConjClass G p → ℤ,
            ∃ x : R₀[IsLocalRing.ResidueField A](G),
              regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
                virtualModularCharacterOnPRegularConjClass
                  (p := p) (A := K) (G := G)
                  (PrimeToPRoot.toFieldLift
                    (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
                  canonicalVirtualModularCartanRangeASpan
                    (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_source_congruence
      (p := p) (A := A) (K := K) (G := G)
      (hforward (A := A) (K := K) e0)
      (hreverse (A := A) (K := K) e0)

include p in
/-- Final transport adapter with the reverse source-congruence endpoint reduced to point masses.

This is the maximally parallel split of the remaining source-product route: the forward
regular-value congruence and the reverse point-mass existential witnesses can be proved
independently. The reverse witnesses are not fixed to any chosen simple class. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_forwardAndReversePointSource
    (hforward :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∀ x : R₀[IsLocalRing.ResidueField A](G),
            virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
                regularValueDivisibilitySubmodule
                  (p := p) (A := A) (K := K) (G := G))
    (hpoint :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          canonicalVirtualModularCartanProductReversePointSourceCongruence
            (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_point_source_congruence
      (p := p) (A := A) (K := K) (G := G)
      (hforward (A := A) (K := K) e0)
      (hpoint (A := A) (K := K) e0)

include p in
/-- Final transport adapter specialized to the global regular-value congruence endpoint.

This is the smallest formal input left by the canonical source-product route: for each full
mixed-characteristic model, actual virtual modular characters must be congruent to their integer
regular-class coordinate functions modulo Serre's divisibility lattice. The reverse representative
side is then formal, by applying the same congruence to the virtual character with prescribed
regular-class coordinates. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_regularValueCongruence
    (hforward :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∀ x : R₀[IsLocalRing.ResidueField A](G),
            virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
                regularValueDivisibilitySubmodule
                  (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence
      (p := p) (A := A) (K := K) (G := G)
      (hforward (A := A) (K := K) e0)

include p in
/-- Final transport adapter from a normalized Brauer-family point-mass source congruence.

This keeps the strongest remaining basis-vector input explicit: for each full mixed-characteristic
model, one must exhibit a coordinate-normalized Brauer family whose basis vectors satisfy the
source-side point-mass congruence. The theorem only transports that input through the existing
forward regular-value endpoint. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_brauerPointMassSource
    (hsource :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
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
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_regularValueCongruence
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    regularValueCongruence_of_exists_brauerPointMassSourceCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hsource (A := A) (K := K) e0)

end CartanFormalRangeSourceCongruenceTransport

end Representation
