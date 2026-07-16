import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSaturation
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanRingEquivTransport

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelProductRegularValueEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanCokernelProductRegularValueEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelProductRegularValueEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Canonical source-product endpoint for Serre 18.5(b) in cokernel-product form.

The only mathematical input is the global regular-value congruence: every descended virtual
modular character is congruent to its integer regular-class coordinate function modulo Serre's
divisibility lattice. The reverse image containment is then formal, using the same congruence on
the virtual character with prescribed regular-class coordinates. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_regularValue_congruence
    (hregular :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence
      (p := p) (A := A) (K := K) (G := G) hregular)

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Per-model product input from the fixed source-span equality.

This is the direct non-cyclic residue-field product route: once the mixed-characteristic Cartan
coordinate `A`-span is identified with Serre's regular divisibility lattice, the already-proved
integer saturation argument gives the abstract Cartan-cokernel product. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_projectiveCartanCoordinate_span_eq
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

end CartanCokernelProductRegularValueEndpoint

section CartanCokernelProductRegularValueTransport

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelProductRegularValueTransportFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelProductRegularValueTransportDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
include p in
/-- Full mixed-characteristic residue-field product input obtained from the regular-value
congruence for each mixed model. -/
theorem cartanCokernel_fullMixedModelProductInput_of_regularValue_congruence
    (hregular :
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
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (e0 : IsLocalRing.ResidueField A ≃+* k) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_regularValue_congruence
    (p := p) (A := A) (K := K) (G := G)
    (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
include p in
/-- Full mixed-characteristic residue-field product input obtained from the source-span equality
for each full mixed model. -/
theorem cartanCokernel_fullMixedModelProductInput_of_projectiveCartanCoordinate_span_eq
    (hspan :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) =
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (e0 : IsLocalRing.ResidueField A ≃+* k) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_projectiveCartanCoordinate_span_eq
    (p := p) (A := A) (K := K) (G := G)
    (hspan (A := A) (K := K) e0)

include p in
/-- Transported cokernel-product endpoint over the requested algebraically closed field.

This theorem is intentionally conditional on the same regular-value congruence over every full
mixed-characteristic model. It avoids the `CartanFormalRange` support theorem and transports only
the abstract cokernel product across the residue-field equivalence. -/
theorem cartanCokernel_product_via_fullMixedModel_regularValue_congruence
    (hregular :
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
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  classical
  obtain ⟨A, instComm, instLocal, instHenselian, instDomain, instDVR, instNoeth,
      instComplete, K, instField, instAlg, instFrac, instCharZero, instRoots, ⟨e0⟩⟩ :=
    existsFullMixedCharacteristicModel_with_all_roots (p := p) (k := k) (G := G)
  letI : CommRing A := instComm
  letI : IsLocalRing A := instLocal
  letI : HenselianLocalRing A := instHenselian
  letI : IsDomain A := instDomain
  letI : IsDiscreteValuationRing A := instDVR
  letI : IsNoetherianRing A := instNoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := instComplete
  letI : Field K := instField
  letI : Algebra A K := instAlg
  letI : IsFractionRing A K := instFrac
  letI : CharZero K := instCharZero
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) := instRoots
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) :=
    IsAlgClosed.of_ringEquiv k (IsLocalRing.ResidueField A) e0.symm
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    charP_of_injective_ringHom
      (R := k) (A := IsLocalRing.ResidueField A) (f := e0.symm.toRingHom)
      e0.symm.injective p
  exact
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_transport_of_ringEquiv
      (p := p) (G := G) e0
      (cartanCokernel_fullMixedModelProductInput_of_regularValue_congruence
        (p := p) (k := k) (G := G) hregular (A := A) (K := K) e0)

include p in
/-- Transported cokernel-product endpoint from the source-span equality over every full mixed
model.

This theorem deliberately exposes the span equality as the remaining input; it does not use the
placeholder support theorem in `CartanFormalRange.lean` or the downstream cyclic product theorem. -/
theorem cartanCokernel_product_via_fullMixedModel_projectiveCartanCoordinate_span_eq
    (hspan :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) =
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  classical
  obtain ⟨A, instComm, instLocal, instHenselian, instDomain, instDVR, instNoeth,
      instComplete, K, instField, instAlg, instFrac, instCharZero, instRoots, ⟨e0⟩⟩ :=
    existsFullMixedCharacteristicModel_with_all_roots (p := p) (k := k) (G := G)
  letI : CommRing A := instComm
  letI : IsLocalRing A := instLocal
  letI : HenselianLocalRing A := instHenselian
  letI : IsDomain A := instDomain
  letI : IsDiscreteValuationRing A := instDVR
  letI : IsNoetherianRing A := instNoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := instComplete
  letI : Field K := instField
  letI : Algebra A K := instAlg
  letI : IsFractionRing A K := instFrac
  letI : CharZero K := instCharZero
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) := instRoots
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) :=
    IsAlgClosed.of_ringEquiv k (IsLocalRing.ResidueField A) e0.symm
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    charP_of_injective_ringHom
      (R := k) (A := IsLocalRing.ResidueField A) (f := e0.symm.toRingHom)
      e0.symm.injective p
  exact
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_transport_of_ringEquiv
      (p := p) (G := G) e0
      (cartanCokernel_fullMixedModelProductInput_of_projectiveCartanCoordinate_span_eq
        (p := p) (k := k) (G := G) hspan (A := A) (K := K) e0)

end CartanCokernelProductRegularValueTransport

end Representation
