import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelCardinalitySourceFaithful
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelProductSourceProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelProductSourceProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelProductSourceProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model regular-value input used by the source-faithful product route.

This is the forward congruence supplied by the 18.5(a) side of the argument. -/
def fullMixedModelRegularValueSourceStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)

/-- Determinant product input for one complete simple family and compatible projective-envelope
family in each full mixed model.

This is the non-cyclic determinant/cardinality side: it does not use the final range theorem or
the final cokernel-product theorem. -/
def fullMixedModelCartanDetNatAbsProductStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ ι : Type u,
      ∃ instFintype : Fintype ι,
      ∃ instDecidableEq : DecidableEq ι,
      letI : Fintype ι := instFintype
      letI : DecidableEq ι := instDecidableEq
      ∃ π : ι → FDRep (IsLocalRing.ResidueField A) G,
      ∃ hπ_pairwise : PairwiseNonisomorphic π,
      ∃ hπ_complete : IsCompleteIrreducibleFamily π,
      ∃ P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
      ∃ hP_envelope :
        ∀ i, ∃ f : (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
          f.IsProjectiveEnvelope,
        Int.natAbs
            (Matrix.det
              (cartanMatrix (IsLocalRing.ResidueField A) G
                (projectiveEnvelope_classes_basis_of_complete_family
                  π hπ_pairwise hπ_complete P hP_envelope)
                (simple_finiteRep_classes_basis_of_complete_family
                  π hπ_pairwise hπ_complete))) =
          ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1

/-- The per-model cardinality statement requested in the determinant/cardinality formulation. -/
def fullMixedModelCartanCokernelCardinalityStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range

/-- The per-model cokernel-product statement requested in the product formulation. -/
def fullMixedModelCartanCokernelProductStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))

omit [IsAlgClosed k] [CharP k p] in
/-- Determinant product input gives the requested cardinality equality in every full mixed
model. -/
theorem fullMixedModelCartanCokernelCardinality_of_detProduct
    (hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hdet (A := A) (K := K) e0 with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, P, hP_envelope,
      hdet_model⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  exact
    cartanCokernel_natCard_eq_regularIntegerImageRange_of_cartanMatrix_det_natAbs_eq_prod
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hdet_model

omit [IsAlgClosed k] [CharP k p] in
/-- Source-faithful forward congruence plus the determinant product input gives the requested
cokernel-product statement in every full mixed model.

This is the non-circular product/cardinality route: the product is obtained from the
regular-value inclusion and the determinant/cardinality equality, not from the final product or
range theorem. -/
theorem fullMixedModelCartanCokernelProduct_of_regularValue_and_detProduct
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hdet (A := A) (K := K) e0 with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, P, hP_envelope,
      hdet_model⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  exact
    cartanCokernel_product_of_regularValue_and_detProduct
      (p := p) (A := A) (K := K) (G := G)
      (by
        simpa [regularValueCongruenceSourceFaithfulStatement] using
          hregular (A := A) (K := K) e0)
      π hπ_pairwise hπ_complete P hP_envelope hdet_model

end CartanCokernelProductSourceProof

end Representation
