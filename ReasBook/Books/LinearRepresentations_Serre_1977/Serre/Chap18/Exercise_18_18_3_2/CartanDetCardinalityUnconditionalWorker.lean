import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCoordinateDivisibilityClosureWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelProductSourceProof

/-!
Determinant/cardinality packaging below the remaining regular-value source input.

This worker does not use the final formal range theorem, the final cokernel-product theorem, or
point-mass Brauer-character assumptions.  It records that the determinant/cardinality side is
closed by the current p-primary saturation route as soon as the source-faithful regular-value
congruence is available.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanDetCardinalityUnconditionalWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanDetCardinalityUnconditionalWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanDetCardinalityUnconditionalWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model determinant/cardinality statement.

This is the unconditional determinant side: after choosing any coordinate-normalized complete
family with projective envelopes, the absolute Cartan determinant is the cardinality of the
Cartan cokernel.  The remaining product assertion is exactly the separate cardinality comparison
with the integer diagonal quotient image. -/
def fullMixedModelCartanDetNatAbsCokernelCardinalityStatement : Prop :=
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
          Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G)

omit [IsAlgClosed k] [CharP k p] in
/-- The determinant/cardinality side is unconditional in every full mixed model. -/
theorem fullMixedModelCartanDetNatAbsCokernelCardinalityStatement_proof :
    fullMixedModelCartanDetNatAbsCokernelCardinalityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP _e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  refine
    ⟨PRegularConjClass G p, inferInstance, inferInstance,
      π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    cartanMatrix_det_natAbs_eq_cartanCokernel_natCard
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope

omit [IsAlgClosed k] [CharP k p] in
/-- Cardinality comparison directly gives the requested determinant/product statement.

This is the direct one-way determinant/cardinality adapter: it uses the unconditional
`|det Cartan| = Nat.card (cartanCokernel ...)` theorem and the intrinsic cardinality of the
integer diagonal quotient image, without passing through an equivalence wrapper. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_cokernelCardinality
    (hcard :
      fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      fullMixedModelCartanDetNatAbsCokernelCardinalityStatement_proof
        (p := p) (k := k) (G := G) (A := A) (K := K) e0 with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, P, hP_envelope,
      hdet_card⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  refine
    ⟨ι, instFintype, instDecidableEq,
      π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  calc
    Int.natAbs
        (Matrix.det
          (cartanMatrix (IsLocalRing.ResidueField A) G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete))) =
        Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) := hdet_card
    _ =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range :=
      hcard (A := A) (K := K) e0
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 :=
      regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_eq_prod
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The regular-value source statement closes the determinant product through the p-primary
saturation route. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) :=
  @fullMixedModelCartanDetNatAbsProductStatement_of_regularValue_pPrimarySaturationSource.{u}
    p k inferInstance G inferInstance inferInstance inferInstance hregular

omit [IsAlgClosed k] [CharP k p] in
/-- The regular-value source statement closes the requested Cartan-cokernel cardinality
statement via the determinant product. -/
theorem fullMixedModelCartanCokernelCardinalityStatement_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hdetFull :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) :=
    @fullMixedModelCartanDetNatAbsProductStatement_of_regularValueSource.{u}
      p k inferInstance G inferInstance inferInstance inferInstance hregular
  rcases hdetFull (A := A) (K := K) e0 with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, P, hP_envelope,
      hdet_model⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  exact
    cartanCokernel_natCard_eq_regularIntegerImageRange_of_cartanMatrix_det_natAbs_eq_prod
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hdet_model

omit [IsAlgClosed k] [CharP k p] in
/-- The regular-value source statement closes the requested Cartan-cokernel product statement:
the same source input gives the determinant product, and the existing source-faithful product
adapter then applies. -/
theorem fullMixedModelCartanCokernelProductStatement_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  have hdetFull :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) :=
    @fullMixedModelCartanDetNatAbsProductStatement_of_regularValueSource.{u}
      p k inferInstance G inferInstance inferInstance inferInstance hregular
  rcases hdetFull (A := A) (K := K) e0 with
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

end CartanDetCardinalityUnconditionalWorker

end Representation
