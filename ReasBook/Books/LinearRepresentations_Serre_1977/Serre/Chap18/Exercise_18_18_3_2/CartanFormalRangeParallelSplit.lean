import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassCoordinateProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanDetProductProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanDetSmithProductEquiv
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanDetProductSpanProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanFormalRangeCokernelProductEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateSpanProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeParallelSplit

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeParallelSplitFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeParallelSplitDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The point-mass coordinate divisibility blocker is exactly the full mixed-model
Brauer-basis readback input used by the source-faithful 18.5(a) endpoint. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_pointMassCoordinateDivisibilityBlocker
    (hpoint :
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)).2
      (hpoint (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model readback gives the full mixed-model regular-value source statement used by
the non-cyclic determinant/product route. -/
theorem fullMixedModelRegularValueSourceStatement_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

/-- Parallel source-faithful endpoint for the last formal Cartan-range support theorem.

The two inputs are independent:
* `hread` is the Serre 18.5(a) readback/divisibility task.
* `hsmith` is the Serre 18.5(b) determinant/cardinality task in Smith-product form.
-/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerReadback_and_smithProduct
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G))
    (hsmith :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
          (p := p) (A := A) (K := K) (G := G)
          (hread (A := A) (K := K) e0)
  have hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      rcases
          exists_coordinate_normalized_complete_family_with_projective_envelopes
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
        ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
      rcases hsmith (A := A) (K := K) e0 with ⟨b, hfull, hprod⟩
      refine
        ⟨PRegularConjClass G p, inferInstance, inferInstance,
          π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
      exact
        cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_smithNormalFormCoeffProduct
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
          b hfull hprod π hπ_pairwise hπ_complete P hP_envelope
  have hproduct :
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
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cokernelProduct_endpoint
      (p := p) (k := k) (G := G)
      (by
        intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
          _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
          _instAlgClosed _instCharP e0
        exact hproduct (A := A) (K := K) e0)

/-- Same endpoint with the 18.5(a) task stated in its point-mass coordinate form. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointMassCoordinateDivisibility_and_smithProduct
    (hpoint :
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G))
    (hsmith :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPointMassCoordinateDivisibility
          (p := p) (A := A) (K := K) (G := G)).2
          (hpoint (A := A) (K := K) e0)
  have hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)
  have hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
    rcases hsmith (A := A) (K := K) e0 with ⟨b, hfull, hprod⟩
    refine
      ⟨PRegularConjClass G p, inferInstance, inferInstance,
        π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
    exact
      cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_smithNormalFormCoeffProduct
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)
        b hfull hprod π hπ_pairwise hπ_complete P hP_envelope
  have hproduct :
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
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cokernelProduct_endpoint
      (p := p) (k := k) (G := G)
      (by
        intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
          _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
          _instAlgClosed _instCharP e0
        exact hproduct (A := A) (K := K) e0)

/-- Parallel endpoint with the 18.5(b) task stated in determinant-product form. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerReadback_and_detProduct
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G))
    (hdet : fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hsmith :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement
        (p := p) (k := k) (G := G) :=
    @fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
      p k inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hdet (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerReadback_and_smithProduct
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hread (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hsmith (A := A) (K := K) e0)

/-- Parallel endpoint with 18.5(a) in point-mass form and 18.5(b) in determinant-product form. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointMassCoordinateDivisibility_and_detProduct
    (hpoint :
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G))
    (hdet : fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hsmith :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement
        (p := p) (k := k) (G := G) :=
    @fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
      p k inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hdet (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointMassCoordinateDivisibility_and_smithProduct
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hpoint (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hsmith (A := A) (K := K) e0)

/-- Parallel endpoint with the 18.5(b) task stated as the source-side Cartan-coordinate span. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerReadback_and_projectiveCartanCoordinateSpan
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G))
    (hspan :
      fullMixedModelProjectiveCartanCoordinateSpanStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) :=
    @fullMixedModelCartanDetNatAbsProductStatement_of_projectiveCartanCoordinate_span
      p k inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hspan (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerReadback_and_detProduct
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hread (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hdet (A := A) (K := K) e0)

/-- Same source-span endpoint with the 18.5(a) task in point-mass coordinate form. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointMassCoordinateDivisibility_and_projectiveCartanCoordinateSpan
    (hpoint :
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G))
    (hspan :
      fullMixedModelProjectiveCartanCoordinateSpanStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) :=
    @fullMixedModelCartanDetNatAbsProductStatement_of_projectiveCartanCoordinate_span
      p k inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hspan (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointMassCoordinateDivisibility_and_detProduct
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hpoint (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hdet (A := A) (K := K) e0)

/-- Final maximum-parallel endpoint: the two remaining source-faithful inputs are independent.

* `hresidual` is the Brauer point-mass residual row-difference from Serre 18.5(a).
* `hforward` is the forward fixed-coordinate diagonal congruence needed for the source-span part
  of Serre 18.5(b).
-/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_residualPointMass_and_forwardDiagonal
    (hresidual :
      fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G))
    (hforward :
      fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hpoint :
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) :=
    (fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_coordinateDivisibilityBlocker
      (p := p) (k := k) (G := G)).1 hresidual
  have hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        (regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_existsPointMassCoordinateDivisibility
          (p := p) (A := A) (K := K) (G := G)).2
          (hpoint (A := A) (K := K) e0)
  have hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
          (p := p) (A := A) (K := K) (G := G)
          (hread (A := A) (K := K) e0)
  have hspan :
      fullMixedModelProjectiveCartanCoordinateSpanStatement
        (p := p) (k := k) (G := G) :=
    @fullMixedModelProjectiveCartanCoordinateSpanStatement_of_regularValue_and_forwardDiagonal
      p k inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hregular (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hforward (A := A) (K := K) e0)
  exact
    @existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointMassCoordinateDivisibility_and_projectiveCartanCoordinateSpan
      p k inferInstance inferInstance inferInstance G inferInstance inferInstance inferInstance
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hpoint (A := A) (K := K) e0)
      (fun {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
          [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
          [HasEnoughRootsOfUnity K (Monoid.exponent G)]
          [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
          (e0 : IsLocalRing.ResidueField A ≃+* k) =>
        hspan (A := A) (K := K) e0)

end CartanFormalRangeParallelSplit

end Representation
