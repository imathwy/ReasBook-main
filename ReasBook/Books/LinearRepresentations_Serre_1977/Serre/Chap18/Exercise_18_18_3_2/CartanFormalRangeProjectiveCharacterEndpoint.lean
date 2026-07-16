import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelProductSourceProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeCokernelProductEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelProductFromQuotient
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCokernelProductImage
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageBasisCriteria
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateSpanProducer
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanFormalRangeProjectiveCharacterEndpoint

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeProjectiveCharacterEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeProjectiveCharacterEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Non-fixed-coordinate product-range input for the projective-character route.

For each full mixed-characteristic model, the already available projective-character quotient
product gives an `A`-linear equivalence from the Cartan-coordinate `A`-span quotient to the
displayed product of fraction-field quotients. The extra input isolated here is exactly that the
actual finite image of the integral Cartan cokernel inside that product is the expected finite
`ZMod` product.

This statement does not mention the fixed `regularClassCoordinateAddEquiv` range equality. -/
def fullMixedModelProjectiveCartanProductRangeStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ e :
        ((PRegularConjClass G p → K) ⧸
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K))) ≃ₗ[A]
          ∀ c : PRegularConjClass G p,
            K ⧸ Submodule.span A
              ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K),
        Nonempty
          ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G) e).range ≃+
            ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))

/-- Full mixed-model source-quotient product image input.

This is the strictly smaller finite-image statement below the `ZMod` product range: the projective
Cartan product range is identified only with the coordinatewise integer image. -/
def fullMixedModelProjectiveCartanSourceQuotientProductImageStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      projectiveCartanSourceQuotientProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)

/-- Full mixed-model one-sided finite-image criterion.

The two components are maximally parallel: construct one projective Cartan product equivalence whose
actual finite image is contained in the coordinatewise integer image, and separately prove the
Cartan-cokernel cardinality equality. -/
def fullMixedModelProjectiveCartanProductFiniteImageCriterionStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      projectiveCartanSourceQuotientProductFiniteImageCriterion
        (p := p) (A := A) (K := K) (G := G)

/-- Full mixed-model forward image inclusion, separated from the determinant/cardinality side. -/
def fullMixedModelProjectiveCartanProductForwardImageStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ e :
        ((PRegularConjClass G p → K) ⧸
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K))) ≃ₗ[A]
          ∀ c : PRegularConjClass G p,
            K ⧸ Submodule.span A
              ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K),
        (cartanCoordinateRangeQuotientToProjectiveCartanProduct
            (p := p) (A := A) (K := K) (G := G) e).range ≤
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range

/-- Basis-vector form of the projective Cartan product forward image inclusion.

For one coordinate-normalized Brauer family, every inverse-Brauer transform of an integer point
mass has an integer representative modulo Serre's regular-value divisibility lattice. By linearity
this gives the forward inclusion of the whole finite projective product range. -/
def fullMixedModelProjectiveCartanProductBrauerInverseForwardBasisStatement : Prop :=
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
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        ∀ i : PRegularConjClass G p,
          ∃ g : PRegularConjClass G p → ℤ,
            (projectiveCartanASpanBrauerReprLinearEquiv
                (p := p) (A := A) (K := K) (G := G)
                π hπ_simple hπ_coord).symm
                (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (Pi.single i (1 : ℤ))) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
                regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The source-faithful regular-value congruence gives the product-range forward basis input.

The integer representative in the weaker forward-basis statement is the same point mass supplied
by the existing inverse-Brauer point-mass form of the regular-value congruence. -/
theorem
    fullMixedModelProjectiveCartanProductBrauerInverseForwardBasisStatement_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductBrauerInverseForwardBasisStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      (regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerInversePointMassInput
        (p := p) (A := A) (K := K) (G := G)).1
        (hregular (A := A) (K := K) e0) with
    ⟨π, hπ_simple, hπ_coord, hpoint⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro i
  exact ⟨Pi.single i (1 : ℤ), hpoint i⟩

omit [IsAlgClosed k] [CharP k p] in
/-- The basis-vector inverse-Brauer integrality condition gives the forward image inclusion. -/
theorem fullMixedModelProjectiveCartanProductForwardImageStatement_of_brauerInverseForwardBasis
    (hbasis :
      fullMixedModelProjectiveCartanProductBrauerInverseForwardBasisStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductForwardImageStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hbasis (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hbasis_model⟩
  let e :=
    projectiveCartanCoordinateASpanQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  refine ⟨e, ?_⟩
  let φ :=
    cartanCoordinateRangeQuotientToProjectiveCartanProduct
      (p := p) (A := A) (K := K) (G := G) e
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  have hsub :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    brauerInverse_forward_integerSubmodule_of_basis
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis_model
  have hrep :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G) e
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) :=
    concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_integerSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hsub
  refine addMonoidHom_range_le_range_of_representatives φ ψ ?_
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro f
  rcases hrep f with ⟨g, hg⟩
  exact
    ⟨QuotientAddGroup.mk'
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g, by
        simpa [φ, ψ, e] using hg⟩

omit [IsAlgClosed k] [CharP k p] in
/-- The source-faithful regular-value congruence gives the projective product forward inclusion.
-/
theorem fullMixedModelProjectiveCartanProductForwardImageStatement_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductForwardImageStatement (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCartanProductForwardImageStatement_of_brauerInverseForwardBasis
    (p := p) (k := k) (G := G)
    (fullMixedModelProjectiveCartanProductBrauerInverseForwardBasisStatement_of_regularValueSource
      (p := p) (k := k) (G := G) hregular)

omit [IsAlgClosed k] [CharP k p] in
/-- The one-sided finite-image criterion packages a source-quotient image match. -/
theorem fullMixedModelProjectiveCartanSourceQuotientProductImageStatement_of_finiteImageCriterion
    (hfinite :
      fullMixedModelProjectiveCartanProductFiniteImageCriterionStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanSourceQuotientProductImageStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanSourceQuotientProductImageMatchesIntegerImage_of_finiteImageCriterion
      (p := p) (A := A) (K := K) (G := G)
      (hfinite (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Forward inclusion plus the Cartan-cokernel cardinality equality gives the finite-image
criterion in every full mixed model. -/
theorem fullMixedModelProjectiveCartanProductFiniteImageCriterion_of_forwardImage_and_cardinality
    (hforward :
      fullMixedModelProjectiveCartanProductForwardImageStatement
        (p := p) (k := k) (G := G))
    (hcard :
      fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductFiniteImageCriterionStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hforward (A := A) (K := K) e0 with ⟨e, hrange⟩
  exact ⟨e, hrange, hcard (A := A) (K := K) e0⟩

omit [IsAlgClosed k] [CharP k p] in
/-- Source-quotient image match gives the requested projective Cartan product range. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_sourceQuotientProductImage
    (himage :
      fullMixedModelProjectiveCartanSourceQuotientProductImageStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanProductRange_nonempty_addEquiv_pi_of_sourceQuotientProduct
      (p := p) (A := A) (K := K) (G := G)
      (himage (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- One-sided finite-image criterion gives the requested projective Cartan product range. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_finiteImageCriterion
    (hfinite :
      fullMixedModelProjectiveCartanProductFiniteImageCriterionStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCartanProductRangeStatement_of_sourceQuotientProductImage
    (p := p) (k := k) (G := G)
    (fullMixedModelProjectiveCartanSourceQuotientProductImageStatement_of_finiteImageCriterion
      (p := p) (k := k) (G := G) hfinite)

omit [IsAlgClosed k] [CharP k p] in
/-- Parallel finite-image endpoint: forward image inclusion plus determinant/cardinality data close
the projective product-range statement. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_forwardImage_and_cardinality
    (hforward :
      fullMixedModelProjectiveCartanProductForwardImageStatement
        (p := p) (k := k) (G := G))
    (hcard :
      fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCartanProductRangeStatement_of_finiteImageCriterion
    (p := p) (k := k) (G := G)
    (fullMixedModelProjectiveCartanProductFiniteImageCriterion_of_forwardImage_and_cardinality
      (p := p) (k := k) (G := G) hforward hcard)

omit [IsAlgClosed k] [CharP k p] in
/-- Source-faithful regular-value congruence plus the Cartan-cokernel cardinality equality close
the projective product-range finite-image statement. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_regularValue_and_cardinality
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hcard :
      fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCartanProductRangeStatement_of_forwardImage_and_cardinality
    (p := p) (k := k) (G := G)
    (fullMixedModelProjectiveCartanProductForwardImageStatement_of_regularValueSource
      (p := p) (k := k) (G := G) hregular)
    hcard

omit [IsAlgClosed k] [CharP k p] in
/-- Source-faithful regular-value congruence plus the determinant product close the projective
product-range finite-image statement. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_regularValue_and_detProduct
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) := by
  refine
    fullMixedModelProjectiveCartanProductRangeStatement_of_regularValue_and_cardinality
      (p := p) (k := k) (G := G) hregular ?_
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
/-- Brauer-basis readback plus the Cartan-cokernel cardinality equality close the projective
product-range finite-image statement. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_brauerBasisReadback_and_cardinality
    (hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G))
    (hcard :
      fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) := by
  refine
    fullMixedModelProjectiveCartanProductRangeStatement_of_regularValue_and_cardinality
      (p := p) (k := k) (G := G) ?_ hcard
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Brauer-basis readback plus the determinant product close the projective product-range
finite-image statement. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_brauerBasisReadback_and_detProduct
    (hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G))
    (hdet :
      fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) := by
  have hcard :
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
  have hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)
  exact
    @fullMixedModelProjectiveCartanProductRangeStatement_of_regularValue_and_cardinality
      p k inferInstance G inferInstance inferInstance inferInstance hregular hcard

omit [IsAlgClosed k] [CharP k p] in
/-- Basis-vector inverse-Brauer integrality plus determinant/cardinality data close the
product-range finite-image statement. -/
theorem
    fullMixedModelProjectiveCartanProductRangeStatement_of_brauerInverseForwardBasis_and_cardinality
    (hbasis :
      fullMixedModelProjectiveCartanProductBrauerInverseForwardBasisStatement
        (p := p) (k := k) (G := G))
    (hcard :
      fullMixedModelCartanCokernelCardinalityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) :=
  fullMixedModelProjectiveCartanProductRangeStatement_of_forwardImage_and_cardinality
    (p := p) (k := k) (G := G)
    (fullMixedModelProjectiveCartanProductForwardImageStatement_of_brauerInverseForwardBasis
      (p := p) (k := k) (G := G) hbasis)
    hcard

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-Cartan product-range input is just the cokernel-product statement transported
across the unconditional quotient-product equivalence.

This direction is useful for checking that the new endpoint has the same strength as the existing
abstract cokernel-product endpoint, while keeping the range statement away from the fixed
coordinate readback. -/
theorem fullMixedModelProjectiveCartanProductRangeStatement_of_cokernelProduct
    (hproduct :
      fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      fullMixedModelProjectiveCartanCoordinateQuotientProductStatement_proof
        (p := p) (k := k) (G := G) (A := A) (K := K) e0 with
    ⟨e⟩
  refine ⟨e, ?_⟩
  rcases hproduct (A := A) (K := K) e0 with ⟨hproduct_model⟩
  exact
    ⟨(cartanCokernel_addEquiv_projectiveCartanProductRange
        (p := p) (A := A) (K := K) (G := G) e).symm.trans hproduct_model⟩

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-Cartan product-range input gives the full mixed-model cokernel product. -/
theorem fullMixedModelCartanCokernelProductStatement_of_projectiveCartanProductRange
    (hrange :
      fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hrange (A := A) (K := K) e0 with ⟨e, himage⟩
  exact
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_projectiveCartanProductRange
      (p := p) (A := A) (K := K) (G := G) e himage

set_option linter.style.longLine false in
/-- Non-circular endpoint for the support theorem in `CartanFormalRange.lean`.

The route is:
projective-character quotient product range input `→` full mixed-model Cartan cokernel product
`→` Smith/invariant-factor adapter `→` existence of some regular-class coordinate equivalence.
No fixed-coordinate Cartan range equality is used. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterProductRange
    (hrange :
      fullMixedModelProjectiveCartanProductRangeStatement (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cokernelProduct_endpoint
      (p := p) (k := k) (G := G) ?_
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    fullMixedModelCartanCokernelProductStatement_of_projectiveCartanProductRange
      (p := p) (k := k) (G := G) hrange (A := A) (K := K) e0

include p in
/-- Cokernel-product specialization of the same endpoint.

This is the shortest one-line replacement available once the non-fixed-coordinate product side
has been proved independently. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterCokernelProduct
    (hproduct :
      fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterProductRange
      (p := p) (k := k) (G := G) ?_
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      fullMixedModelProjectiveCartanCoordinateQuotientProductStatement_proof
        (p := p) (k := k) (G := G) (A := A) (K := K) e0 with
    ⟨e⟩
  refine ⟨e, ?_⟩
  rcases hproduct (A := A) (K := K) e0 with ⟨hproduct_model⟩
  exact
    ⟨(cartanCokernel_addEquiv_projectiveCartanProductRange
        (p := p) (A := A) (K := K) (G := G) e).symm.trans hproduct_model⟩

end CartanFormalRangeProjectiveCharacterEndpoint

end Representation
