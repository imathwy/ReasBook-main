import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductSerreBasisSourceQuotient
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanSmithProductFromProjectiveLattice
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeCokernelDescent

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section SourceProductSmithCompletionLocal

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

local instance sourceProductSmithCompletionLocalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance sourceProductSmithCompletionLocalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- A complete Serre-basis package carrying exactly the two source representatives modulo
Serre's divisibility lattice: forward representatives for Brauer rows and reverse point-mass
representatives for integer regular-class functions. -/
def canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack : Prop :=
  ∃ ι : Type u,
  ∃ instFintype : Fintype ι,
  ∃ instDecidableEq : DecidableEq ι,
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  ∃ π : ι → FDRep k G,
    PairwiseNonisomorphic π ∧
      IsCompleteIrreducibleFamily π ∧
        canonicalSourceProductSerreBasisIntegerRepresentativesModuloD
          (p := p) (A := A) (K := K) (G := G) π

/-- Projective-character witness form of the same Serre-basis package.  The conversion to the
integer-representative package is precisely the formalized Serre 18.5(a) divisibility lattice
input. -/
def canonicalSourceProductSerreBasisProjectiveWitnessPack : Prop :=
  ∃ ι : Type u,
  ∃ instFintype : Fintype ι,
  ∃ instDecidableEq : DecidableEq ι,
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  ∃ π : ι → FDRep k G,
    PairwiseNonisomorphic π ∧
      IsCompleteIrreducibleFamily π ∧
        canonicalSourceProductSerreBasisForwardProjectiveWitness
          (p := p) (A := A) (K := K) (G := G) π ∧
          canonicalSourceProductSerreBasisReversePointProjectiveWitness
            (p := p) (A := A) (K := K) (G := G) π

/-- Serre 18.5(a) turns projective-character witnesses into the forward/reverse integer
representatives modulo the regular divisibility lattice. -/
theorem canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack_of_projectiveWitness
    (hwitness :
      canonicalSourceProductSerreBasisProjectiveWitnessPack
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hwitness with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, hforward, hreverse⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  refine ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, ?_⟩
  exact
    (serreBasisProjectiveWitness_iff_integerRepresentativesModuloD
      (p := p) (A := A) (K := K) (G := G) π).1
      ⟨hforward, hreverse⟩

/-- The two Serre-basis integer representative directions identify the canonical source-product
image with the coordinatewise integer image. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasisIntegerRepresentativesModuloDPack
    (hreps :
      canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hreps with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, hreps⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis_integerRepresentativesModuloD_sourceQuotient
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete hreps

/-- Projective-character witness form of the canonical source-product image statement. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasisProjectiveWitnessPack
    (hwitness :
      canonicalSourceProductSerreBasisProjectiveWitnessPack
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasisIntegerRepresentativesModuloDPack
    (p := p) (A := A) (K := K) (G := G)
    (canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack_of_projectiveWitness
      (p := p) (A := A) (K := K) (G := G) hwitness)

end SourceProductSmithCompletionLocal

section SourceProductSmithCompletionFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance sourceProductSmithCompletionFullMixedFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance sourceProductSmithCompletionFullMixedDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model canonical source-product image statement.  This is the source-product input
below the fixed Cartan-range support theorem: each mixed model only has to identify the actual
canonical source-product image with the coordinatewise integer image. -/
def fullMixedModelCanonicalSourceProductImageStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)

/-- Full mixed-model version of the exact forward/reverse Serre-basis representative input left
by the canonical source-product route. -/
def fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement :
    Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack
        (p := p) (A := A) (K := K) (G := G)

/-- Full mixed-model projective-character witness version of the same source representatives. -/
def fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      canonicalSourceProductSerreBasisProjectiveWitnessPack
        (p := p) (A := A) (K := K) (G := G)

/-- Full mixed-model split whose forward half is the projective-character lattice representative
congruence and whose reverse half is the source representative for every integer regular-class
function. -/
def fullMixedModelProjectiveCharacterLatticeReverseSourceStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      projectiveCharacterLatticeIntegerRepresentativeCongruence
          (p := p) (A := A) (K := K) (G := G) ∧
        ∀ g : PRegularConjClass G p → ℤ,
          ∃ x : R₀[IsLocalRing.ResidueField A](G),
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
              virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
                canonicalVirtualModularCartanRangeASpan
                  (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character witnesses give the full mixed-model integer representatives modulo
Serre's divisibility lattice. -/
theorem
    fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement_of_projectiveWitness
    (hwitness :
      fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    canonicalSourceProductSerreBasisIntegerRepresentativesModuloDPack_of_projectiveWitness
      (p := p) (A := A) (K := K) (G := G)
      (hwitness (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed-model Serre-basis representatives close the canonical source-product image
statement in every mixed model. -/
theorem fullMixedModelCanonicalSourceProductImageStatement_of_serreBasisIntegerRepresentativesModuloD
    (hreps :
      fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasisIntegerRepresentativesModuloDPack
      (p := p) (A := A) (K := K) (G := G)
      (hreps (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character witness form of the full mixed-model canonical source-product image
statement. -/
theorem fullMixedModelCanonicalSourceProductImageStatement_of_serreBasisProjectiveWitness
    (hwitness :
      fullMixedModelCanonicalSourceProductSerreBasisProjectiveWitnessStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) :=
  fullMixedModelCanonicalSourceProductImageStatement_of_serreBasisIntegerRepresentativesModuloD
    (p := p) (k := k) (G := G)
    (fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement_of_projectiveWitness
      (p := p) (k := k) (G := G) hwitness)

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-character lattice forward congruence plus reverse source representatives
close the full mixed-model canonical source-product image statement. -/
theorem
    fullMixedModelCanonicalSourceProductImageStatement_of_projectiveCharacterLattice_reverseSource
    (hsource :
      fullMixedModelProjectiveCharacterLatticeReverseSourceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hsource (A := A) (K := K) e0 with ⟨hlattice, hreverse⟩
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_reverse_source_congruence
      (p := p) (A := A) (K := K) (G := G) hlattice hreverse

omit [IsAlgClosed k] [CharP k p] in
/-- Canonical source-product image matching gives the full mixed-model Cartan cokernel product. -/
theorem fullMixedModelCartanCokernelProductStatement_of_canonicalSourceProductImage
    (himage :
      fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
      (p := p) (A := A) (K := K) (G := G)
      (himage (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Canonical source-product image matching gives the non-cyclic Smith coefficient product
statement. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_canonicalSourceProductImage
    (himage :
      fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement (p := p) (k := k) (G := G) := by
  have hproduct :
      fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
          (p := p) (A := A) (K := K) (G := G)
          (himage (A := A) (K := K) e0)
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      (cartanCokernelProduct_iff_exists_smith_coeffs_perm
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).1
        (hproduct (A := A) (K := K) e0) with
    ⟨b, hfull, σ, hcoeff⟩
  refine ⟨b, hfull, ?_⟩
  calc
    (∏ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
            b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p (σ c).1 := by
      exact Finset.prod_congr rfl fun c _ ↦ hcoeff c
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
      exact
        Fintype.prod_equiv σ
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p (σ c).1)
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
          (fun _ ↦ rfl)

omit [IsAlgClosed k] [CharP k p] in
/-- Canonical source-product image matching gives the Cartan determinant product statement. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_canonicalSourceProductImage
    (himage :
      fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  have hproduct :
      fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
          (p := p) (A := A) (K := K) (G := G)
          (himage (A := A) (K := K) e0)
  have hsmith :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      rcases
          (cartanCokernelProduct_iff_exists_smith_coeffs_perm
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).1
            (hproduct (A := A) (K := K) e0) with
        ⟨b, hfull, σ, hcoeff⟩
      refine ⟨b, hfull, ?_⟩
      calc
        (∏ c : PRegularConjClass G p,
            Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
                b hfull c)) =
            ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p (σ c).1 := by
          exact Finset.prod_congr rfl fun c _ ↦ hcoeff c
        _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
          exact
            Fintype.prod_equiv σ
              (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p (σ c).1)
              (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
              (fun _ ↦ rfl)
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

omit [IsAlgClosed k] [CharP k p] in
/-- The Serre-basis forward/reverse representatives imply the full mixed-model Cartan cokernel
product. -/
theorem fullMixedModelCartanCokernelProductStatement_of_serreBasisIntegerRepresentativesModuloD
    (hreps :
      fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) := by
  have himage :
      fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) :=
    fullMixedModelCanonicalSourceProductImageStatement_of_serreBasisIntegerRepresentativesModuloD
      (p := p) (k := k) (G := G) hreps
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
      (p := p) (A := A) (K := K) (G := G)
      (himage (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The Serre-basis forward/reverse representatives imply the full mixed-model Smith product. -/
theorem
    fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_serreBasisIntegerRepresentativesModuloD
    (hreps :
      fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement (p := p) (k := k) (G := G) := by
  have himage :
      fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) :=
    fullMixedModelCanonicalSourceProductImageStatement_of_serreBasisIntegerRepresentativesModuloD
      (p := p) (k := k) (G := G) hreps
  have hproduct :
      fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
          (p := p) (A := A) (K := K) (G := G)
          (himage (A := A) (K := K) e0)
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      (cartanCokernelProduct_iff_exists_smith_coeffs_perm
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).1
        (hproduct (A := A) (K := K) e0) with
    ⟨b, hfull, σ, hcoeff⟩
  refine ⟨b, hfull, ?_⟩
  calc
    (∏ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
            b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p (σ c).1 := by
      exact Finset.prod_congr rfl fun c _ ↦ hcoeff c
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
      exact
        Fintype.prod_equiv σ
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p (σ c).1)
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
          (fun _ ↦ rfl)

omit [IsAlgClosed k] [CharP k p] in
/-- The Serre-basis forward/reverse representatives imply the full mixed-model determinant
product. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_serreBasisIntegerRepresentativesModuloD
    (hreps :
      fullMixedModelCanonicalSourceProductSerreBasisIntegerRepresentativesModuloDStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  have himage :
      fullMixedModelCanonicalSourceProductImageStatement (p := p) (k := k) (G := G) :=
    fullMixedModelCanonicalSourceProductImageStatement_of_serreBasisIntegerRepresentativesModuloD
      (p := p) (k := k) (G := G) hreps
  have hproduct :
      fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      exact
        cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
          (p := p) (A := A) (K := K) (G := G)
          (himage (A := A) (K := K) e0)
  have hsmith :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      rcases
          (cartanCokernelProduct_iff_exists_smith_coeffs_perm
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).1
            (hproduct (A := A) (K := K) e0) with
        ⟨b, hfull, σ, hcoeff⟩
      refine ⟨b, hfull, ?_⟩
      calc
        (∏ c : PRegularConjClass G p,
            Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
                b hfull c)) =
            ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p (σ c).1 := by
          exact Finset.prod_congr rfl fun c _ ↦ hcoeff c
        _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
          exact
            Fintype.prod_equiv σ
              (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p (σ c).1)
              (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
              (fun _ ↦ rfl)
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

omit [IsAlgClosed k] [CharP k p] in
/-- The non-fixed source quotient/product image input implies the full mixed-model determinant
product via the non-cyclic Smith coefficient product. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_sourceQuotientProductImage
    (himage :
      fullMixedModelProjectiveCartanSourceQuotientProductImageStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  have hsmith :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement (p := p) (k := k) (G := G) :=
    by
      intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
        _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
        _instAlgClosed _instCharP e0
      have hproduct :
          Nonempty
            (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
              ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
        cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_sourceQuotientProduct
          (p := p) (A := A) (K := K) (G := G)
          (himage (A := A) (K := K) e0)
      rcases
          (cartanCokernelProduct_iff_exists_smith_coeffs_perm
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).1 hproduct with
        ⟨b, hfull, σ, hcoeff⟩
      refine ⟨b, hfull, ?_⟩
      calc
        (∏ c : PRegularConjClass G p,
            Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
                b hfull c)) =
            ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p (σ c).1 := by
          exact Finset.prod_congr rfl fun c _ ↦ hcoeff c
        _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
          exact
            Fintype.prod_equiv σ
              (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p (σ c).1)
              (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
              (fun _ ↦ rfl)
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

end SourceProductSmithCompletionFullMixed

end Representation
