import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageCardinalityEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeHom
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.SmithDiagonal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CartanCokernelCardinalityDeterminant

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

include p in
/-- Index/determinant form of the Cartan cokernel cardinality.

This is independent of the cyclic-product target: for any complete simple family and compatible
projective-envelope family, the absolute determinant of the Cartan matrix is exactly the order of
the Cartan cokernel. -/
theorem cartanMatrix_det_natAbs_eq_cartanCokernel_natCard
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope) :
    Int.natAbs
        (Matrix.det
          (cartanMatrix k G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete))) =
      Nat.card (cartanCokernel k G) := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bR :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hCokernelFinite : Finite (cartanCokernel k G) :=
    cartanCokernel_finite (p := p) (k := k) (G := G)
  letI : (cartanHom k G).range.FiniteIndex := by
    have hquot :
        Finite (R₀[k](G) ⧸ (cartanHom k G).range) := by
      simpa [cartanCokernel] using hCokernelFinite
    exact AddSubgroup.finiteIndex_of_finite_quotient
  have hcartan : Function.Injective (cartanHom k G) :=
    cartanHom_injective (k := k) (G := G)
  let eRange : P₀[k](G) ≃+ (cartanHom k G).range :=
    AddMonoidHom.ofInjective hcartan
  let bRange : Module.Basis ι ℤ (cartanHom k G).range :=
    Module.Basis.map bP eRange.toIntLinearEquiv
  have hindex :
      (cartanHom k G).range.index =
        Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) := by
    rw [AddSubgroup.index_eq_natAbs_det bR (cartanHom k G).range bRange]
    congr 1
    have hbRange :
        (fun i ↦ ((bRange i : (cartanHom k G).range) : R₀[k](G))) =
          (cartanHom k G) ∘ bP := by
      ext i
      change ↑(eRange (bP i)) = cartanHom k G (bP i)
      simpa [eRange] using
        (AddMonoidHom.ofInjective_apply (f := cartanHom k G) hcartan (x := bP i))
    rw [hbRange, Module.Basis.det_apply]
    congr
    ext i j
    simp [cartanMatrix, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  calc
    Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
        (cartanHom k G).range.index := hindex.symm
    _ = Nat.card (cartanCokernel k G) := by
      simpa [cartanCokernel] using
        (AddSubgroup.index_eq_card (H := (cartanHom k G).range) (G := R₀[k](G)))

end CartanCokernelCardinalityDeterminant

section CartanCokernelCardinalitySourceFaithful

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanCokernelCardinalitySourceFaithfulFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelCardinalitySourceFaithfulDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The coordinatewise integer image has cardinality equal to the displayed product of
centralizer `p`-parts. -/
theorem regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_eq_prod :
    Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range =
      ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
  calc
    Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range =
        Nat.card
          (∀ c : PRegularConjClass G p,
            ZMod (ConjClasses.centralizerPPart p c.1)) := by
      exact
        Nat.card_congr
          (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
            (p := p) (A := A) (K := K) (G := G)).toEquiv
    _ =
        ∏ c : PRegularConjClass G p,
          Nat.card (ZMod (ConjClasses.centralizerPPart p c.1)) := by
      simpa using (Nat.card_pi : Nat.card
        (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) =
          ∏ c : PRegularConjClass G p,
            Nat.card (ZMod (ConjClasses.centralizerPPart p c.1)))
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
      simp [Nat.card_zmod]

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The desired finite-cardinality input is exactly the non-cyclic Cartan determinant formula. -/
theorem cartanCokernel_natCard_eq_regularIntegerImageRange_iff_cartanMatrix_det_natAbs_eq_prod
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope) :
    (Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range) ↔
      Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
  constructor
  · intro hcard
    calc
      Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
          Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) :=
        cartanMatrix_det_natAbs_eq_cartanCokernel_natCard
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
          π hπ_pairwise hπ_complete P hP_envelope
      _ =
          Nat.card
            (regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)).range := hcard
      _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 :=
        regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_eq_prod
          (p := p) (A := A) (K := K) (G := G)
  · intro hdet
    calc
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
          Int.natAbs
            (Matrix.det
              (cartanMatrix (IsLocalRing.ResidueField A) G
                (projectiveEnvelope_classes_basis_of_complete_family
                  π hπ_pairwise hπ_complete P hP_envelope)
                (simple_finiteRep_classes_basis_of_complete_family
                  π hπ_pairwise hπ_complete))) :=
        (cartanMatrix_det_natAbs_eq_cartanCokernel_natCard
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
          π hπ_pairwise hπ_complete P hP_envelope).symm
      _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := hdet
      _ =
          Nat.card
            (regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)).range :=
        (regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_eq_prod
          (p := p) (A := A) (K := K) (G := G)).symm

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Determinant-product form of the cardinality input needed by the finite-image adapter. -/
theorem cartanCokernel_natCard_eq_regularIntegerImageRange_of_cartanMatrix_det_natAbs_eq_prod
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (hdet :
      Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1) :
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range :=
  (cartanCokernel_natCard_eq_regularIntegerImageRange_iff_cartanMatrix_det_natAbs_eq_prod
    (p := p) (A := A) (K := K) (G := G)
    π hπ_pairwise hπ_complete P hP_envelope).2 hdet

omit [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
  [CharP (IsLocalRing.ResidueField A) p]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Smith-normal-form cardinality of the Cartan cokernel. -/
theorem cartanCokernel_natCard_eq_prod_smithNormalFormCoeffs
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[IsLocalRing.ResidueField A](G)))
    (hfull :
      Module.finrank ℤ
          ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G))) :
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      ∏ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
            b hfull c) := by
  classical
  let a : PRegularConjClass G p → ℕ :=
    fun c ↦
      Int.natAbs
        (Submodule.smithNormalFormCoeffs
          (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
          b hfull c)
  have hquot :
      cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ((c : PRegularConjClass G p) → ZMod (a c)) := by
    simpa [cartanCokernel, a] using
      (Submodule.quotientEquivPiZMod
        ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
        b hfull)
  calc
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card ((c : PRegularConjClass G p) → ZMod (a c)) :=
      Nat.card_congr hquot.toEquiv
    _ = ∏ c : PRegularConjClass G p, Nat.card (ZMod (a c)) := by
      simpa using (Nat.card_pi : Nat.card
        ((c : PRegularConjClass G p) → ZMod (a c)) =
          ∏ c : PRegularConjClass G p, Nat.card (ZMod (a c)))
    _ = ∏ c : PRegularConjClass G p, a c := by
      simp [Nat.card_zmod]
    _ =
        ∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
              b hfull c) := rfl

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- A non-cyclic Smith input sufficient for the desired finite-cardinality equality.

Unlike the cyclic-product route, this asks only for equality of the product of Smith moduli with
the product of the centralizer `p`-parts. It gives cardinality, not a cyclic-product
decomposition by itself. -/
theorem cartanCokernel_natCard_eq_regularIntegerImageRange_of_smithNormalFormCoeff_prod
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[IsLocalRing.ResidueField A](G)))
    (hfull :
      Module.finrank ℤ
          ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G)))
    (hprod :
      (∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
              b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1) :
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range := by
  calc
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        ∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
              b hfull c) :=
      cartanCokernel_natCard_eq_prod_smithNormalFormCoeffs
        (p := p) (A := A) (G := G) b hfull
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := hprod
    _ =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range :=
      (regularIntegerDiagonalQuotientToIntegerImageProductRange_natCard_eq_prod
        (p := p) (A := A) (K := K) (G := G)).symm

/-- Determinant/cardinality route to the canonical source-product image equality. -/
theorem canonicalProductImage_of_regularValue_and_detProduct
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (hdet :
      Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_le_of_domain_natCard_eq
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProductRange_le_integerImage_of_regularValue_congruence
      (p := p) (A := A) (K := K) (G := G) hforward)
    (cartanCokernel_natCard_eq_regularIntegerImageRange_of_cartanMatrix_det_natAbs_eq_prod
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hdet)

/-- Smith-product/cardinality route to the canonical source-product image equality. -/
theorem canonicalProductImage_of_regularValue_and_smithCoeffProduct
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[IsLocalRing.ResidueField A](G)))
    (hfull :
      Module.finrank ℤ
          ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G)))
    (hprod :
      (∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
              b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_le_of_domain_natCard_eq
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProductRange_le_integerImage_of_regularValue_congruence
      (p := p) (A := A) (K := K) (G := G) hforward)
    (cartanCokernel_natCard_eq_regularIntegerImageRange_of_smithNormalFormCoeff_prod
      (p := p) (A := A) (K := K) (G := G) b hfull hprod)

/-- Product-decomposition output from determinant plus the source-faithful forward congruence. -/
theorem cartanCokernel_product_of_regularValue_and_detProduct
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope)
    (hdet :
      Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
    (p := p) (A := A) (K := K) (G := G)
    (canonicalProductImage_of_regularValue_and_detProduct
      (p := p) (A := A) (K := K) (G := G)
      hforward π hπ_pairwise hπ_complete P hP_envelope hdet)

/-- Product-decomposition output from Smith coefficient product plus the source-faithful forward
congruence. -/
theorem cartanCokernel_product_of_regularValue_and_smithCoeffProduct
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[IsLocalRing.ResidueField A](G)))
    (hfull :
      Module.finrank ℤ
          ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G)))
    (hprod :
      (∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
              b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
    (p := p) (A := A) (K := K) (G := G)
    (canonicalProductImage_of_regularValue_and_smithCoeffProduct
      (p := p) (A := A) (K := K) (G := G)
      hforward b hfull hprod)

end CartanCokernelCardinalitySourceFaithful

end Representation
