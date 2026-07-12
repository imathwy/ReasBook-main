import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibilityEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageSourceFaithful
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ReversePointSourceEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CartanMatrixDeterminantFromCokernelProduct

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanMatrixDeterminantFromCokernelProductFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanMatrixDeterminantFromCokernelProductDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Determinant form of the abstract cokernel-product input.

This is the non-fixed-column determinant endpoint: if Serre 18.5(b) supplies the abstract product
decomposition of the Cartan cokernel, then every complete simple/projective-envelope Cartan
matrix has determinant with absolute value the product of the centralizer `p`-parts. -/
theorem cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_cokernelProduct
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hCokernel :
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)))
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
      ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
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
  have hdet_card :
      Int.natAbs
          (Matrix.det (cartanMatrix k G bP bR)) =
        Nat.card (cartanCokernel k G) := by
    have hcartan : Function.Injective (cartanHom k G) :=
      cartanHom_injective (k := k) (G := G)
    let eRange : P₀[k](G) ≃+ (cartanHom k G).range :=
      AddMonoidHom.ofInjective hcartan
    let bRange : Module.Basis ι ℤ (cartanHom k G).range :=
      Module.Basis.map bP eRange.toIntLinearEquiv
    have hindex :
        (cartanHom k G).range.index =
          Int.natAbs
            (Matrix.det (cartanMatrix k G bP bR)) := by
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
      Int.natAbs
          (Matrix.det (cartanMatrix k G bP bR)) =
          (cartanHom k G).range.index := hindex.symm
      _ = Nat.card (cartanCokernel k G) := by
        simpa [cartanCokernel] using
          (AddSubgroup.index_eq_card (H := (cartanHom k G).range) (G := R₀[k](G)))
  have hcard_prod :
      Nat.card (cartanCokernel k G) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
    rcases hCokernel with ⟨e⟩
    calc
      Nat.card (cartanCokernel k G) =
          Nat.card
            (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
        exact Nat.card_congr e.toEquiv
      _ =
          ∏ c : PRegularConjClass G p,
            Nat.card (ZMod (ConjClasses.centralizerPPart p c.1)) := by
        simpa using (Nat.card_pi : Nat.card
          (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) =
            ∏ c : PRegularConjClass G p,
              Nat.card (ZMod (ConjClasses.centralizerPPart p c.1)))
      _ = ∏ c : PRegularConjClass G p,
            ConjClasses.centralizerPPart p c.1 := by
        simp [Nat.card_zmod]
  exact hdet_card.trans hcard_prod

end CartanMatrixDeterminantFromCokernelProduct

section ProjectiveCharacterLatticeCokernelDescent

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCharacterLatticeCokernelDescentFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeCokernelDescentDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Projective-character lattice form of the integer-representative congruence.

For every residue-field virtual character, its descended virtual modular character should differ
from the integer regular-class coordinate representative by the regular restriction of a
projective character. Serre 18.5(a) identifies this projective-character lattice with the
coordinatewise divisibility lattice; this statement is the non-fixed-coordinate input needed by
the source-product route. -/
def projectiveCharacterLatticeIntegerRepresentativeCongruence : Prop :=
  ∀ x : R₀[IsLocalRing.ResidueField A](G),
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G))

/-- Serre's projective-character lattice identification turns the projective-lattice
integer-representative congruence into the regular-value congruence used by the canonical
source-product image endpoint. -/
theorem regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulStatement
      (p := p) (A := A) (K := K) (G := G) := by
  intro x
  simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G)] using hlattice x

/-- The projective-character lattice representative statement is equivalent to the global
regular-value congruence; the equivalence is exactly Serre 18.5(a) after regular restriction. -/
theorem projectiveCharacter_latticeIntegerRepresentatives_iff_regularValueCongruence :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
        (p := p) (A := A) (K := K) (G := G)
  · intro hregular x
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hregular x

/-- Cardinality-gap endpoint.

The projective-character lattice supplies the forward image inclusion; the only remaining input is
the `Nat.card` equality between the actual Cartan cokernel and the coordinatewise integer image.
No fixed coordinate-span equality or fixed Cartan-column witness is used. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_natCard_eq
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G))
    (hcard :
      Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalProductImage_of_regularValue_congruence_and_natCard_eq
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)
    hcard

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Cokernel-product form of the `Nat.card` equality needed by the projective-character lattice
route. This is the cardinality half of Serre 18.5(b): the abstract product decomposition of
`Coker(c)` has the same size as the coordinatewise integer image. -/
theorem projectiveCharacter_lattice_natCard_eq_regularIntegerImageRange_of_cokernelProduct
    (hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
      Nat.card
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range :=
  cartanCokernel_natCard_eq_regularIntegerImageRange_of_cokernelProduct
    (p := p) (A := A) (K := K) (G := G) hCokernel

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Span-equality determinant endpoint for a full mixed-characteristic model.

This records the non-cyclic route from the source-span equality to the determinant formula without
using `CartanFormalRange.lean` or the downstream product theorem in `Exercise_18_18_3_2.lean`. -/
theorem cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_projectiveCartanCoordinate_span_eq
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope) :
    Int.natAbs
        (Matrix.det
          (cartanMatrix (IsLocalRing.ResidueField A) G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete))) =
      ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 :=
  cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_cokernelProduct
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)
    π hπ_pairwise hπ_complete P hP_envelope

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Determinant form of the `Nat.card` equality needed by the projective-character lattice
route. If an arbitrary complete simple/projective-envelope Cartan matrix has determinant with
absolute value `∏ |C_G(s)|_p`, then the actual Cartan cokernel has the same cardinality as the
coordinatewise integer image. -/
theorem projectiveCharacter_lattice_natCard_eq_regularIntegerImageRange_of_cartanMatrix_det_natAbs
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
          (p := p) (A := A) (K := K) (G := G)).range := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bR :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hCokernelFinite : Finite (cartanCokernel (IsLocalRing.ResidueField A) G) :=
    cartanCokernel_finite (p := p) (k := IsLocalRing.ResidueField A) (G := G)
  letI : (cartanHom (IsLocalRing.ResidueField A) G).range.FiniteIndex := by
    have hquot :
        Finite
          (R₀[IsLocalRing.ResidueField A](G) ⧸
            (cartanHom (IsLocalRing.ResidueField A) G).range) := by
      simpa [cartanCokernel] using hCokernelFinite
    exact AddSubgroup.finiteIndex_of_finite_quotient
  have hdet_card :
      Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G bP bR)) =
        Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) := by
    have hcartan : Function.Injective (cartanHom (IsLocalRing.ResidueField A) G) :=
      cartanHom_injective (k := IsLocalRing.ResidueField A) (G := G)
    let eRange : P₀[IsLocalRing.ResidueField A](G) ≃+
        (cartanHom (IsLocalRing.ResidueField A) G).range :=
      AddMonoidHom.ofInjective hcartan
    let bRange : Module.Basis ι ℤ (cartanHom (IsLocalRing.ResidueField A) G).range :=
      Module.Basis.map bP eRange.toIntLinearEquiv
    have hindex :
        (cartanHom (IsLocalRing.ResidueField A) G).range.index =
          Int.natAbs
            (Matrix.det
              (cartanMatrix (IsLocalRing.ResidueField A) G bP bR)) := by
      rw [AddSubgroup.index_eq_natAbs_det bR
        (cartanHom (IsLocalRing.ResidueField A) G).range bRange]
      congr 1
      have hbRange :
          (fun i ↦
              ((bRange i : (cartanHom (IsLocalRing.ResidueField A) G).range) :
                R₀[IsLocalRing.ResidueField A](G))) =
            (cartanHom (IsLocalRing.ResidueField A) G) ∘ bP := by
        ext i
        change ↑(eRange (bP i)) = cartanHom (IsLocalRing.ResidueField A) G (bP i)
        simpa [eRange] using
          (AddMonoidHom.ofInjective_apply
            (f := cartanHom (IsLocalRing.ResidueField A) G) hcartan (x := bP i))
      rw [hbRange, Module.Basis.det_apply]
      congr
      ext i j
      simp [cartanMatrix, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    calc
      Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G bP bR)) =
          (cartanHom (IsLocalRing.ResidueField A) G).range.index := hindex.symm
      _ = Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) := by
        simpa [cartanCokernel] using
          (AddSubgroup.index_eq_card
            (H := (cartanHom (IsLocalRing.ResidueField A) G).range)
            (G := R₀[IsLocalRing.ResidueField A](G)))
  have himage_card :
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
  calc
    Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) =
        Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G bP bR)) := hdet_card.symm
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := hdet
    _ =
        Nat.card
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range := himage_card.symm

/-- Projective-character lattice plus the abstract cokernel-product decomposition identifies the
canonical source-product image with the coordinatewise integer image, using only finite
cardinality and injectivity. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_cokernelProduct
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G))
    (hCokernel :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_natCard_eq
    (p := p) (A := A) (K := K) (G := G) hlattice
    (projectiveCharacter_lattice_natCard_eq_regularIntegerImageRange_of_cokernelProduct
      (p := p) (A := A) (K := K) (G := G) hCokernel)

/-- Determinant version of the projective-character lattice image endpoint. The determinant
identity supplies exactly the finite `Nat.card` equality; the projective-character lattice
supplies the forward image inclusion. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_cartanMatrix_det_natAbs
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G))
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
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_natCard_eq
    (p := p) (A := A) (K := K) (G := G) hlattice
    (projectiveCharacter_lattice_natCard_eq_regularIntegerImageRange_of_cartanMatrix_det_natAbs
      (p := p) (A := A) (K := K) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hdet)

/-- Reverse-source-congruence endpoint.

After the projective-character lattice supplies forward integer representatives, it is enough to
produce integer regular-class representatives modulo the canonical source span in the reverse
direction. This isolates the remaining gap as an integer representative lemma. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_reverse_source_congruence
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
              canonicalVirtualModularCartanRangeASpan
                (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_source_congruence
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)
    hreverse

/-- Surjectivity/range-inclusion endpoint.

The reverse half can also be exposed as the concrete inclusion of the coordinatewise integer image
in the actual canonical source-product range. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_from_projectiveCharacter_lattice_of_integerImage_le_productRange
    (hlattice :
      projectiveCharacterLatticeIntegerRepresentativeCongruence
        (p := p) (A := A) (K := K) (G := G))
    (hrange :
      (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range ≤
        (cartanCokernelToCanonicalVirtualModularCartanProduct
          (p := p) (A := A) (K := K) (G := G)).range) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_regularValue_congruence_and_reverse_point_source_congruence
    (p := p) (A := A) (K := K) (G := G)
    (regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G) hlattice)
    (canonicalVirtualModularCartanProductReversePointSourceCongruence_of_integerImage_le_productRange
      (p := p) (A := A) (K := K) (G := G) hrange)

end ProjectiveCharacterLatticeCokernelDescent

section ProjectiveCharacterLatticeCokernelDescentTransport

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance projectiveCharacterLatticeCokernelDescentTransportFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeCokernelDescentTransportDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Full mixed-characteristic transport endpoint with the remaining gap expressed as a
projective-character lattice representative statement plus the finite `Nat.card` equality. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_projectiveCharacter_lattice_natCard
    (hlattice :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          projectiveCharacterLatticeIntegerRepresentativeCongruence
            (p := p) (A := A) (K := K) (G := G))
    (hcard :
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
                (p := p) (A := A) (K := K) (G := G)).range) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_cardinalityRoute
      (p := p) (k := k) (G := G) ?_ hcard
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_projectiveCharacter_lattice
      (p := p) (A := A) (K := K) (G := G)
      (hlattice (A := A) (K := K) e0)

/-- Full mixed-characteristic projective-character lattice endpoint with the cardinality input
supplied by Serre's abstract cokernel-product decomposition. This specializes the bare
`Nat.card` route to the product form appearing in Exercise 18.5(b). -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_projectiveCharacter_lattice_cokernelProduct
    (hlattice :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          projectiveCharacterLatticeIntegerRepresentativeCongruence
            (p := p) (A := A) (K := K) (G := G))
    (hproduct :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          Nonempty
            (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
              ∀ c : PRegularConjClass G p,
                ZMod (ConjClasses.centralizerPPart p c.1))) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_projectiveCharacter_lattice_natCard
      (p := p) (k := k) (G := G) hlattice ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  exact
    projectiveCharacter_lattice_natCard_eq_regularIntegerImageRange_of_cokernelProduct
      (p := p) (A := A) (K := K) (G := G)
      (hproduct (A := A) (K := K) e0)

end ProjectiveCharacterLatticeCokernelDescentTransport

end Representation
