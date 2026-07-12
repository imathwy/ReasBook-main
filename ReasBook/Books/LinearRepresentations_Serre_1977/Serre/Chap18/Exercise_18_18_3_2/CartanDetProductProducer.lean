import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelProductSourceProof
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelSmithProduct
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCoordinates

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CartanDetProductProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanDetProductProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanDetProductProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] [Fact p.Prime] in
/-- Pure Smith-cardinality form for the Cartan cokernel over a residue field.

This is the determinant/product route's non-cyclic Smith input: no cyclic-product decomposition
of the cokernel is used, only the product of the Smith moduli of the intrinsic Cartan image. -/
theorem cartanCokernel_natCard_eq_prod_smithNormalFormCoeffs_field
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
    (hfull :
      Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[k](G))) :
    Nat.card (cartanCokernel k G) =
      ∏ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom k G).range.toIntSubmodule) b hfull c) := by
  classical
  let a : PRegularConjClass G p → ℕ :=
    fun c ↦
      Int.natAbs
        (Submodule.smithNormalFormCoeffs
          (N := (cartanHom k G).range.toIntSubmodule) b hfull c)
  have hquot :
      cartanCokernel k G ≃+
        ((c : PRegularConjClass G p) → ZMod (a c)) := by
    simpa [cartanCokernel, a] using
      (Submodule.quotientEquivPiZMod
        ((cartanHom k G).range.toIntSubmodule) b hfull)
  calc
    Nat.card (cartanCokernel k G) =
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
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) := rfl

/-- Non-cyclic Smith-product producer for the local Cartan determinant formula.

If the product of the Smith moduli of `(cartanHom k G).range` is the displayed centralizer
`p`-part product, then every complete simple family and compatible projective-envelope family has
Cartan determinant with that absolute value. -/
theorem cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_smithNormalFormCoeffProduct
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
    (hfull :
      Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[k](G)))
    (hprod :
      (∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1)
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
  calc
    Int.natAbs
        (Matrix.det
          (cartanMatrix k G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete))) =
        Nat.card (cartanCokernel k G) :=
      cartanMatrix_det_natAbs_eq_cartanCokernel_natCard
        (p := p) (k := k) (G := G)
        π hπ_pairwise hπ_complete P hP_envelope
    _ =
        ∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) :=
      cartanCokernel_natCard_eq_prod_smithNormalFormCoeffs_field
        (p := p) (k := k) (G := G) b hfull
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := hprod

/-- Permuted Smith-coefficient form of
`cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_smithNormalFormCoeffProduct`. -/
theorem cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_smith_coeffs_perm
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
    (hfull :
      Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[k](G)))
    (σ : PRegularConjClass G p ≃ PRegularConjClass G p)
    (hcoeff :
      ∀ c : PRegularConjClass G p,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
          ConjClasses.centralizerPPart p (σ c).1)
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
  refine
    cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_smithNormalFormCoeffProduct
      (p := p) (k := k) (G := G) b hfull ?_
      π hπ_pairwise hπ_complete P hP_envelope
  calc
    (∏ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom k G).range.toIntSubmodule) b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p (σ c).1 := by
      exact Finset.prod_congr rfl fun c _ ↦ hcoeff c
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
      exact
        Fintype.prod_equiv σ
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p (σ c).1)
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
          (fun _ ↦ rfl)

/-- Full mixed-model Smith-product input sufficient for the determinant/product statement. -/
def fullMixedModelCartanSmithNormalFormCoeffProductStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ (b : Module.Basis (PRegularConjClass G p) ℤ
          (R₀[IsLocalRing.ResidueField A](G)))
        (hfull :
          Module.finrank ℤ
              ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G))),
        (∏ c : PRegularConjClass G p,
            Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
                b hfull c)) =
          ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model cokernel-product input gives the intrinsic Smith-product input.

This is the product-to-Smith half of Serre 18.5(b): finite `p`-primary uniqueness converts the
abstract cyclic product for `Coker(c)` into Smith coefficients up to permutation, and the finite
product removes that permutation. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_cokernelProduct
    (hproduct :
      fullMixedModelCartanCokernelProductStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
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
/-- Full mixed-model determinant/product producer from the non-cyclic Smith-product input. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_smithNormalFormCoeffProduct
    (hSmithProduct :
      fullMixedModelCartanSmithNormalFormCoeffProductStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  rcases hSmithProduct (A := A) (K := K) e0 with ⟨b, hfull, hprod⟩
  refine
    ⟨PRegularConjClass G p, inferInstance, inferInstance,
      π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_smithNormalFormCoeffProduct
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      b hfull hprod π hπ_pairwise hπ_complete P hP_envelope

end CartanDetProductProducer

end Representation
