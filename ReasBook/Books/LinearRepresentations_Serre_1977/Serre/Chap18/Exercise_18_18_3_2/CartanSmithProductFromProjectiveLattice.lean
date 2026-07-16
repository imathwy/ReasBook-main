import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanProjectiveSmith
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanDetProductProducer
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeProjectiveCharacterEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanSmithProductFromProjectiveLattice

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanSmithProductFromProjectiveLatticeFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanSmithProductFromProjectiveLatticeDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model version of the smallest projective-character lattice coordinate input used
by `CartanProjectiveSmith.lean`.

For every full mixed-characteristic model with residue field identified with `k`, the intrinsic
Cartan image over that residue field admits some projective-character diagonal coordinate
description. This does not use the fixed final support theorem in `CartanFormalRange.lean`. -/
def fullMixedModelProjectiveCharacterLatticeDiagonalCoordinateStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      cartanRange_projectiveCharacterLattice_diagonalCoordinateStatement
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- A Smith-coefficient package up to permutation gives the corresponding product identity. -/
theorem cartanSmithNormalFormCoeffProduct_of_exists_smith_coeffs_perm
    {F : Type u} [Field F] [IsAlgClosed F] [CharP F p]
    (hSmith :
      ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[F](G)))
        (hfull :
          Module.finrank ℤ ((cartanHom F G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[F](G)))
        (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
        ∀ c : PRegularConjClass G p,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom F G).range.toIntSubmodule) b hfull c) =
            ConjClasses.centralizerPPart p (σ c).1) :
    ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[F](G)))
      (hfull :
        Module.finrank ℤ ((cartanHom F G).range.toIntSubmodule) =
          Module.finrank ℤ (R₀[F](G))),
      (∏ c : PRegularConjClass G p,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom F G).range.toIntSubmodule) b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
  rcases hSmith with ⟨b, hfull, σ, hcoeff⟩
  refine ⟨b, hfull, ?_⟩
  calc
    (∏ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom F G).range.toIntSubmodule) b hfull c)) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p (σ c).1 := by
      exact Finset.prod_congr rfl fun c _ ↦ hcoeff c
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
      exact
        Fintype.prod_equiv σ
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p (σ c).1)
          (fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
          (fun _ ↦ rfl)

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-character lattice diagonal coordinates imply the full mixed-model Smith-product
input for Serre 18.5(b).

The proof uses only the non-final Smith package
`cartanRange_exists_smith_coeffs_perm_via_projectiveCharacterLattice` and then removes the
permutation from the finite product. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_projectiveCharacterLatticeDiagonal
    (hCoordinate :
      fullMixedModelProjectiveCharacterLatticeDiagonalCoordinateStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      cartanRange_exists_smith_coeffs_perm_via_projectiveCharacterLattice
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)
        (hCoordinate (A := A) (K := K) e0) with
    hSmith
  exact
    cartanSmithNormalFormCoeffProduct_of_exists_smith_coeffs_perm
      (p := p) (F := IsLocalRing.ResidueField A) (G := G) hSmith

omit [IsAlgClosed k] [CharP k p] in
/-- The non-fixed projective Cartan product-range input also gives the full mixed-model
Smith-product statement, via the abstract cokernel product and the existing Smith adapter. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_projectiveCartanProductRange
    (hrange :
      fullMixedModelProjectiveCartanProductRangeStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hrange (A := A) (K := K) e0 with ⟨e, himage⟩
  have hproduct :
      Nonempty
        (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_projectiveCartanProductRange
      (p := p) (A := A) (K := K) (G := G) e himage
  have hSmith :
      ∃ (b :
          Module.Basis (PRegularConjClass G p) ℤ (R₀[IsLocalRing.ResidueField A](G)))
        (hfull :
          Module.finrank ℤ
              ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G)))
        (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
        ∀ c : PRegularConjClass G p,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
                b hfull c) =
            ConjClasses.centralizerPPart p (σ c).1 :=
    (cartanCokernelProduct_iff_exists_smith_coeffs_perm
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).1 hproduct
  exact
    cartanSmithNormalFormCoeffProduct_of_exists_smith_coeffs_perm
      (p := p) (F := IsLocalRing.ResidueField A) (G := G) hSmith

omit [IsAlgClosed k] [CharP k p] in
/-- Source-quotient product image matching is enough for the full mixed-model Smith-product
statement. This is below the final Cartan range endpoint and avoids the fixed A-side readback. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_sourceQuotientProductImage
    (himage :
      fullMixedModelProjectiveCartanSourceQuotientProductImageStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
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
  have hSmith :
      ∃ (b :
          Module.Basis (PRegularConjClass G p) ℤ (R₀[IsLocalRing.ResidueField A](G)))
        (hfull :
          Module.finrank ℤ
              ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G)))
        (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
        ∀ c : PRegularConjClass G p,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
                b hfull c) =
            ConjClasses.centralizerPPart p (σ c).1 :=
    (cartanCokernelProduct_iff_exists_smith_coeffs_perm
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).1 hproduct
  exact
    cartanSmithNormalFormCoeffProduct_of_exists_smith_coeffs_perm
      (p := p) (F := IsLocalRing.ResidueField A) (G := G) hSmith

end CartanSmithProductFromProjectiveLattice

end Representation
