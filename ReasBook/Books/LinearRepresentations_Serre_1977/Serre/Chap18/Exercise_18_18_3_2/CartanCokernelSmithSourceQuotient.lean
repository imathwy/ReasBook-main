import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelProductFromQuotient
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelSmithProduct

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelSmithSourceQuotient

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelSmithSourceQuotientFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelSmithSourceQuotientDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Smith-coefficient package obtained from the abstract source-faithful diagonal endpoint.

This is the non-fixed-column route: once Serre 18.5 identifies the Cartan cokernel with the
coordinatewise cyclic product, finite `p`-primary uniqueness identifies the Smith moduli of the
intrinsic Cartan image up to permutation. -/
theorem cartanCokernel_exists_smith_coeffs_perm_of_sourceFaithfulDiagonalProduct
    (hdiag : cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G)) :
    ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
      (hfull :
        Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
          Module.finrank ℤ (R₀[k](G)))
      (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
      ∀ c : PRegularConjClass G p,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
          ConjClasses.centralizerPPart p (σ c).1 := by
  exact
    (cartanCokernelProduct_iff_exists_smith_coeffs_perm
      (p := p) (k := k) (G := G)).1
      ((cartanCokernelSourceFaithfulDiagonalProduct_iff_cokernelProduct
        (p := p) (k := k) (G := G)).1 hdiag)

/-- Conversely, the Smith package feeds back into the source-faithful diagonal endpoint.

This records that the Smith route and the abstract source quotient/product route have the same
formal target, with no fixed Cartan-column witness. -/
theorem cartanCokernelSourceFaithfulDiagonalProduct_of_exists_smith_coeffs_perm
    (hSmith :
      ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
        (hfull :
          Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[k](G)))
        (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
        ∀ c : PRegularConjClass G p,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
            ConjClasses.centralizerPPart p (σ c).1) :
    cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G) := by
  exact
    (cartanCokernelSourceFaithfulDiagonalProduct_iff_cokernelProduct
      (p := p) (k := k) (G := G)).2
      ((cartanCokernelProduct_iff_exists_smith_coeffs_perm
        (p := p) (k := k) (G := G)).2 hSmith)

/-- The abstract source-faithful diagonal endpoint is equivalent to the intrinsic Smith package. -/
theorem cartanCokernelSourceFaithfulDiagonalProduct_iff_exists_smith_coeffs_perm :
    cartanCokernelSourceFaithfulDiagonalProduct (p := p) (k := k) (G := G) ↔
      ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
        (hfull :
          Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[k](G)))
        (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
        ∀ c : PRegularConjClass G p,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
            ConjClasses.centralizerPPart p (σ c).1 := by
  constructor
  · exact
      cartanCokernel_exists_smith_coeffs_perm_of_sourceFaithfulDiagonalProduct
        (p := p) (k := k) (G := G)
  · exact
      cartanCokernelSourceFaithfulDiagonalProduct_of_exists_smith_coeffs_perm
        (p := p) (k := k) (G := G)

end CartanCokernelSmithSourceQuotient

section CartanCokernelSmithCanonicalSourceQuotient

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanCokernelSmithCanonicalSourceQuotientFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelSmithCanonicalSourceQuotientDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Smith-coefficient package obtained from the canonical source-product range decomposition.

This is Serre 18.5(b) in the source-quotient form: a cyclic-product description of the actual
finite canonical image gives the intrinsic Smith moduli of the residue-field Cartan image. -/
theorem cartanCokernel_exists_smith_coeffs_perm_of_canonicalVirtualModularCartanProductRange
    (himage :
      Nonempty
        ((cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
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
          ConjClasses.centralizerPPart p (σ c).1 := by
  exact
    cartanCokernel_exists_smith_coeffs_perm_of_cokernelProduct
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductRange
        (p := p) (A := A) (K := K) (G := G) himage)

/-- Smith-coefficient package obtained from the canonical source-product image-match endpoint. -/
theorem cartanCokernel_exists_smith_coeffs_perm_of_canonicalVirtualModularCartanProductImage
    (himage :
      canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
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
          ConjClasses.centralizerPPart p (σ c).1 := by
  exact
    cartanCokernel_exists_smith_coeffs_perm_of_cokernelProduct
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      ((canonicalVirtualModularCartanProductImageMatchesIntegerImage_iff_cokernelProduct
        (p := p) (A := A) (K := K) (G := G)).1 himage)

/-- The canonical source-product image-match endpoint is equivalent to the intrinsic Smith
coefficient package for the residue-field Cartan image. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_iff_exists_smith_coeffs_perm :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G) ↔
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
            ConjClasses.centralizerPPart p (σ c).1 := by
  constructor
  · exact
      cartanCokernel_exists_smith_coeffs_perm_of_canonicalVirtualModularCartanProductImage
        (p := p) (A := A) (K := K) (G := G)
  · intro hSmith
    exact
      (canonicalVirtualModularCartanProductImageMatchesIntegerImage_iff_cokernelProduct
        (p := p) (A := A) (K := K) (G := G)).2
        ((cartanCokernelProduct_iff_exists_smith_coeffs_perm
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).2 hSmith)

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Smith-coefficient package obtained from the non-fixed source quotient/product image input. -/
theorem cartanCokernel_exists_smith_coeffs_perm_of_sourceQuotientProduct
    (himage :
      projectiveCartanSourceQuotientProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
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
          ConjClasses.centralizerPPart p (σ c).1 := by
  exact
    cartanCokernel_exists_smith_coeffs_perm_of_cokernelProduct
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_sourceQuotientProduct
        (p := p) (A := A) (K := K) (G := G) himage)

end CartanCokernelSmithCanonicalSourceQuotient

end Representation
