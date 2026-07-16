import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelProductSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelSmithProduct

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelSmithProductFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelSmithProductDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Smith-coefficient form of Serre 18.5(b).

If the Smith coefficients of the intrinsic Cartan image, for some ambient integral basis, are the
centralizer `p`-parts up to reindexing, then the abstract Cartan cokernel is the corresponding
product of cyclic groups.  The proof goes through an arbitrary Smith coordinate equivalence, not
through the fixed `regularClassCoordinateAddEquiv`. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_smith_coeffs_perm
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
          ConjClasses.centralizerPPart p (σ c).1) :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_sourceFaithful
    (p := p) (k := k) (G := G)
    (existsCartanRangeCoordinateEquiv_of_smith_coeffs_perm
      (p := p) (k := k) (G := G) b hfull σ hcoeff)

omit [IsAlgClosed k] [CharP k p] in
/-- Existential Smith-coefficient package form of
`cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_smith_coeffs_perm`. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_exists_smith_coeffs_perm
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
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases hSmith with ⟨b, hfull, σ, hcoeff⟩
  exact
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_smith_coeffs_perm
      (p := p) (k := k) (G := G) b hfull σ hcoeff

/-- The abstract cokernel product determines the same Smith-coefficient package.

This is the reverse finite `p`-primary uniqueness direction: the product presentation and the
uniqueness of products of `p`-power cyclic groups force the Smith moduli of the Cartan image to
be the centralizer `p`-parts up to permutation. -/
theorem cartanCokernel_exists_smith_coeffs_perm_of_cokernelProduct
    (hCokernel :
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
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
  classical
  let hbasis : Nonempty (Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G))) :=
    ⟨Classical.choose (simple_basis_on_pRegular_classes_ring_owner (p := p) (k := k) (G := G))⟩
  have hquot :
      Nonempty
        (R₀[k](G) ⧸ (cartanHom k G).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
    simpa [cartanCokernel] using hCokernel
  exact
    addSubgroup_exists_smith_coeffs_natAbs_perm_of_quotientEquivPiZMod
      (N := (cartanHom k G).range)
      (hbasis := hbasis)
      (d := fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
      (hd := centralizerPPart_pRegular_ne_zero (p := p) (G := G))
      (hquot := hquot)
      (hunique := cartanCokernelCentralizerPPartProductUniqueness_holds (p := p) (G := G))

/-- Finite Smith-invariant reformulation of the abstract cokernel product.

This packages the maximal Smith-route reduction: proving the displayed product for the Cartan
cokernel is equivalent to proving that the Smith invariant factors of the intrinsic Cartan image
are the centralizer `p`-parts, up to permutation. -/
theorem cartanCokernelProduct_iff_exists_smith_coeffs_perm :
    Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) ↔
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
  · exact cartanCokernel_exists_smith_coeffs_perm_of_cokernelProduct
      (p := p) (k := k) (G := G)
  · exact cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_exists_smith_coeffs_perm
      (p := p) (k := k) (G := G)

end CartanCokernelSmithProduct

end Representation
