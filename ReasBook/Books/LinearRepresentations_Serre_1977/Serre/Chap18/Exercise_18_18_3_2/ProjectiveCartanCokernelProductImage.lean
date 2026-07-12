import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanProductImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanCokernelProductImage

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanCokernelProductImageFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanCokernelProductImageDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- If the projective Cartan product range is the expected centralizer-`p`-part product, then the
Cartan cokernel over the residue field has the same product decomposition. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_projectiveCartanProductRange
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
    (himage :
      Nonempty
        ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
            (p := p) (A := A) (K := K) (G := G) e).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases himage with ⟨himage⟩
  exact
    ⟨(cartanCokernel_addEquiv_projectiveCartanProductRange
        (p := p) (A := A) (K := K) (G := G) e).trans himage⟩

/-- Concrete residue-field cokernel product decomposition obtained from the concrete Cartan
product image match. -/
theorem cartanCokernel_nonempty_addEquiv_pi_of_concreteProjectiveCartanProductImage
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (himage :
      concreteProjectiveCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  exact
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_projectiveCartanProductRange
      (p := p) (A := A) (K := K) (G := G)
      (projectiveCartanCoordinateASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
      (concreteProjectiveCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord himage)

end ProjectiveCartanCokernelProductImage

end Representation
