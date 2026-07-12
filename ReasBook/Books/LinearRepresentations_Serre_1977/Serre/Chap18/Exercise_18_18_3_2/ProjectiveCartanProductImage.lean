import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegralProductBridge
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.IntegerQuotientImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section RegularIntegerImageProduct

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local instance regularIntegerImageProductFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

/-- The purely coordinatewise integer map from the regular diagonal quotient into Serre's
displayed product of fraction-field quotients.

This is the image one obtains before applying the Brauer-coordinate transport used in the
concrete Cartan-span quotient. -/
noncomputable def regularIntegerDiagonalQuotientToIntegerImageProduct :
    ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) →+
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) := by
  let D : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
  let φ : (PRegularConjClass G p → ℤ) →+
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) :=
    { toFun := fun f c =>
        integerQuotientImageHom
          (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (f c)
      map_zero' := by
        ext c
        exact map_zero
          (integerQuotientImageHom
            (A := A) (K := K) (ConjClasses.centralizerPPart p c.1))
      map_add' := by
        intro f g
        ext c
        exact map_add
          (integerQuotientImageHom
            (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)) (f c) (g c) }
  exact QuotientAddGroup.lift D φ (by
    intro f hf
    ext c
    have hfD : f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) := by
      simpa [D] using hf
    rcases (mem_regularIntegerDiagonalSubmodule_iff (p := p) (G := G) f).1 hfD c with
      ⟨a, ha⟩
    simpa [integerQuotientImageSubmodule] using
      (integerQuotientImageHom_eq_zero_of_mem_zmultiples
        (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)
        (Int.mem_zmultiples_iff.mpr ⟨a, by simp [ha, mul_comm]⟩)))

omit [IsLocalRing A] [IsDomain A] [IsFractionRing A K] [CharZero K]
  [CharP (IsLocalRing.ResidueField A) p] in
@[simp]
theorem regularIntegerDiagonalQuotientToIntegerImageProduct_mk
    (f : PRegularConjClass G p → ℤ) :
    regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup f) =
      fun c : PRegularConjClass G p =>
        integerQuotientImageHom
          (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (f c) := by
  rw [regularIntegerDiagonalQuotientToIntegerImageProduct]
  rfl

/-- The coordinatewise integer map is injective. The only arithmetic input is the rank-one
mixed-characteristic descent from `IntegerQuotientImage.lean`. -/
theorem regularIntegerDiagonalQuotientToIntegerImageProduct_injective :
    Function.Injective
      (regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    rw [AddSubgroup.mem_bot]
    revert hq
    refine QuotientAddGroup.induction_on q ?_
    intro f hf
    have hcoord :
        ∀ c : PRegularConjClass G p,
          integerQuotientImageHom
              (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (f c) =
            0 := by
      intro c
      have h := congrFun hf c
      simpa [integerQuotientImageSubmodule] using h
    have hfD : f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) := by
      refine (mem_regularIntegerDiagonalSubmodule_iff (p := p) (G := G) f).2 ?_
      intro c
      rcases ConjClasses.centralizerPPart_eq_prime_pow (p := p) (G := G) c.1 with
        ⟨e, he⟩
      have hker :
          f c ∈
            (integerQuotientImageHom
              (A := A) (K := K) (ConjClasses.centralizerPPart p c.1)).ker := by
        simpa [AddMonoidHom.mem_ker] using hcoord c
      have hz :
          f c ∈ AddSubgroup.zmultiples (ConjClasses.centralizerPPart p c.1 : ℤ) := by
        simpa [
          integerQuotientImageHom_ker_eq_zmultiples_of_eq_prime_pow
            (p := p) (A := A) (K := K) (d := ConjClasses.centralizerPPart p c.1)
            (e := e) he] using hker
      rcases Int.mem_zmultiples_iff.mp hz with ⟨a, ha⟩
      exact ⟨a, by simpa using ha⟩
    exact
      (QuotientAddGroup.eq_zero_iff
        (N := (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) f).2
        (by simpa using hfD)
  · exact bot_le

/-- The coordinatewise integer image in Serre's displayed product is the expected finite product
of the cyclic groups `ZMod |C_G(c)|_p`. -/
noncomputable def regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod :
    (regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)).range ≃+
      ∀ c : PRegularConjClass G p,
        ZMod (ConjClasses.centralizerPPart p c.1) :=
  (AddMonoidHom.ofInjective
      (regularIntegerDiagonalQuotientToIntegerImageProduct_injective
        (p := p) (A := A) (K := K) (G := G))).symm.trans
    (regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G))

/-- Nonempty packaging of the coordinatewise integer-image identification. -/
theorem regularIntegerDiagonalQuotientToIntegerImageProductRange_nonempty_addEquiv_pi :
    Nonempty
      ((regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range ≃+
        ∀ c : PRegularConjClass G p,
          ZMod (ConjClasses.centralizerPPart p c.1)) :=
  ⟨regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
    (p := p) (A := A) (K := K) (G := G)⟩

end RegularIntegerImageProduct

section ConcreteCartanProductImage

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance concreteCartanProductImageFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance concreteCartanProductImageDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Any Cartan-span product equivalence whose integer Cartan image matches the coordinatewise
integer image has the expected cyclic-product image. This covers an equivalence obtained from the
nonempty wrapper as soon as its image is identified. -/
theorem projectiveCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
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
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range)) :
    Nonempty
      ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e).range ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases himage with ⟨himage⟩
  exact
    ⟨himage.trans
      (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
        (p := p) (A := A) (K := K) (G := G))⟩

omit [HenselianLocalRing A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Adapter from the image-match form to the existing Cartan-range coordinate theorem, for an
arbitrary Cartan-span product equivalence `e`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_productImage_matchesIntegerImage
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
          (regularIntegerDiagonalQuotientToIntegerImageProduct
            (p := p) (A := A) (K := K) (G := G)).range)) :
    ∃ coord : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map coord.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    existsCartanRangeCoordinateEquiv_of_projectiveCartanProductRange_equiv_pi
      (p := p) (A := A) (K := K) (G := G) e
      (projectiveCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
        (p := p) (A := A) (K := K) (G := G) e himage)

/-- Minimal concrete image-identification input left by the current API.

For the concrete Cartan-span quotient equivalence built from a normalized Brauer family, it says
that the actual Cartan product image is additively the same finite subgroup as the coordinatewise
integer image above. Proving this requires an additional integrality statement for the
Brauer-coordinate transport; it is not supplied by the existing span theorem
`projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span`. -/
def concreteProjectiveCartanProductImageMatchesIntegerImage
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  Nonempty
    ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (projectiveCartanCoordinateASpanQuotientLinearEquivPi
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)).range ≃+
      (regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)).range)

/-- If the concrete Cartan-span product image matches the coordinatewise integer image, then that
concrete image is the expected product of cyclic groups. -/
theorem concreteProjectiveCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
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
      ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G)
          (projectiveCartanCoordinateASpanQuotientLinearEquivPi
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)).range ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  exact
    projectiveCartanProductRange_nonempty_addEquiv_pi_of_matches_integerImage
      (p := p) (A := A) (K := K) (G := G)
      (projectiveCartanCoordinateASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
      himage

/-- Adapter to the existing Cartan-range coordinate theorem.

Thus the precise remaining task for the concrete Cartan-span route is the image-identification
input `concreteProjectiveCartanProductImageMatchesIntegerImage`; once supplied, no additional
Smith or formal-range work is needed here. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_concreteProductImage
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
    ∃ coord : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map coord.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_productImage_matchesIntegerImage
      (p := p) (A := A) (K := K) (G := G)
      (projectiveCartanCoordinateASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
      himage

end ConcreteCartanProductImage

end Representation
