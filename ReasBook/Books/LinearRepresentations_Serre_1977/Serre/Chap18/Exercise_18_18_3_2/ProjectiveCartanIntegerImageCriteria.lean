import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanProductImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u v w

namespace Representation

section AddMonoidHomRangeCriteria

variable {M : Type u} {N : Type v} {P : Type w}
variable [AddGroup M] [AddGroup N] [AddGroup P]

/-- If two additive maps into the same additive group contain each other's values, with explicit
preimage witnesses, then their range subgroups are additively equivalent. -/
noncomputable def rangeAddEquivOfMutualRepresentativeImages
    (φ : M →+ P) (ψ : N →+ P)
    (hφψ : ∀ x : M, ∃ y : N, φ x = ψ y)
    (hψφ : ∀ y : N, ∃ x : M, ψ y = φ x) :
    φ.range ≃+ ψ.range where
  toFun z := by
    refine ⟨z.1, ?_⟩
    rcases z.2 with ⟨x, hx⟩
    rcases hφψ x with ⟨y, hy⟩
    exact ⟨y, by rw [← hy, hx]⟩
  invFun z := by
    refine ⟨z.1, ?_⟩
    rcases z.2 with ⟨y, hy⟩
    rcases hψφ y with ⟨x, hx⟩
    exact ⟨x, by rw [← hx, hy]⟩
  left_inv z := by
    ext
    rfl
  right_inv z := by
    ext
    rfl
  map_add' z z' := by
    ext
    rfl

/-- Nonempty packaging of `rangeAddEquivOfMutualRepresentativeImages`. -/
theorem range_nonempty_addEquiv_of_mutualRepresentativeImages
    (φ : M →+ P) (ψ : N →+ P)
    (hφψ : ∀ x : M, ∃ y : N, φ x = ψ y)
    (hψφ : ∀ y : N, ∃ x : M, ψ y = φ x) :
    Nonempty (φ.range ≃+ ψ.range) :=
  ⟨rangeAddEquivOfMutualRepresentativeImages φ ψ hφψ hψφ⟩

end AddMonoidHomRangeCriteria

section ProjectiveCartanIntegerImageCriteria

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanIntegerImageCriteriaFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegerImageCriteriaDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharZero K]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Representative-level criterion for identifying a Cartan product image with the coordinatewise
integer image.

The forward hypothesis checks every integer representative of the concrete Cartan-product source.
The reverse hypothesis checks every integer representative of the regular diagonal quotient. -/
theorem projectiveCartanProductImageMatchesIntegerImage_of_integerRepresentatives
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
    (hforward :
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
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
            cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G) e
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f)) :
    Nonempty
      ((cartanCoordinateRangeQuotientToProjectiveCartanProduct
          (p := p) (A := A) (K := K) (G := G) e).range ≃+
        (regularIntegerDiagonalQuotientToIntegerImageProduct
          (p := p) (A := A) (K := K) (G := G)).range) := by
  let φ :=
    cartanCoordinateRangeQuotientToProjectiveCartanProduct
      (p := p) (A := A) (K := K) (G := G) e
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  refine range_nonempty_addEquiv_of_mutualRepresentativeImages φ ψ ?_ ?_
  · intro q
    refine QuotientAddGroup.induction_on q ?_
    intro f
    rcases hforward f with ⟨g, hg⟩
    refine ⟨QuotientAddGroup.mk'
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g, ?_⟩
    simpa [φ, ψ] using hg
  · intro q
    refine QuotientAddGroup.induction_on q ?_
    intro g
    rcases hreverse g with ⟨f, hf⟩
    refine ⟨QuotientAddGroup.mk'
      (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f, ?_⟩
    simpa [φ, ψ] using hf

/-- Concrete version of the representative-level criterion for the normalized Brauer-coordinate
product equivalence used by `concreteProjectiveCartanProductImageMatchesIntegerImage`. -/
theorem concreteProjectiveCartanProductImageMatchesIntegerImage_of_integerRepresentatives
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hforward :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (projectiveCartanCoordinateASpanQuotientLinearEquivPi
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
            cartanCoordinateRangeQuotientToProjectiveCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (projectiveCartanCoordinateASpanQuotientLinearEquivPi
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
              (QuotientAddGroup.mk'
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f)) :
    concreteProjectiveCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  exact
    projectiveCartanProductImageMatchesIntegerImage_of_integerRepresentatives
      (p := p) (A := A) (K := K) (G := G)
      (projectiveCartanCoordinateASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
      hforward hreverse

end ProjectiveCartanIntegerImageCriteria

end Representation
