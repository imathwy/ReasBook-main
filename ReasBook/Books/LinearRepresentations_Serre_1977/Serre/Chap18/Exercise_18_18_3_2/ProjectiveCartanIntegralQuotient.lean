import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSaturation
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSpanStability

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegralQuotient

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local instance projectiveCartanIntegralQuotientFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegralQuotientDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Integral-to-fraction-field quotient map for the fixed Cartan coordinate range.

An integer regular-class function is first cast to `K`, then projected to the quotient by the
`A`-span of the field-valued Cartan coordinate range. The map is well-defined on the integer
quotient because cast Cartan coordinate vectors lie in that `A`-span. -/
noncomputable def cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient :
    ((PRegularConjClass G p → ℤ) ⧸
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) →+
      ((PRegularConjClass G p → K) ⧸
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K))) := by
  let N : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (cartanCoordinateAddHom
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range
  let S : Submodule A (PRegularConjClass G p → K) :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set (PRegularConjClass G p → K))
  let φ : (PRegularConjClass G p → ℤ) →+
      ((PRegularConjClass G p → K) ⧸ S) :=
    S.mkQ.toAddMonoidHom.comp
      (regularIntegerFunctionCast (p := p) (K := K) (G := G))
  exact QuotientAddGroup.lift N φ (by
    intro f hf
    change
      Submodule.Quotient.mk (p := S)
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    rcases (by simpa [N] using hf) with ⟨x, rfl⟩
    rw [regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G) x]
    exact Submodule.subset_span ⟨x, rfl⟩)

omit [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [CharZero K] in
/-- The integral quotient map sends a representative to the corresponding cast class. -/
@[simp] theorem cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient_mk
    (f : PRegularConjClass G p → ℤ) :
    cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          ((cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) f) =
      (Submodule.Quotient.mk
        (p := Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set (PRegularConjClass G p → K)))
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) := by
  rw [cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient]
  rfl

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- A representative maps to zero in the fraction-field Cartan-span quotient exactly when it was
already in the integral Cartan coordinate range. -/
theorem cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient_mk_eq_zero_iff
    (f : PRegularConjClass G p → ℤ) :
    cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          ((cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) f) = 0 ↔
      f ∈
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
  rw [cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient_mk]
  constructor
  · intro hf
    have hspan :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) := by
      exact (Submodule.Quotient.mk_eq_zero
        (p := Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)))).1 hf
    exact cartanCoordinateAddHom_range_cast_saturated
      (p := p) (A := A) (K := K) (G := G) f hspan
  · rintro ⟨x, rfl⟩
    rw [Submodule.Quotient.mk_eq_zero]
    rw [regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G) x]
    exact Submodule.subset_span ⟨x, rfl⟩

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- The cast-saturation theorem makes the integral quotient embed in the fraction-field quotient
by the Cartan coordinate `A`-span. This is the precise descent consequence available without
assuming that the Cartan `A`-span is the regular value-divisibility lattice. -/
theorem cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient_injective :
    Function.Injective
      (cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient
        (p := p) (A := A) (K := K) (G := G)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    rw [AddSubgroup.mem_bot]
    revert hq
    refine QuotientAddGroup.induction_on q ?_
    intro f hf
    exact (QuotientAddGroup.eq_zero_iff
      (N := (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) f).2
        ((cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient_mk_eq_zero_iff
          (p := p) (A := A) (K := K) (G := G) f).1 (by simpa using hf))
  · exact bot_le

/-- Compose the integral quotient embedding with any Serre 18.5(a) product equivalence for the
Cartan coordinate `A`-span. The result records what the source-product route currently gives:
an injected integer Cartan-coordinate quotient inside the displayed product of `K`-quotients. -/
noncomputable def cartanCoordinateRangeQuotientToProjectiveCartanProduct
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) :
    ((PRegularConjClass G p → ℤ) ⧸
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) →+
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) :=
  e.toLinearMap.toAddMonoidHom.comp
    (cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient
      (p := p) (A := A) (K := K) (G := G))

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- The product-valued integral quotient map is injective for every product equivalence supplied
by the Cartan coordinate `A`-span quotient. -/
theorem cartanCoordinateRangeQuotientToProjectiveCartanProduct_injective
    (e :
      ((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) :
    Function.Injective
      (cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G) e) :=
  e.injective.comp
    (cartanCoordinateRangeQuotientToProjectiveCartanASpanQuotient_injective
      (p := p) (A := A) (K := K) (G := G))

/-- Nonempty source-product packaging: Serre 18.5(a), transported to the Cartan coordinate
`A`-span, together with integer cast-saturation gives an injective map from the integral Cartan
coordinate quotient into the coordinatewise product of `K`-quotients. -/
theorem cartanCoordinateRangeQuotient_projectiveCartanProductEmbedding_nonempty
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Nonempty
      { φ :
          ((PRegularConjClass G p → ℤ) ⧸
              (cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) →+
            ∀ c : PRegularConjClass G p,
              K ⧸ Submodule.span A
                ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) //
        Function.Injective φ } := by
  rcases
      projectiveCartanCoordinateASpanQuotientLinearEquivPi_nonempty
        (p := p) (A := A) (K := K) (G := G) with
    ⟨e⟩
  exact
    ⟨⟨cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G) e,
      cartanCoordinateRangeQuotientToProjectiveCartanProduct_injective
        (p := p) (A := A) (K := K) (G := G) e⟩⟩

end ProjectiveCartanIntegralQuotient

end Representation
