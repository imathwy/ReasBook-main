import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageReverse

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegerImageForwardSubmodule

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanIntegerImageForwardSubmoduleFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegerImageForwardSubmoduleDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Finite-basis reduction for the forward inverse-Brauer submodule condition.

It is enough to check the congruence for the standard integer basis vectors
`Pi.single c 1`; arbitrary integer-valued regular-class functions are finite integer
linear combinations of those vectors, and the divisibility target is an additive subgroup. -/
theorem brauerInverse_integerSubmodule_of_basisVector_congruences
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ c : PRegularConjClass G p,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      ∀ f : PRegularConjClass G p → ℤ,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  let T : (PRegularConjClass G p → K) ≃ₗ[A] (PRegularConjClass G p → K) :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  choose g hg using hbasis
  intro f
  let gsum : PRegularConjClass G p → ℤ := ∑ c : PRegularConjClass G p, f c • g c
  refine ⟨gsum, ?_⟩
  have hcast_sum :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f =
        ∑ c : PRegularConjClass G p,
          f c •
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
    ext d
    simp [regularIntegerFunctionCast, Pi.single_apply]
  have hT_sum :
      T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) =
        ∑ c : PRegularConjClass G p,
          f c •
            T.symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) := by
    rw [hcast_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [map_zsmul]
  have hgsum_cast :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum =
        ∑ c : PRegularConjClass G p,
          f c • regularIntegerFunctionCast (p := p) (K := K) (G := G) (g c) := by
    ext d
    simp [gsum, regularIntegerFunctionCast, Finset.sum_apply]
  have hdiff :
      T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum =
        ∑ c : PRegularConjClass G p,
          f c •
            (T.symm
                (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (g c)) := by
    rw [hT_sum, hgsum_cast]
    symm
    calc
      (∑ c : PRegularConjClass G p,
          f c •
            (T.symm
                (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (g c))) =
          ∑ c : PRegularConjClass G p,
            (f c •
                T.symm
                  (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                    (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
              f c • regularIntegerFunctionCast (p := p) (K := K) (G := G) (g c)) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [zsmul_sub]
      _ =
          (∑ c : PRegularConjClass G p,
              f c •
                T.symm
                  (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                    (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))) -
            ∑ c : PRegularConjClass G p,
              f c • regularIntegerFunctionCast (p := p) (K := K) (G := G) (g c) := by
            rw [Finset.sum_sub_distrib]
  rw [hdiff]
  refine Submodule.sum_mem D ?_
  intro c _
  exact D.toAddSubgroup.zsmul_mem (by simpa [D, T] using hg c) (f c)

/-- Forward representative condition reduced to basis-vector inverse-Brauer congruences. -/
theorem concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_basisVectorSubmodule
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ c : PRegularConjClass G p,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
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
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) := by
  exact
    concreteProjectiveCartanProduct_forwardRepresentative_of_brauerInverse_integerSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (brauerInverse_integerSubmodule_of_basisVector_congruences
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis)

end ProjectiveCartanIntegerImageForwardSubmodule

end Representation
