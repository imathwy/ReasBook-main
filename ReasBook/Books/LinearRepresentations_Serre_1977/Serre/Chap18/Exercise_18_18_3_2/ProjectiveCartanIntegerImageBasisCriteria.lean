import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageReverse

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegerImageBasisCriteria

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanIntegerImageBasisCriteriaFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegerImageBasisCriteriaDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsLocalRing A] [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
  [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Expand the cast of an integer-valued regular-class function in the standard integer
point-mass basis. -/
theorem regularIntegerFunctionCast_eq_sum_single
    (f : PRegularConjClass G p → ℤ) :
    regularIntegerFunctionCast (p := p) (K := K) (G := G) f =
      ∑ i : PRegularConjClass G p,
        f i • regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single i (1 : ℤ)) := by
  ext c
  simp [regularIntegerFunctionCast, Pi.single_apply]

omit [IsLocalRing A] [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
  [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Casting commutes with finite integer linear combinations. -/
theorem regularIntegerFunctionCast_sum_zsmul
    (n : PRegularConjClass G p → ℤ)
    (g : PRegularConjClass G p → PRegularConjClass G p → ℤ) :
    regularIntegerFunctionCast (p := p) (K := K) (G := G) (∑ i, n i • g i) =
      ∑ i : PRegularConjClass G p,
        n i • regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [map_zsmul]

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Basis-vector criterion for the forward inverse-Brauer integer-submodule condition. -/
theorem brauerInverse_forward_integerSubmodule_of_basis
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ i : PRegularConjClass G p,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single i (1 : ℤ))) -
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
  intro f
  choose g hg using hbasis
  refine ⟨∑ i, f i • g i, ?_⟩
  let T :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let D := regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  have hdiff :
      T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (∑ i, f i • g i) =
        ∑ i : PRegularConjClass G p,
          f i •
            (T.symm
                (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (Pi.single i (1 : ℤ))) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i)) := by
    rw [regularIntegerFunctionCast_eq_sum_single (p := p) (K := K) (G := G) f]
    rw [regularIntegerFunctionCast_sum_zsmul (p := p) (K := K) (G := G) f g]
    rw [map_sum]
    simp_rw [map_zsmul]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [zsmul_sub]
  rw [hdiff]
  exact Submodule.sum_mem D fun i _hi => zsmul_mem (hg i) (f i)

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Basis-vector criterion for the reverse inverse-Brauer integer-submodule condition. -/
theorem brauerInverse_reverse_integerSubmodule_of_basis
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbasis :
      ∀ i : PRegularConjClass G p,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single i (1 : ℤ)) -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  intro g
  choose f hf using hbasis
  refine ⟨∑ i, g i • f i, ?_⟩
  let T :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let D := regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  have hdiff :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
          T.symm
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (∑ i, g i • f i)) =
        ∑ i : PRegularConjClass G p,
          g i •
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single i (1 : ℤ)) -
              T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) (f i))) := by
    rw [regularIntegerFunctionCast_eq_sum_single (p := p) (K := K) (G := G) g]
    rw [regularIntegerFunctionCast_sum_zsmul (p := p) (K := K) (G := G) g f]
    rw [map_sum]
    simp_rw [map_zsmul]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [zsmul_sub]
  rw [hdiff]
  exact Submodule.sum_mem D fun i _hi => zsmul_mem (hf i) (g i)

/-- Basis-vector criterion for the final concrete image-match statement. -/
theorem concreteProjectiveCartanProductImageMatchesIntegerImage_of_brauerInverse_basis
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hforward :
      ∀ i : PRegularConjClass G p,
        ∃ g : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single i (1 : ℤ))) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hreverse :
      ∀ i : PRegularConjClass G p,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single i (1 : ℤ)) -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    concreteProjectiveCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  exact
    concreteProjectiveCartanProductImageMatchesIntegerImage_of_brauerInverse_integerSubmodules
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (brauerInverse_forward_integerSubmodule_of_basis
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hforward)
      (brauerInverse_reverse_integerSubmodule_of_basis
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hreverse)

end ProjectiveCartanIntegerImageBasisCriteria

end Representation
