import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageReverse

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegerImageReverseSubmodule

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanIntegerImageReverseSubmoduleFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanIntegerImageReverseSubmoduleDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Cartan-span-side formulation of the reverse integer representative condition.

The existing reverse submodule hypothesis is phrased after applying `T.symm`, where `T` is the
Brauer-coordinate equivalence. Since the established comparison theorem gives `T(D) = S`, with
`D` the regular value-divisibility lattice and `S` the Cartan-coordinate `A`-span, it is enough to
check the congruence before applying `T.symm`. -/
theorem brauerInverse_reverseIntegerSubmodule_of_cartanCoordinateSpan
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hspan :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord)
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              Submodule.span A
                ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                  Set (PRegularConjClass G p → K))) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  let E := PRegularConjClass G p → K
  let D : Submodule A E :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let S : Submodule A E :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set E)
  let T : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hTD : Submodule.map (T : E →ₗ[A] E) D = S := by
    simpa [D, S, T, E, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hSD : Submodule.map (T.symm : E →ₗ[A] E) S = D :=
    (Submodule.map_symm_eq_iff T).mpr hTD
  intro g
  rcases hspan g with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  have hfS : T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈ S := by
    simpa [S, T, E] using hf
  have hmap :
      T.symm
          (T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
        Submodule.map (T.symm : E →ₗ[A] E) S := by
    exact Submodule.mem_map.mpr ⟨_, hfS, rfl⟩
  have hD :
      T.symm
          (T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈ D := by
    simpa [hSD] using hmap
  simpa [D, T, E, map_sub] using hD

/-- The reverse submodule condition implies the Cartan-span-side condition. This is the converse
of `brauerInverse_reverseIntegerSubmodule_of_cartanCoordinateSpan`, and records that the proposed
Cartan-span-side form is not a strengthening. -/
theorem cartanCoordinateSpan_of_brauerInverse_reverseIntegerSubmodule
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsub :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord)
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              Submodule.span A
                ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                  Set (PRegularConjClass G p → K)) := by
  let E := PRegularConjClass G p → K
  let D : Submodule A E :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let S : Submodule A E :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set E)
  let T : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hTD : Submodule.map (T : E →ₗ[A] E) D = S := by
    simpa [D, S, T, E, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  intro g
  rcases hsub g with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  have hfD : regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
      T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈ D := by
    simpa [D, T, E] using hf
  have hmap :
      T
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) ∈
        Submodule.map (T : E →ₗ[A] E) D := by
    exact Submodule.mem_map.mpr ⟨_, hfD, rfl⟩
  have hS :
      T
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f)) ∈ S := by
    simpa [hTD] using hmap
  simpa [S, T, E, map_sub] using hS

/-- Equivalence between the existing reverse submodule hypothesis and the Cartan-span-side form.
-/
theorem brauerInverse_reverseIntegerSubmodule_iff_cartanCoordinateSpan
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      (∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord)
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              Submodule.span A
                ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                  Set (PRegularConjClass G p → K))) := by
  constructor
  · exact cartanCoordinateSpan_of_brauerInverse_reverseIntegerSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  · exact brauerInverse_reverseIntegerSubmodule_of_cartanCoordinateSpan
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Finite-generator reduction for the Cartan-span-side reverse condition.

It is enough to solve the congruence for the standard integer point masses. The witness for a
general integer-valued function is the same integer linear combination of the point-mass witnesses.
-/
theorem cartanCoordinateSpan_of_single_cartanCoordinateSpan
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsingle :
      ∀ c : PRegularConjClass G p,
        ∃ f : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord)
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              Submodule.span A
                ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                  Set (PRegularConjClass G p → K))) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord)
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              Submodule.span A
                ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                  Set (PRegularConjClass G p → K)) := by
  classical
  let E := PRegularConjClass G p → K
  let S : Submodule A E :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set E)
  let T : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  choose f hf using hsingle
  have hfS :
      ∀ c : PRegularConjClass G p,
        T
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (f c) ∈ S := by
    intro c
    simpa [S, T, E] using hf c
  intro g
  refine ⟨∑ c : PRegularConjClass G p, g c • f c, ?_⟩
  have hg :
      g =
        ∑ c : PRegularConjClass G p,
          g c • (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
    ext d
    simp [Pi.single_apply]
  have hcast_g :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) g =
        ∑ c : PRegularConjClass G p,
          g c •
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
    rw [hg]
    ext d
    simp [regularIntegerFunctionCast, Pi.single_apply, zsmul_eq_mul]
  have hcast_f :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (∑ c : PRegularConjClass G p, g c • f c) =
        ∑ c : PRegularConjClass G p,
          g c • regularIntegerFunctionCast (p := p) (K := K) (G := G) (f c) := by
    ext d
    simp [regularIntegerFunctionCast, zsmul_eq_mul]
  have hsum :
      (∑ c : PRegularConjClass G p,
        g c •
          (T
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) (f c))) ∈ S := by
    refine Submodule.sum_mem S ?_
    intro c _hc
    exact zsmul_mem (hfS c) (g c)
  have htarget :
      T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (∑ c : PRegularConjClass G p, g c • f c) =
        ∑ c : PRegularConjClass G p,
          g c •
            (T
                (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (f c)) := by
    rw [hcast_g, hcast_f]
    rw [map_sum]
    simp only [map_zsmul]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    rw [zsmul_sub]
  change
    T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (∑ c : PRegularConjClass G p, g c • f c) ∈ S
  rw [htarget]
  exact hsum

/-- Point-mass criterion for the original reverse submodule hypothesis. -/
theorem brauerInverse_reverseIntegerSubmodule_of_single_cartanCoordinateSpan
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsingle :
      ∀ c : PRegularConjClass G p,
        ∃ f : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord)
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              Submodule.span A
                ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                  Set (PRegularConjClass G p → K))) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          regularIntegerFunctionCast (p := p) (K := K) (G := G) g -
            (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord).symm
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    brauerInverse_reverseIntegerSubmodule_of_cartanCoordinateSpan
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (cartanCoordinateSpan_of_single_cartanCoordinateSpan
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hsingle)

/-- Direct reverse representative adapter using the Cartan-span-side formulation. -/
theorem concreteProjectiveCartanProduct_reverseRepresentative_of_cartanCoordinateSpan
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hspan :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ f : PRegularConjClass G p → ℤ,
          (projectiveCartanASpanBrauerReprLinearEquiv
              (p := p) (A := A) (K := K) (G := G)
              π hπ_simple hπ_coord)
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              Submodule.span A
                ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                  Set (PRegularConjClass G p → K))) :
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
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) := by
  exact
    concreteProjectiveCartanProduct_reverseRepresentative_of_brauerInverse_integerSubmodule
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (brauerInverse_reverseIntegerSubmodule_of_cartanCoordinateSpan
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hspan)

end ProjectiveCartanIntegerImageReverseSubmodule

end Representation
