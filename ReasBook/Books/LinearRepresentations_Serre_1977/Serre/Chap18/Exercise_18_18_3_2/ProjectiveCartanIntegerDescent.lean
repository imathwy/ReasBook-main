import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanASpan

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanIntegerDescent

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local instance instFintypePRegularConjClassProjectiveCartanIntegerDescent :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance instDecidableEqPRegularConjClassProjectiveCartanIntegerDescent :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Helper for Exercise 18-18.3-2: cast integer-valued regular-class functions to the
fraction-field-valued function space used by the projective-character lattice. -/
noncomputable def regularIntegerFunctionCast :
    (PRegularConjClass G p → ℤ) →+ (PRegularConjClass G p → K) where
  toFun f c := (f c : K)
  map_zero' := by
    ext c
    simp
  map_add' f g := by
    ext c
    simp

omit [IsLocalRing A] [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
  [CharZero K] in
/-- Helper for Exercise 18-18.3-2: casting an integer scaled point mass gives the corresponding
`A`-valued scaled point mass in the fraction field. -/
theorem regularIntegerFunctionCast_scaled_regular_integer_indicator
    (c : PRegularConjClass G p) :
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (scaled_regular_integer_indicator (p := p) (G := G) c) =
      scaled_regular_indicator (p := p) (A := A) (K := K) (G := G) c := by
  ext d
  by_cases hdc : d = c
  · subst hdc
    simp [regularIntegerFunctionCast, scaled_regular_integer_indicator,
      scaled_regular_indicator]
  · simp [regularIntegerFunctionCast, scaled_regular_integer_indicator,
      scaled_regular_indicator, hdc]

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Helper for Exercise 18-18.3-2: every integer diagonal-lattice vector becomes an element of
Serre's regular-value divisibility lattice after casting to the fraction field. -/
theorem regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
    {f : PRegularConjClass G p → ℤ}
    (hf : f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  refine (mem_regularValueDivisibilitySubmodule_iff
    (p := p) (A := A) (K := K) (G := G) _).2 ?_
  intro c
  rcases (mem_regularIntegerDiagonalSubmodule_iff (p := p) (G := G) f).1 hf c with
    ⟨a, ha⟩
  refine ⟨(a : A), ?_⟩
  simp [regularIntegerFunctionCast, ha]

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Helper for Exercise 18-18.3-2: the `A`-span of the cast integer diagonal lattice is exactly
the regular-value divisibility lattice from Serre 18.5(a). -/
theorem regularValueDivisibilitySubmodule_eq_span_regularIntegerDiagonal_cast :
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) =
      Submodule.span A
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) ''
          (regularIntegerDiagonalSubmodule (p := p) (G := G) :
            Set (PRegularConjClass G p → ℤ))) := by
  classical
  apply le_antisymm
  · rw [regularValueDivisibilitySubmodule_eq_span_scaled_regular_indicator
      (p := p) (A := A) (K := K) (G := G)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    have hdiag :
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G) := by
      rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
        (p := p) (G := G)]
      exact Submodule.subset_span ⟨c, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨scaled_regular_integer_indicator (p := p) (G := G) c, hdiag, ?_⟩
    exact (regularIntegerFunctionCast_scaled_regular_integer_indicator
      (p := p) (A := A) (K := K) (G := G) c)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
      (p := p) (A := A) (K := K) (G := G) hf

omit [IsLocalRing A] [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
  [CharP (IsLocalRing.ResidueField A) p] [Finite G] in
/-- Helper for Exercise 18-18.3-2: the cast from integer-valued regular-class functions to the
fraction-field-valued regular-class functions is injective. -/
theorem regularIntegerFunctionCast_injective :
    Function.Injective (regularIntegerFunctionCast (p := p) (K := K) (G := G)) := by
  intro f g hfg
  ext c
  have hc := congrArg (fun φ : PRegularConjClass G p → K ↦ φ c) hfg
  have hc' : (f c : K) = (g c : K) := by
    simpa [regularIntegerFunctionCast] using hc
  exact Int.cast_injective hc'

omit [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [CharZero K] in
/-- Helper for Exercise 18-18.3-2: the field-valued Cartan coordinate map is exactly the cast of
the integer-valued Cartan coordinate map. -/
theorem regularIntegerFunctionCast_cartanCoordinateAddHom
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) =
      projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x := by
  ext c
  rfl

omit [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [CharZero K] in
/-- Helper for Exercise 18-18.3-2: the range of the field-valued Cartan coordinate map is the
cast image of the integer-valued Cartan coordinate range. -/
theorem projectiveCartanCoordinateCast_range_eq_regularIntegerFunctionCast_image
    :
    ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set (PRegularConjClass G p → K)) =
      regularIntegerFunctionCast (p := p) (K := K) (G := G) ''
        (((cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
          Set (PRegularConjClass G p → ℤ)) := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x,
      ⟨x, rfl⟩, ?_⟩
    exact regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G) x
  · rintro ⟨fℤ, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G) x).symm⟩

omit [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [CharZero K] in
/-- Helper for Exercise 18-18.3-2: the `A`-span of the field-valued Cartan coordinate range is
the `A`-span of the cast integer-valued Cartan coordinate range. -/
theorem projectiveCartanCoordinate_span_eq_span_regularIntegerFunctionCast_image :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      Submodule.span A
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) ''
          (((cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
            Set (PRegularConjClass G p → ℤ))) := by
  rw [projectiveCartanCoordinateCast_range_eq_regularIntegerFunctionCast_image
    (p := p) (A := A) (K := K) (G := G)]

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Helper for Exercise 18-18.3-2: if the integer Cartan coordinate range is contained in the
regular diagonal lattice, then its field-valued `A`-span is contained in Serre's regular-value
divisibility lattice. -/
theorem projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_range_le
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) ≤
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  rw [projectiveCartanCoordinate_span_eq_span_regularIntegerFunctionCast_image
    (p := p) (A := A) (K := K) (G := G)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  exact regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
    (p := p) (A := A) (K := K) (G := G) (by simpa using hsubset hf)

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Helper for Exercise 18-18.3-2: if every scaled integer regular-class point mass is already in
the integer Cartan coordinate range, then Serre's regular-value divisibility lattice is contained
in the `A`-span of the field-valued Cartan coordinate range. -/
theorem regularValueDivisibilitySubmodule_le_projectiveCartanCoordinate_span_of_scaled_mem_range
    (hscaled :
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ≤
      Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) := by
  rw [regularValueDivisibilitySubmodule_eq_span_scaled_regular_indicator
    (p := p) (A := A) (K := K) (G := G)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, rfl⟩
  rw [projectiveCartanCoordinate_span_eq_span_regularIntegerFunctionCast_image
    (p := p) (A := A) (K := K) (G := G)]
  have hcast :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
        Submodule.span A
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) ''
            (((cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
              Set (PRegularConjClass G p → ℤ))) :=
    Submodule.subset_span ⟨scaled_regular_integer_indicator (p := p) (G := G) c,
      hscaled c, rfl⟩
  simpa [regularIntegerFunctionCast_scaled_regular_integer_indicator
    (p := p) (A := A) (K := K) (G := G) c] using hcast

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Helper for Exercise 18-18.3-2: the standard integer range criterion has the expected
field-valued `A`-span shadow. -/
theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_range_le_and_scaled_mem
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hscaled :
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact le_antisymm
    (projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_range_le
      (p := p) (A := A) (K := K) (G := G) hsubset)
    (regularValueDivisibilitySubmodule_le_projectiveCartanCoordinate_span_of_scaled_mem_range
      (p := p) (A := A) (K := K) (G := G) hscaled)

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Helper for Exercise 18-18.3-2: if the integer Cartan coordinate range is cast-saturated
inside its field-valued `A`-span, then equality of the `A`-span with Serre's regular-value
divisibility lattice descends to equality with the integer diagonal lattice. -/
theorem cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq_and_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  apply le_antisymm
  · exact hsubset
  · intro f hf
    refine hsaturated f ?_
    rw [hspan]
    exact regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
      (p := p) (A := A) (K := K) (G := G) (by simpa using hf)

omit [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Helper for Exercise 18-18.3-2: the range of `cartanCoordinateAddHom` is the Cartan range
transported by the fixed regular-class coordinate equivalence. -/
theorem cartanCoordinateAddHom_range_eq_cartanHom_range_map :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (cartanHom (IsLocalRing.ResidueField A) G).range.map
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).toAddMonoidHom := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨cartanHom (IsLocalRing.ResidueField A) G x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- Helper for Exercise 18-18.3-2: the Brauer-coordinate map used in
`ProjectiveCartanASpan` is an `A`-linear equivalence after restricting scalars from `K`. -/
noncomputable def projectiveCartanASpanBrauerReprLinearEquiv
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (PRegularConjClass G p → K) ≃ₗ[A] (PRegularConjClass G p → K) :=
  LinearEquiv.restrictScalars A
    (((projectiveCartanASpanBrauerBasis
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite K K (PRegularConjClass G p)))

omit [CharZero K] in
/-- Helper for Exercise 18-18.3-2: the equivalence form of the Brauer-coordinate map has the same
underlying `A`-linear map as `projectiveCartanASpanBrauerRepr`. -/
theorem projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :
      (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K)) =
      projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  rfl

/-- Helper for Exercise 18-18.3-2: combining Serre 18.5(a) with the `c = d ∘ e` triangle gives
the Cartan coordinate span as the Brauer-coordinate image of the regular divisibility lattice. -/
theorem projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord)
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
      Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  rw [← projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G) hω]
  exact projectiveCharacterSubmodule_regularRestriction_brauerRepr_eq_cartanCoordinate_span
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Helper for Exercise 18-18.3-2: the Cartan coordinate `A`-span is obtained from the `A`-span
of the cast integer diagonal lattice by the Brauer-coordinate equivalence. -/
theorem projectiveCartanASpanBrauerRepr_span_regularIntegerDiagonal_cast_eq_cartanCoordinate_span
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord)
        (Submodule.span A
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) ''
            (regularIntegerDiagonalSubmodule (p := p) (G := G) :
              Set (PRegularConjClass G p → ℤ)))) =
      Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) := by
  rw [← regularValueDivisibilitySubmodule_eq_span_regularIntegerDiagonal_cast
    (p := p) (A := A) (K := K) (G := G)]
  exact projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Helper for Exercise 18-18.3-2: the quotient of regular functions by Serre's regular-value
divisibility lattice splits coordinatewise over `A`. This is the coefficient-ring analogue of the
integer diagonal quotient used in part (b). -/
noncomputable def regularValueDivisibilityQuotientLinearEquivPi :
    ((PRegularConjClass G p → K) ⧸
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≃ₗ[A]
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) :=
  Submodule.quotientPi fun c : PRegularConjClass G p ↦
    Submodule.span A
      ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)

/-- Helper for Exercise 18-18.3-2: the `A`-module quotient by the Cartan coordinate span is
equivalent to the coordinatewise quotient by the centralizer-`p`-part ideals. This is the exact
formal output of the current projective-character APIs before the remaining integer descent to
`ℤ`-cokernels. -/
noncomputable def projectiveCartanCoordinateASpanQuotientLinearEquivPi
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    ((PRegularConjClass G p → K) ⧸
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K))) ≃ₗ[A]
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) :=
  (Submodule.Quotient.equiv
      (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
      (Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)))
      (projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
      (by
        simpa [projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
          projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)).symm.trans
    (regularValueDivisibilityQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G))

end ProjectiveCartanIntegerDescent

end Representation
