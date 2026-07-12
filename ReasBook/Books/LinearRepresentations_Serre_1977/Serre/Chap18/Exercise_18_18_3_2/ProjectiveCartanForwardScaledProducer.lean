import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardDiagonalBasis

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanForwardScaledProducer

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanForwardScaledProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanForwardScaledProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The forward fixed-coordinate Cartan-span inclusion gives the scaled-indicator
Brauer-coordinate congruence.

This is the basis-vector version of the B-side forward inclusion: it uses only the established
identity `T(D) = span(cartanCoordinateCast.range)`, where `D` is Serre's regular-value
divisibility lattice. -/
theorem projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_cartanCoordinate_span_le
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hspan_le :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ c : PRegularConjClass G p,
      projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (scaled_regular_integer_indicator (p := p) (G := G) c)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro c
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let S : Submodule A (PRegularConjClass G p → K) :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set (PRegularConjClass G p → K))
  let T : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K) :=
    projectiveCartanASpanBrauerRepr
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hdiag :
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G) := by
    rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
      (p := p) (G := G)]
    exact Submodule.subset_span ⟨c, rfl⟩
  have hcast :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c) ∈ D :=
    regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
      (p := p) (A := A) (K := K) (G := G) hdiag
  have hT_span :
      T (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c)) ∈ S := by
    have hmem :
        T (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (scaled_regular_integer_indicator (p := p) (G := G) c)) ∈
          Submodule.map T D :=
      ⟨regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c), hcast, rfl⟩
    have hmap :=
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    simpa [D, S, T] using (by
      rw [hmap] at hmem
      exact hmem)
  have hT : T (regularIntegerFunctionCast (p := p) (K := K) (G := G)
      (scaled_regular_integer_indicator (p := p) (G := G) c)) ∈ D :=
    hspan_le (by simpa [S] using hT_span)
  exact D.sub_mem hT hcast

/-- The scaled-indicator congruences are exactly the forward fixed-coordinate Cartan-span
inclusion.

The reverse direction is the useful producer. The forward direction records that the
scaled-indicator target is not weaker than the B-side forward inclusion: the scaled indicators
generate Serre's divisibility lattice. -/
theorem projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_iff_cartanCoordinate_span_le
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (∀ c : PRegularConjClass G p,
      projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (scaled_regular_integer_indicator (p := p) (G := G) c)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hscaled
    let D : Submodule A (PRegularConjClass G p → K) :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let T : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K) :=
      projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    have hdiag :
        ∀ f : PRegularConjClass G p → ℤ,
          f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
            projectiveCartanASpanBrauerRepr
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
                (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
                regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
      brauerRepr_forward_regularIntegerDiagonal_congruence_of_scaled_indicators
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hscaled
    have hforward :
        Submodule.map T D ≤ D := by
      simpa [D, T] using
        projectiveCartanASpanBrauerRepr_regularValueDivisibility_forward_le_of_regularIntegerDiagonal_congruence
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hdiag
    intro y hy
    have hmap :=
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    have hy_map0 :
        y ∈
          Submodule.map
            (projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) := by
      rw [hmap]
      exact hy
    have hy_map : y ∈ Submodule.map T D := by
      simpa [D, T] using hy_map0
    exact hforward hy_map
  · intro hspan_le
    exact
      projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_cartanCoordinate_span_le
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hspan_le

/-- Fixed-coordinate Cartan range inclusion gives the scaled-indicator forward congruence. -/
theorem projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_cartanCoordinate_range_le
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrange_le :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    ∀ c : PRegularConjClass G p,
      projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (scaled_regular_integer_indicator (p := p) (G := G) c)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_cartanCoordinate_span_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_range_le
        (p := p) (A := A) (K := K) (G := G) hrange_le)

/-- Coordinatewise Cartan divisibility is enough for the scaled-indicator forward congruence. -/
theorem projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_coordinate_divisible
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hdiv :
      ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
            (ConjClasses.centralizerPPart p c.1 : ℤ) * a) :
    ∀ c : PRegularConjClass G p,
      projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
          (regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (scaled_regular_integer_indicator (p := p) (G := G) c)) -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_cartanCoordinate_range_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_coordinate_divisible
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) hdiv)

end ProjectiveCartanForwardScaledProducer

section FullMixedModelProjectiveCartanForwardScaledProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelProjectiveCartanForwardScaledProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelProjectiveCartanForwardScaledProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model form of the forward fixed-coordinate `A`-span inclusion. -/
def fullMixedModelProjectiveCartanCoordinateSpanLeStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model scaled-indicator target is equivalent to the forward fixed-coordinate
Cartan-span inclusion. -/
theorem fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement_iff_cartanCoordinateSpanLe :
    fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement
        (p := p) (k := k) (G := G) ↔
      fullMixedModelProjectiveCartanCoordinateSpanLeStatement
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hscaled A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hscaled (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hbasis⟩
    exact
      (projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_iff_cartanCoordinate_span_le
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hbasis
  · intro hspan A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_cartanCoordinate_span_le
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (hspan (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Producer from the forward fixed-coordinate Cartan-span inclusion to the scaled-indicator
target. -/
theorem fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement_of_cartanCoordinateSpanLe
    (hspan :
      fullMixedModelProjectiveCartanCoordinateSpanLeStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement
      (p := p) (k := k) (G := G) :=
  (fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement_iff_cartanCoordinateSpanLe
    (p := p) (k := k) (G := G)).2 hspan

/-- Full mixed-model form of the integer Cartan-coordinate range inclusion. -/
def fullMixedModelForwardScaledCartanCoordinateRangeLeStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup

/-- Full mixed-model coordinatewise Cartan divisibility. This is the fixed-coordinate forward
half only; no generator statement is included. -/
def fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
            (ConjClasses.centralizerPPart p c.1 : ℤ) * a

omit [IsAlgClosed k] [CharP k p] in
/-- Integer range inclusion gives the full mixed-model `A`-span inclusion. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanLeStatement_of_cartanCoordinateRangeLe
    (hrange_le :
      fullMixedModelForwardScaledCartanCoordinateRangeLeStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanLeStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_range_le
      (p := p) (A := A) (K := K) (G := G)
      (hrange_le (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Coordinatewise divisibility gives the full mixed-model integer range inclusion. -/
theorem fullMixedModelForwardScaledCartanCoordinateRangeLeStatement_of_coordinateDivisibility
    (hdiv :
      fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledCartanCoordinateRangeLeStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_coordinate_divisible
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (hdiv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The existing divisibility-and-generators package contains the smaller forward divisibility
input isolated here. -/
theorem fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_divisibilityAndGenerators
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hsource (A := A) (K := K) e0 with ⟨_π, _hπ_coord, hdiv, _hgen⟩
  exact hdiv

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed-model scaled-indicator target follows from the smaller fixed-coordinate
integer range inclusion. -/
theorem fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement_of_cartanCoordinateRangeLe
    (hrange_le :
      fullMixedModelForwardScaledCartanCoordinateRangeLeStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_cartanCoordinate_range_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (hrange_le (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Coordinatewise Cartan divisibility is the strict remaining source input for the full
scaled-indicator target. -/
theorem fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement_of_coordinateDivisibility
    (hdiv :
      fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_coordinate_divisible
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (hdiv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The older stronger source package closes the scaled-indicator target through its forward
coordinate-divisibility half. -/
theorem
    fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement_of_coordinateDivisibilityAndGenerators
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hsource (A := A) (K := K) e0 with ⟨_π0, _hπ0_coord, hdiv, _hgen⟩
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    projectiveCartanASpanBrauerRepr_forward_scaledIndicator_congruence_of_coordinate_divisible
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hdiv

end FullMixedModelProjectiveCartanForwardScaledProducer

end Representation
