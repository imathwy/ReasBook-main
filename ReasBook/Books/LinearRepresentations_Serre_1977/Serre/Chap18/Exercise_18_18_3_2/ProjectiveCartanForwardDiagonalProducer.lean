import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateDivisibilityProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanForwardDiagonalProducer

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanForwardDiagonalProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanForwardDiagonalProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Fixed-coordinate span inclusion gives the forward diagonal Brauer-coordinate congruence.

This is the forward half needed by the B-side source-span route.  It only uses the already proved
identity
`T(D) = span(cartanCoordinateCast.range)`, where `D` is Serre's regular-value divisibility
lattice, and does not use the final Cartan range/product endpoint. -/
theorem
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_cartanCoordinate_span_le
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
    ∀ f : PRegularConjClass G p → ℤ,
      f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
        projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro f hf
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let T : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K) :=
    projectiveCartanASpanBrauerRepr
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hcast :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈ D :=
    regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
      (p := p) (A := A) (K := K) (G := G) hf
  have hT_span :
      T (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) := by
    have hmem :
        T (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈
          Submodule.map T D :=
      ⟨regularIntegerFunctionCast (p := p) (K := K) (G := G) f, hcast, rfl⟩
    have hmap :=
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    simpa [D, T] using (by
      rw [hmap] at hmem
      exact hmem)
  have hT : T (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) ∈ D :=
    hspan_le hT_span
  exact D.sub_mem hT hcast

/-- The forward diagonal congruence is equivalent to the fixed-coordinate Cartan-span inclusion.

Thus B3's remaining forward blocker is precisely the forward inclusion
`span(cartanCoordinateCast.range) ≤ regularValueDivisibilitySubmodule`, not the stronger final
range equality. -/
theorem
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_iff_cartanCoordinate_span_le
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (∀ f : PRegularConjClass G p → ℤ,
      f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
        projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hdiag
    let D : Submodule A (PRegularConjClass G p → K) :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let T : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K) :=
      projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
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
      projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_cartanCoordinate_span_le
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hspan_le

/-- Fixed-coordinate Cartan range inclusion gives the forward diagonal congruence. -/
theorem projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_cartanCoordinate_range_le
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
    ∀ f : PRegularConjClass G p → ℤ,
      f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
        projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_cartanCoordinate_span_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_range_le
        (p := p) (A := A) (K := K) (G := G) hrange_le)

/-- Coordinatewise Cartan divisibility is enough for the forward diagonal congruence.

This is the strict B3 reduction: no fixed generator statement and no final range/product theorem
is used. -/
theorem projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_coordinate_divisible
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
    ∀ f : PRegularConjClass G p → ℤ,
      f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
        projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_cartanCoordinate_range_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_coordinate_divisible
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) hdiv)

end ProjectiveCartanForwardDiagonalProducer

section FullMixedModelProjectiveCartanForwardDiagonalProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelProjectiveCartanForwardDiagonalProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelProjectiveCartanForwardDiagonalProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model form of the forward Cartan-coordinate inclusion. -/
def fullMixedModelCartanCoordinateRangeLeStatement : Prop :=
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

/-- Full mixed-model coordinatewise Cartan divisibility.  This is strictly smaller than
`fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement`: the generator half is not
needed for the forward diagonal congruence. -/
def fullMixedModelCartanCoordinateDivisibilityStatement : Prop :=
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

/-- Full mixed-model coordinatewise Cartan divisibility restricted to the nontrivial
centralizer `p`-part coordinates. -/
def fullMixedModelCartanCoordinateNontrivialDivisibilityStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
        ConjClasses.centralizerPPart p c.1 ≠ 1 →
          ∃ a : ℤ,
            cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
              (ConjClasses.centralizerPPart p c.1 : ℤ) * a

omit [IsAlgClosed k] [CharP k p] in
/-- Nontrivial centralizer `p`-part divisibility is enough for the full coordinatewise
Cartan-divisibility statement; trivial `p`-part coordinates are automatic. -/
theorem fullMixedModelCartanCoordinateDivisibilityStatement_of_nontrivial
    (hdiv :
      fullMixedModelCartanCoordinateNontrivialDivisibilityStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    cartanCoordinateAddHom_coordinate_divisible_of_nontrivial_centralizerPPart
      (p := p) (A := A) (G := G)
      (hdiv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Coordinatewise divisibility gives the full mixed-model forward range inclusion. -/
theorem fullMixedModelCartanCoordinateRangeLeStatement_of_coordinateDivisibility
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateRangeLeStatement (p := p) (k := k) (G := G) := by
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
theorem fullMixedModelCartanCoordinateDivisibilityStatement_of_divisibilityAndGenerators
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hsource (A := A) (K := K) e0 with ⟨_π, _hπ_coord, hdiv, _hgen⟩
  exact hdiv

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-envelope cast regular-value input supplies the Cartan-coordinate
divisibility input needed by the full forward diagonal producer. -/
theorem fullMixedModelCartanCoordinateDivisibilityStatement_of_projectiveEnvelope_castRegularValue
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_projectiveEnvelope_castRegularValue
      (p := p) (k := k) (G := G) hcast
      (A := A) (K := K) e0

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-envelope cast regular-value input gives the forward Cartan-coordinate range
inclusion used by the full forward diagonal producer. -/
theorem fullMixedModelCartanCoordinateRangeLeStatement_of_projectiveEnvelope_castRegularValue
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanCoordinateRangeLeStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_coordinate_divisible
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_projectiveEnvelope_castRegularValue
        (p := p) (k := k) (G := G) hcast
        (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full B3 forward diagonal statement follows from the smaller fixed-coordinate range
inclusion. -/
theorem fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_cartanCoordinateRangeLe
    (hrange_le :
      fullMixedModelCartanCoordinateRangeLeStatement (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
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
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_cartanCoordinate_range_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (hrange_le (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Coordinatewise Cartan divisibility is the strict remaining source input for the full B3
forward diagonal congruence. -/
theorem fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_coordinateDivisibility
    (hdiv :
      fullMixedModelCartanCoordinateDivisibilityStatement (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
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
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_coordinate_divisible
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (hdiv (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The projective-envelope cast regular-value input closes the full forward diagonal
congruence through the non-cyclic coordinate-divisibility route. -/
theorem
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_projectiveEnvelope_castRegularValue
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
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
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_coordinate_divisible
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_projectiveEnvelope_castRegularValue
        (p := p) (k := k) (G := G) hcast
        (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- In particular, the older stronger source package still closes B3, but only through its
coordinate-divisibility half. -/
theorem fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_coordinateDivisibilityAndGenerators
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
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
    projectiveCartanASpanBrauerRepr_regularIntegerDiagonal_congruence_of_coordinate_divisible
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hdiv

end FullMixedModelProjectiveCartanForwardDiagonalProducer

end Representation
