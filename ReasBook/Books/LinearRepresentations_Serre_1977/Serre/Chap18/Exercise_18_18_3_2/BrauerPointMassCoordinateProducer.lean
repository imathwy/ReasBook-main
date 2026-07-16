import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionProducer
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulBlocker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassCoordinateProducer

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerPointMassCoordinateProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassCoordinateProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The residual row-difference left after subtracting the regular restriction of the chosen
projective envelope from the desired point-mass row.

The companion producer already proves the projective-envelope regular restriction itself is in
Serre's centralizer-`p`-part divisibility lattice.  This definition records exactly the remaining
coordinatewise input needed to close the fixed point-mass row, without asserting that a single
projective envelope is equal to that row. -/
def brauerPointMassProjectiveEnvelopeResidualDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

/-- Once the residual row-difference is known, the projective-envelope divisibility producer
closes the fixed point-mass coordinate divisibility statement. -/
theorem brauerPointMassCoordinateDivisibility_of_projectiveEnvelopeResidualDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    brauerPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c d
  have hprojective :=
    coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
  rcases hresidual c d with ⟨a, ha⟩
  rcases hprojective c d with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  let x : K :=
    FDRep.modularCharacterOnPRegularConjClass
      (p := p) (G := G) (A := K) (π c)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d
  let y : K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
  have hsplit : x = (x - y) + y := by ring
  have hx_sub : x - y =
      algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
    simpa [x, y] using ha
  have hy :
      y = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * b) := by
    simpa [y] using hb
  calc
    FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d
        = (x - y) + y := hsplit
    _ =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) +
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * b) := by
          rw [hx_sub, hy]
    _ =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * (a + b)) := by
          rw [← map_add, mul_add]

/-- Conversely, a fixed point-mass divisibility proof implies the residual divisibility after
subtracting any coordinate-normalized projective-envelope regular-restriction row. -/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_of_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hpoint :
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c d
  have hprojective :=
    coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
  rcases hpoint c d with ⟨a, ha⟩
  rcases hprojective c d with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  let x : K :=
    FDRep.modularCharacterOnPRegularConjClass
      (p := p) (G := G) (A := K) (π c)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d
  let y : K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
  have hx :
      x = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
    simpa [x] using ha
  have hy :
      y = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * b) := by
    simpa [y] using hb
  calc
    (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d) -
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d
        = x - y := rfl
    _ =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) -
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * b) := by
          rw [hx, hy]
    _ =
        algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * (a - b)) := by
          rw [← map_sub, mul_sub]

/-- For a fixed coordinate-normalized family and chosen projective envelopes, the residual
form is equivalent to the original point-mass coordinate divisibility.  The equivalence uses only
that projective-envelope rows themselves satisfy Serre's centralizer-`p`-part divisibility. -/
theorem brauerPointMassProjectiveEnvelopeResidualDivisibility_iff_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope) :
    brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P ↔
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  constructor
  · exact
      brauerPointMassCoordinateDivisibility_of_projectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope
  · exact
      brauerPointMassProjectiveEnvelopeResidualDivisibility_of_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope

/-- Existential residual form for one coordinate-normalized family and its projective envelopes.
-/
def regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)
              ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        ∃ P : PRegularConjClass G p →
            FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
          ∃ _ :
            ∀ c, ∃ f :
              (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
              f.IsProjectiveEnvelope,
            brauerPointMassProjectiveEnvelopeResidualDivisibility
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P

/-- The residual form is a precise adapter to the existing point-mass coordinate blocker. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility_of_projectiveEnvelopeResidualDivisibility
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with
    ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hresidual⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassCoordinateDivisibility_of_projectiveEnvelopeResidualDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope hresidual

/-- The existential residual formulation is equivalent to the existing existential point-mass
coordinate blocker.  In the forward direction, projective envelopes are supplied by the standard
finite projective-envelope existence theorem for simple `k[G]`-modules. -/
theorem
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_coordinateDivisibility :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility_of_projectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)
  · rintro ⟨π, hπ_simple, hπ_coord, hpoint⟩
    have hP_exists :
        ∀ c : PRegularConjClass G p,
          ∃ P : FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
            ∃ f : P.V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
              f.IsProjectiveEnvelope := by
      intro c
      letI : Simple (π c) := hπ_simple c
      exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
    choose P hP_envelope using hP_exists
    refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
    exact
      brauerPointMassProjectiveEnvelopeResidualDivisibility_of_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hpoint

end BrauerPointMassCoordinateProducer

section FullMixedModelBrauerPointMassCoordinateProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassCoordinateProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassCoordinateProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic residual version of the point-mass coordinate blocker. -/
def fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed residual blocker is equivalent to the endpoint-facing point-mass coordinate
blocker. -/
theorem
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker_iff_coordinateDivisibilityBlocker :
    fullMixedModelPointMassProjectiveEnvelopeResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).1
        (hblock (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassProjectiveEnvelopeResidualDivisibility_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

end FullMixedModelBrauerPointMassCoordinateProducer

end Representation
