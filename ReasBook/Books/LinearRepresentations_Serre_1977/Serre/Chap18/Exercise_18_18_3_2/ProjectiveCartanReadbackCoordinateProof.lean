import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanReadbackPreservationEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithfulProof

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanReadbackCoordinateProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance readbackCoordinateProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance readbackCoordinateProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The source-faithful regular-value congruence proves exactly the local projective-envelope
congruence blocker: the regular restriction of each projective-envelope row and the cast
Cartan-coordinate readback are congruent modulo Serre's regular-value divisibility lattice. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence_of_regularValueCongruence
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
      (p := p) (A := A) (K := K) (G := G) P := by
  intro c
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let row : PRegularConjClass G p → K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)
  let χ : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
      (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀)
  let coord : PRegularConjClass G p → ℤ :=
    cartanCoordinateAddHom
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀
  let coordK : PRegularConjClass G p → K :=
    regularIntegerFunctionCast (p := p) (K := K) (G := G) coord
  have hrow_eq : row = χ := by
    simpa [row, χ, projectiveCartanASpanFieldLift] using
      (regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row
        (p := p) (A := A) (K := K) (G := G) (x := [P c]ₚ₀))
  have hcong : χ - coordK ∈ D := by
    simpa [χ, coordK, coord, cartanCoordinateAddHom, D] using
      hregular (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀)
  simpa [coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence,
    row, coordK, coord, D, hrow_eq] using hcong

/-- Direct local cast-membership consequence of the source-faithful regular-value congruence,
factored through the projective-envelope congruence blocker. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_sourceFaithfulRegularValueCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence_of_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P hregular)

/-- Direct integer-coordinate divisibility consequence of the source-faithful regular-value
congruence for projective-envelope Cartan rows. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_sourceFaithfulRegularValueCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ c d : PRegularConjClass G p,
      ∃ a : ℤ,
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
          (ConjClasses.centralizerPPart p d.1 : ℤ) * a := by
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence_of_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P hregular)

/-- The source-faithful regular-value congruence is enough to preserve divisibility after
Brauer-coordinate readback on projective-envelope rows.

The proof is local and does not use the final Cartan range/product endpoint.  The projective row
is already in Serre's regular-value divisibility lattice; the regular-value congruence identifies
that row modulo the same lattice with its fixed Cartan-coordinate cast, so the cast row is in the
lattice as well. -/
theorem
    coordinate_normalized_projective_envelope_brauerReadbackCoordinateDivisibility_of_regularValueCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    coordinate_normalized_projective_envelope_brauerReadbackCoordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c d
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let row : PRegularConjClass G p → K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)
  let χ : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
      (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀)
  let coord : PRegularConjClass G p → ℤ :=
    cartanCoordinateAddHom
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀
  let coordK : PRegularConjClass G p → K :=
    regularIntegerFunctionCast (p := p) (K := K) (G := G) coord
  have hrow_eq : row = χ := by
    simpa [row, χ, projectiveCartanASpanFieldLift] using
      (regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row
        (p := p) (A := A) (K := K) (G := G) (x := [P c]ₚ₀))
  have hrowD : row ∈ D :=
    coordinate_normalized_projective_envelope_regularRestriction_mem_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c
  have hχD : χ ∈ D := by
    simpa [hrow_eq, D] using hrowD
  have hcong : χ - coordK ∈ D := by
    simpa [χ, coordK, coord, cartanCoordinateAddHom, D] using
      hregular (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀)
  have hcoordD : coordK ∈ D := by
    have hdiff : χ - (χ - coordK) ∈ D := D.sub_mem hχD hcong
    have hdiff_eq : χ - (χ - coordK) = coordK := by
      ext e
      simp only [Pi.sub_apply]
      ring
    simpa [hdiff_eq] using hdiff
  rcases
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) coordK).1
        (by simpa [D] using hcoordD) d with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hrepr :=
    projectiveCartanASpanBrauerRepr_regularRestriction_projectiveCharacter
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord [P c]ₚ₀
  calc
    projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord row d
        = coordK d := by
            simpa [row, coordK, coord, projectiveCartanCoordinateCast,
              regularIntegerFunctionCast] using congrFun hrepr d
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := ha

end ProjectiveCartanReadbackCoordinateProof

section FullMixedModelProjectiveCartanReadbackCoordinateProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelReadbackCoordinateProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelReadbackCoordinateProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model reduction of the projective-envelope cast target to the local congruence
blocker, supplied here by the source-faithful regular-value congruence. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateRegularValueCongruenceStatement_of_regularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateRegularValueCongruenceStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G) P
      (hregular (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model B-side bridge from the source-faithful regular-value congruence to the
projective-envelope readback-preservation input. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_regularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
      (p := p) (k := k) (G := G) := by
  exact
    (fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_iff_regularValueCongruence
      (p := p) (k := k) (G := G)).2
      (fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateRegularValueCongruenceStatement_of_regularValueCongruence
        (p := p) (k := k) (G := G) hregular)

omit [IsAlgClosed k] [CharP k p] in
/-- The existing full mixed-model Brauer-basis readback input supplies the B-side
projective-envelope readback-preservation input. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
      (p := p) (k := k) (G := G) := by
  refine
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_of_regularValueCongruence
      (p := p) (k := k) (G := G) ?_
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
      (p := p) (A := A) (K := K) (G := G)
      (hread (A := A) (K := K) e0)

end FullMixedModelProjectiveCartanReadbackCoordinateProof

end Representation
