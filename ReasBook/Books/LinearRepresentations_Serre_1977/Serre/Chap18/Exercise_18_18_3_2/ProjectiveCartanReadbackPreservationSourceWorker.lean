import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ForwardDiagonalWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanReadbackCoordinateProof

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanReadbackPreservationSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance readbackPreservationSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance readbackPreservationSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal forward source statement for this local B-side readback problem.

This is only the forward fixed-coordinate inclusion from Serre `18.5(b)`: the `A`-span of the
fixed Cartan-coordinate rows is contained in Serre's regular-value divisibility lattice.  It is
strictly weaker than the final span/range equality and does not use any Cartan cokernel/product
endpoint. -/
def projectiveCartanReadbackPreservationForwardSource : Prop :=
  Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set (PRegularConjClass G p → K)) ≤
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharZero K]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The forward source immediately gives regular-value membership for each projective-envelope
Cartan-coordinate cast row. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_forwardSource
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hsource :
      projectiveCartanReadbackPreservationForwardSource
        (p := p) (A := A) (K := K) (G := G)) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro c
  have hcast_span :
      projectiveCartanCoordinateCast
          (p := p) (A := A) (K := K) (G := G) [P c]ₚ₀ ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) :=
    Submodule.subset_span ⟨[P c]ₚ₀, rfl⟩
  have hcastD := hsource hcast_span
  simpa [projectiveCartanReadbackPreservationForwardSource,
    regularIntegerFunctionCast_cartanCoordinateAddHom]
    using hcastD

/-- The forward fixed-coordinate inclusion proves the local projective-envelope
readback-preservation statement. -/
theorem
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility_of_forwardSource
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hsource :
      projectiveCartanReadbackPreservationForwardSource
        (p := p) (A := A) (K := K) (G := G)) :
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c
  have hcastD :=
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_forwardSource
      (p := p) (A := A) (K := K) (G := G) P hsource c
  have hrepr :=
    projectiveCartanASpanBrauerRepr_regularRestriction_projectiveCharacter
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord [P c]ₚ₀
  simpa [regularIntegerFunctionCast_cartanCoordinateAddHom, hrepr] using hcastD

/-- With the existing projective-envelope row divisibility theorem, the same forward source gives
the equivalent congruence form `regularRestriction - cast ∈ D`. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence_of_forwardSource
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
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
        asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hsource :
      projectiveCartanReadbackPreservationForwardSource
        (p := p) (A := A) (K := K) (G := G)) :
    coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
      (p := p) (A := A) (K := K) (G := G) P := by
  exact
    (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope).1
      (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_forwardSource
        (p := p) (A := A) (K := K) (G := G) P hsource)

/-- Local equivalence between readback preservation and the regular-value congruence form. -/
theorem
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility_iff_regularValueCongruence
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
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
        asModule (π c).ρ, f.IsProjectiveEnvelope) :
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P ↔
      coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P := by
  constructor
  · intro hreadback
    exact
      (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).1
        (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_readbackPreserves
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord P hreadback)
  · intro hcong c
    have hcastD :
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
      (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).2 hcong c
    have hrepr :=
      projectiveCartanASpanBrauerRepr_regularRestriction_projectiveCharacter
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord [P c]ₚ₀
    simpa [regularIntegerFunctionCast_cartanCoordinateAddHom, hrepr] using hcastD

end ProjectiveCartanReadbackPreservationSourceWorker

section FullMixedProjectiveCartanReadbackPreservationSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedReadbackPreservationSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedReadbackPreservationSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model B-side source adapter: the forward Cartan-coordinate span inclusion gives
the projective-envelope cast/readback preservation rows. -/
theorem
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_cartanCoordinateSpanLe
    (hsource :
      fullMixedModelProjectiveCartanCoordinateSpanLeStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
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
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_forwardSource
      (p := p) (A := A) (K := K) (G := G) P
      (hsource (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Integer Cartan-coordinate range inclusion is a concrete forward-source statement for the same
projective-envelope cast/readback preservation rows. -/
theorem
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_cartanCoordinateRangeLe
    (hrange :
      fullMixedModelForwardScaledCartanCoordinateRangeLeStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement
      (p := p) (k := k) (G := G) := by
  refine
    fullMixedModelForwardDiagonalWorkerProjectiveEnvelopeCastReadbackPreservationStatement_of_cartanCoordinateSpanLe
      (p := p) (k := k) (G := G) ?_
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_range_le
      (p := p) (A := A) (K := K) (G := G)
      (hrange (A := A) (K := K) e0)

end FullMixedProjectiveCartanReadbackPreservationSourceWorker

end Representation
