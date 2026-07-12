import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueRowSourceFinal

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalPointMassProjectiveRestrictionSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance pointMassProjectiveRestrictionSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance pointMassProjectiveRestrictionSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal missing source construction for the point-mass projective-restriction route.

For a coordinate-normalized Brauer family `π` and projective envelopes `P`, subtract the visible
projective-envelope row from the point-mass row difference.  The missing API is an explicit
projective character `Ψ` whose regular restriction is this residual, for every regular class `c`.
-/
def coordinateNormalizedPointMassResidualProjectiveRestrictionConstruction
    (π : PRegularConjClass G p → FDRep kA G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G) : Prop :=
  ∀ c : PRegularConjClass G p,
    ∃ Ψ : A ⊗R[K](G),
      Ψ ∈ projectiveCharacterSubmodule (A := A) (K := K) (G := G) ∧
        regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ =
          (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
              ([π c]₀ : R₀[kA](G)) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) -
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- If the residual after subtracting the visible projective-envelope row is itself a
projective-character restriction, then adding the projective-envelope row gives the desired
point-mass projective-restriction witness. -/
theorem brauerPointMassProjectiveRestrictionWitness_of_residualRestrictionConstruction
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hresidual :
      coordinateNormalizedPointMassResidualProjectiveRestrictionConstruction
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    brauerPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  intro c
  let row : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[kA](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  let ΦP : A ⊗R[K](G) :=
    projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀
  rcases hresidual c with ⟨Ψ, hΨ, hΨres⟩
  refine ⟨Ψ + ΦP, ?_, ?_⟩
  · exact
      (projectiveCharacterSubmodule (A := A) (K := K) (G := G)).add_mem hΨ
        (projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
          (A := A) (K := K) (G := G) [P c]ₚ₀)
  · calc
      regularRestriction (p := p) (A := A) (K := K) (G := G) (Ψ + ΦP)
          =
            regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ +
              regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP := by
              simpa [regularRestrictionLinearMap] using
                (regularRestrictionLinearMap
                  (p := p) (A := A) (K := K) (G := G)).map_add Ψ ΦP
      _ = (row - regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP) +
            regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP := by
            rw [show
              regularRestriction (p := p) (A := A) (K := K) (G := G) Ψ =
                row - regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP by
                simpa [row, ΦP] using hΨres]
      _ = row := by
            ext d
            simp [row]

/-- Existential form of the residual projective-restriction construction, including the
projective-envelope family selected by Exercise `18.4`. -/
def regularValueCongruenceSourceFaithfulExistsPointMassResidualRestrictionConstruction :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G,
          ∃ _hP_envelope :
            ∀ c, ∃ f : (P c).V →ₗ[kA[G]] asModule (π c).ρ, f.IsProjectiveEnvelope,
            coordinateNormalizedPointMassResidualProjectiveRestrictionConstruction
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The minimal residual construction closes the local point-mass projective-restriction
witness. -/
theorem existsPointMassProjectiveRestrictionWitness_of_residualRestrictionConstruction
    (hresidual :
      regularValueCongruenceSourceFaithfulExistsPointMassResidualRestrictionConstruction
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassProjectiveRestrictionWitness
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hresidual with
    ⟨π, hπ_simple, hπ_coord, P, _hP_envelope, hresidual⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerPointMassProjectiveRestrictionWitness_of_residualRestrictionConstruction
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hresidual

/-- Existing regular-value residual divisibility is enough to provide the minimal residual
projective-restriction construction by Serre `18.5(a)`.  This separates the remaining source
problem: prove the residual divisibility/projective restriction itself, not another global
equivalence. -/
theorem residualRestrictionConstruction_of_projectiveEnvelopeResidualDivisibility
    (π : PRegularConjClass G p → FDRep kA G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule kA G)
    (hresidual :
      brauerPointMassProjectiveEnvelopeResidualDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    coordinateNormalizedPointMassResidualProjectiveRestrictionConstruction
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c
  let row : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        ([π c]₀ : R₀[kA](G)) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
  let ΦP : A ⊗R[K](G) :=
    projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀
  let residual : PRegularConjClass G p → K :=
    row - regularRestriction (p := p) (A := A) (K := K) (G := G) ΦP
  have hresidualD :
      residual ∈ regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) := by
    refine
      (mem_regularValueDivisibilitySubmodule_iff
        (p := p) (A := A) (K := K) (G := G) residual).2 ?_
    intro d
    rcases hresidual c d with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [residual, row, ΦP, virtualModularCharacterOnPRegularConjClass_class] using ha
  have hresidualMap :
      residual ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    simpa [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hresidualD
  rcases Submodule.mem_map.1 hresidualMap with ⟨Ψ, hΨ, hΨres⟩
  refine ⟨Ψ, hΨ, ?_⟩
  simpa [coordinateNormalizedPointMassResidualProjectiveRestrictionConstruction,
    residual, row, ΦP, regularRestrictionLinearMap] using hΨres

end LocalPointMassProjectiveRestrictionSourceWorker

end Representation
