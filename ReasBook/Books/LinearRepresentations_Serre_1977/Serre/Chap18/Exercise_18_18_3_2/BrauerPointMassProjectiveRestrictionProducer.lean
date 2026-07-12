import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassProjectiveRestrictionProducer

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerPointMassProjectiveRestrictionProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassProjectiveRestrictionProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre `18.4` plus projective-envelope orthogonality gives the explicit
centralizer-`p`-part divisibility of each coordinate-normalized projective-envelope regular
restriction.

This is the source-facing producer immediately upstream of the point-mass readback problem: it
does not use the final range/product theorem, and the witness coefficient is the Exercise `18.4`
coordinate of the prime-to-`p` regular indicator. -/
theorem coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G)
            ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope) :
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
  intro c d
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) π hπ_simple hπ_coord
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A)
      liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  refine
    ⟨bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c, ?_⟩
  exact
    coordinate_normalized_projective_envelope_regularRestriction_value
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c d

/-- Existential version of
`coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility`, using the
coordinate-normalized complete family with projective envelopes already constructed upstream. -/
theorem exists_coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility :
    ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
      ∃ _ : ∀ c, Simple (π c),
        ∃ _ :
          ∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (G := G)
                ([π c]₀ : R₀[IsLocalRing.ResidueField A](G)) =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
          ∃ P : PRegularConjClass G p →
              FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
            ∃ _ :
              ∀ c, ∃ f :
                (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
                f.IsProjectiveEnvelope,
              ∀ c d : PRegularConjClass G p,
                ∃ a : A,
                  regularRestriction (p := p) (A := A) (K := K) (G := G)
                      (projectiveCharacterScalarExtension
                        (A := A) (K := K) (G := G) [P c]ₚ₀) d =
                    algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
  rcases exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, P, hP_envelope⟩
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope

end BrauerPointMassProjectiveRestrictionProducer

end Representation
