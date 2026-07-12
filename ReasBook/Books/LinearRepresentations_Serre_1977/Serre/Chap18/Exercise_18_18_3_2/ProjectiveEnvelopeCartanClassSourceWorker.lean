import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

set_option linter.unusedSectionVars false

section ProjectiveEnvelopeCartanClassSourceWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance projectiveEnvelopeCartanClassSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveEnvelopeCartanClassSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The projective-envelope Cartan class identity is exactly the fixed-coordinate scaled-generator
formula after applying the regular-class coordinate equivalence. -/
theorem projectiveEnvelope_cartan_class_iff_cartanCoordinate_scaled_indicator
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (c : PRegularConjClass G p) :
    cartanHom k G [P c]ₚ₀ =
        (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ ↔
      cartanCoordinateAddHom (p := p) (G := G) [P c]ₚ₀ =
        scaled_regular_integer_indicator (p := p) (G := G) c := by
  constructor
  · intro hcartan
    exact
      cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_cartan_class
        (p := p) (G := G) (π := π) hπ_coord [P c]ₚ₀ c hcartan
  · intro hcoord
    apply (regularClassCoordinateAddEquiv (p := p) (G := G)).injective
    change
      regularClassCoordinateAddEquiv (p := p) (G := G)
          (cartanHom k G [P c]ₚ₀) =
        regularClassCoordinateAddEquiv (p := p) (G := G)
          ((ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀)
    calc
      regularClassCoordinateAddEquiv (p := p) (G := G)
          (cartanHom k G [P c]ₚ₀)
          =
        cartanCoordinateAddHom (p := p) (G := G) [P c]ₚ₀ := rfl
      _ = scaled_regular_integer_indicator (p := p) (G := G) c := hcoord
      _ =
        regularClassCoordinateAddEquiv (p := p) (G := G)
          ((ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) := by
          rw [map_zsmul, hπ_coord c]
          ext d
          by_cases hdc : d = c
          · subst hdc
            simp [scaled_regular_integer_indicator]
          · simp [scaled_regular_integer_indicator, hdc]

/-- Family form of
`projectiveEnvelope_cartan_class_iff_cartanCoordinate_scaled_indicator`. -/
theorem projectiveEnvelope_cartan_class_family_iff_cartan_generator_formula
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G) :
    (∀ c : PRegularConjClass G p,
      cartanHom k G [P c]ₚ₀ =
        (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) ↔
    (∀ c : PRegularConjClass G p,
      cartanCoordinateAddHom (p := p) (G := G) [P c]ₚ₀ =
        scaled_regular_integer_indicator (p := p) (G := G) c) := by
  constructor
  · intro hcartan c
    exact
      (projectiveEnvelope_cartan_class_iff_cartanCoordinate_scaled_indicator
        (p := p) (A := A) (G := G) (π := π) hπ_coord P c).1
        (hcartan c)
  · intro hgen c
    exact
      (projectiveEnvelope_cartan_class_iff_cartanCoordinate_scaled_indicator
        (p := p) (A := A) (G := G) (π := π) hπ_coord P c).2
        (hgen c)

/-- Missing source-side readback statement isolated by the projective-envelope route: the explicit
row supplied by Exercise `18.4` and projective-envelope orthogonality has scaled coordinates in
the field-valued Brauer basis. -/
def coordinateNormalizedProjectiveEnvelopeExplicitRowBrauerReprScaled
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
  let liftK : PrimeToPRoot p k →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  let hliftK : Function.Injective liftK := by
    intro y z hyz
    apply primeToPRoot_unitsLift_injective (p := p) (A := A)
    apply IsFractionRing.injective A K
    exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  let bK :=
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) (K := K) liftK hliftK
      π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    bK.repr
        (fun d' : PRegularConjClass G p =>
          algebraMap A K
            ((ConjClasses.centralizerPPart p d'.1 : A) *
              (bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G)
                  (inversePRegularConjClass (p := p) d')) c))) d =
      ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K)

/-- Adapter from the explicit-row readback statement to the actual projective-envelope row
readback. The only representation-theoretic input used here is the already-proved
projective-envelope regular-restriction value formula. -/
theorem projectiveEnvelope_brauerRepr_scaled_of_explicitRow_brauerRepr_scaled
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hexplicit :
      coordinateNormalizedProjectiveEnvelopeExplicitRowBrauerReprScaled
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    let liftK : PrimeToPRoot p k →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    let hliftK : Function.Injective liftK := by
      intro y z hyz
      apply primeToPRoot_unitsLift_injective (p := p) (A := A)
      apply IsFractionRing.injective A K
      exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (K := K) liftK hliftK
        π hπ_pairwise hπ_complete
    ∀ c d : PRegularConjClass G p,
      bK.repr
          (regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d =
        ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K) := by
  classical
  intro liftK hliftK hπ_pairwise hπ_complete bK c d
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  let explicitRow : PRegularConjClass G p → K := fun d' =>
    algebraMap A K
      ((ConjClasses.centralizerPPart p d'.1 : A) *
        (bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G)
            (inversePRegularConjClass (p := p) d')) c))
  have hrow :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) =
        explicitRow := by
    funext d'
    simpa [explicitRow, liftA, hliftA, bA, hπ_pairwise, hπ_complete] using
      (coordinate_normalized_projective_envelope_regularRestriction_value
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d')
  rw [hrow]
  simpa [coordinateNormalizedProjectiveEnvelopeExplicitRowBrauerReprScaled,
    explicitRow, liftA, hliftA, liftK, hliftK, hπ_pairwise, hπ_complete, bA, bK] using
    hexplicit c d

/-- If the actual projective-envelope row has scaled Brauer-basis coordinates, then the Cartan
class identity follows by the readback theorem and integer-coordinate injectivity. -/
theorem projectiveEnvelope_cartan_class_of_brauerRepr_scaled
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hscaled :
      let liftK : PrimeToPRoot p k →* Kˣ :=
        (Units.map (algebraMap A K).toMonoidHom).comp
          (primeToPRoot_unitsLift (p := p) (A := A))
      let hliftK : Function.Injective liftK := by
        intro y z hyz
        apply primeToPRoot_unitsLift_injective (p := p) (A := A)
        apply IsFractionRing.injective A K
        exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      let bK :=
        exercise_18_18_2_9_field_irreducible_modular_characters_basis
          (p := p) (K := K) liftK hliftK
          π hπ_pairwise hπ_complete
      ∀ c d : PRegularConjClass G p,
        bK.repr
            (regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d =
          ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K)) :
    ∀ c : PRegularConjClass G p,
      cartanHom k G [P c]ₚ₀ =
        (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := by
  classical
  intro c
  refine
    (projectiveEnvelope_cartan_class_iff_cartanCoordinate_scaled_indicator
      (p := p) (A := A) (G := G) (π := π) hπ_coord P c).2 ?_
  ext d
  let liftK : PrimeToPRoot p k →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  have hliftK : Function.Injective liftK := by
    intro y z hyz
    apply primeToPRoot_unitsLift_injective (p := p) (A := A)
    apply IsFractionRing.injective A K
    exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bK :=
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) (K := K) liftK hliftK
      π hπ_pairwise hπ_complete
  have hreadback :=
    coordinate_normalized_projective_envelope_cartan_coordinate_readback
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P c d
  have hscaled_cd := hscaled c d
  have hcast :
      ((cartanCoordinateAddHom (p := p) (G := G) [P c]ₚ₀ d : ℤ) : K) =
        ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K) := by
    change
      ((regularClassCoordinateAddEquiv (p := p) (G := G)
          (cartanHom k G [P c]ₚ₀) d : ℤ) : K) =
        ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K)
    exact
      hreadback.symm.trans
        (by
          simpa [liftK, hliftK, hπ_pairwise, hπ_complete, bK] using hscaled_cd)
  exact Int.cast_injective hcast

/-- Conversely, the Cartan class identity makes the projective-envelope row have scaled
Brauer-basis coordinates via the readback theorem. -/
theorem projectiveEnvelope_brauerRepr_scaled_of_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    let liftK : PrimeToPRoot p k →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    let hliftK : Function.Injective liftK := by
      intro y z hyz
      apply primeToPRoot_unitsLift_injective (p := p) (A := A)
      apply IsFractionRing.injective A K
      exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (K := K) liftK hliftK
        π hπ_pairwise hπ_complete
    ∀ c d : PRegularConjClass G p,
      bK.repr
          (regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d =
        ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K) := by
  classical
  intro liftK hliftK hπ_pairwise hπ_complete bK c d
  have hreadback :=
    coordinate_normalized_projective_envelope_cartan_coordinate_readback
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P c d
  have hcoord :
      cartanCoordinateAddHom (p := p) (G := G) [P c]ₚ₀ =
        scaled_regular_integer_indicator (p := p) (G := G) c :=
    (projectiveEnvelope_cartan_class_iff_cartanCoordinate_scaled_indicator
      (p := p) (A := A) (G := G) (π := π) hπ_coord P c).1
      (hcartan c)
  calc
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d
        =
      ((cartanCoordinateAddHom (p := p) (G := G) [P c]ₚ₀ d : ℤ) : K) := by
        simpa [liftK, hliftK, hπ_pairwise, hπ_complete, bK] using hreadback
    _ = ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K) := by
        rw [hcoord]

/-- The explicit Exercise `18.4` row readback is equivalent to the projective-envelope Cartan
class identity, after the existing pointwise regular-restriction and readback APIs are applied. -/
theorem explicitRow_brauerRepr_scaled_iff_projectiveEnvelope_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) :
    coordinateNormalizedProjectiveEnvelopeExplicitRowBrauerReprScaled
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ↔
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := by
  constructor
  · intro hexplicit
    exact
      projectiveEnvelope_cartan_class_of_brauerRepr_scaled
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P
        (projectiveEnvelope_brauerRepr_scaled_of_explicitRow_brauerRepr_scaled
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord P hP_envelope hexplicit)
  · intro hcartan
    classical
    intro c d
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA : Function.Injective liftA :=
      primeToPRoot_unitsLift_injective (p := p) (A := A)
    let liftK : PrimeToPRoot p k →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    have hliftK : Function.Injective liftK := by
      intro y z hyz
      apply primeToPRoot_unitsLift_injective (p := p) (A := A)
      apply IsFractionRing.injective A K
      exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (K := K) liftK hliftK
        π hπ_pairwise hπ_complete
    let explicitRow : PRegularConjClass G p → K := fun d' =>
      algebraMap A K
        ((ConjClasses.centralizerPPart p d'.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d')) c))
    have hrow :
        regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) =
          explicitRow := by
      funext d'
      simpa [explicitRow, liftA, hliftA, bA, hπ_pairwise, hπ_complete] using
        (coordinate_normalized_projective_envelope_regularRestriction_value
          (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord P hP_envelope c d')
    have hactual :=
      projectiveEnvelope_brauerRepr_scaled_of_cartan_class
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hcartan
    have hactual_cd := hactual c d
    change bK.repr explicitRow d =
      ((scaled_regular_integer_indicator (p := p) (G := G) c d : ℤ) : K)
    rw [← hrow]
    simpa [coordinateNormalizedProjectiveEnvelopeExplicitRowBrauerReprScaled,
      liftA, hliftA, liftK, hliftK, hπ_pairwise, hπ_complete, bA, bK, explicitRow] using
      hactual_cd

end ProjectiveEnvelopeCartanClassSourceWorker

end Representation
