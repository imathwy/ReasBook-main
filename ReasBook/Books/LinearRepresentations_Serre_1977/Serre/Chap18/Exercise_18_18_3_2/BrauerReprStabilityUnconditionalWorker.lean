import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanASpan
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerExercise18_4OrthogonalityAPI
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CentralizerUnitDenominatorWorker

/-!
Unconditional local API for the Brauer-coordinate stability problem.

This file does not prove the stability equality.  It records the source-side computation of the
Brauer-coordinate map on the scaled point-mass generators of Serre's regular-value divisibility
lattice.  Thus the remaining forward stability gap is the concrete generator-membership statement
that the right hand side below is again divisible by the target centralizer `p`-part.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerReprStabilityUnconditionalWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance brauerReprStabilityUnconditionalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReprStabilityUnconditionalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Unconditional readout of the Brauer-coordinate map by the projective-envelope pairing
functional.

This is the source-side computation behind the generator version of
`Submodule.map T D ≤ D`: for any regular class function `φ`, its `d`-th Brauer coordinate is the
standard projective-envelope pairing with the projective envelope of the simple indexed by `d`.
-/
theorem projectiveCartanASpanBrauerRepr_apply_eq_projectiveEnvelope_pairingSum
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
    (φ : PRegularConjClass G p → K) (d : PRegularConjClass G p) :
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord φ d =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              φ (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
            else 0) := by
  classical
  let lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
    projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)
  have hlift : Function.Injective lift :=
    projectiveCartanASpanFieldLift_injective (p := p) (A := A) (K := K)
  have hred :
      ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
        algebraMap A K a = ((lift x : Kˣ) : K) ∧
          IsLocalRing.residue A a =
            ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := by
    intro x
    refine ⟨((primeToPRoot_unitsLift (p := p) (A := A) x : Aˣ) : A), ?_, ?_⟩
    · simp [lift, projectiveCartanASpanFieldLift]
    · exact residue_primeToPRoot_unitLift (p := p) (A := A) x
  simpa [projectiveCartanASpanBrauerRepr, projectiveCartanASpanBrauerBasis,
    projectiveCartanASpanFieldLift, lift] using
    (fixed_basis_repr_eq_projective_envelope_regular_pairing_of_function
      (p := p) (A := A) (K := K) (G := G)
      (lift := lift) (hlift := hlift) (hred := hred)
      (π := π) (hπ_simple := hπ_simple) (hπ_coord := hπ_coord)
      (P := P) (hP_envelope := hP_envelope) φ d)

/-- Generator specialization of the projective-envelope pairing readout for the scaled point
masses spanning Serre's regular-value divisibility lattice. -/
theorem brauerRepr_scaledIndicator_apply_eq_projectiveEnvelope_pairingSum
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
    (c d : PRegularConjClass G p) :
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (scaled_regular_indicator (p := p) (A := A) (K := K) c) d =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              scaled_regular_indicator (p := p) (A := A) (K := K) c
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
            else 0) := by
  exact
    projectiveCartanASpanBrauerRepr_apply_eq_projectiveEnvelope_pairingSum
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope
      (scaled_regular_indicator (p := p) (A := A) (K := K) c) d

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The projective-envelope pairing against a scaled regular point mass reads the inverse-class
regular value, up to the prime-to-`p` centralizer unit.

This is the class-sum normalization left after replacing Serre's prime-to-`p` point mass by the
scaled point mass.  It does not assert the remaining target-column divisibility. -/
theorem projectiveEnvelope_pairing_scaled_regular_indicator_eq_ordCompl_inv_mul_inverse_regularRestriction
    (i : FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (c : PRegularConjClass G p) :
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              scaled_regular_indicator (p := p) (A := A) (K := K) c
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
            else 0) =
      (algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A))⁻¹ *
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
          (inversePRegularConjClass (p := p) c) := by
  classical
  let z : K := algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)
  let q : K := algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
  let row : PRegularConjClass G p → K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
  let prime : G → K := fun s =>
    if hs : IsPRegular p s then
      algebraMap A K
        ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
          (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
    else 0
  let scaled : G → K := fun s =>
    if hs : IsPRegular p s then
      scaled_regular_indicator (p := p) (A := A) (K := K) c
        (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
    else 0
  have hq_ne : q ≠ 0 := by
    rcases ordCompl_centralizerCard_isUnit (p := p) (A := A) (G := G) c with ⟨u, hu⟩
    have hu_ne : ((u : Aˣ) : A) ≠ 0 := Units.ne_zero u
    have hqA_ne : (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) ≠ 0 := by
      simpa [hu] using hu_ne
    exact fun hq0 => hqA_ne (IsFractionRing.injective A K (by simpa [q] using hq0))
  have hz_ne : z ≠ 0 :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) c
  have hscaled_prime :
      ∀ s : G, scaled s = z * q⁻¹ * prime s := by
    intro s
    by_cases hs : IsPRegular p s
    · let t : PRegularConjClass G p :=
        PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩
      have hscaled_eval :
          scaled s =
            scaled_regular_indicator (p := p) (A := A) (K := K) c t := by
        dsimp [scaled]
        rw [dif_pos hs]
      have hprime_eval :
          prime s =
            algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c) t) := by
        dsimp [prime]
        rw [dif_pos hs]
      by_cases ht : t = c
      · rw [hscaled_eval, hprime_eval, ht]
        calc
          scaled_regular_indicator (p := p) (A := A) (K := K) c c = z := by
            simp [scaled_regular_indicator, z]
          _ = z * q⁻¹ * q := by
            field_simp [hq_ne]
          _ =
              z * q⁻¹ *
                algebraMap A K
                  ((primeToP_regular_indicator (p := p) (A := A) (G := G) c) c) := by
              simp [primeToP_regular_indicator, q]
      · rw [hscaled_eval, hprime_eval]
        simp [scaled_regular_indicator, primeToP_regular_indicator, ht]
    · simp [scaled, prime, hs]
  have hpair_prime :
      (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            (if hs : IsPRegular p (s⁻¹) then
              row (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
            else 0) * prime s =
        z⁻¹ * row (inversePRegularConjClass (p := p) c) := by
    simpa [row, prime, z] using
      (projectiveEnvelope_pairing_primeToP_indicator_eq_inverse_regularRestriction
        (p := p) (A := A) (K := K) (G := G) (i := i) c)
  calc
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              scaled_regular_indicator (p := p) (A := A) (K := K) c
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
            else 0)
        =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            row (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) * scaled s := by
          rfl
    _ =
      z * q⁻¹ *
        ((Fintype.card G : K)⁻¹ *
          ∑ s : G,
            (if hs : IsPRegular p (s⁻¹) then
              row (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
            else 0) * prime s) := by
          calc
            (Fintype.card G : K)⁻¹ *
                ∑ s : G,
                  (if hs : IsPRegular p (s⁻¹) then
                    row (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                  else 0) * scaled s
                =
              (Fintype.card G : K)⁻¹ *
                ∑ s : G,
                  (z * q⁻¹) *
                    ((if hs : IsPRegular p (s⁻¹) then
                      row (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                    else 0) * prime s) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro s hs
                rw [hscaled_prime s]
                ring
            _ =
              (Fintype.card G : K)⁻¹ *
                ((z * q⁻¹) *
                  ∑ s : G,
                    (if hs : IsPRegular p (s⁻¹) then
                      row (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                    else 0) * prime s) := by
                rw [← Finset.mul_sum]
            _ =
              z * q⁻¹ *
                ((Fintype.card G : K)⁻¹ *
                  ∑ s : G,
                    (if hs : IsPRegular p (s⁻¹) then
                      row (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                    else 0) * prime s) := by
                ring
    _ =
      z * q⁻¹ * (z⁻¹ * row (inversePRegularConjClass (p := p) c)) := by
          rw [hpair_prime]
    _ =
      q⁻¹ * row (inversePRegularConjClass (p := p) c) := by
          field_simp [hz_ne]
    _ =
      (algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A))⁻¹ *
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
          (inversePRegularConjClass (p := p) c) := by
          rfl

/-- Sharpened generator readout: the Brauer coordinate of a scaled point mass is the inverse-class
value of the projective-envelope character, divided by the prime-to-`p` centralizer factor. -/
theorem brauerRepr_scaledIndicator_apply_eq_ordCompl_inv_mul_projectiveEnvelope_regularRestriction
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
    (c d : PRegularConjClass G p) :
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (scaled_regular_indicator (p := p) (A := A) (K := K) c) d =
      (algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A))⁻¹ *
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
          (inversePRegularConjClass (p := p) c) := by
  rw [brauerRepr_scaledIndicator_apply_eq_projectiveEnvelope_pairingSum
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope c d]
  exact
    projectiveEnvelope_pairing_scaled_regular_indicator_eq_ordCompl_inv_mul_inverse_regularRestriction
      (p := p) (A := A) (K := K) (G := G) (i := P d) c

/-- Exercise `18.4` coefficient form of the scaled point-mass generator readout.

The prime-to-`p` centralizer factor is absorbed as a DVR unit.  Thus the remaining forward
stability obstruction for the generator indexed by `c` is exactly target-column divisibility of
the displayed `A`-coefficient by `centralizerPPart p d.1`. -/
theorem brauerRepr_scaledIndicator_apply_eq_algebraMap_unitInv_mul_sourcePPart_mul_inversePrimeToPIndicatorCoeff
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
    (c d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (scaled_regular_indicator (p := p) (A := A) (K := K) c) d =
      algebraMap A K
        ((((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (bA.repr
              (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d)) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let uA : Aˣ := centralizerPrimeToPUnit (p := p) (A := A) (G := G) c
  let zc : A := ConjClasses.centralizerPPart p c.1
  let coeff : A :=
    (bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d
  have hunit_inv :
      (algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A))⁻¹ =
        algebraMap A K (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    simpa [map_mul] using
      algebraMap_centralizerPrimeToPUnit_inv_mul_ordCompl
        (p := p) (A := A) (K := K) (G := G) c
  have hvalue :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
          (inversePRegularConjClass (p := p) c) =
        algebraMap A K (zc * coeff) := by
    simpa [hπ_pairwise, hπ_complete, bA, zc, coeff,
      inversePRegularConjClass_involutive, inversePRegularConjClass_val,
      ConjClasses.centralizerPPart_inv] using
      (canonicalDVRBrauerBasis_projectiveEnvelope_regularRestriction_value
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope d (inversePRegularConjClass (p := p) c))
  calc
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (scaled_regular_indicator (p := p) (A := A) (K := K) c) d =
      (algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A))⁻¹ *
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
          (inversePRegularConjClass (p := p) c) := by
          rw [brauerRepr_scaledIndicator_apply_eq_ordCompl_inv_mul_projectiveEnvelope_regularRestriction
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P hP_envelope c d]
    _ =
      algebraMap A K
        ((((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (bA.repr
              (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d)) := by
          rw [hunit_inv, hvalue]
          simp [map_mul, zc, coeff]

/-- A scaled point-mass generator maps back into Serre's regular-value divisibility lattice once
the remaining target-column divisibility exposed by the coefficient readout is supplied.

This is deliberately a direct membership adapter, not an equivalence boundary: the only input is
the concrete `A`-divisibility of the coefficient displayed in
`brauerRepr_scaledIndicator_apply_eq_algebraMap_unitInv_mul_sourcePPart_mul_inversePrimeToPIndicatorCoeff`.
-/
theorem brauerRepr_scaledIndicator_mem_regularValueDivisibility_of_coeffTargetDivisibility
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
    (c : PRegularConjClass G p)
    (hcoeff :
      ∀ d : PRegularConjClass G p,
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        let bA :=
          canonicalDVRBrauerBasis
            (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
        ∃ a : A,
          (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
              ((ConjClasses.centralizerPPart p c.1 : A) *
                (bA.repr
                  (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d) =
            (ConjClasses.centralizerPPart p d.1 : A) * a) :
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (scaled_regular_indicator (p := p) (A := A) (K := K) c) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  refine
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G) _).2 ?_
  intro d
  rcases hcoeff d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [
    brauerRepr_scaledIndicator_apply_eq_algebraMap_unitInv_mul_sourcePPart_mul_inversePrimeToPIndicatorCoeff
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c d]
  exact congrArg (algebraMap A K) ha

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Forward half of Brauer-coordinate stability reduced to the generator image membership exposed
by the theorem above.

Since Serre's regular-value divisibility lattice is generated by the scaled point masses, it is
enough to prove that the Brauer-coordinate image of each scaled point mass is again in that
lattice. -/
theorem brauerRepr_regularValueDivisibility_forward_le_of_scaledIndicator_mem
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hscaled :
      ∀ c : PRegularConjClass G p,
        projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
            (scaled_regular_indicator (p := p) (A := A) (K := K) c) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let T : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K) :=
    projectiveCartanASpanBrauerRepr
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  rintro _ ⟨f, hf, rfl⟩
  change T f ∈ D
  rw [regularValueDivisibilitySubmodule_eq_span_scaled_regular_indicator
    (p := p) (A := A) (K := K) (G := G)] at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩
      exact hscaled c
  | zero =>
      simp [D, T]
  | add y z _ _ hy hz =>
      simpa [map_add] using D.add_mem hy hz
  | smul a y _ hy =>
      simpa [map_smul] using D.smul_mem a hy

/-- Forward Brauer-coordinate stability follows from the concrete target-column divisibility for
all scaled point-mass generators.

The hypothesis is exactly the remaining local obstruction left by the unconditional source-side
readout: for every source class `c` and target class `d`, the displayed Exercise `18.4`
coefficient is divisible by the target centralizer `p`-part. -/
theorem brauerRepr_regularValueDivisibility_forward_le_of_coeffTargetDivisibility
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
    (hcoeff :
      ∀ c d : PRegularConjClass G p,
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        let bA :=
          canonicalDVRBrauerBasis
            (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
        ∃ a : A,
          (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
              ((ConjClasses.centralizerPPart p c.1 : A) *
                (bA.repr
                  (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d) =
            (ConjClasses.centralizerPPart p d.1 : A) * a) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  brauerRepr_regularValueDivisibility_forward_le_of_scaledIndicator_mem
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (fun c =>
      brauerRepr_scaledIndicator_mem_regularValueDivisibility_of_coeffTargetDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c (hcoeff c))

end BrauerReprStabilityUnconditionalWorker

end Representation
