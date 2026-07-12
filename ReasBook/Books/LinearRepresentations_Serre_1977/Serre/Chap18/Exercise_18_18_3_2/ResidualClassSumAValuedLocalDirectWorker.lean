import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.OrthogonalityResidualDirectCompletionWorker

/-!
Direct local `A`-valuedness for residual class sums.

The key point is the denominator calculation already available for pairing with an inverse
prime-to-`p` class indicator: the class sum is the value on the target class divided by the
target centralizer `p`-part.  Hence an explicit pointwise `centralizerPPart` divisibility
witness gives `A`-valuedness of the class sum itself.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ResidualClassSumAValuedLocalDirectWorker

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

local instance residualClassSumAValuedLocalDirectWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance residualClassSumAValuedLocalDirectWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Pairing an `A`-valued regular class function with the inverse prime-to-`p` indicator is
`A`-valued as soon as the target value is divisible by the target centralizer `p`-part. -/
theorem regularClassFunctionPairingSum_inversePrimeToPIndicator_AValued_of_value_centralizerPPart_mul
    (φ : PRegularConjClass G p → A) (d : PRegularConjClass G p)
    (hφ :
      ∃ a : A,
        φ d = (ConjClasses.centralizerPPart p d.1 : A) * a) :
    ∃ a : A,
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          φ
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
        algebraMap A K a := by
  classical
  rcases hφ with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  let invd := inversePRegularConjClass (p := p) d
  let z : A := ConjClasses.centralizerPPart p d.1
  have hz : algebraMap A K z ≠ 0 :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) d
  have hpair :
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          φ
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) invd) =
        (algebraMap A K z)⁻¹ * algebraMap A K (φ d) := by
    simpa [invd, z, inversePRegularConjClass_involutive,
      inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] using
      (regularClassFunctionPairingSum_primeToPIndicator_eq_inverse_value
        (p := p) (A := A) (K := K) (G := G) φ invd)
  calc
    regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
        φ
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))
        =
      (algebraMap A K z)⁻¹ * algebraMap A K (φ d) := by
        simpa [invd] using hpair
    _ = (algebraMap A K z)⁻¹ * algebraMap A K (z * a) := by
        simp [ha, z]
    _ = algebraMap A K a := by
        rw [map_mul]
        field_simp [hz]

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Unit-denominator column case of the preceding local class-sum `A`-valuedness theorem. -/
theorem regularClassFunctionPairingSum_inversePrimeToPIndicator_AValued_of_centralizerPPart_eq_one
    (φ : PRegularConjClass G p → A) (d : PRegularConjClass G p)
    (hd : ConjClasses.centralizerPPart p d.1 = 1) :
    ∃ a : A,
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          φ
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
        algebraMap A K a :=
  regularClassFunctionPairingSum_inversePrimeToPIndicator_AValued_of_value_centralizerPPart_mul
    (p := p) (A := A) (K := K) (G := G) φ d
    ⟨φ d, by simp [hd]⟩

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Direct residual-row class-sum `A`-valuedness from the corresponding pointwise row
divisibility at one target class. -/
theorem coordinateNormalizedBrauerBasisResidualClassSum_at_AValued_of_rowDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p)
    (hrow :
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
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a) :
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
      regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
          (fun e =>
            bA c e -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
        algebraMap A K a := by
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
  let diff : PRegularConjClass G p → A := fun e =>
    bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A)
  have hdiff :
      ∃ a : A,
        diff d = (ConjClasses.centralizerPPart p d.1 : A) * a := by
    simpa [hπ_pairwise, hπ_complete, bA, diff] using hrow
  simpa [hπ_pairwise, hπ_complete, bA, diff] using
    regularClassFunctionPairingSum_inversePrimeToPIndicator_AValued_of_value_centralizerPPart_mul
      (p := p) (A := A) (K := K) (G := G) diff d hdiff

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The A-side pairing residual directly implies the residual class-sum `A`-valuedness, with no
projective-envelope auxiliary family. -/
theorem coordinateNormalizedBrauerBasisResidualClassSumAValued_of_pairingResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hres :
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisResidualClassSumAValued
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
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
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
            (fun e =>
              bA c e -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
          algebraMap A K a
  intro c d
  let z : A := ConjClasses.centralizerPPart p d.1
  let coeff : A :=
    (bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d))) c
  have hrow :
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          z * a := by
    rcases hres c d with ⟨a, ha⟩
    have ha' :
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          z * coeff =
            z * a := by
      simpa [coordinateNormalizedBrauerBasisPairingResidualDivisibility,
        hπ_pairwise, hπ_complete, bA, z, coeff] using ha
    refine ⟨a + coeff, ?_⟩
    calc
      bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)
          =
        (bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            z * coeff) + z * coeff := by
          ring
      _ = z * a + z * coeff := by
          rw [ha']
      _ = z * (a + coeff) := by
          rw [mul_add]
  have hrow' :
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
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
    simpa [hπ_pairwise, hπ_complete, bA, z] using hrow
  simpa [hπ_pairwise, hπ_complete, bA] using
    coordinateNormalizedBrauerBasisResidualClassSum_at_AValued_of_rowDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord c d hrow'

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- If all target centralizer `p`-parts are trivial, the fixed-family residual class-sum
`A`-valuedness follows directly. -/
theorem coordinateNormalizedBrauerBasisResidualClassSumAValued_of_forall_centralizerPPart_eq_one
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hcentral :
      ∀ d : PRegularConjClass G p, ConjClasses.centralizerPPart p d.1 = 1) :
    coordinateNormalizedBrauerBasisResidualClassSumAValued
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
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
  change
    ∀ c d : PRegularConjClass G p,
      ∃ a : A,
        regularClassFunctionPairingSum (p := p) (A := A) (K := K) (G := G)
            (fun e =>
              bA c e -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A))
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) =
          algebraMap A K a
  intro c d
  let diff : PRegularConjClass G p → A := fun e =>
    bA c e - ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) e : A)
  have hdiff :
      ∃ a : A,
        diff d = (ConjClasses.centralizerPPart p d.1 : A) * a :=
    ⟨diff d, by simp [diff, hcentral d]⟩
  simpa [diff] using
    regularClassFunctionPairingSum_inversePrimeToPIndicator_AValued_of_value_centralizerPPart_mul
      (p := p) (A := A) (K := K) (G := G) diff d hdiff

end ResidualClassSumAValuedLocalDirectWorker

end Representation
