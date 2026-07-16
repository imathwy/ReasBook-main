import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReprStabilityUnconditionalWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Exercise18_4BasisInverseCompletionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CentralizerUnitDenominatorWorker

/-!
Matrix form of the local Brauer-coordinate stability obstruction.

The unconditional readout in `BrauerReprStabilityUnconditionalWorker` expresses `T` on the
scaled point-mass generators through the Brauer-basis coefficient of the prime-to-`p` indicator.
This file removes the prime-to-`p` unit and rewrites that coefficient as an inverse
change-of-basis matrix entry.  Thus the forward stability problem for generators is exactly the
target-column divisibility of

```
  centralizerPPart(c) * Binv d c
```

by `centralizerPPart(d)`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerReprStabilityMatrixWorker

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

local instance brauerReprStabilityMatrixWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReprStabilityMatrixWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsLocalRing A] [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed k] [CharP k p]
    [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Prime-to-`p` indicator coefficients are inverse change-of-basis matrix entries, with the
prime-to-`p` centralizer factor attached to the source class. -/
theorem basisInverseCompletion_repr_primeToPIndicator_eq_sourceOrdCompl_mul_inverseMatrixEntry
    (b : Module.Basis (PRegularConjClass G p) A (PRegularConjClass G p → A))
    (c d : PRegularConjClass G p) :
    b.repr
        (primeToP_regular_indicator (p := p) (A := A) (G := G) c) d =
      (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) *
        basisInverseCompletionInverseMatrix b d c := by
  simpa [inversePRegularConjClass_involutive, inversePRegularConjClass_val,
    ConjClasses.centralizerCard_inv] using
    (basisInverseCompletion_repr_primeToPIndicator_eq_ordCompl_mul_inverseMatrixEntry
      (p := p) (A := A) (G := G) b d (inversePRegularConjClass (p := p) c))

omit [IsFractionRing A K] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The unit-normalized coefficient appearing in the scaled-generator readout is exactly
`centralizerPPart(c) * Binv d c`. -/
theorem centralizerUnit_inv_mul_sourcePPart_mul_primeToPIndicatorCoeff_eq_sourcePPart_mul_inverseMatrixEntry
    (b : Module.Basis (PRegularConjClass G p) A (PRegularConjClass G p → A))
    (c d : PRegularConjClass G p) :
    (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
        ((ConjClasses.centralizerPPart p c.1 : A) *
          (b.repr
            (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d) =
      (ConjClasses.centralizerPPart p c.1 : A) *
        basisInverseCompletionInverseMatrix b d c := by
  let uinv : A :=
    (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A)
  let zc : A := ConjClasses.centralizerPPart p c.1
  let q : A := ordCompl[p] (ConjClasses.centralizerCard c.1)
  let entry : A := basisInverseCompletionInverseMatrix b d c
  have hcoeff :
      (b.repr
        (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d =
        q * entry := by
    simpa [q, entry] using
      (basisInverseCompletion_repr_primeToPIndicator_eq_sourceOrdCompl_mul_inverseMatrixEntry
        (p := p) (A := A) (G := G) b c d)
  have hunit : uinv * q = 1 := by
    simp [uinv, q, centralizerPrimeToPUnit_inv_mul_ordCompl
      (p := p) (A := A) (G := G) c]
  calc
    (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
        ((ConjClasses.centralizerPPart p c.1 : A) *
          (b.repr
            (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d) =
      uinv * (zc * (q * entry)) := by
        simp [uinv, zc, q, entry, hcoeff]
    _ = zc * ((uinv * q) * entry) := by
        ring
    _ = (ConjClasses.centralizerPPart p c.1 : A) *
        basisInverseCompletionInverseMatrix b d c := by
        simp [hunit, zc, entry]

/-- Matrix-entry form of the scaled point-mass generator readout.

This is the sharp local basis/inverse-matrix identity behind the forward stability question:
`T` sends the generator indexed by `c` to the coordinate function whose `d`-coordinate is the
image in `K` of `centralizerPPart(c) * Binv d c`. -/
theorem brauerRepr_scaledIndicator_apply_eq_algebraMap_sourcePPart_mul_inverseMatrixEntry
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ,
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
    let Binv := basisInverseCompletionInverseMatrix bA
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (scaled_regular_indicator (p := p) (A := A) (K := K) c) d =
      algebraMap A K
        ((ConjClasses.centralizerPPart p c.1 : A) * Binv d c) := by
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
  let Binv := basisInverseCompletionInverseMatrix bA
  have hreadout :
      projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
          (scaled_regular_indicator (p := p) (A := A) (K := K) c) d =
        algebraMap A K
          ((((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
            ((ConjClasses.centralizerPPart p c.1 : A) *
              (bA.repr
                (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d)) := by
    simpa [hπ_pairwise, hπ_complete, bA] using
      (brauerRepr_scaledIndicator_apply_eq_algebraMap_unitInv_mul_sourcePPart_mul_inversePrimeToPIndicatorCoeff
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c d)
  have hmatrix :
      (((centralizerPrimeToPUnit (p := p) (A := A) (G := G) c)⁻¹ : Aˣ) : A) *
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (bA.repr
              (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) d) =
        (ConjClasses.centralizerPPart p c.1 : A) * Binv d c :=
    centralizerUnit_inv_mul_sourcePPart_mul_primeToPIndicatorCoeff_eq_sourcePPart_mul_inverseMatrixEntry
      (p := p) (A := A) (G := G) bA c d
  rw [hreadout, hmatrix]

/-- A scaled generator is stable under `T` once the inverse-matrix entry readout is divisible
by the target centralizer `p`-part in every target coordinate. -/
theorem brauerRepr_scaledIndicator_mem_regularValueDivisibility_of_inverseMatrixEntryTargetDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (c : PRegularConjClass G p)
    (hmatrix :
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
        let Binv := basisInverseCompletionInverseMatrix bA
        ∃ a : A,
          (ConjClasses.centralizerPPart p c.1 : A) * Binv d c =
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
  rcases hmatrix d with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [
    brauerRepr_scaledIndicator_apply_eq_algebraMap_sourcePPart_mul_inverseMatrixEntry
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c d]
  exact congrArg (algebraMap A K) ha

/-- Forward stability of Serre's divisibility lattice follows from the inverse-matrix target
divisibility for every scaled point-mass generator. -/
theorem brauerRepr_regularValueDivisibility_forward_le_of_inverseMatrixEntryTargetDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hmatrix :
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
        let Binv := basisInverseCompletionInverseMatrix bA
        ∃ a : A,
          (ConjClasses.centralizerPPart p c.1 : A) * Binv d c =
            (ConjClasses.centralizerPPart p d.1 : A) * a) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  brauerRepr_regularValueDivisibility_forward_le_of_scaledIndicator_mem
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (fun c =>
      brauerRepr_scaledIndicator_mem_regularValueDivisibility_of_inverseMatrixEntryTargetDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c (hmatrix c))

end BrauerReprStabilityMatrixWorker

end Representation
