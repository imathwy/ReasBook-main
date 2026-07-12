import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectProof
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassBrauerBasisEntryCongruenceWorker

/-!
Prime-to-`p` indicator coefficients in the Exercise `18.4` Brauer basis.

This worker stays on the pure `A`-linear side.  The unconditional content is the
`Basis.sum_repr` expansion of the inverse prime-to-`p` point mass: after multiplying its
coefficients by the target centralizer `p`-part, the reconstructed function is the full
centralizer point mass at the inverse regular class.

The final section records the smallest coefficient residual still needed to obtain the
point-mass source congruence.  It is only divisibility of

```
  bA c d - delta_cd - z(d) * coeff(c,d)
```

where `coeff(c,d)` is the Exercise `18.4` coefficient of the inverse prime-to-`p` indicator.
No Cartan range, cokernel, determinant, or product endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PrimeToPIndicatorBasisCoefficientWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance primeToPIndicatorBasisCoefficientWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance primeToPIndicatorBasisCoefficientWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsLocalRing A] [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed k] [CharP k p] in
/-- Evaluating the inverse prime-to-`p` point mass after multiplying by the target
centralizer `p`-part gives the full centralizer point mass at the inverse class. -/
theorem centralizerPPart_mul_inversePrimeToPIndicator_apply_eq_inversePointMass
    (d t : PRegularConjClass G p) :
    (ConjClasses.centralizerPPart p d.1 : A) *
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) t =
      if t = inversePRegularConjClass (p := p) d then
        (ConjClasses.centralizerCard d.1 : A)
      else 0 := by
  classical
  by_cases ht : t = inversePRegularConjClass (p := p) d
  · subst t
    have hcardA :
        (ConjClasses.centralizerCard d.1 : A) =
          (ConjClasses.centralizerPPart p d.1 : A) *
            (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) := by
      simpa [Nat.cast_mul] using
        congrArg (fun n : ℕ => (n : A))
          (ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
            (p := p) (G := G) d.1)
    simpa [primeToP_regular_indicator, inversePRegularConjClass_val,
      ConjClasses.centralizerCard_inv] using hcardA.symm
  · simp [primeToP_regular_indicator, ht]

omit [IsLocalRing A] [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed k] [CharP k p] in
/-- Function-valued form of the previous point-mass calculation. -/
theorem centralizerPPart_mul_inversePrimeToPIndicator_eq_inversePointMass
    (d : PRegularConjClass G p) :
    (fun t : PRegularConjClass G p =>
        (ConjClasses.centralizerPPart p d.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) t) =
      Pi.single (inversePRegularConjClass (p := p) d)
        (ConjClasses.centralizerCard d.1 : A) := by
  classical
  funext t
  rw [centralizerPPart_mul_inversePrimeToPIndicator_apply_eq_inversePointMass
    (p := p) (A := A) (G := G) d t]
  by_cases ht : t = inversePRegularConjClass (p := p) d
  · subst t
    simp
  · simp [ht]

/-- The unconditional Exercise `18.4` basis-coefficient identity for the inverse
prime-to-`p` indicator.  The coefficient column

```
  z(d) * bA.repr (primeToP_regular_indicator (d^{-1})) i
```

reconstructs the full centralizer point mass at `d^{-1}`. -/
theorem canonicalDVRBrauerBasis_inversePrimeToPIndicator_weightedExpansion_eq_inversePointMass
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (d t : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    let f :=
      primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
    ∑ i : PRegularConjClass G p,
        bA i t *
          ((ConjClasses.centralizerPPart p d.1 : A) * (bA.repr f i)) =
      if t = inversePRegularConjClass (p := p) d then
        (ConjClasses.centralizerCard d.1 : A)
      else 0 := by
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
  let f :=
    primeToP_regular_indicator
      (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
  calc
    ∑ i : PRegularConjClass G p,
        bA i t *
          ((ConjClasses.centralizerPPart p d.1 : A) * (bA.repr f i))
        =
      (ConjClasses.centralizerPPart p d.1 : A) * f t := by
        simpa [hπ_pairwise, hπ_complete, bA, f] using
          (canonicalDVRBrauerBasis_primeToPIndicator_sum_repr_basisAlgebra
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord d t)
    _ =
      if t = inversePRegularConjClass (p := p) d then
        (ConjClasses.centralizerCard d.1 : A)
      else 0 := by
        simpa [f] using
          (centralizerPPart_mul_inversePrimeToPIndicator_apply_eq_inversePointMass
            (p := p) (A := A) (G := G) d t)

/-- Extensional form of the unconditional weighted coefficient-column identity. -/
theorem canonicalDVRBrauerBasis_inversePrimeToPIndicator_weightedExpansion_funext
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    let f :=
      primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
    (fun t : PRegularConjClass G p =>
        ∑ i : PRegularConjClass G p,
          bA i t *
            ((ConjClasses.centralizerPPart p d.1 : A) * (bA.repr f i))) =
      Pi.single (inversePRegularConjClass (p := p) d)
        (ConjClasses.centralizerCard d.1 : A) := by
  classical
  funext t
  rw [canonicalDVRBrauerBasis_inversePrimeToPIndicator_weightedExpansion_eq_inversePointMass
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord d t]
  by_cases ht : t = inversePRegularConjClass (p := p) d
  · subst t
    simp
  · simp [ht]

/-- The minimal coefficient residual left after the unconditional inverse-indicator
coefficient column has been split off.  Since the split-off term is visibly a
`centralizerPPart`-multiple, this residual divisibility is equivalent to the point-mass source
row congruence. -/
def inversePrimeToPIndicatorCoefficientResidualDivisibility
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The coefficient residual is exactly the pairing residual already isolated by the
Exercise `18.4` readback route. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pairingResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    inversePrimeToPIndicatorCoefficientResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  rfl

/-- The coefficient-residual formulation is equivalent to the point-mass source congruence. -/
theorem inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    inversePrimeToPIndicatorCoefficientResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  constructor
  · intro hresidual
    have hpairing :
        coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hresidual
    have hvisible :
        coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback_basisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hpairing
    simpa [hπ_pairwise, hπ_complete] using
      orthogonalityPairingSumPointMassSourceCongruence_of_visibleReadbackBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hvisible
  · intro hsource
    have hvisible :
        coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      visibleReadbackBasisAlgebra_of_orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
        (by simpa [hπ_pairwise, hπ_complete] using hsource)
    have hpairing :
        coordinateNormalizedBrauerBasisPairingResidualDivisibility
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback_basisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hvisible
    exact
      (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pairingResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpairing

/-- A stronger exact coefficient readback would immediately give the source row congruence.
The unconditional basis expansion above proves the weighted column identity; this exact row-wise
readback is the missing bridge if one wants to close the congruence only from coefficient
transport. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_inversePrimeToPIndicatorCoefficientExact
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hexact :
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      let bA :=
        canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
      ∀ c d : PRegularConjClass G p,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c)) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
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
  have hsource :
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
    intro c d
    refine ⟨
      (bA.repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G)
          (inversePRegularConjClass (p := p) d)) c), ?_⟩
    simpa [orthogonalityPairingSumPointMassSourceCongruence, hπ_pairwise,
      hπ_complete, bA, canonicalDVRBrauerBasis] using hexact c d
  simpa [hπ_pairwise, hπ_complete] using hsource

end PrimeToPIndicatorBasisCoefficientWorker

end Representation
