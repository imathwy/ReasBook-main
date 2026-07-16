import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PrimeToPIndicatorBasisCoefficientWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerOrthogonalitySourceAPIWorker

/-!
Basis-inverse completion boundary for Exercise `18.4`.

This file stays on the Exercise `18.4` basis / inverse-prime-to-`p`-indicator route.  The
unconditional basis computation reads the coefficient of the inverse prime-to-`p` point mass as
an inverse change-of-basis matrix entry.  The remaining non-circular input is exactly the same
row congruence, and it is enough to ask for it only in the columns with nontrivial centralizer
`p`-part.

No Cartan range, cokernel, Smith/product, determinant endpoint, or synthetic source shortcut is
used here.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PureBasisInverseCompletion

variable {ι : Type u}
variable {R : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Evaluation matrix of a function basis, with rows indexed by function arguments. -/
abbrev basisInverseCompletionEvaluationMatrix
    (b : Module.Basis ι R (ι → R)) : Matrix ι ι R :=
  (Pi.basisFun R ι).toMatrix b

/-- Reverse basis-change matrix: standard point masses written in the basis `b`. -/
abbrev basisInverseCompletionInverseMatrix
    (b : Module.Basis ι R (ι → R)) : Matrix ι ι R :=
  b.toMatrix (Pi.basisFun R ι)

omit [DecidableEq ι] in
@[simp] theorem basisInverseCompletionEvaluationMatrix_apply
    (b : Module.Basis ι R (ι → R)) (d c : ι) :
    basisInverseCompletionEvaluationMatrix b d c = b c d := by
  simp [basisInverseCompletionEvaluationMatrix, Module.Basis.toMatrix_apply, Pi.basisFun_repr]

@[simp] theorem basisInverseCompletionInverseMatrix_apply
    (b : Module.Basis ι R (ι → R)) (c d : ι) :
    basisInverseCompletionInverseMatrix b c d = b.repr (Pi.single d (1 : R)) c := by
  simp [basisInverseCompletionInverseMatrix, Module.Basis.toMatrix_apply, Pi.basisFun_apply]

end PureBasisInverseCompletion

section Exercise18_4BasisInverseCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance basisInverseCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance basisInverseCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsLocalRing A] [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed k] [CharP k p] in
/-- The inverse prime-to-`p` indicator coefficient is the inverse basis-change entry scaled by
the prime-to-`p` centralizer factor. -/
theorem basisInverseCompletion_repr_primeToPIndicator_eq_ordCompl_mul_inverseMatrixEntry
    (b : Module.Basis (PRegularConjClass G p) A (PRegularConjClass G p → A))
    (c d : PRegularConjClass G p) :
    b.repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c =
      (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
        basisInverseCompletionInverseMatrix b c (inversePRegularConjClass (p := p) d) := by
  classical
  let invd := inversePRegularConjClass (p := p) d
  let q : A := ordCompl[p] (ConjClasses.centralizerCard d.1)
  have hindicator :
      primeToP_regular_indicator (p := p) (A := A) (G := G) invd =
        q • (Pi.single invd (1 : A) : PRegularConjClass G p → A) := by
    funext t
    by_cases ht : t = invd
    · subst t
      simp [primeToP_regular_indicator, invd, q, inversePRegularConjClass_val,
        ConjClasses.centralizerCard_inv]
    · simp [primeToP_regular_indicator, invd, q, ht]
  calc
    b.repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c
        = b.repr (q • (Pi.single invd (1 : A) : PRegularConjClass G p → A)) c := by
            simpa [invd] using congrArg (fun f => b.repr f c) hindicator
    _ = (q • b.repr (Pi.single invd (1 : A) : PRegularConjClass G p → A)) c := by
            rw [map_smul]
    _ = q * b.repr (Pi.single invd (1 : A)) c := by
            simp
    _ = (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
        basisInverseCompletionInverseMatrix b c (inversePRegularConjClass (p := p) d) := by
            simp [q, invd]

/-- Matrix-entry form of the source-side expansion of the inverse prime-to-`p` indicator.
After multiplying the coefficient column by the target centralizer `p`-part, the column is read
as an inverse basis-change matrix column. -/
theorem canonicalDVRBrauerBasis_inversePrimeToPIndicator_centralizerPPart_inverseMatrix_sum_apply
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
    let B := basisInverseCompletionEvaluationMatrix bA
    let Binv := basisInverseCompletionInverseMatrix bA
    let f :=
      primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
    ∑ i : PRegularConjClass G p,
        B t i *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
              Binv i (inversePRegularConjClass (p := p) d))) =
      (ConjClasses.centralizerPPart p d.1 : A) * f t := by
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
  let B := basisInverseCompletionEvaluationMatrix bA
  let Binv := basisInverseCompletionInverseMatrix bA
  let f :=
    primeToP_regular_indicator
      (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
  have hcoeff :
      ∀ i : PRegularConjClass G p,
        bA.repr f i =
          (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
            Binv i (inversePRegularConjClass (p := p) d) := by
    intro i
    simpa [Binv, f] using
      (basisInverseCompletion_repr_primeToPIndicator_eq_ordCompl_mul_inverseMatrixEntry
        (p := p) (A := A) (G := G) bA i d)
  have hsource :=
    canonicalDVRBrauerBasis_inversePrimeToPIndicator_centralizerPPart_sum_apply
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord t d
  simpa [hπ_pairwise, hπ_complete, bA, B, Binv, f, hcoeff] using hsource

/-- Point-mass form of the previous inverse-matrix column expansion.  This is the local
Exercise `18.4` A-basis / inverse-dual-basis matrix readback for a fixed target column. -/
theorem canonicalDVRBrauerBasis_inversePointMass_centralizerPPart_inverseMatrix_sum_apply
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
    let B := basisInverseCompletionEvaluationMatrix bA
    let Binv := basisInverseCompletionInverseMatrix bA
    ∑ i : PRegularConjClass G p,
        B t i *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
              Binv i (inversePRegularConjClass (p := p) d))) =
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
  let B := basisInverseCompletionEvaluationMatrix bA
  let Binv := basisInverseCompletionInverseMatrix bA
  let f :=
    primeToP_regular_indicator
      (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
  calc
    ∑ i : PRegularConjClass G p,
        B t i *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
              Binv i (inversePRegularConjClass (p := p) d)))
        =
      (ConjClasses.centralizerPPart p d.1 : A) * f t := by
        simpa [hπ_pairwise, hπ_complete, bA, B, Binv, f] using
          (canonicalDVRBrauerBasis_inversePrimeToPIndicator_centralizerPPart_inverseMatrix_sum_apply
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord d t)
    _ =
      if t = inversePRegularConjClass (p := p) d then
        (ConjClasses.centralizerCard d.1 : A)
      else 0 := by
        simpa [f] using
          (centralizerPPart_mul_inversePrimeToPIndicator_apply_eq_inversePointMass
            (p := p) (A := A) (G := G) d t)

/-- Matrix-entry form of the source-side inverse point-mass identity.  This is the
Exercise `18.4` A-basis / inverse-dual-basis route with the coefficient column read back as the
inverse change-of-basis matrix. -/
theorem canonicalDVRBrauerBasis_inversePointMass_centralizerPPart_inverseMatrix_sum_eq
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
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
    let B := basisInverseCompletionEvaluationMatrix bA
    let Binv := basisInverseCompletionInverseMatrix bA
    ∑ i : PRegularConjClass G p,
        B (inversePRegularConjClass (p := p) c) i *
          ((ConjClasses.centralizerPPart p d.1 : A) *
            ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
              Binv i (inversePRegularConjClass (p := p) d))) =
      if c = d then (ConjClasses.centralizerCard d.1 : A) else 0 := by
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
  let B := basisInverseCompletionEvaluationMatrix bA
  let Binv := basisInverseCompletionInverseMatrix bA
  have hcoeff :
      ∀ i : PRegularConjClass G p,
        bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) i =
          (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
            Binv i (inversePRegularConjClass (p := p) d) := by
    intro i
    simpa [Binv] using
      (basisInverseCompletion_repr_primeToPIndicator_eq_ordCompl_mul_inverseMatrixEntry
        (p := p) (A := A) (G := G) bA i d)
  have hsource :=
    canonicalDVRBrauerBasis_inversePointMass_centralizerPPart_sum_eq
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d
  simpa [hπ_pairwise, hπ_complete, bA, B, Binv, hcoeff] using hsource

/-- Nontrivial-column inverse-matrix residual left by the prime-to-`p` indicator coefficient
route.  The subtracted term is the visible centralizer-`p`-part multiple of the inverse
prime-to-`p` point-mass coefficient. -/
def canonicalDVRBrauerBasisInverseMatrixNontrivialResidualDivisibility
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
  let B := basisInverseCompletionEvaluationMatrix bA
  let Binv := basisInverseCompletionInverseMatrix bA
  ∀ c d : PRegularConjClass G p,
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      ∃ a : A,
        B d c - (1 : Matrix (PRegularConjClass G p) (PRegularConjClass G p) A) d c -
          (ConjClasses.centralizerPPart p d.1 : A) *
            ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
              Binv c (inversePRegularConjClass (p := p) d)) =
          (ConjClasses.centralizerPPart p d.1 : A) * a

omit [IsLocalRing A] [HenselianLocalRing A] [Finite G] [IsDomain A]
    [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime] [IsAlgClosed k] [CharP k p] in
/-- Pointwise delta entry for the standard point-mass matrix. -/
theorem basisInverseCompletion_oneMatrix_entry_eq_pointMass
    (c d : PRegularConjClass G p) :
    (1 : Matrix (PRegularConjClass G p) (PRegularConjClass G p) A) d c =
      ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
  classical
  by_cases hdc : d = c
  · subst d
    simp
  · simp [hdc]

/-- The nontrivial-column inverse-matrix residual is exactly the visible Brauer-row readback
congruence.  This is the algebraic cancellation step for the basis-inverse route: the inverse
prime-to-`p` indicator coefficient term is already a `centralizerPPart(d)`-multiple. -/
theorem canonicalDVRBrauerBasisInverseMatrixNontrivialResidualDivisibility_iff_visibleReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    canonicalDVRBrauerBasisInverseMatrixNontrivialResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
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
  let B := basisInverseCompletionEvaluationMatrix bA
  let Binv := basisInverseCompletionInverseMatrix bA
  constructor
  · intro hres c d
    by_cases hd : ConjClasses.centralizerPPart p d.1 = 1
    · refine
        ⟨bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A), ?_⟩
      have hz : (ConjClasses.centralizerPPart p d.1 : A) = 1 := by
        simp [hd]
      simp [bA, hz]
    · rcases hres c d hd with ⟨a, ha⟩
      have hdelta := basisInverseCompletion_oneMatrix_entry_eq_pointMass
        (p := p) (A := A) (G := G) c d
      have hresidual :
          ∃ a : A,
            bA c d -
                ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
              (ConjClasses.centralizerPPart p d.1 : A) *
                ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
                  Binv c (inversePRegularConjClass (p := p) d)) =
              (ConjClasses.centralizerPPart p d.1 : A) * a := by
        refine ⟨a, ?_⟩
        simpa [B, hdelta] using ha
      exact
        (residual_divisibility_iff_visible_divisibility
          (x := bA c d)
          (delta := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
          (z := (ConjClasses.centralizerPPart p d.1 : A))
          (coeff :=
            (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
              Binv c (inversePRegularConjClass (p := p) d))).1 hresidual
  · intro hvisible c d _hd
    rcases hvisible c d with ⟨a, ha⟩
    have hdelta := basisInverseCompletion_oneMatrix_entry_eq_pointMass
      (p := p) (A := A) (G := G) c d
    have hresidual :
        ∃ a : A,
          bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            (ConjClasses.centralizerPPart p d.1 : A) *
              ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
                Binv c (inversePRegularConjClass (p := p) d)) =
            (ConjClasses.centralizerPPart p d.1 : A) * a :=
      (residual_divisibility_iff_visible_divisibility
        (x := bA c d)
        (delta := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
        (z := (ConjClasses.centralizerPPart p d.1 : A))
        (coeff :=
          (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
            Binv c (inversePRegularConjClass (p := p) d))).2 ⟨a, ha⟩
    rcases hresidual with ⟨a', ha'⟩
    refine ⟨a', ?_⟩
    simpa [B, hdelta] using ha'

/-- Adapter from the sharp nontrivial inverse-matrix residual to the fixed-family point-mass
source congruence. -/
theorem orthogonalityPairingSumPointMassSourceCongruence_of_inverseMatrixNontrivialResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hres :
      canonicalDVRBrauerBasisInverseMatrixNontrivialResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    orthogonalityPairingSumPointMassSourceCongruence
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
  orthogonalityPairingSumPointMassSourceCongruence_of_visibleReadbackBasisAlgebra
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord
    ((canonicalDVRBrauerBasisInverseMatrixNontrivialResidualDivisibility_iff_visibleReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hres)

/-- Source theorem consisting only of the nontrivial-column inverse-matrix residual for every
coordinate-normalized Exercise `18.4` family. -/
def exercise18_4PointMassRowCongruenceInverseMatrixNontrivialResidualSourceTheorem : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      canonicalDVRBrauerBasisInverseMatrixNontrivialResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The requested Exercise `18.4` row source theorem is equivalent to the sharp nontrivial
basis-inverse residual source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_iff_inverseMatrixNontrivialResidualSourceTheorem :
    exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowCongruenceInverseMatrixNontrivialResidualSourceTheorem
        (p := p) (A := A) (G := G) := by
  constructor
  · intro hsource π hπ_simple hπ_coord
    have hpoint :
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
      simpa [exercise18_4PointMassRowCongruenceAPI] using
        hsource π hπ_simple hπ_coord
    have hvisible :
        coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
      visibleReadbackBasisAlgebra_of_orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpoint
    exact
      (canonicalDVRBrauerBasisInverseMatrixNontrivialResidualDivisibility_iff_visibleReadback
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hvisible
  · intro hres π hπ_simple hπ_coord
    have hpoint :
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
      orthogonalityPairingSumPointMassSourceCongruence_of_inverseMatrixNontrivialResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord
        (hres π hπ_simple hπ_coord)
    simpa [exercise18_4PointMassRowCongruenceAPI] using hpoint

/-- Forward adapter from the nontrivial inverse-matrix residual theorem to the requested source
theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_inverseMatrixNontrivialResidualSourceTheorem
    (hres :
      exercise18_4PointMassRowCongruenceInverseMatrixNontrivialResidualSourceTheorem
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) :=
  (exercise18_4PointMassRowCongruenceSourceTheorem_iff_inverseMatrixNontrivialResidualSourceTheorem
    (p := p) (A := A) (G := G)).2 hres

end Exercise18_4BasisInverseCompletionWorker

section PureMatrixResidualGap

/-- A two-by-two change-of-basis matrix used to test what the weighted inverse-column
identities can prove by themselves. -/
def basisInverseCompletionMatrixGapB : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 0, 1]

/-- The inverse matrix for `basisInverseCompletionMatrixGapB`. -/
def basisInverseCompletionMatrixGapBinv : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, -1; 0, 1]

/-- A toy column weight with one nontrivial column. -/
def basisInverseCompletionMatrixGapWeight (d : Fin 2) : ℤ :=
  if d = 0 then 2 else 1

/-- The toy matrices satisfy the same basic inverse identity used by the A-basis route. -/
theorem basisInverseCompletionMatrixGap_mul_inverse :
    basisInverseCompletionMatrixGapB * basisInverseCompletionMatrixGapBinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisInverseCompletionMatrixGapB, basisInverseCompletionMatrixGapBinv]

/-- After weighting each inverse-matrix column, the point-mass readback identity is still just
the previous inverse identity with a scalar on the selected column. -/
theorem basisInverseCompletionMatrixGap_weighted_column_identity
    (c d : Fin 2) :
    ∑ i : Fin 2,
        basisInverseCompletionMatrixGapB c i *
          (basisInverseCompletionMatrixGapWeight d *
            basisInverseCompletionMatrixGapBinv i d) =
      if c = d then basisInverseCompletionMatrixGapWeight d else 0 := by
  fin_cases c <;> fin_cases d <;>
    norm_num [basisInverseCompletionMatrixGapB, basisInverseCompletionMatrixGapBinv,
      basisInverseCompletionMatrixGapWeight]

/-- The weighted inverse-column identities do not force the visible row-entry residual.

For this explicit matrix, the weighted point-mass identities hold, but the entry
`B 0 1 - I 0 1 = 1` is not divisible by the nontrivial weight `2`.  Thus the missing input for
the Exercise `18.4` source theorem is not another instance of `B * B⁻¹ = I`; it is precisely an
entrywise congruence for the evaluation matrix itself. -/
theorem basisInverseCompletionMatrixGap_weightedIdentity_not_force_visibleResidual :
    (∀ c d : Fin 2,
      ∑ i : Fin 2,
          basisInverseCompletionMatrixGapB c i *
            (basisInverseCompletionMatrixGapWeight d *
              basisInverseCompletionMatrixGapBinv i d) =
        if c = d then basisInverseCompletionMatrixGapWeight d else 0) ∧
      ¬ ∃ a : ℤ,
        basisInverseCompletionMatrixGapB 0 1 -
            (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
          basisInverseCompletionMatrixGapWeight 0 * a := by
  constructor
  · exact basisInverseCompletionMatrixGap_weighted_column_identity
  · rintro ⟨a, ha⟩
    norm_num [basisInverseCompletionMatrixGapB, basisInverseCompletionMatrixGapWeight] at ha
    omega

end PureMatrixResidualGap

end Representation
