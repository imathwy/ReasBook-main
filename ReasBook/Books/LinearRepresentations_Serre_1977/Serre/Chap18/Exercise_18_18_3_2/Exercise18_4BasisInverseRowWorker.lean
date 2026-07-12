import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.Exercise18_4PointMassRowCongruenceProofWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PrimeToPIndicatorBasisCoefficientWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointMassBrauerBasisEntryCongruenceWorker

/-!
Exercise `18.4` A-basis matrix / inverse-matrix readback worker.

This file keeps the point-mass row congruence on the Exercise `18.4` basis side.  For a basis
`b : Basis ι A (ι → A)`, its evaluation matrix is the matrix of `b` in the standard point-mass
basis, and its inverse matrix is the reverse basis-change matrix.  The coefficient
`b.repr (primeToP_regular_indicator d⁻¹) c` is then read as a prime-to-`p` scalar times an entry
of that inverse matrix.

No endpoint machinery is used here.  Determinants only appear in the local basis linear algebra
statement identifying the inverse matrix with the adjugate formula.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PureBasisInverseMatrix

variable {ι : Type u}
variable {R : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Evaluation matrix of a basis of functions, in the standard point-mass basis.
Rows are function coordinates and columns are basis vectors. -/
abbrev basisEvaluationMatrix (b : Module.Basis ι R (ι → R)) : Matrix ι ι R :=
  (Pi.basisFun R ι).toMatrix b

/-- The inverse basis-change matrix: standard point masses written in the basis `b`. -/
abbrev basisInverseEvaluationMatrix (b : Module.Basis ι R (ι → R)) : Matrix ι ι R :=
  b.toMatrix (Pi.basisFun R ι)

omit [DecidableEq ι] in
@[simp] theorem basisEvaluationMatrix_apply
    (b : Module.Basis ι R (ι → R)) (d c : ι) :
    basisEvaluationMatrix b d c = b c d := by
  simp [basisEvaluationMatrix, Module.Basis.toMatrix_apply, Pi.basisFun_repr]

@[simp] theorem basisInverseEvaluationMatrix_apply
    (b : Module.Basis ι R (ι → R)) (c d : ι) :
    basisInverseEvaluationMatrix b c d = b.repr (Pi.single d (1 : R)) c := by
  simp [basisInverseEvaluationMatrix, Module.Basis.toMatrix_apply, Pi.basisFun_apply]

@[simp] theorem basisEvaluationMatrix_mul_inverse
    (b : Module.Basis ι R (ι → R)) :
    basisEvaluationMatrix b * basisInverseEvaluationMatrix b = 1 := by
  simp [basisEvaluationMatrix, basisInverseEvaluationMatrix]

@[simp] theorem basisInverseEvaluationMatrix_mul_evaluation
    (b : Module.Basis ι R (ι → R)) :
    basisInverseEvaluationMatrix b * basisEvaluationMatrix b = 1 := by
  simp [basisEvaluationMatrix, basisInverseEvaluationMatrix]

/-- The inverse matrix in Mathlib's nonsingular-inverse sense is the reverse basis-change
matrix. -/
theorem basisEvaluationMatrix_nonsing_inv_eq_inverse
    (b : Module.Basis ι R (ι → R)) :
    (basisEvaluationMatrix b)⁻¹ = basisInverseEvaluationMatrix b :=
  Matrix.inv_eq_right_inv (basisEvaluationMatrix_mul_inverse b)

/-- Coordinate readback from the inverse matrix column. -/
theorem basisEvaluationMatrix_nonsing_inv_apply_eq_repr_single
    (b : Module.Basis ι R (ι → R)) (c d : ι) :
    (basisEvaluationMatrix b)⁻¹ c d = b.repr (Pi.single d (1 : R)) c := by
  rw [basisEvaluationMatrix_nonsing_inv_eq_inverse]
  simp

/-- The determinant of the evaluation matrix is a unit because the matrix is a basis-change
matrix. -/
theorem basisEvaluationMatrix_det_isUnit
    (b : Module.Basis ι R (ι → R)) :
    IsUnit (basisEvaluationMatrix b).det := by
  letI : Invertible (basisEvaluationMatrix b) :=
    Module.Basis.invertibleToMatrix (Pi.basisFun R ι) b
  exact Matrix.isUnit_det_of_invertible (basisEvaluationMatrix b)

/-- Adjugate form of the inverse basis-change matrix.  This is local linear algebra for the
Exercise `18.4` basis, not a final determinant endpoint. -/
theorem basisInverseEvaluationMatrix_eq_det_inv_smul_adjugate
    (b : Module.Basis ι R (ι → R)) :
    basisInverseEvaluationMatrix b =
      ↑((basisEvaluationMatrix_det_isUnit b).unit⁻¹) •
        (basisEvaluationMatrix b).adjugate := by
  rw [← basisEvaluationMatrix_nonsing_inv_eq_inverse]
  exact Matrix.nonsing_inv_apply
    (basisEvaluationMatrix b) (basisEvaluationMatrix_det_isUnit b)

/-- Entrywise adjugate readback for the inverse basis-change matrix. -/
theorem basisInverseEvaluationMatrix_apply_eq_det_inv_mul_adjugate
    (b : Module.Basis ι R (ι → R)) (c d : ι) :
    basisInverseEvaluationMatrix b c d =
      ↑((basisEvaluationMatrix_det_isUnit b).unit⁻¹) *
        (basisEvaluationMatrix b).adjugate c d := by
  simpa using
    congr_fun (congr_fun (basisInverseEvaluationMatrix_eq_det_inv_smul_adjugate b) c) d

end PureBasisInverseMatrix

section BrauerBasisInverseMatrixReadback

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance basisInverseRowWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance basisInverseRowWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsLocalRing A] [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed k] [CharP k p] in
/-- The prime-to-`p` indicator coefficient is an inverse-matrix entry, scaled by the
prime-to-`p` centralizer factor. -/
theorem basis_repr_primeToPIndicator_eq_ordCompl_mul_inverseMatrixEntry
    (b : Module.Basis (PRegularConjClass G p) A (PRegularConjClass G p → A))
    (c d : PRegularConjClass G p) :
    b.repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)) c =
      (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
        basisInverseEvaluationMatrix b c (inversePRegularConjClass (p := p) d) := by
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
        basisInverseEvaluationMatrix b c (inversePRegularConjClass (p := p) d) := by
            simp [q, invd]

/-- Pure inverse-matrix form of the fixed-family residual left by the
inverse-prime-to-`p` coefficient route. -/
def canonicalDVRBrauerBasisInverseMatrixResidualDivisibility
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
  let B := basisEvaluationMatrix bA
  let Binv := basisInverseEvaluationMatrix bA
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      B d c - (1 : Matrix (PRegularConjClass G p) (PRegularConjClass G p) A) d c -
        (ConjClasses.centralizerPPart p d.1 : A) *
          ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
            Binv c (inversePRegularConjClass (p := p) d)) =
        (ConjClasses.centralizerPPart p d.1 : A) * a

/-- Pointwise bridge from the pure inverse-matrix residual to the coefficient residual already
isolated by `PrimeToPIndicatorBasisCoefficientWorker`. -/
theorem canonicalDVRBrauerBasisInverseMatrixResidual_pointwise_iff_coefficientResidual
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
    let B := basisEvaluationMatrix bA
    let Binv := basisInverseEvaluationMatrix bA
    (∃ a : A,
      B d c - (1 : Matrix (PRegularConjClass G p) (PRegularConjClass G p) A) d c -
        (ConjClasses.centralizerPPart p d.1 : A) *
          ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
            Binv c (inversePRegularConjClass (p := p) d)) =
        (ConjClasses.centralizerPPart p d.1 : A) * a) ↔
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c) =
            (ConjClasses.centralizerPPart p d.1 : A) * a := by
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
  let B := basisEvaluationMatrix bA
  let Binv := basisInverseEvaluationMatrix bA
  have hdelta :
      (1 : Matrix (PRegularConjClass G p) (PRegularConjClass G p) A) d c =
        ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) := by
    by_cases hdc : d = c
    · subst d
      simp
    · simp [hdc]
  have hcoeff' :
      (ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
          (bA.repr (Pi.single (inversePRegularConjClass (p := p) d) (1 : A)) c) =
        bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G)
            (inversePRegularConjClass (p := p) d)) c := by
    simpa [Binv] using
      (basis_repr_primeToPIndicator_eq_ordCompl_mul_inverseMatrixEntry
        (p := p) (A := A) (G := G) bA c d).symm
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have ha' :
        bA c d -
              ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
            (ConjClasses.centralizerPPart p d.1 : A) *
              ((ordCompl[p] (ConjClasses.centralizerCard d.1) : A) *
                (bA.repr (Pi.single (inversePRegularConjClass (p := p) d) (1 : A)) c)) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
      simpa [B, Binv, hdelta] using ha
    rw [hcoeff'] at ha'
    exact ha'
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have ha' := ha
    rw [← hcoeff'] at ha'
    simpa [B, Binv, hdelta] using ha'

/-- Fixed-family equivalence between the inverse-matrix residual and the earlier
coefficient-residual formulation. -/
theorem canonicalDVRBrauerBasisInverseMatrixResidualDivisibility_iff_coefficientResidual
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    canonicalDVRBrauerBasisInverseMatrixResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      inversePrimeToPIndicatorCoefficientResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hmat c d
    exact
      (canonicalDVRBrauerBasisInverseMatrixResidual_pointwise_iff_coefficientResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d).1
        (hmat c d)
  · intro hcoeff c d
    exact
      (canonicalDVRBrauerBasisInverseMatrixResidual_pointwise_iff_coefficientResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d).2
        (hcoeff c d)

/-- Fixed-family inverse-matrix residual is equivalent to the point-mass source congruence. -/
theorem canonicalDVRBrauerBasisInverseMatrixResidualDivisibility_iff_pointMassSourceCongruence
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
    canonicalDVRBrauerBasisInverseMatrixResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      orthogonalityPairingSumPointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete := by
  exact
    (canonicalDVRBrauerBasisInverseMatrixResidualDivisibility_iff_coefficientResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).trans
      (inversePrimeToPIndicatorCoefficientResidualDivisibility_iff_pointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord)

/-- Global source theorem asking only for the pure inverse-matrix residual for every
coordinate-normalized Exercise `18.4` family. -/
def exercise18_4PointMassRowCongruenceInverseMatrixSourceTheorem : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
      canonicalDVRBrauerBasisInverseMatrixResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- The requested `exercise18_4PointMassRowCongruenceSourceTheorem` is exactly the pure
inverse-matrix residual source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_iff_inverseMatrixResidualSourceTheorem :
    exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G) ↔
      exercise18_4PointMassRowCongruenceInverseMatrixSourceTheorem
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
    exact
      (canonicalDVRBrauerBasisInverseMatrixResidualDivisibility_iff_pointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hpoint
  · intro hmatrix π hπ_simple hπ_coord
    have hpoint :
        let hπ_pairwise :=
          pairwiseNonisomorphic_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_coord
        let hπ_complete :=
          complete_irreducible_family_of_regularClassCoordinate_single
            (p := p) (G := G) (π := π) hπ_simple hπ_coord
        orthogonalityPairingSumPointMassSourceCongruence
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
      (canonicalDVRBrauerBasisInverseMatrixResidualDivisibility_iff_pointMassSourceCongruence
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1
        (hmatrix π hπ_simple hπ_coord)
    simpa [exercise18_4PointMassRowCongruenceAPI] using hpoint

/-- Source-theorem adapter: a proof of the pure inverse-matrix residual source theorem closes
the requested Exercise `18.4` point-mass row congruence source theorem. -/
theorem exercise18_4PointMassRowCongruenceSourceTheorem_of_inverseMatrixResidualSourceTheorem
    (hmatrix :
      exercise18_4PointMassRowCongruenceInverseMatrixSourceTheorem
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowCongruenceSourceTheorem
      (p := p) (A := A) (G := G) :=
  (exercise18_4PointMassRowCongruenceSourceTheorem_iff_inverseMatrixResidualSourceTheorem
    (p := p) (A := A) (G := G)).2 hmatrix

/-- Reverse adapter, useful when transporting an existing point-mass source proof into the
pure inverse-matrix residual form. -/
theorem exercise18_4PointMassRowCongruenceInverseMatrixResidualSourceTheorem_of_sourceTheorem
    (hsource :
      exercise18_4PointMassRowCongruenceSourceTheorem
        (p := p) (A := A) (G := G)) :
    exercise18_4PointMassRowCongruenceInverseMatrixSourceTheorem
      (p := p) (A := A) (G := G) :=
  (exercise18_4PointMassRowCongruenceSourceTheorem_iff_inverseMatrixResidualSourceTheorem
    (p := p) (A := A) (G := G)).1 hsource

end BrauerBasisInverseMatrixReadback

end Representation
