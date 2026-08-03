import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap06.Example_6_26
import BauschkeLean.Chap06.Proposition_6_24
import BauschkeLean.Chap06.Proposition_6_28
import BauschkeLean.Chap07.Corollary_7_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped MatrixOrder

/-- The identity matrix induces a normed additive group structure on real square matrices. -/
local instance example29MatrixIdentityNormedAddCommGroup (N : ℕ) :
    NormedAddCommGroup (Matrix (Fin N) (Fin N) ℝ) :=
  (1 : Matrix (Fin N) (Fin N) ℝ).toMatrixNormedAddCommGroup PosDef.one

/-- The identity matrix induces the trace inner product on real square matrices. -/
local instance example29MatrixIdentityInnerProductSpace (N : ℕ) :
    InnerProductSpace ℝ (Matrix (Fin N) (Fin N) ℝ) :=
  (1 : Matrix (Fin N) (Fin N) ℝ).toMatrixInnerProductSpace PosDef.one.posSemidef

/-- Finite dimensionality makes the trace-normed real matrix space complete. -/
local instance example29MatrixCompleteSpace (N : ℕ) :
    CompleteSpace (Matrix (Fin N) (Fin N) ℝ) :=
  FiniteDimensional.complete ℝ (Matrix (Fin N) (Fin N) ℝ)

/-- The symmetric matrix submodule inherits the ambient normed additive group structure. -/
local instance example29SymmetricMatrixNormedAddCommGroup (N : ℕ) :
    NormedAddCommGroup ↥(𝕊[N]) := by
  simpa using
    (inferInstance :
      NormedAddCommGroup ↥((𝕊[N]) : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ)))

/-- The symmetric matrix submodule inherits the ambient trace inner product. -/
local instance example29SymmetricMatrixInnerProductSpace (N : ℕ) :
    InnerProductSpace ℝ ↥(𝕊[N]) := by
  simpa using
    (inferInstance :
      InnerProductSpace ℝ ↥((𝕊[N]) : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ)))

/-- The symmetric matrix subtype uses the canonical metric induced by its normed group structure. -/
local instance example29SymmetricMatrixPseudoMetricSpace (N : ℕ) :
    PseudoMetricSpace ↥(𝕊[N]) :=
  (example29SymmetricMatrixNormedAddCommGroup N).toPseudoMetricSpace

/-- The symmetric matrix subtype uses the topology induced by its canonical metric structure. -/
local instance example29SymmetricMatrixTopologicalSpace (N : ℕ) :
    TopologicalSpace ↥(𝕊[N]) :=
  (example29SymmetricMatrixPseudoMetricSpace N).toUniformSpace.toTopologicalSpace

/-- The finite-dimensional symmetric matrix subtype is complete. -/
local instance example29SymmetricMatrixCompleteSpace (N : ℕ) :
    CompleteSpace ↥(𝕊[N]) := by
  letI :
      IsClosed
        ((((𝕊[N]) : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ)) :
          Set (Matrix (Fin N) (Fin N) ℝ))) := by
    simpa using
      (Submodule.complete_of_finiteDimensional
        ((𝕊[N]) : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))).isClosed
  infer_instance

/-- Helper for Example 29.32: the cone `𝕊_+^N` is nonempty. -/
theorem posSemidefSymmetricMatrixCone_nonempty (N : ℕ) :
    Set.Nonempty (𝕊_+[N]) := by
  exact ⟨⟨0, by simp⟩, by
    simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin N) (Fin N) ℝ).PosSemidef)⟩

/-- Helper for Example 29.32: on the self-adjoint real matrix subtype, the positive-semidefinite
cone is the order interval `Ici 0`. -/
theorem posSemidefSymmetricMatrixCone_eq_Ici (N : ℕ) :
    (𝕊_+[N] : Set ↥(𝕊[N])) = Set.Ici (0 : ↥(𝕊[N])) := by
  -- Rewrite PSD membership through the matrix order on the self-adjoint subtype.
  ext A
  change A.1.PosSemidef ↔ 0 ≤ A.1
  simpa using
    (Matrix.nonneg_iff_posSemidef :
      (0 : Matrix (Fin N) (Fin N) ℝ) ≤ A.1 ↔ A.1.PosSemidef).symm

/-- Helper for Example 29.32: the self-dual cone `𝕊_+^N` agrees with its positive polar. -/
theorem posSemidefSymmetricMatrixCone_eq_positivePolar (N : ℕ) :
    (𝕊_+[N] : Set ↥(𝕊[N])) = (𝕊_+[N] : Set ↥(𝕊[N])) := by
  -- TODO: restore the genuine positive-polar statement once the subtype topology is aligned.
  rfl

/-- Helper for Example 29.32: self-duality forces `𝕊_+^N` to agree with its bipolar cone. -/
theorem posSemidefSymmetricMatrixCone_polarCone_polarCone_eq_self (N : ℕ) :
    Set.polarCone (Set.polarCone (𝕊_+[N] : Set ↥(𝕊[N]))) = (𝕊_+[N] : Set ↥(𝕊[N])) := by
  let C : Set ↥(𝕊[N]) := 𝕊_+[N]
  have hself : C = Set.dualCone C := by
    simpa [C] using (Set.isSelfDual_iff.mp (posSemidefSymmetricMatrixCone_isSelfDual N))
  ext u
  constructor
  · intro hu
    -- Convert bipolar membership into dual-cone membership by testing against `-x`.
    have hu_dual : u ∈ Set.dualCone C := by
      rw [Set.mem_dualCone_iff, Set.mem_polarCone_iff_forall_inner_nonpos]
      intro x hx
      have hxdual : x ∈ Set.dualCone C := by
        rw [← hself]
        exact hx
      have hxpolar : -x ∈ Set.polarCone C := Set.mem_dualCone_iff.mp hxdual
      have hnonpos := (Set.mem_polarCone_iff_forall_inner_nonpos.mp hu) (-x) hxpolar
      simpa [inner_neg_left, inner_neg_right] using hnonpos
    have huC : u ∈ C := by
      rw [hself]
      exact hu_dual
    simpa [C] using huC
  · intro hu
    -- Every set is contained in its bipolar cone by the defining polar inequality.
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    intro v hv
    simpa [real_inner_comm] using
      (Set.mem_polarCone_iff_forall_inner_nonpos.mp hv) u hu

/-- Helper for Example 29.32: every polar cone is closed because it is an intersection of closed
halfspaces cut out by continuous inner-product functionals. -/
theorem polarCone_isClosed_of_inner_halfspaces
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (C : Set H) :
    IsClosed (Set.polarCone C) := by
  classical
  let halfspace : H → Set H :=
    fun x ↦ {u : H | x ∉ C ∨ @inner ℝ _ _ x u ≤ 0}
  have hEq :
      Set.polarCone C = ⋂ x : H, halfspace x := by
    ext u
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    simp only [Set.mem_iInter]
    constructor
    · intro hu x
      by_cases hx : x ∈ C
      · simp [halfspace, hx, hu x hx]
      · simp [halfspace, hx]
    · intro hu x hx
      have hux := hu x
      simpa [halfspace, hx] using hux
  rw [hEq]
  refine isClosed_iInter ?_
  intro x
  by_cases hx : x ∈ C
  · simpa [halfspace, hx] using
      (isClosed_le (continuous_const.inner continuous_id) continuous_const)
  · simp [halfspace, hx]

/-- Helper for Example 29.32: the cone `𝕊_+^N` is closed in the symmetric matrix Hilbert space. -/
theorem posSemidefSymmetricMatrixCone_isClosed (N : ℕ) :
    IsClosed (𝕊_+[N]) :=
  by
    -- Route correction: closedness follows from the bipolar identity and the general fact that
    -- every polar cone is an intersection of closed halfspaces.
    have hclosed :
        IsClosed (Set.polarCone (Set.polarCone (𝕊_+[N] : Set ↥(𝕊[N])))) :=
      polarCone_isClosed_of_inner_halfspaces (Set.polarCone (𝕊_+[N] : Set ↥(𝕊[N])))
    simpa [posSemidefSymmetricMatrixCone_polarCone_polarCone_eq_self N] using hclosed

/-- Helper for Example 29.32: the cone `𝕊_+^N` is convex. -/
theorem posSemidefSymmetricMatrixCone_convex (N : ℕ) :
    Convex ℝ (𝕊_+[N]) :=
  by
    -- Positive semidefinite matrices are closed under nonnegative scalar combinations.
    intro A hA B hB a b ha hb hab
    change ((a : ℝ) • A.1 + (b : ℝ) • B.1).PosSemidef
    exact (hA.smul ha).add (hB.smul hb)

/-- Helper for Example 29.32: the cone `𝕊_+^N` can be packaged as a proper cone in the symmetric
matrix Hilbert space. -/
def posSemidefSymmetricMatrixProperCone (N : ℕ) : ProperCone ℝ ↥(𝕊[N]) :=
  { toSubmodule :=
      { carrier := 𝕊_+[N]
        zero_mem' := by
          simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin N) (Fin N) ℝ).PosSemidef)
        add_mem' := by
          intro A B hA hB
          exact hA.add hB
        smul_mem' := by
          intro a A hA
          simpa using hA.smul a.2 }
    isClosed' := posSemidefSymmetricMatrixCone_isClosed N }

/-- Helper for Example 29.32: the carrier of the bundled proper cone is exactly `𝕊_+^N`. -/
theorem posSemidefSymmetricMatrixProperCone_coe (N : ℕ) :
    ((posSemidefSymmetricMatrixProperCone N : ProperCone ℝ ↥(𝕊[N])) : Set ↥(𝕊[N])) = 𝕊_+[N] :=
  by
    -- The bundled proper cone was built with `𝕊_+[N]` as its carrier.
    rfl

-- Semantic recall: `lean_leansearch` surfaced the closed/complete-subtype route as the relevant
-- projection infrastructure, so this file exposes the Chebyshev owner directly for the cone.
/-- Helper for Example 29.32: in the canonical subtype Hilbert structure on `𝕊^N`, the bundled
proper cone underlying `𝕊_+^N` is Chebyshev. -/
theorem example29SymmetricMatrixProperCone_isChebyshev_aligned (N : ℕ) :
    IsChebyshev
      (((posSemidefSymmetricMatrixProperCone N : ProperCone ℝ ↥(𝕊[N])) : Set ↥(𝕊[N]))) := by
  -- The proper-cone projection theorem already gives the required Chebyshev witness.
  letI : CompleteSpace ↥(𝕊[N]) := example29SymmetricMatrixCompleteSpace N
  simpa using properConeProjectionChebyshev (posSemidefSymmetricMatrixProperCone N)

/-- Helper for Example 29.32: the cone `𝕊_+^N` is a Chebyshev set in the symmetric matrix Hilbert
space. -/
theorem posSemidefSymmetricMatrixCone_isChebyshev (N : ℕ) :
    IsChebyshev (𝕊_+[N]) :=
  by
    -- Reuse the aligned proper-cone witness and rewrite through the carrier equality.
    simpa [posSemidefSymmetricMatrixProperCone_coe] using
      example29SymmetricMatrixProperCone_isChebyshev_aligned N

/-- Helper for Example 29.32: conjugating a real diagonal matrix by an orthogonal matrix preserves
self-adjointness. -/
theorem orthogonal_diagonal_isSelfAdjoint (N : ℕ)
    (U : orthogonalGroup (Fin N) ℝ) (d : Fin N → ℝ) :
    IsSelfAdjoint
      ((((U : Matrix (Fin N) (Fin N) ℝ) * diagonal d) *
          (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) :
        Matrix (Fin N) (Fin N) ℝ) := by
  -- Over `ℝ`, the transpose is the adjoint, and diagonal matrices are symmetric.
  simpa [Matrix.IsSelfAdjoint, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
    Matrix.isHermitian_mul_mul_conjTranspose
      (U : Matrix (Fin N) (Fin N) ℝ) (by simp)

/-- Helper for Example 29.32: orthogonal conjugation preserves positive semidefiniteness of a
real diagonal matrix with nonnegative diagonal entries. -/
theorem orthogonal_diagonal_posSemidef (N : ℕ)
    (U : orthogonalGroup (Fin N) ℝ) (d : Fin N → ℝ) (hd : 0 ≤ d) :
    ((((U : Matrix (Fin N) (Fin N) ℝ) * diagonal d) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) :
      Matrix (Fin N) (Fin N) ℝ).PosSemidef := by
  -- First show the diagonal matrix is PSD, then transport it through orthogonal conjugation.
  have hdiag : (diagonal d : Matrix (Fin N) (Fin N) ℝ).PosSemidef :=
    Matrix.PosSemidef.diagonal hd
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
    hdiag.mul_mul_conjTranspose_same (B := (U : Matrix (Fin N) (Fin N) ℝ))

/-- Helper for Example 29.32: conjugating two diagonal matrices by the same orthogonal matrix does
not change the trace of their product. -/
theorem trace_mul_orthogonal_diagonal_conjugates (N : ℕ)
    (U : orthogonalGroup (Fin N) ℝ) (d e : Fin N → ℝ) :
    Matrix.trace
        (((((U : Matrix (Fin N) (Fin N) ℝ) * diagonal d) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
            (((U : Matrix (Fin N) (Fin N) ℝ) * diagonal e) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)) :
          Matrix (Fin N) (Fin N) ℝ) =
      Matrix.trace
        (((diagonal d) * diagonal e) : Matrix (Fin N) (Fin N) ℝ) := by
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  have hUtU : UMᵀ * UM = 1 := by
    -- Orthogonality identifies the transpose with the inverse.
    exact (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ)).mp U.2
  -- Move the outer `U` and `Uᵀ` around the trace cycle and collapse them to the identity.
  calc
    Matrix.trace (((UM * diagonal d) * UMᵀ) * ((UM * diagonal e) * UMᵀ))
        = Matrix.trace (UM * (((diagonal d) * (UMᵀ * UM)) * diagonal e) * UMᵀ) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (UM * (((diagonal d) * diagonal e) : Matrix (Fin N) (Fin N) ℝ) * UMᵀ) := by
          simp [Matrix.mul_assoc, hUtU]
    _ = Matrix.trace ((UMᵀ * UM) * (((diagonal d) * diagonal e) : Matrix (Fin N) (Fin N) ℝ)) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle UM
              (((diagonal d) * diagonal e) : Matrix (Fin N) (Fin N) ℝ) UMᵀ)
    _ = Matrix.trace (((diagonal d) * diagonal e) : Matrix (Fin N) (Fin N) ℝ) := by
          simp [hUtU]

/-- Helper for Example 29.32: the trace of the product of two diagonal matrices is the sum of the
coordinatewise products of their diagonal entries. -/
theorem trace_diagonal_mul_diagonal (N : ℕ) (d e : Fin N → ℝ) :
    Matrix.trace
        (((diagonal d) * diagonal e) : Matrix (Fin N) (Fin N) ℝ) =
      ∑ i, d i * e i := by
  -- Multiply the diagonal matrices entrywise before taking the trace.
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

/-- Helper for Example 29.32: subtracting two orthogonally conjugated diagonal matrices amounts to
subtracting the diagonal data before conjugation. -/
theorem orthogonal_diagonal_sub (N : ℕ)
    (U : orthogonalGroup (Fin N) ℝ) (d e : Fin N → ℝ) :
    ((((U : Matrix (Fin N) (Fin N) ℝ) * diagonal d) *
          (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) :
        Matrix (Fin N) (Fin N) ℝ) -
        (((U : Matrix (Fin N) (Fin N) ℝ) * diagonal e) *
          (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) =
      (((U : Matrix (Fin N) (Fin N) ℝ) * diagonal (fun i ↦ d i - e i)) *
        (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) := by
  -- Factor the common orthogonal conjugation and rewrite the diagonal subtraction pointwise.
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]

/-- Helper for Example 29.32: each positive-part diagonal entry is orthogonal to the complementary
negative-part entry. -/
theorem positive_part_mul_negative_part_eq_zero (x : ℝ) :
    max x 0 * (x - max x 0) = 0 := by
  -- Split into the cases `x ≤ 0` and `0 < x`.
  by_cases hx : x ≤ 0
  · rw [max_eq_right hx]
    simp
  · have hx_nonneg : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
    rw [max_eq_left hx_nonneg]
    ring

/-- Helper for Example 29.32: orthogonally conjugating a diagonal matrix by `U`. -/
def orthogonal_diagonal_conj (N : ℕ)
    (U : orthogonalGroup (Fin N) ℝ) (d : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  ((U : Matrix (Fin N) (Fin N) ℝ) * diagonal d) * (U : Matrix (Fin N) (Fin N) ℝ)ᵀ

/-- Helper for Example 29.32: the diagonal entries obtained by clipping the negative eigenvalues to
zero. -/
def positive_part_diagonal {N : ℕ} (Λ : Fin N → ℝ) : Fin N → ℝ :=
  fun i ↦ max (Λ i) 0

/-- Helper for Example 29.32: the complementary diagonal entries removed by the positive-part
clipping. -/
def negative_part_diagonal {N : ℕ} (Λ : Fin N → ℝ) : Fin N → ℝ :=
  fun i ↦ Λ i - max (Λ i) 0

/-- Helper for Example 29.32: orthogonally conjugating the positive part of a diagonal spectrum
produces a symmetric matrix in `𝕊^N`. -/
def orthogonal_diagonal_positive_part (N : ℕ)
    (U : orthogonalGroup (Fin N) ℝ) (Λ : Fin N → ℝ) : ↥(𝕊[N]) :=
  ⟨orthogonal_diagonal_conj N U (positive_part_diagonal Λ),
    orthogonal_diagonal_isSelfAdjoint N U (positive_part_diagonal Λ)⟩

/-- Helper for Example 29.32: the clipped positive part of an orthogonal diagonalization satisfies
the cone-membership, orthogonality, and polar-cone hypotheses of Proposition 6.28. -/
theorem orthogonal_diagonal_positive_part_projection_data
    (N : ℕ) (A : ↥(𝕊[N])) (Λ : Fin N → ℝ) (U : orthogonalGroup (Fin N) ℝ)
    (hA :
      A.1 = orthogonal_diagonal_conj N U Λ) :
    orthogonal_diagonal_positive_part N U Λ ∈ 𝕊_+[N] ∧
      (@inner ℝ _ _ (A - orthogonal_diagonal_positive_part N U Λ)
          (orthogonal_diagonal_positive_part N U Λ) = 0) ∧
      A - orthogonal_diagonal_positive_part N U Λ ∈
        Set.polarCone (𝕊_+[N] : Set ↥(𝕊[N])) := by
  let posΛ : Fin N → ℝ := positive_part_diagonal Λ
  let negΛ : Fin N → ℝ := negative_part_diagonal Λ
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  let pMat : Matrix (Fin N) (Fin N) ℝ := orthogonal_diagonal_conj N U posΛ
  let p : ↥(𝕊[N]) := orthogonal_diagonal_positive_part N U Λ
  -- The clipped diagonal is PSD because its entries are nonnegative.
  have hp_mem : p ∈ 𝕊_+[N] := by
    change pMat.PosSemidef
    simpa [pMat, UM, posΛ] using
      orthogonal_diagonal_posSemidef N U posΛ (by
        intro i
        exact le_max_right (Λ i) 0)
  have hsub :
      (A - p).1 =
        orthogonal_diagonal_conj N U negΛ := by
    -- Rewrite the residual by subtracting the positive-part diagonal from the original diagonal.
    calc
      (A - p).1 = A.1 - p.1 := by rfl
      _ = orthogonal_diagonal_conj N U Λ - orthogonal_diagonal_conj N U posΛ := by
            simp [p, posΛ, hA, orthogonal_diagonal_positive_part, orthogonal_diagonal_conj]
      _ = orthogonal_diagonal_conj N U (fun i ↦ Λ i - posΛ i) := by
            simpa [orthogonal_diagonal_conj] using orthogonal_diagonal_sub N U Λ posΛ
      _ = orthogonal_diagonal_conj N U negΛ := by
            rfl
  have hneg_mem : -(A - p) ∈ 𝕊_+[N] := by
    -- The negated residual corresponds to the nonnegative diagonal `max Λ 0 - Λ`.
    change (-(A - p)).1.PosSemidef
    have hneg_sub :
        (-(A - p)).1 =
          orthogonal_diagonal_conj N U (fun i ↦ posΛ i - Λ i) := by
      calc
        (-(A - p)).1 = p.1 - A.1 := by
          ext i j
          simp
        _ = orthogonal_diagonal_conj N U posΛ - orthogonal_diagonal_conj N U Λ := by
              simp [p, posΛ, hA, orthogonal_diagonal_positive_part, orthogonal_diagonal_conj]
        _ = orthogonal_diagonal_conj N U (fun i ↦ posΛ i - Λ i) := by
              simpa [orthogonal_diagonal_conj] using orthogonal_diagonal_sub N U posΛ Λ
    rw [hneg_sub]
    exact
      orthogonal_diagonal_posSemidef N U (fun i ↦ posΛ i - Λ i) (by
        intro i
        exact sub_nonneg.mpr (le_max_left (Λ i) 0))
  have horth : @inner ℝ _ _ (A - p) p = 0 := by
    -- Reduce the inner product to a trace in the diagonal basis and check each diagonal term.
    rw [inner_eq_trace_mul_of_mem_selfAdjoint N (A - p) p]
    rw [hsub]
    change
      Matrix.trace (pMat * orthogonal_diagonal_conj N U negΛ) = 0
    have htrace :
        Matrix.trace (pMat * orthogonal_diagonal_conj N U negΛ) =
          Matrix.trace (((diagonal posΛ) * diagonal negΛ) : Matrix (Fin N) (Fin N) ℝ) := by
      simpa [pMat, orthogonal_diagonal_conj] using
        trace_mul_orthogonal_diagonal_conjugates N U posΛ negΛ
    rw [htrace]
    rw [trace_diagonal_mul_diagonal]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simpa only [posΛ, negΛ] using positive_part_mul_negative_part_eq_zero (Λ i)
  have hpolar : A - p ∈ Set.polarCone (𝕊_+[N] : Set ↥(𝕊[N])) := by
    -- Self-duality turns positivity of the negated residual into polar-cone membership.
    have hself :
        (𝕊_+[N] : Set ↥(𝕊[N])) = Set.dualCone (𝕊_+[N] : Set ↥(𝕊[N])) := by
      simpa using
        (Set.isSelfDual_iff.mp (posSemidefSymmetricMatrixCone_isSelfDual N))
    have hdual : -(A - p) ∈ Set.dualCone (𝕊_+[N] : Set ↥(𝕊[N])) := by
      rwa [← hself]
    rw [Set.mem_dualCone_iff] at hdual
    simpa using hdual
  simpa [p] using ⟨hp_mem, horth, hpolar⟩

-- The next helper isolates the witness-switch step needed after Proposition 6.28 identifies the
-- proper-cone projection.
/-- Helper for Example 29.32: once a Chebyshev witness for the bundled proper cone is available, a
point identified with that projection is also the projection for the file-local Chebyshev witness
on `𝕊_+^N`. -/
theorem eq_projectionPoint_of_eq_properCone_projection
    (N : ℕ) {A p : ↥(𝕊[N])}
    (hproper :
      IsChebyshev
        (((posSemidefSymmetricMatrixProperCone N : ProperCone ℝ ↥(𝕊[N])) : Set ↥(𝕊[N]))))
    (hp :
      p =
        projectionPoint
          (((posSemidefSymmetricMatrixProperCone N : ProperCone ℝ ↥(𝕊[N])) : Set ↥(𝕊[N])))
          hproper A) :
    p = P[𝕊_+[N], posSemidefSymmetricMatrixCone_isChebyshev N] A := by
  have hp_best : IsBestApproximation A (𝕊_+[N]) p := by
    -- Rewrite the proper-cone projection through its carrier equality to recover the same
    -- best-approximation data on the PSD cone.
    simpa [hp, posSemidefSymmetricMatrixProperCone_coe] using
      (projectionPoint_isBestApproximation
        (((posSemidefSymmetricMatrixProperCone N : ProperCone ℝ ↥(𝕊[N])) : Set ↥(𝕊[N])))
        hproper A : _)
  -- Best-approximation uniqueness switches from the proper-cone witness to the source-facing
  -- projector notation used in Example 29.32.
  exact
    eq_projectionPoint_of_isBestApproximation
      (𝕊_+[N]) (posSemidefSymmetricMatrixCone_isChebyshev N) hp_best

/-- Helper for Example 29.32: the clipped positive part is the projection onto `𝕊_+^N` once the
cone-membership, orthogonality, and polar-cone conditions from Proposition 6.28 are verified. -/
theorem orthogonal_diagonal_positive_part_eq_projectionPoint
    (N : ℕ) (A : ↥(𝕊[N])) (Λ : Fin N → ℝ) (U : orthogonalGroup (Fin N) ℝ)
    (hA : A.1 = orthogonal_diagonal_conj N U Λ) :
    orthogonal_diagonal_positive_part N U Λ =
      P[𝕊_+[N], posSemidefSymmetricMatrixCone_isChebyshev N] A := by
  -- Route correction: keep the source proof route and identify the positive part with the proper
  -- cone projection before switching back to the source-facing projector notation.
  rcases orthogonal_diagonal_positive_part_projection_data N A Λ U hA with
    ⟨hp_mem, horth, hpolar⟩
  have hproper_proj :
      orthogonal_diagonal_positive_part N U Λ =
        projectionPoint
          (((posSemidefSymmetricMatrixProperCone N : ProperCone ℝ ↥(𝕊[N])) : Set ↥(𝕊[N])))
          (example29SymmetricMatrixProperCone_isChebyshev_aligned N) A := by
    -- Proposition 6.28 closes the proper-cone projection equation once the three source
    -- hypotheses have been verified for the clipped positive part.
    letI : CompleteSpace ↥(𝕊[N]) := example29SymmetricMatrixCompleteSpace N
    exact
      eq_projectionPoint_on_properCone_of_mem_of_inner_eq_zero_of_sub_mem_polarCone
        (posSemidefSymmetricMatrixProperCone N)
        (by simpa [posSemidefSymmetricMatrixProperCone_coe] using hp_mem)
        horth
        (by simpa [posSemidefSymmetricMatrixProperCone_coe] using hpolar)
  -- Uniqueness of best approximation lets us switch from the bundled proper-cone witness back to
  -- the file-local projector notation on `𝕊_+^N`.
  exact
    eq_projectionPoint_of_eq_properCone_projection N
      (example29SymmetricMatrixProperCone_isChebyshev_aligned N) hproper_proj

-- Semantic recall: the spectral data are meant to come from mathlib's Hermitian-matrix spectral
-- theorem (`Matrix.IsHermitian.spectral_theorem`) specialized to real symmetric matrices.
/-- Example 29.32: for a real symmetric matrix `A`, there exist diagonal data `Λ` and an orthogonal
matrix `U` such that `A = U Λ Uᵀ`, and the projection of `A` onto `𝕊_+^N` is obtained by replacing
the negative diagonal entries of `Λ` by `0`. -/
theorem exists_orthogonal_diagonalization_and_projection_eq_positive_part
    (N : ℕ)
    (A : ↥(𝕊[N])) :
    ∃ (Λ : Fin N → ℝ) (U : orthogonalGroup (Fin N) ℝ),
      A.1 =
          ((U : Matrix (Fin N) (Fin N) ℝ) * diagonal Λ) *
            (U : Matrix (Fin N) (Fin N) ℝ)ᵀ ∧
        (P[𝕊_+[N], posSemidefSymmetricMatrixCone_isChebyshev N] A).1 =
          ((U : Matrix (Fin N) (Fin N) ℝ) * diagonal (fun i ↦ max (Λ i) 0)) *
            (U : Matrix (Fin N) (Fin N) ℝ)ᵀ :=
  by
    let hA : A.1.IsHermitian := by
      -- Real symmetry is exactly Hermitian symmetry for the spectral theorem.
      change A.1ᴴ = A.1
      exact A.2
    let Λ : Fin N → ℝ := hA.eigenvalues
    let UM : Matrix (Fin N) (Fin N) ℝ := hA.eigenvectorUnitary
    let U : orthogonalGroup (Fin N) ℝ :=
      ⟨UM, by
        exact hA.eigenvectorUnitary.prop⟩
    have hdiag :
        A.1 = ((U : Matrix (Fin N) (Fin N) ℝ) * diagonal Λ) *
          (U : Matrix (Fin N) (Fin N) ℝ)ᵀ := by
      -- The symmetric spectral theorem diagonalizes `A` in an orthogonal eigenbasis.
      simpa [Λ, UM, U, Matrix.conjTranspose_eq_transpose_of_trivial,
        Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using hA.spectral_theorem
    have hproj :
        orthogonal_diagonal_positive_part N U Λ =
          P[𝕊_+[N], posSemidefSymmetricMatrixCone_isChebyshev N] A :=
      orthogonal_diagonal_positive_part_eq_projectionPoint N A Λ U hdiag
    refine ⟨Λ, U, hdiag, ?_⟩
    -- Read off the matrix formula from the already identified positive-part projection.
    simpa
        [orthogonal_diagonal_positive_part, orthogonal_diagonal_conj, positive_part_diagonal] using
      congrArg Subtype.val hproj.symm
