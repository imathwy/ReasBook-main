import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix MatrixOrder

-- Domain sampling for this theorem:
-- * primary domain: semidefinite programming over real symmetric matrices
-- * project owner surface inspected: Chapter 3
--   `primal_feasible_region`, `dual_feasible_region`,
--   `primal_objective_values`, `dual_objective_values`
-- * core/canonical owners reused directly: `Matrix.PosSemidef`, `Matrix.PosDef`,
--   `Matrix.PosDef.posSemidef`, `Matrix.PosSemidef.submatrix`
-- * source-facing owners kept here: `sdp_dual_slack`, `sdp_primal_feasible_region`,
--   `sdp_dual_feasible_region`, `sdp_primal_objective`, `sdp_dual_objective`,
--   `sdp_primal_objective_values`, `sdp_dual_objective_values`

section Theorem101

variable {m n : ℕ}

noncomputable instance instNormedAddCommGroupRealMatrix :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := by
  exact Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

noncomputable instance instInnerProductSpaceRealMatrix :
    InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  exact Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

noncomputable instance instNormedSpaceRealMatrix :
    NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  letI : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := instInnerProductSpaceRealMatrix
  infer_instance

/-- The primal feasible region consists of positive semidefinite matrices satisfying the equality
constraints `Tr (Aᵢ X) = bᵢ`. -/
def sdp_primal_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ ∀ i, Matrix.trace (A i * X) = b i}

/-- Membership in `sdp_primal_feasible_region A b` means positive semidefiniteness together with
the trace constraints `Tr (Aᵢ X) = bᵢ`. -/
theorem mem_sdp_primal_feasible_region_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ sdp_primal_feasible_region A b ↔
      X.PosSemidef ∧ ∀ i, Matrix.trace (A i * X) = b i := Iff.rfl

/-- The dual slack matrix `∑ᵢ yᵢ Aᵢ - C` associated to a dual vector `y`. -/
def sdp_dual_slack
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (∑ i, y i • A i) - C

/-- The dual feasible region consists of vectors whose slack matrix `∑ᵢ yᵢ Aᵢ - C` is positive
semidefinite. -/
def sdp_dual_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin m → ℝ) :=
  {y | (sdp_dual_slack A C y).PosSemidef}

/-- Membership in `sdp_dual_feasible_region A C` means positive semidefiniteness of the dual
slack matrix. -/
theorem mem_sdp_dual_feasible_region_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) :
    y ∈ sdp_dual_feasible_region A C ↔ (sdp_dual_slack A C y).PosSemidef := Iff.rfl

/-- The primal objective values attained on the primal feasible region. -/
def sdp_primal_objective
    (C : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (C * X)

/-- The dual objective `∑ᵢ yᵢ bᵢ` attached to the right-hand side `b`. -/
def sdp_dual_objective
    (b : Fin m → ℝ) (y : Fin m → ℝ) : ℝ :=
  ∑ i, y i * b i

/-- The primal objective values attained on the primal feasible region. -/
def sdp_primal_objective_values
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  sdp_primal_objective C '' sdp_primal_feasible_region A b

/-- Membership in `sdp_primal_objective_values A b C` means that some primal-feasible matrix
attains the value `r`. -/
theorem mem_sdp_primal_objective_values_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    r ∈ sdp_primal_objective_values A b C ↔
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        X ∈ sdp_primal_feasible_region A b ∧ sdp_primal_objective C X = r := Iff.rfl

/-- The dual objective values attained by vectors whose slack matrix `∑ᵢ yᵢ Aᵢ - C` is positive
semidefinite. -/
def sdp_dual_objective_values
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  sdp_dual_objective b '' sdp_dual_feasible_region A C

/-- Membership in `sdp_dual_objective_values A b C` means that some dual-feasible vector attains
the value `r`. -/
theorem mem_sdp_dual_objective_values_iff
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    r ∈ sdp_dual_objective_values A b C ↔
      ∃ y : Fin m → ℝ,
        y ∈ sdp_dual_feasible_region A C ∧ sdp_dual_objective b y = r := Iff.rfl

/-- The primal problem is strictly feasible when one feasible matrix is positive definite. -/
def sdp_primal_strictly_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ X : Matrix (Fin n) (Fin n) ℝ, X.PosDef ∧ ∀ i, Matrix.trace (A i * X) = b i

/-- The dual problem is strictly feasible when one dual slack matrix is positive definite. -/
def sdp_dual_strictly_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ y : Fin m → ℝ, (sdp_dual_slack A C y).PosDef

namespace sdp_primal_strictly_feasible

/-- A strictly feasible primal witness is, in particular, a primal-feasible matrix. -/
theorem exists_mem_primal_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (h : sdp_primal_strictly_feasible A b) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X ∈ sdp_primal_feasible_region A b ∧ X.PosDef := by
  rcases h with ⟨X, hX, hAX⟩
  exact ⟨X, ⟨hX.posSemidef, hAX⟩, hX⟩

end sdp_primal_strictly_feasible

namespace sdp_dual_strictly_feasible

/-- A strictly feasible dual witness is, in particular, dual feasible. -/
theorem exists_mem_dual_feasible_region
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (h : sdp_dual_strictly_feasible A C) :
    ∃ y : Fin m → ℝ,
      y ∈ sdp_dual_feasible_region A C ∧ (sdp_dual_slack A C y).PosDef := by
  rcases h with ⟨y, hy⟩
  exact ⟨y, hy.posSemidef, hy⟩

end sdp_dual_strictly_feasible

/-- Helper for Theorem 10.1: the trace pairing of two positive semidefinite real matrices is
nonnegative. -/
lemma psdTraceMulNonneg
    {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ Matrix.trace (X * Y) := by
  classical
  -- Rewrite one PSD factor as `Zᴴ * Z` so the remaining trace is visibly nonnegative.
  obtain ⟨Z, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  have htrace : 0 ≤ Matrix.trace (Z * X * Zᴴ) :=
    (hX.mul_mul_conjTranspose_same Z).trace_nonneg
  -- Cycle the trace back to the original product.
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm] at htrace
  simpa [Matrix.mul_assoc] using htrace

/-- Helper for Theorem 10.1: any primal-feasible matrix and dual-feasible vector satisfy the SDP
weak-duality inequality. -/
lemma sdpWeakDualityFeasiblePair
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    {X : Matrix (Fin n) (Fin n) ℝ} {y : Fin m → ℝ}
    (hX : X ∈ sdp_primal_feasible_region A b)
    (hy : y ∈ sdp_dual_feasible_region A C) :
    sdp_primal_objective C X ≤ sdp_dual_objective b y := by
  rcases hX with ⟨hXpsd, hprimal⟩
  have hdual : (sdp_dual_slack A C y).PosSemidef := hy
  have hdualTrace :
      Matrix.trace ((∑ i, y i • A i) * X) = sdp_dual_objective b y := by
    -- Expand the trace term and substitute the primal trace constraints.
    calc
      Matrix.trace ((∑ i, y i • A i) * X)
          = Matrix.trace (∑ i, (y i • A i) * X) := by
              rw [Finset.sum_mul]
      _ = ∑ i, Matrix.trace ((y i • A i) * X) := by
            rw [Matrix.trace_sum]
      _ = ∑ i, y i * Matrix.trace (A i * X) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [smul_mul_assoc, Matrix.trace_smul]
            ring
      _ = ∑ i, y i * b i := by
            simp [hprimal]
      _ = sdp_dual_objective b y := rfl
  have hslackTrace :
      Matrix.trace ((sdp_dual_slack A C y) * X) =
        sdp_dual_objective b y - sdp_primal_objective C X := by
    -- Rewrite the slack matrix as `(∑ i, y i • A i) - C` and separate the trace.
    calc
      Matrix.trace ((sdp_dual_slack A C y) * X)
          = Matrix.trace ((((∑ i, y i • A i) - C) * X)) := by
              rfl
      _ = Matrix.trace (((∑ i, y i • A i) * X) - C * X) := by
            rw [sub_mul]
      _ = Matrix.trace (((∑ i, y i • A i) * X)) - Matrix.trace (C * X) := by
            rw [Matrix.trace_sub]
      _ = sdp_dual_objective b y - sdp_primal_objective C X := by
            rw [hdualTrace, sdp_primal_objective]
  have hnonneg : 0 ≤ Matrix.trace ((sdp_dual_slack A C y) * X) :=
    psdTraceMulNonneg hdual hXpsd
  -- The trace of the slack product is the duality gap.
  have hgap : 0 ≤ sdp_dual_objective b y - sdp_primal_objective C X := by
    simpa [hslackTrace] using hnonneg
  exact sub_nonneg.mp hgap

/-- Helper for Theorem 10.1: the dual slack matrix stays symmetric when the SDP data are
symmetric. -/
lemma sdpDualSlack_isSymm
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) (y : Fin m → ℝ) :
    (sdp_dual_slack A C y).IsSymm := by
  -- Symmetry is preserved by the finite linear combination defining the slack matrix.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  calc
    (sdp_dual_slack A C y) j i = ((∑ k, y k • A k) - C) j i := by
      rfl
    _ = (∑ k, y k * A k j i) - C j i := by
      simp [Matrix.sub_apply, Matrix.sum_apply]
    _ = (∑ k, y k * A k i j) - C i j := by
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro k hk
        rw [(hA k).apply i j]
      · rw [hC.apply i j]
    _ = ((∑ k, y k • A k) - C) i j := by
      simp [Matrix.sub_apply, Matrix.sum_apply]
    _ = (sdp_dual_slack A C y) i j := by
      rfl

/-- Helper for Theorem 10.1: symmetric matrices form a linear subspace of the ambient matrix
space, so we package them as a submodule to inherit the canonical additive and topological API. -/
def symmSubmodule (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | X.IsSymm}
  zero_mem' := by simpa using Matrix.isSymm_zero
  add_mem' := by
    intro X Y hX hY
    simpa using hX.add hY
  smul_mem' := by
    intro r X hX
    simpa using hX.smul r

/-- Helper for Theorem 10.1: the symmetric-matrix ambient space used for cone separation. -/
abbrev SymmMat (n : ℕ) : Type := ↥(symmSubmodule n)

instance instAddCommGroupSymmMat : AddCommGroup (SymmMat n) :=
  inferInstanceAs (AddCommGroup ↥(symmSubmodule n))

instance instModuleSymmMat : Module ℝ (SymmMat n) :=
  inferInstanceAs (Module ℝ ↥(symmSubmodule n))

noncomputable instance instNormedAddCommGroupSymmMat : NormedAddCommGroup (SymmMat n) := by
  exact Submodule.normedAddCommGroup (symmSubmodule n)

noncomputable instance instPseudoMetricSpaceSymmMat : PseudoMetricSpace (SymmMat n) :=
  instNormedAddCommGroupSymmMat.toPseudoMetricSpace

noncomputable instance instTopologicalSpaceSymmMat : TopologicalSpace (SymmMat n) :=
  instPseudoMetricSpaceSymmMat.toUniformSpace.toTopologicalSpace

noncomputable instance instNormedSpaceSymmMat : NormedSpace ℝ (SymmMat n) := by
  infer_instance

/-- Helper for Theorem 10.1: the symmetric ambient space inherits the Frobenius inner product from
the ambient matrix space, which is the inner-product structure used by the cone-separation API. -/
noncomputable instance instInnerProductSpaceSymmMat : InnerProductSpace ℝ (SymmMat n) := by
  infer_instance

/-- Helper for Theorem 10.1: the symmetric ambient space is complete, so `ProperCone` separation
theorems apply once the cone packaging is normalized. -/
noncomputable instance instCompleteSpaceSymmMat : CompleteSpace (SymmMat n) := by
  exact FiniteDimensional.complete ℝ (SymmMat n)

/-- Helper for Theorem 10.1: the rank-one matrix `u uᵀ` is symmetric. -/
lemma isSymm_vecMulVec_self (u : Fin n → ℝ) :
    (Matrix.vecMulVec u u).IsSymm := by
  -- Each entry is `u i * u j`, so commutativity swaps the indices.
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- Helper for Theorem 10.1: the canonical symmetric rank-one generator `u uᵀ`. -/
def rankOneSymmGenerator (u : Fin n → ℝ) : SymmMat n :=
  ⟨Matrix.vecMulVec u u, isSymm_vecMulVec_self u⟩

/-- Helper for Theorem 10.1: multiplying by the rank-one matrix `u uᵀ` and taking the trace
recovers the quadratic form `uᵀ X u`. -/
lemma trace_mul_rankOneSymmGenerator_eq_dotProduct_mulVec
    (u : Fin n → ℝ) (X : SymmMat n) :
    Matrix.trace (X.1 * Matrix.vecMulVec u u) = u ⬝ᵥ (X.1 *ᵥ u) := by
  -- Push the rank-one factor through the matrix product so `trace_vecMulVec` applies directly.
  calc
    Matrix.trace (X.1 * Matrix.vecMulVec u u)
        = Matrix.trace (Matrix.vecMulVec (X.1 *ᵥ u) u) := by
            rw [Matrix.mul_vecMulVec]
    _ = (X.1 *ᵥ u) ⬝ᵥ u := by
          rw [Matrix.trace_vecMulVec]
    _ = u ⬝ᵥ (X.1 *ᵥ u) := by
          rw [dotProduct_comm]

/-- Helper for Theorem 10.1: the inherited Frobenius inner product on `SymmMat n` evaluates
against a rank-one generator as the corresponding quadratic form. -/
lemma rankOneSymmGenerator_inner_eq_dotProduct_mulVec
    (u : Fin n → ℝ) (X : SymmMat n) :
    inner ℝ (rankOneSymmGenerator u) X = u ⬝ᵥ (X.1 *ᵥ u) := by
  -- Move from the subtype inner product to the ambient matrix pairing, then collapse the
  -- Frobenius trace formula against the symmetric rank-one matrix.
  rw [Submodule.coe_inner]
  calc
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ) * 1 * (Matrix.vecMulVec u u)ᴴ)
        = Matrix.trace (X.1 * Matrix.vecMulVec u u) := by
            rw [Matrix.mul_one, Matrix.conjTranspose_vecMulVec]
            simp
    _ = u ⬝ᵥ (X.1 *ᵥ u) := trace_mul_rankOneSymmGenerator_eq_dotProduct_mulVec u X

/-- Helper for Theorem 10.1: the PSD cone on symmetric matrices packaged as the inner dual of the
rank-one generators. -/
noncomputable def symmPsdProperCone (n : ℕ) :
    @ProperCone ℝ (SymmMat n) Real.semiring Real.partialOrder Real.instIsOrderedRing
      instNormedAddCommGroupSymmMat.toAddCommMonoid
      instNormedAddCommGroupSymmMat.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      instInnerProductSpaceSymmMat.toModule :=
  ProperCone.innerDual (Set.range rankOneSymmGenerator)

/-- Helper for Theorem 10.1: membership in the symmetric inner-dual cone is exactly positive
semidefiniteness of the underlying symmetric matrix. -/
lemma mem_symmPsdProperCone_iff
    (X : SymmMat n) :
    X ∈ symmPsdProperCone n ↔ X.1.PosSemidef := by
  constructor
  · intro hX
    -- Rewrite inner-dual membership into quadratic-form nonnegativity on all rank-one generators.
    have hsymm : X.1.IsSymm := X.2
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.ext fun i j => by simpa using hsymm.apply i j
    · intro u
      have hmem : rankOneSymmGenerator u ∈ (Set.range rankOneSymmGenerator : Set (SymmMat n)) :=
        ⟨u, rfl⟩
      have hu :
          0 ≤ inner ℝ (rankOneSymmGenerator u) X := by
        exact (ProperCone.mem_innerDual.mp (by simpa [symmPsdProperCone] using hX)) hmem
      rw [rankOneSymmGenerator_inner_eq_dotProduct_mulVec] at hu
      exact hu
  · intro hX
    -- Positive semidefiniteness gives nonnegative pairing with each rank-one generator.
    rw [symmPsdProperCone, ProperCone.mem_innerDual]
    intro Y hY
    rcases hY with ⟨u, rfl⟩
    rw [rankOneSymmGenerator_inner_eq_dotProduct_mulVec]
    exact hX.dotProduct_mulVec_nonneg u

/-- Helper for Theorem 10.1: the homogenized domain cone combines symmetric PSD matrices with a
nonnegative scalar coordinate. -/
noncomputable def symmPsdScalarProperCone (n : ℕ) : ProperCone ℝ (SymmMat n × ℝ) :=
  { toSubmodule :=
      { carrier := {p | p.1.1.PosSemidef ∧ 0 ≤ p.2}
        zero_mem' := by
          constructor
          · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
          · simp
        add_mem' := by
          intro x y hx hy
          constructor
          · exact hx.1.add hy.1
          · simpa using add_nonneg hx.2 hy.2
        smul_mem' := by
          intro a x hx
          constructor
          · exact hx.1.smul a.2
          · simpa [smul_eq_mul] using mul_nonneg a.2 hx.2 }
    isClosed' := by
      have hMatrix : IsClosed {X : SymmMat n | X.1.PosSemidef} := by
        convert (symmPsdProperCone n).isClosed using 1
        ext X
        rw [mem_symmPsdProperCone_iff]
      have hScalar : IsClosed {τ : ℝ | 0 ≤ τ} := isClosed_Ici
      simpa [Set.preimage, Set.setOf_and]
        using (hMatrix.preimage continuous_fst).inter (hScalar.preimage continuous_snd) }

/-- Helper for Theorem 10.1: membership in the homogenized cone is exactly PSD together with a
nonnegative scale. -/
lemma mem_symmPsdScalarProperCone_iff
    (X : SymmMat n) (τ : ℝ) :
    (X, τ) ∈ symmPsdScalarProperCone n ↔ X.1.PosSemidef ∧ 0 ≤ τ := by
  -- The product-cone packaging is only a thin wrapper around the two component memberships.
  rfl

/-- Helper for Theorem 10.1: the symmetric trace-constraint map landing in the right-hand side
space `Fin m → ℝ`. -/
noncomputable def sdpConstraintMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : SymmMat n →L[ℝ] (Fin m → ℝ) :=
  let L : SymmMat n →ₗ[ℝ] Fin m → ℝ :=
    { toFun := fun X i => Matrix.trace (A i * X.1)
      map_add' := by
        intro X Y
        ext i
        -- Each coordinate is linear because trace respects addition in the matrix argument.
        simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro r X
        ext i
        -- Pull the scalar through the matrix product and the trace.
        simp [Matrix.trace_smul] }
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- Helper for Theorem 10.1: evaluating the symmetric trace-constraint map just replays the trace
constraints on the underlying matrix. -/
lemma sdpConstraintMap_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (X : SymmMat n) (i : Fin m) :
    sdpConstraintMap A X i = Matrix.trace (A i * X.1) := rfl

/-- Helper for Theorem 10.1: the objective trace map on the symmetric ambient space. -/
noncomputable def sdpObjectiveMap
    (C : Matrix (Fin n) (Fin n) ℝ) : SymmMat n →L[ℝ] ℝ :=
  let L : SymmMat n →ₗ[ℝ] ℝ :=
    { toFun := fun X => Matrix.trace (C * X.1)
      map_add' := by
        intro X Y
        -- The objective is linear in the matrix variable.
        simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro r X
        -- Again the scalar moves through matrix multiplication and trace.
        simp [Matrix.trace_smul] }
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- Helper for Theorem 10.1: evaluating the symmetric objective map is the textbook trace
objective on the underlying matrix. -/
lemma sdpObjectiveMap_apply
    (C : Matrix (Fin n) (Fin n) ℝ) (X : SymmMat n) :
    sdpObjectiveMap C X = Matrix.trace (C * X.1) := rfl

/-- Helper for Theorem 10.1: the homogenization scale map `τ ↦ τ b`. -/
noncomputable def rhsScaleMap
    (b : Fin m → ℝ) : ℝ →L[ℝ] (Fin m → ℝ) :=
  let L : ℝ →ₗ[ℝ] Fin m → ℝ :=
    { toFun := fun τ i => τ * b i
      map_add' := by
        intro τ σ
        ext i
        -- The right-hand side scales coordinatewise.
        simpa [add_mul]
      map_smul' := by
        intro r τ
        ext i
        -- Scalar multiplication on the scale coordinate is ordinary multiplication.
        simpa [smul_eq_mul, mul_assoc] }
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- Helper for Theorem 10.1: evaluating the right-hand-side scale map produces the coordinatewise
product `τ b`. -/
lemma rhsScaleMap_apply
    (b : Fin m → ℝ) (τ : ℝ) (i : Fin m) :
    rhsScaleMap b τ i = τ * b i := rfl

/-- Helper for Theorem 10.1: the projected homogenized primal map used for cone separation. -/
noncomputable def primalHomogenizedSdpMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (SymmMat n × ℝ) →L[ℝ] (Fin m → ℝ) × ℝ :=
  (((sdpConstraintMap A).comp (ContinuousLinearMap.fst ℝ (SymmMat n) ℝ)) -
      ((rhsScaleMap b).comp (ContinuousLinearMap.snd ℝ (SymmMat n) ℝ))).prod
    (((sdpObjectiveMap C).comp (ContinuousLinearMap.fst ℝ (SymmMat n) ℝ)) -
      α • (ContinuousLinearMap.snd ℝ (SymmMat n) ℝ))

/-- Helper for Theorem 10.1: the projected homogenized map records the primal constraint residual
and the objective gap against `α`. -/
lemma primalHomogenizedSdpMap_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (X : SymmMat n) (τ : ℝ) :
    primalHomogenizedSdpMap A b C α (X, τ) =
      (fun i => Matrix.trace (A i * X.1) - τ * b i, Matrix.trace (C * X.1) - α * τ) := by
  -- Unfold the product map once so later separation lemmas can rewrite by a single formula.
  ext i <;> simp [primalHomogenizedSdpMap, sdpConstraintMap, rhsScaleMap, sdpObjectiveMap]

/-- Helper for Theorem 10.1: the graph homogenized map appends the explicit scale coordinate to the
projected separation map. -/
noncomputable def primalHomogenizedGraphMap
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (SymmMat n × ℝ) →L[ℝ] ((Fin m → ℝ) × ℝ) × ℝ :=
  (primalHomogenizedSdpMap A b C α).prod (ContinuousLinearMap.snd ℝ (SymmMat n) ℝ)

/-- Helper for Theorem 10.1: the graph map keeps the projected residuals and remembers the scale
coordinate explicitly. -/
lemma primalHomogenizedGraphMap_apply
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (X : SymmMat n) (τ : ℝ) :
    primalHomogenizedGraphMap A b C α (X, τ) =
      ((fun i => Matrix.trace (A i * X.1) - τ * b i, Matrix.trace (C * X.1) - α * τ), τ) := by
  -- The graph map is just the projected map together with the remembered homogenization scale.
  simp [primalHomogenizedGraphMap, primalHomogenizedSdpMap_apply]

/-- Helper for Theorem 10.1: every dual-feasible objective value bounds the primal supremum from
above once the primal problem is strictly feasible. -/
lemma csSup_primalValues_le_dualObjective_of_dualFeasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_primal_strictly_feasible A b) {y : Fin m → ℝ}
    (hy : y ∈ sdp_dual_feasible_region A C) :
    sSup (sdp_primal_objective_values A b C) ≤ sdp_dual_objective b y := by
  rcases
      sdp_primal_strictly_feasible.exists_mem_primal_feasible_region A b hstrict with
    ⟨X₀, hX₀, _⟩
  have hnonempty : (sdp_primal_objective_values A b C).Nonempty := by
    exact ⟨sdp_primal_objective C X₀, ⟨X₀, hX₀, rfl⟩⟩
  -- Weak duality bounds every attainable primal value by the chosen dual-feasible objective.
  refine csSup_le hnonempty ?_
  intro z hz
  rcases (mem_sdp_primal_objective_values_iff A b C z).1 hz with ⟨X, hX, rfl⟩
  exact sdpWeakDualityFeasiblePair A b C hX hy

/-- Helper for Theorem 10.1: every primal-feasible objective value lies below the dual infimum
once the dual problem is strictly feasible. -/
lemma primalObjective_le_csInf_dualValues_of_primalFeasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hstrict : sdp_dual_strictly_feasible A C) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ sdp_primal_feasible_region A b) :
    sdp_primal_objective C X ≤ sInf (sdp_dual_objective_values A b C) := by
  rcases sdp_dual_strictly_feasible.exists_mem_dual_feasible_region A C hstrict with
    ⟨y₀, hy₀, _⟩
  have hnonempty : (sdp_dual_objective_values A b C).Nonempty := by
    exact ⟨sdp_dual_objective b y₀, ⟨y₀, hy₀, rfl⟩⟩
  -- Weak duality supplies the lower bound against every dual-feasible value.
  refine le_csInf hnonempty ?_
  intro z hz
  rcases (mem_sdp_dual_objective_values_iff A b C z).1 hz with ⟨y, hy, rfl⟩
  exact sdpWeakDualityFeasiblePair A b C hX hy

/-- Helper for Theorem 10.1: under primal strict feasibility and bounded primal objective values,
the dual objective attains the primal supremum. -/
lemma sdpDualOptimalCertificateAtPrimalSup
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C)) :
    ∃ y : Fin m → ℝ,
      y ∈ sdp_dual_feasible_region A C ∧
        sdp_dual_objective b y = sSup (sdp_primal_objective_values A b C) := by
  let α := sSup (sdp_primal_objective_values A b C)
  have hboundFromAnyDual :
      ∀ y : Fin m → ℝ, y ∈ sdp_dual_feasible_region A C → α ≤ sdp_dual_objective b y := by
    intro y hy
    exact csSup_primalValues_le_dualObjective_of_dualFeasible A b C hstrict hy
  -- Route correction: the proved frontier is now the universal weak-duality bound at `α`; the
  -- remaining missing piece is the homogenized separation argument that must manufacture one
  -- dual-feasible `y` attaining this lower envelope.
  -- TODO: use `symmPsdProperCone` and `mem_symmPsdProperCone_iff` to build the primal-side
  -- homogenized cone map, then prove the vertical point `(0, 1)` is not in its mapped cone image.
  -- After that exclusion lemma, `ProperCone.hyperplane_separation_of_notMem` should produce the
  -- separator whose adjoint-membership condition is already in the right PSD normal form.
  sorry

/-- Helper for Theorem 10.1: under dual strict feasibility and bounded dual objective values, the
primal objective attains the dual infimum. -/
lemma sdpPrimalOptimalCertificateAtDualInf
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_dual_strictly_feasible A C)
    (hbounded : BddBelow (sdp_dual_objective_values A b C)) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X ∈ sdp_primal_feasible_region A b ∧
        sdp_primal_objective C X = sInf (sdp_dual_objective_values A b C) := by
  let β := sInf (sdp_dual_objective_values A b C)
  have hboundAgainstAnyPrimal :
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        X ∈ sdp_primal_feasible_region A b → sdp_primal_objective C X ≤ β := by
    intro X hX
    exact primalObjective_le_csInf_dualValues_of_primalFeasible A b C hstrict hX
  -- Route correction: the mirror argument already has the universal lower envelope `β` isolated;
  -- the only missing ingredient is again the homogenized separator that turns dual strict
  -- feasibility plus boundedness into an exact primal witness at that boundary level.
  -- TODO: mirror the primal-side cone-separation step with the same symmetric PSD cone package,
  -- isolate the dual-side vertical-point exclusion at `β`, and then normalize the separator into a
  -- primal-feasible matrix whose objective value is forced to equal `β` by `hboundAgainstAnyPrimal`.
  sorry

/-- Theorem 10.1 (1). If the primal semidefinite problem is strictly feasible and its objective
values are bounded above, then the dual problem admits an optimal solution and the primal and dual
optimal values coincide. -/
theorem sdp_dual_has_optimal_solution_of_primal_strict_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_primal_strictly_feasible A b)
    (hbounded : BddAbove (sdp_primal_objective_values A b C)) :
    (∃ y : Fin m → ℝ,
      y ∈ sdp_dual_feasible_region A C ∧
        IsLeast (sdp_dual_objective_values A b C) (sdp_dual_objective b y)) ∧
      sSup (sdp_primal_objective_values A b C) = sInf (sdp_dual_objective_values A b C) := by
  rcases
      sdpDualOptimalCertificateAtPrimalSup A b C hA hC hstrict hbounded with
    ⟨y, hy, hyEq⟩
  have hprimalValuesNonempty : (sdp_primal_objective_values A b C).Nonempty := by
    rcases
        sdp_primal_strictly_feasible.exists_mem_primal_feasible_region A b hstrict with
      ⟨X, hX, _⟩
    exact ⟨sdp_primal_objective C X, ⟨X, hX, rfl⟩⟩
  have hyLeast :
      IsLeast (sdp_dual_objective_values A b C) (sdp_dual_objective b y) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    intro r hr
    rcases (mem_sdp_dual_objective_values_iff A b C r).1 hr with ⟨u, hu, rfl⟩
    rw [hyEq]
    -- Every dual-feasible value bounds all primal-feasible objective values from above.
    refine csSup_le hprimalValuesNonempty ?_
    intro z hz
    rcases (mem_sdp_primal_objective_values_iff A b C z).1 hz with ⟨X, hX, rfl⟩
    exact sdpWeakDualityFeasiblePair A b C hX hu
  refine ⟨⟨y, hy, hyLeast⟩, ?_⟩
  -- The attained least dual value identifies the common optimum.
  calc
    sSup (sdp_primal_objective_values A b C) = sdp_dual_objective b y := hyEq.symm
    _ = sInf (sdp_dual_objective_values A b C) := hyLeast.csInf_eq.symm

/-- Theorem 10.1 (2). If the dual semidefinite problem is strictly feasible and its objective
values are bounded below, then the primal problem admits an optimal solution and the primal and
dual optimal values coincide. -/
theorem sdp_primal_has_optimal_solution_of_dual_strict_feasible
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm)
    (hstrict : sdp_dual_strictly_feasible A C)
    (hbounded : BddBelow (sdp_dual_objective_values A b C)) :
    (∃ X : Matrix (Fin n) (Fin n) ℝ,
      X ∈ sdp_primal_feasible_region A b ∧
        IsGreatest (sdp_primal_objective_values A b C) (sdp_primal_objective C X)) ∧
      sSup (sdp_primal_objective_values A b C) = sInf (sdp_dual_objective_values A b C) := by
  rcases
      sdpPrimalOptimalCertificateAtDualInf A b C hA hC hstrict hbounded with
    ⟨X, hX, hXEq⟩
  have hdualValuesNonempty : (sdp_dual_objective_values A b C).Nonempty := by
    rcases sdp_dual_strictly_feasible.exists_mem_dual_feasible_region A C hstrict with
      ⟨y, hy, _⟩
    exact ⟨sdp_dual_objective b y, ⟨y, hy, rfl⟩⟩
  have hXGreatest :
      IsGreatest (sdp_primal_objective_values A b C) (sdp_primal_objective C X) := by
    refine ⟨⟨X, hX, rfl⟩, ?_⟩
    intro r hr
    rcases (mem_sdp_primal_objective_values_iff A b C r).1 hr with ⟨Z, hZ, rfl⟩
    rw [hXEq]
    -- Every dual-feasible value bounds each primal-feasible value from above.
    refine le_csInf hdualValuesNonempty ?_
    intro w hw
    rcases (mem_sdp_dual_objective_values_iff A b C w).1 hw with ⟨y, hy, rfl⟩
    exact sdpWeakDualityFeasiblePair A b C hZ hy
  refine ⟨⟨X, hX, hXGreatest⟩, ?_⟩
  -- The attained greatest primal value is the same as the attained dual infimum.
  calc
    sSup (sdp_primal_objective_values A b C) = sdp_primal_objective C X := hXGreatest.csSup_eq
    _ = sInf (sdp_dual_objective_values A b C) := hXEq

/- Theorem 10.1 (3). The principal-submatrix statement is already the canonical mathlib theorem
`Matrix.PosSemidef.submatrix`, so this file recalls that owner directly instead of keeping a
parallel local wrapper. -/
recall Matrix.PosSemidef.submatrix

end Theorem101
