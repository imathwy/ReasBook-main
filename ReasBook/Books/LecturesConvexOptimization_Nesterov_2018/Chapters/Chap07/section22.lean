import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_22 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators

/-
Definition 7.22 lies in the chapter's truss-topology / simplex-constrained minimization domain.

Sampled owner-style declarations:
- `StdSimplex.Strict` in `Chap03/Definition_3_4`, the chapter owner for strictly positive simplex
  weights;
- `Matrix.PosDef`, the canonical positive-definite matrix owner for the inverse-defined stiffness
  domain;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective on a fixed ambient design space;
- `SetConstrainedMinimizationProblem.optimalValue` and `optimalValue_eq_sInf_image` in
  `Chap01/Definition_1_3_7`, the canonical constrained optimal-value owner on that ambient space;
- `Fin.castLE`, the canonical inclusion of a smaller `Fin` type into a larger one.

Best owner abstraction:
- source-facing: the truss data, the stiffness operator `B(t)`, and the objective on feasible
  strict-simplex designs;
- core/canonical: `SetConstrainedMinimizationProblem (StdSimplex.Strict ℝ (Fin m))`, with
  feasibility cutting out exactly the designs for which `B(t)` is positive definite;
- bridge/view: the source-facing feasible-design objective together with the explicit
  `sInf`-over-feasible-designs formula for the owner optimal value.

Primitive data:
- node positions, arc endpoints, the order constraint `i_k < j_k`, and external forces.
- per-arc geometric nondegeneracy, so every bar has nonzero length.

Derived API:
- the induced full-node inclusion `tailNode`;
- the optional free head `freeHead?`;
- the arc displacement, direction/vector, stacked force vector, and stiffness matrix;
- the feasible-set predicate `B(t).PosDef` on strict simplex designs;
- the objective on the feasible subtype of strict simplex designs;
- the Chapter 1 bridge `toSetConstrainedMinimizationProblem`.

Source/core/bridge triage:
- source-facing: `TrussTopologyDesignProblem` and its truss-specific geometric constructions;
- core/canonical: the constrained minimization owner on the ambient strict-simplex design space;
- bridge/view: the feasible-set and optimal-value rewrites attached to that owner.

The source-facing truss data stay in this file. The only duplicate wheel removed here is the local
infimum-valued `optimalValue` definition: the optimization layer now reuses the Chapter 1 owner
directly, which also gives the faithful `EReal` codomain for empty or unbounded cases. The
source-facing truss objective is the canonical function on the feasible subtype of strict simplex
weights, while the Chapter 1 owner keeps the ambient strict-simplex design space and uses the
feasible-set predicate only in the constrained bridge.
-/

/-- Definition 7.22: a truss topology design problem consists of node positions in `ℝ²`, arcs
joining a free node to a later node, and external forces on the free nodes. The free nodes are
indexed by `Fin n`, the fixed nodes occupy the remaining indices in `Fin (n + p)`, and the
strictly positive simplex weights used for the design objective are introduced below. The endpoint
positions of each arc are required to be distinct, so the normalized bar directions are
well-defined. -/
structure TrussTopologyDesignProblem (n p m : ℕ) where
  /-- The positions of all free and fixed nodes in `ℝ²`. -/
  nodePosition : Fin (n + p) → EuclideanSpace ℝ (Fin 2)
  /-- The tail of each arc, required to be a free node. -/
  tail : Fin m → Fin n
  /-- The head of each arc, allowed to be either free or fixed. -/
  head : Fin m → Fin (n + p)
  /-- Each arc joins its free tail to a later node, matching the condition `j_k > i_k`. -/
  tail_lt_head : ∀ k, ((tail k : Fin n) : ℕ) < (head k : ℕ)
  /-- Each arc has nonzero geometric length, so its endpoint positions are distinct. -/
  endpointPosition_ne :
    ∀ k,
      nodePosition (Fin.castLE (Nat.le_add_right n p) (tail k)) ≠ nodePosition (head k)
  /-- The external forces applied at the free nodes. -/
  externalForce : Fin n → EuclideanSpace ℝ (Fin 2)

namespace TrussTopologyDesignProblem

variable {n p m : ℕ}

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Efree" => EuclideanSpace ℝ (Fin n × Fin 2)

/-- The inclusion of a free-node index into the full node index set. -/
def tailNode (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : Fin (n + p) :=
  Fin.castLE (Nat.le_add_right n p) (problem.tail k)

/-- The free-node index corresponding to the head of an arc, when that head is not fixed. -/
def freeHead? (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : Option (Fin n) :=
  if h : (problem.head k : ℕ) < n then
    some ⟨(problem.head k : ℕ), h⟩
  else
    none

/-- The displacement vector `x_{i_k} - x_{j_k}` along an arc. -/
def arcDisplacement (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : E2 :=
  problem.nodePosition (problem.tailNode k) - problem.nodePosition (problem.head k)

/-- The endpoint positions of an arc are distinct, so the arc displacement is nonzero. -/
theorem arcDisplacement_ne_zero (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    problem.arcDisplacement k ≠ 0 := by
  simpa [arcDisplacement] using sub_ne_zero.mpr (problem.endpointPosition_ne k)

/-- The squared Euclidean length of an arc is positive. -/
theorem arcLengthSq_pos (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    0 < ‖problem.arcDisplacement k‖ ^ (2 : ℕ) := by
  refine pow_pos ?_ 2
  exact norm_pos_iff.mpr (problem.arcDisplacement_ne_zero k)

/-- The squared Euclidean length of an arc is nonzero. -/
theorem arcLengthSq_ne_zero (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    ‖problem.arcDisplacement k‖ ^ (2 : ℕ) ≠ 0 :=
  (problem.arcLengthSq_pos k).ne'

/-- The normalized direction vector `d_k = (x_{i_k} - x_{j_k}) / ‖x_{i_k} - x_{j_k}‖²` attached
to an arc. -/
def arcDirection (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : E2 :=
  (‖problem.arcDisplacement k‖ ^ (2 : ℕ))⁻¹ • problem.arcDisplacement k

/-- The block vector `a_k ∈ ℝ^(2n)` with block `d_k` at the tail, block `-d_k` at a free head,
and zero otherwise. -/
def arcVector (problem : TrussTopologyDesignProblem n p m) (k : Fin m) : Efree :=
  WithLp.toLp 2 <| fun qc : Fin n × Fin 2 ↦
    if qc.1 = problem.tail k then
      problem.arcDirection k qc.2
    else
      match problem.freeHead? k with
      | some j => if qc.1 = j then -(problem.arcDirection k qc.2) else 0
      | none => 0

/-- The stacked external force vector `f = (f₁, …, fₙ)` in block coordinates. -/
def forceVector (problem : TrussTopologyDesignProblem n p m) : Efree :=
  WithLp.toLp 2 <| fun qc : Fin n × Fin 2 ↦ problem.externalForce qc.1 qc.2

/-- The stiffness matrix `B(t) = ∑ₖ t^(k) a_k a_kᵀ` associated to a simplex design vector. -/
def stiffnessMatrix (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex ℝ (Fin m)) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  ∑ k, t.weights k • Matrix.vecMulVec (problem.arcVector k) (problem.arcVector k)

namespace StiffnessMatrix

/- Source-facing Lean notation for the textbook stiffness operator `B(t)`. -/
scoped notation:max "B[" problem:arg "](" t:arg ")" => stiffnessMatrix problem t

end StiffnessMatrix

open scoped StiffnessMatrix

/-- The admissible strict-simplex designs are exactly those for which the stiffness matrix `B(t)`
is positive definite. -/
def feasibleSet (problem : TrussTopologyDesignProblem n p m) : Set (StdSimplex.Strict ℝ (Fin m)) :=
  {t | (B[problem](t)).PosDef}

/-- Membership in the feasible set means positive definiteness of the stiffness matrix `B(t)`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex.Strict ℝ (Fin m)) :
    t ∈ problem.feasibleSet ↔ (B[problem](t)).PosDef :=
  Iff.rfl

/-- Every feasible strict-simplex design has positive-definite stiffness matrix. -/
theorem stiffnessMatrix_posDef
    {problem : TrussTopologyDesignProblem n p m} {t : StdSimplex.Strict ℝ (Fin m)}
    (ht : t ∈ problem.feasibleSet) :
    (B[problem](t)).PosDef := by
  simpa using ht

/-- The objective value `⟪B(t)⁻¹ f, f⟫` evaluated on the feasible-design subtype. -/
def objective (problem : TrussTopologyDesignProblem n p m) :
    problem.feasibleSet → ℝ :=
  fun t ↦ dotProduct (((B[problem](t))⁻¹).mulVec problem.forceVector) problem.forceVector

/-- A truss topology design problem can be used as its objective on feasible strict-simplex
designs. -/
instance : CoeFun (TrussTopologyDesignProblem n p m) (fun problem ↦ problem.feasibleSet → ℝ) where
  coe problem := problem.objective

/-- Evaluating a truss topology design problem at a feasible design returns the source-facing
objective value. -/
@[simp] theorem coe_apply
    (problem : TrussTopologyDesignProblem n p m) (t : problem.feasibleSet) :
    problem t = problem.objective t :=
  rfl

/-- The canonical Chapter 1 minimization owner attached to the truss topology design objective on
the ambient strict-simplex design space. -/
def toSetConstrainedMinimizationProblem
    (problem : TrussTopologyDesignProblem n p m) :
    SetConstrainedMinimizationProblem (StdSimplex.Strict ℝ (Fin m)) where
  feasibleSet := problem.feasibleSet
  objective := fun t ↦ by
    classical
    by_cases ht : t ∈ problem.feasibleSet
    · exact problem.objective ⟨t, ht⟩
    · exact 0

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : TrussTopologyDesignProblem n p m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- On a feasible design, the Chapter 1 bridge recovers the source-facing truss objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply_of_mem_feasibleSet
    (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex.Strict ℝ (Fin m))
    (ht : t ∈ problem.feasibleSet) :
    problem.toSetConstrainedMinimizationProblem t = problem.objective ⟨t, ht⟩ := by
  simp [toSetConstrainedMinimizationProblem, objective, ht]

/-- Expanding `arcDirection` gives the normalized difference
of the endpoint positions of the arc. -/
-- Proof sketch: unfold `arcDirection`.
theorem arcDirection_eq (problem : TrussTopologyDesignProblem n p m) (k : Fin m) :
    problem.arcDirection k =
      let xi := problem.nodePosition (problem.tailNode k)
      let xj := problem.nodePosition (problem.head k)
      (‖xi - xj‖ ^ (2 : ℕ))⁻¹ • (xi - xj) := sorry

/-- Evaluating the stacked force vector at a block index recovers the corresponding coordinate of
the external force at that free node. -/
-- Proof sketch: unfold `forceVector`; `WithLp.toLp` preserves the displayed coordinate function.
theorem forceVector_apply
    (problem : TrussTopologyDesignProblem n p m) (q : Fin n) (c : Fin 2) :
    problem.forceVector (q, c) = problem.externalForce q c := sorry

/-- Expanding `B[problem](t)` gives the weighted sum of the rank-one matrices `a_k a_kᵀ`. -/
-- Proof sketch: unfold `stiffnessMatrix`.
theorem stiffnessMatrix_apply
    (problem : TrussTopologyDesignProblem n p m) (t : StdSimplex ℝ (Fin m)) :
    B[problem](t) =
      ∑ k, t.weights k • Matrix.vecMulVec (problem.arcVector k) (problem.arcVector k) := sorry

/-- Expanding `objective` gives the quadratic form `⟪B(t)⁻¹ f, f⟫` at a feasible design. -/
-- Proof sketch: unfold `objective`.
theorem objective_eq
    (problem : TrussTopologyDesignProblem n p m) (t : problem.feasibleSet) :
    problem.objective t =
      dotProduct (((B[problem](t))⁻¹).mulVec problem.forceVector)
        problem.forceVector := sorry

/-- The canonical owner optimal value for Definition 7.22 is the infimum of the objective over
feasible strict-simplex designs, viewed in `EReal`. -/
theorem optimalValue_eq_sInf_range (problem : TrussTopologyDesignProblem n p m) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      sInf (Set.range fun t : problem.feasibleSet ↦ (problem.objective t : EReal)) := by
  rw [problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  congr 1
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    simpa using
      congrArg (fun r : ℝ ↦ (r : EReal))
        (problem.toSetConstrainedMinimizationProblem_apply_of_mem_feasibleSet t ht).symm
  · rintro ⟨t, rfl⟩
    refine ⟨t.1, t.2, ?_⟩
    exact
      congrArg (fun r : ℝ ↦ (r : EReal))
        (problem.toSetConstrainedMinimizationProblem_apply_of_mem_feasibleSet t.1 t.2)

end TrussTopologyDesignProblem

/-! ### Lemma_7_22 (from Chap07) -/
noncomputable section

open scoped RelativeScaleTransformNotation

universe u v

/- Lemma 7.22 lies in the chapter's relative-scale transform / algebraic metric-update domain.

Sampled owner-style declarations:
- `relativeScaleTransformedObjective` in `Lemma_7_20`, the Chapter 7 owner of the textbook
  transform `f̂`;
- `relativeScaleTransformedObjective_apply` in `Lemma_7_20`, the owner-side evaluation formula for
  `f̂`;
- `relativeScaleTransformedSubgradient` in `Lemma_7_20`, the Chapter 7 owner of the textbook
  transformed subgradient `ĝ[f; x] g`;
- `relativeScaleTransformedSubgradient_def` in `Lemma_7_20`, the owner-side evaluation formula for
  `ĝ[f; x] g`.

Best owner abstraction:
- source-facing: the progress identity for the transformed objective and transformed subgradient;
- core/canonical: the Chapter 7 owners `relativeScaleTransformedObjective` and
  `relativeScaleTransformedSubgradient`;
- bridge/view: this purely algebraic simplification theorem for an abstract squared dual norm.

Primitive data:
- a type `X` carrying scalar multiplication by `ℝ`;
- a metric parameter type `Metric` and a squared dual norm `dualNormSq : Metric → X → ℝ`;
- the current and updated metrics, an objective `f`, points `xk`, `gk`, and scalars `a`, `δ`.

Derived API:
- the transformed objective notation `f̂ xk`;
- the transformed subgradient notation `ĝ[f; xk] gk`;
- the algorithmic progress identity below.

This lemma is algebraic: it uses only the Chapter 7 transform owners and scalar arithmetic, so the
ambient space should stay on the weakest owner-compatible layer rather than the concrete model
`EuclideanSpace ℝ (Fin n)`.
-/
/-- Lemma 7.22: if the transformed subgradient norm at the updated metric `G_{k+1}` scales by
`f(x_k)^2`, the rank-one metric update sends the squared dual norm of `g_k` from `G_k` to
`(1 - δ)` times its old value, the accuracy parameter satisfies `δ ≠ 1`, and the step size `a_k`
satisfies the displayed reciprocal norm identity, then the algorithmic progress identity
`(1 / 2) a_k^2 ‖ĝ[f; x_k] g_k‖_{G_{k+1}}^{*2} = δ a_k f̂ x_k` holds. -/
theorem algorithmic_progress_identity
    {X : Type u} [SMul ℝ X] {Metric : Type v} (dualNormSq : Metric → X → ℝ)
    {Gk GkNext : Metric} {f : X → ℝ} {xk gk : X} {a δ : ℝ}
    (hδ : δ ≠ 1)
    (htransformed_norm :
      dualNormSq GkNext (ĝ[f; xk] gk) =
        (f xk) ^ (2 : ℕ) * dualNormSq GkNext gk)
    (hmetric_update :
      dualNormSq GkNext gk = (1 - δ) * dualNormSq Gk gk)
    (hstep :
      dualNormSq Gk gk = δ / ((1 - δ) * a)) :
    (1 / 2 : ℝ) * a ^ (2 : ℕ) *
        dualNormSq GkNext (ĝ[f; xk] gk) =
      δ * a * f̂ xk := by
  rw [htransformed_norm, hmetric_update, hstep, relativeScaleTransformedObjective_apply]
  have hδ' : 1 - δ ≠ 0 := sub_ne_zero.mpr hδ.symm
  by_cases ha : a = 0
  · subst ha
    simp
  · field_simp [hδ', ha]

end

/-! ### Proposition_7_22 (from Chap07) -/
noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

universe u

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Proposition 7.22 lies in Chapter 7's symmetric-matrix spectral-radius minimization domain.

Sampled owner-style declarations:
- `ρ(X)` in `Definition_7_17`, the chapter owner for the real-valued spectral radius on `𝕊^n`;
- `𝕊^n` in Chapter 5, the chapter owner for real symmetric matrices;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project's
  canonical optimization-value owner for a feasible set and real-valued objective;
- `SpectralRadiusMinimizationProblem.maxRank` in `Definition_7_45`, the later chapter owner for
  `sup_y rank(A y)` in the specialized optimization problem.

Best owner abstraction:
- source-facing: Proposition 7.22's induced lower and upper bounds for `f_p*` along an arbitrary
  family `A : Q → 𝕊^n`;
- core/canonical: the chapter owners `𝕊^n` and `ρ(X)`, together with the Chapter 1 constrained
  minimization owner for the induced infima and `sSup` for the rank bound;
- bridge/view: the named source quantities `inducedRadiusInf`, `inducedRankSup`, and
  `inducedObjectiveInf`.

Primitive data:
- a feasible type `Q`;
- a family `A : Q → 𝕊^n`;
- an exponent parameter `p : ℕ+`;
- the objective `F_p : 𝕊^n → ℝ`;
- the pointwise lower and upper bounds on `F_p`.

Derived API:
- `φ*` as the canonical owner optimal value of `y ↦ ρ(A y)`;
- `r = sup_y rank(A y)`;
- `f_p*` as the canonical owner optimal value of `y ↦ F_p(A y)`.

Source/core/bridge triage:
- source-facing: the proposition below and the three named source quantities `φ*`, `r`, `f_p*`;
- core/canonical: `ρ(X)` on `𝕊^n`, `SetConstrainedMinimizationProblem.optimalValue`, and `sSup`;
- bridge/view: the explicit `EReal`-infimum formulas and the final real-valued inequality bridge.

The previous file duplicated the chapter symmetric-matrix carrier with a local subtype
`selfAdjoint (Matrix ...)`, treated the spectral radius as an arbitrary parameter `ρ`, and
totalized the source infima as plain real `sInf` values on an arbitrary type `Q`. This refinement
keeps the source-facing quantities `φ*`, `r`, and `f_p*`, but moves the two infima onto the
canonical Chapter 1 optimal-value owner so empty families no longer silently collapse to `0`. The
proposition itself is then the finite real-surface bridge for those canonical optimal values.
-/

/-- The infimum `φ*` of the spectral radii `ρ(A y)` along a family of symmetric matrices, encoded
as the canonical constrained optimal value on the feasible type `Q`. -/
def inducedRadiusInf {Q : Type u} (A : Q → SymmMat) : EReal :=
  (.mk Set.univ fun y : Q ↦ ρ(A y) : SetConstrainedMinimizationProblem Q).optimalValue

/-- Expanding `inducedRadiusInf` recovers the extended-real infimum of `ρ(A y)` over `Q`. -/
theorem inducedRadiusInf_eq_sInf_range {Q : Type u} (A : Q → SymmMat) :
    inducedRadiusInf A = sInf (Set.range fun y : Q ↦ (ρ(A y) : EReal)) := by
  let problem : SetConstrainedMinimizationProblem Q := .mk Set.univ fun y ↦ ρ(A y)
  simpa [inducedRadiusInf, problem, Set.image_univ] using problem.optimalValue_eq_sInf_image

/-- The supremum `r` of the ranks of the symmetric matrices `A y`. -/
def inducedRankSup {Q : Type u} (A : Q → SymmMat) : ℕ :=
  sSup (Set.range fun y : Q ↦ Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ))

/-- The induced objective infimum `f_p*`, encoded as the canonical constrained optimal value of
`y ↦ F_p(A y)` on the feasible type `Q`. -/
def inducedObjectiveInf {Q : Type u} (F_p : SymmMat → ℝ) (A : Q → SymmMat) : EReal :=
  (.mk Set.univ fun y : Q ↦ F_p (A y) : SetConstrainedMinimizationProblem Q).optimalValue

/-- Expanding `inducedObjectiveInf` recovers the extended-real infimum of `F_p(A y)` over `Q`. -/
theorem inducedObjectiveInf_eq_sInf_range {Q : Type u} (F_p : SymmMat → ℝ) (A : Q → SymmMat) :
    inducedObjectiveInf F_p A = sInf (Set.range fun y : Q ↦ (F_p (A y) : EReal)) := by
  let problem : SetConstrainedMinimizationProblem Q := .mk Set.univ fun y ↦ F_p (A y)
  simpa [inducedObjectiveInf, problem, Set.image_univ] using
    problem.optimalValue_eq_sInf_image

-- Proof sketch: because `Q` is nonempty, the two owner optimal values are finite and their
-- `toReal` projections recover the textbook real infima. Apply the assumed pointwise inequalities
-- to `A y`; the lower bound follows by taking infima of `(1 / 2) * ρ(A y)^2 ≤ F_p(A y)`, and the
-- upper bound uses `Matrix.rank (A y) ≤ inducedRankSup A` before taking infima.
/-- Proposition 7.22: if `F_p` satisfies the pointwise bounds
`(1 / 2) ρ(X)^2 ≤ F_p(X) ≤ (1 / 2) ρ(X)^2 (rank X)^(1 / p)` on real symmetric matrices, then the
induced infimum `f_p* = inf_y F_p(A y)`, read as the real part of the canonical owner optimal
value on a nonempty feasible type `Q`, satisfies
`(1 / 2) φ*^2 ≤ f_p* ≤ (1 / 2) φ*^2 r^(1 / p)`, where
`φ* = inf_y ρ(A y)` is read in the same way and `r = sup_y rank(A y)`. -/
theorem inducedObjectiveInf_bounds
    {Q : Type u} [Nonempty Q] (p : ℕ+) (F_p : SymmMat → ℝ) (A : Q → SymmMat)
    (h_lower : ∀ X, (1 / 2 : ℝ) * ρ(X) ^ (2 : ℕ) ≤ F_p X)
    (h_upper : ∀ X,
      F_p X ≤ (1 / 2 : ℝ) * ρ(X) ^ (2 : ℕ) *
        ((Matrix.rank (X : Matrix (Fin n) (Fin n) ℝ) : ℝ) ^ (1 / (p : ℝ)))) :
    (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) ≤
        (inducedObjectiveInf F_p A).toReal ∧
      (inducedObjectiveInf F_p A).toReal ≤
        (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) *
          ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) :=
  sorry
