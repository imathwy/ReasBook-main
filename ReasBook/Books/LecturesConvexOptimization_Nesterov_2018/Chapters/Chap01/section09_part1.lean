import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_9_1 (from Chap01) -/
noncomputable section

open Matrix

/- Definition 1.9.1 lies in the finite-dimensional quadratic optimization domain.

Sampled owner-style declarations:
* `Matrix.PosDef`, which canonically packages symmetry together with positive definiteness;
* `Matrix.PosDef.inv`, which supplies the inverse positive-definite matrix used in `A⁻¹`;
* `SetConstrainedMinimizationProblem`, the Chapter 1 owner of an ambient feasible set and
  objective function;
* `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`, the canonical bridge to the
  earlier minimization-problem owner.

Best owner abstractions:
* `Matrix.PosDef` for the Hessian-side linear-algebra data;
* `SetConstrainedMinimizationProblem` for the ambient unconstrained minimization problem.

Primitive data:
* `α`, `a`, `A : Mat`, and `posDef : A.PosDef`

Derived API:
* `A`
* `posDef`
* `objective`
* `minimizer`
* `toSetConstrainedMinimizationProblem`
* the coercion to the ambient objective function through
  `toSetConstrainedMinimizationProblem`

Source/core/bridge triage:
* source-facing: `UnconstrainedQuadraticMinimizationProblem`
* core/canonical: `Matrix.PosDef`, `SetConstrainedMinimizationProblem`
* bridge/view: `toSetConstrainedMinimizationProblem`
-/

/-- The quadratic objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫` on `ℝⁿ`. -/
def quadraticObjective {n : ℕ} (α : ℝ) (a : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x

/-- Definition 1.9.1: An unconstrained quadratic minimization problem on `ℝⁿ` is determined by a
constant term `α`, a linear coefficient `a`, and a symmetric positive-definite matrix `A`, with
objective function `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫`, minimized over all `x ∈ ℝⁿ`. The symmetry
is carried canonically by `Matrix.PosDef`, while the ambient unconstrained minimization problem is
recovered through `toSetConstrainedMinimizationProblem`. -/
structure UnconstrainedQuadraticMinimizationProblem (n : ℕ) where
  α : ℝ
  a : EuclideanSpace ℝ (Fin n)
  A : Matrix (Fin n) (Fin n) ℝ
  posDef : A.PosDef

namespace UnconstrainedQuadraticMinimizationProblem

variable {n : ℕ}

/-- The objective function attached to an unconstrained quadratic minimization problem. -/
def objective (problem : UnconstrainedQuadraticMinimizationProblem n) :=
  quadraticObjective problem.α problem.a problem.A

/-- The canonical critical point `-A⁻¹ a` of an unconstrained quadratic minimization problem. -/
def minimizer (problem : UnconstrainedQuadraticMinimizationProblem n) :=
  -((problem.A⁻¹).toEuclideanLin problem.a)

/-- The ambient Chapter 1 owner attached to an unconstrained quadratic minimization problem. -/
def toSetConstrainedMinimizationProblem
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := Set.univ
  objective := problem.objective

/-- The ambient feasible set of an unconstrained quadratic minimization problem is all of `ℝⁿ`. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ :=
  rfl

/-- The owner bridge evaluates to the quadratic objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : EuclideanSpace ℝ (Fin n)) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- An unconstrained quadratic minimization problem coerces to its objective through the canonical
ambient Chapter 1 owner. -/
instance : CoeFun (UnconstrainedQuadraticMinimizationProblem n)
    (fun _ : UnconstrainedQuadraticMinimizationProblem n ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating an unconstrained quadratic minimization problem returns its objective value. -/
@[simp] theorem coe_apply (problem : UnconstrainedQuadraticMinimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n)) :
    problem x = problem.objective x :=
  rfl

end UnconstrainedQuadraticMinimizationProblem

/-! ### Definition_1_9_1 (from Items/Chap01) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 1.9.1 lies in the finite-dimensional quadratic-optimization domain.

Relevant owner-style declarations sampled before drafting:
* `Matrix.PosDef`, the mathlib owner packaging symmetry together with positive definiteness for
  the Hessian matrix;
* `SetConstrainedMinimizationProblem`, the chapter owner of an ambient feasible set together with
  an objective function;
* `quadraticObjective`, the chapter owner of the quadratic function
  `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫`;
* `UnconstrainedQuadraticMinimizationProblem`, the source-facing owner of the associated
  unconstrained quadratic minimization problem.

Best owner abstraction:
* source-facing: `quadraticObjective` and `UnconstrainedQuadraticMinimizationProblem n`;
* core/canonical: `Matrix.PosDef` and
  `SetConstrainedMinimizationProblem`.

Primitive data:
* `α`, `a`, `A`, and the positive-definiteness witness on `A`

Derived API:
* the displayed quadratic objective
* the stored positive-definite matrix witness `problem.posDef`
* the bridge `problem.toSetConstrainedMinimizationProblem` to the ambient Chapter 1 owner

Source/core/bridge triage:
* source-facing: the quadratic function and its associated unconstrained minimization problem;
* core/canonical: `Matrix.PosDef` and `SetConstrainedMinimizationProblem`;
* bridge/view: the ambient `SetConstrainedMinimizationProblem` over `Set.univ`.

This item is therefore best formalized as a split recall-style file. The exact source-facing owner
API already exists in the chapter file, so this item reuses it directly instead of introducing a
parallel local wrapper. -/

section

variable (α : ℝ) (a : E) (A : Mat)

/- Definition 1.9.1 (1): for `α ∈ ℝ`, `a ∈ ℝⁿ`, and a symmetric positive-definite matrix `A`,
the quadratic function is `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫`. -/
recall quadraticObjective (α : ℝ) (a : E) (A : Mat) : E → ℝ

variable (x : E)

#check
  (show
      quadraticObjective α a A x =
        α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x from
    rfl)

/- Definition 1.9.1 (2): the associated unconstrained quadratic minimization problem on `ℝⁿ` is
the chapter owner `UnconstrainedQuadraticMinimizationProblem n`, whose objective is the quadratic
function above and whose ambient feasible set is all of `ℝⁿ`. -/
recall UnconstrainedQuadraticMinimizationProblem (n : ℕ) : Type

variable (problem : UnconstrainedQuadraticMinimizationProblem n)

/- The positive-definite matrix-side hypothesis is stored canonically as `problem.posDef`. -/
recall UnconstrainedQuadraticMinimizationProblem.posDef
    (problem : UnconstrainedQuadraticMinimizationProblem n) : problem.A.PosDef

/- The attached objective function is canonically `quadraticObjective problem.α problem.a
problem.A`. -/
recall UnconstrainedQuadraticMinimizationProblem.objective
    (problem : UnconstrainedQuadraticMinimizationProblem n) : E → ℝ

#check
  (show
      problem.objective = quadraticObjective problem.α problem.a problem.A from
    rfl)

/- Pointwise, the attached objective has the displayed quadratic formula. -/
#check
  (show
      problem.objective x =
        problem.α + inner ℝ problem.a x +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin x) x from
    rfl)

/- The ambient Chapter 1 owner packages the problem over feasible set `Set.univ`. -/
recall UnconstrainedQuadraticMinimizationProblem.toSetConstrainedMinimizationProblem
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    SetConstrainedMinimizationProblem E

recall UnconstrainedQuadraticMinimizationProblem.toSetConstrainedMinimizationProblem_feasibleSet
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ

end

/-! ### Definition_1_9_2 (from Chap01) -/
noncomputable section

open scoped Gradient

/-
Definition 1.9.2 lies in the linear-algebra / Krylov-subspace domain.

Sampled owner declarations:
* `Submodule.span`, the canonical owner for linear spans of iterates;
* `Submodule.map`, the canonical owner for images of Krylov stages;
* `LinearMap.krylovSubspace`, the ambient owner for an endomorphism and a seed vector;
* `UnconstrainedQuadraticMinimizationProblem.krylovSubspace`, the quadratic specialization.

Best owner abstraction:
* `LinearMap.krylovSubspace` as the ambient owner, specialized to
  `problem.krylovSubspace x₀ k` in the quadratic setting.

Primitive data:
* ambient owner: an endomorphism `f` and a seed vector `x`;
* source-facing specialization: a quadratic problem `problem` and an initial point `x₀`.

Derived API:
* monotonicity of Krylov stages;
* the successor-stage image lemma;
* the successor-stage `sup` decomposition and finrank bound;
* the positive-iterate span bridge for quadratic problems.

Source/core/bridge triage:
* source-facing: `problem.krylovSubspace x₀ k`;
* core/canonical: `LinearMap.krylovSubspace`;
* bridge/view: `problem.krylovSubspace_eq_span_positiveIterates`.
-/
namespace LinearMap

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The Krylov subspace generated by the endomorphism `f` and the seed vector `x` is the span of
`x`, `f x`, ..., `f^(k - 1) x`. -/
def krylovSubspace (f : M →ₗ[R] M) (k : ℕ+) (x : M) : Submodule R M :=
  Submodule.span R
    (Set.range fun i : Fin (k : ℕ) ↦
      (f ^ (i : ℕ)) x)

/-- The Krylov subspaces form a one-step increasing chain. -/
-- Proof sketch: enlarge the indexing set from `Fin k` to `Fin (k + 1)` and apply
-- `Submodule.span_mono`.
theorem krylovSubspace_le_succ (f : M →ₗ[R] M) (k : ℕ+) (x : M) :
    f.krylovSubspace k x ≤ f.krylovSubspace (k + 1) x := by
  -- Enlarge the generator index set from `Fin k` to `Fin (k + 1)`.
  rw [LinearMap.krylovSubspace, LinearMap.krylovSubspace]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castSucc, rfl⟩

/-- The Krylov subspaces are monotone in the stage index. -/
-- Proof sketch: iterate the one-step inclusion or directly embed `Fin j` into `Fin k` and use
-- `Submodule.span_mono`.
theorem krylovSubspace_mono (f : M →ₗ[R] M) (x : M) {j k : ℕ+} (hjk : j ≤ k) :
    f.krylovSubspace j x ≤ f.krylovSubspace k x := by
  -- Embed `Fin j` into `Fin k` using the monotonicity hypothesis on the stage indices.
  rw [LinearMap.krylovSubspace, LinearMap.krylovSubspace]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castLE (show (j : ℕ) ≤ (k : ℕ) from hjk), rfl⟩

/-- Applying the generating endomorphism sends the `k`th Krylov subspace into the next stage. -/
-- Proof sketch: prove the claim on generators `f^i x`, where applying `f` raises the iterate by
-- one, and extend by `Submodule.span_induction`.
theorem map_mem_krylovSubspace_succ
    (f : M →ₗ[R] M) (x : M) {k : ℕ+} {y : M}
    (hy : y ∈ f.krylovSubspace k x) :
    f y ∈ f.krylovSubspace (k + 1) x := by
  let generators : Set M :=
    Set.range fun i : Fin (k : ℕ) ↦ (f ^ (i : ℕ)) x
  let succGenerators : Set M :=
    Set.range fun i : Fin (((k + 1 : ℕ+) : ℕ)) ↦ (f ^ (i : ℕ)) x
  -- Map the whole Krylov span into the span of the image and identify each image generator with
  -- the corresponding successor iterate.
  rw [LinearMap.krylovSubspace] at hy ⊢
  have himage : f y ∈ Submodule.span R (f '' generators) := by
    simpa [generators] using (Submodule.apply_mem_span_image_of_mem_span f hy)
  have hsubset : f '' generators ⊆ succGenerators := by
    rintro _ ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨i.1 + 1, Nat.succ_lt_succ i.2⟩, by
      simp [pow_succ', Module.End.mul_apply]⟩
  exact (Submodule.span_mono hsubset) himage

/-- The successor Krylov stage is obtained by adjoining the last new iterate. -/
theorem krylovSubspace_succ_eq_sup_span_last
    (f : M →ₗ[R] M) (k : ℕ+) (x : M) :
    f.krylovSubspace (k + 1) x = f.krylovSubspace k x ⊔ R ∙ (f ^ (k : ℕ)) x := by
  rw [LinearMap.krylovSubspace, LinearMap.krylovSubspace]
  let xs : Fin ((k + 1 : ℕ+) : ℕ) → M := fun i ↦ (f ^ (i : ℕ)) x
  have hset :
      Set.range xs =
        insert (xs (Fin.last k)) (Set.range (Fin.init xs)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.lastCases ?_ ?_ i
      · left
        rfl
      · intro j
        right
        exact ⟨j, rfl⟩
    · intro hy
      rcases hy with rfl | ⟨i, rfl⟩
      · exact ⟨Fin.last k, by simp⟩
      · exact ⟨i.castSucc, rfl⟩
  have hspan :
      Submodule.span R (Set.range xs) =
        Submodule.span R (Set.range (Fin.init xs)) ⊔ R ∙ xs (Fin.last k) := by
    rw [hset, Submodule.span_insert, sup_comm]
  simpa [xs, Fin.init] using hspan

/-- If the seed lies in the image of the previous Krylov stage, then the next stage maps into the
image of that previous stage. -/
theorem krylovSubspace_succ_le_map_of_preimage_mem
    (f : M →ₗ[R] M) (k : ℕ+) (x y : M)
    (hy : y ∈ f.krylovSubspace k x) (hfx : f y = x) :
    f.krylovSubspace (k + 1) x ≤ Submodule.map f (f.krylovSubspace k x) := by
  rw [LinearMap.krylovSubspace]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact ⟨y, hy, by simpa using hfx⟩
  · refine ⟨(f ^ (j : ℕ)) x, ?_, ?_⟩
    · rw [LinearMap.krylovSubspace]
      exact Submodule.subset_span ⟨j, rfl⟩
    · simp [pow_succ', Module.End.pow_apply]

section Finrank

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The dimension of a Krylov stage increases by at most one when passing to the next stage. -/
theorem finrank_krylovSubspace_succ_le
    (f : V →ₗ[K] V) (k : ℕ+) (x : V) :
    Module.finrank K ↥(f.krylovSubspace (k + 1) x) ≤
      Module.finrank K ↥(f.krylovSubspace k x) + 1 := by
  rw [LinearMap.krylovSubspace_succ_eq_sup_span_last]
  by_cases hx : (f ^ (k : ℕ)) x ∈ f.krylovSubspace k x
  · have hs :
        f.krylovSubspace k x ⊔ K ∙ (f ^ (k : ℕ)) x = f.krylovSubspace k x := by
      rw [sup_comm]
      exact sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
    rw [hs]
    exact Nat.le_succ _
  · change
      Module.finrank K ↥(f.krylovSubspace k x ⊔ Submodule.span K {(f ^ (k : ℕ)) x}) ≤
        Module.finrank K ↥(f.krylovSubspace k x) + 1
    exact le_of_eq (Submodule.finrank_sup_span_singleton hx)

end Finrank

end LinearMap

/-
Definition 1.9.2 is represented by the owner-side declaration

`problem.krylovSubspace x₀ k`.

The primitive data are the quadratic problem `problem` and the starting point `x₀`. The matrix
formula `span {A (x₀ - x*), ..., Aᵏ (x₀ - x*)}` is a derived specialization of the standard Krylov
subspace generated by `problem.A` and the intrinsic initial gradient `∇ problem.objective x₀`.
-/

namespace UnconstrainedQuadraticMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Definition 1.9.2: for an unconstrained quadratic minimization problem `problem`, a starting
point `x₀`, and `k ≥ 1`, the Krylov subspace `𝓛ₖ` is the subspace generated by
`A (x₀ - x*)`, ..., `Aᵏ (x₀ - x*)`, implemented canonically as the standard Krylov subspace of
`problem.A` generated by the initial gradient `∇ problem.objective x₀`. -/
def krylovSubspace (problem : UnconstrainedQuadraticMinimizationProblem n)
    (x0 : E) (k : ℕ+) : Submodule ℝ E :=
  let A := problem.A.toEuclideanLin
  A.krylovSubspace k (∇ problem.objective x0)

notation "𝓛(" problem ", " x0 ", " k ")" =>
  UnconstrainedQuadraticMinimizationProblem.krylovSubspace problem x0 k

/-- The quadratic Krylov subspaces are monotone in the stage index. -/
-- Proof sketch: unfold to the owner-side `LinearMap.krylovSubspace` and apply the monotonicity
-- theorem there.
theorem krylovSubspace_mono (problem : UnconstrainedQuadraticMinimizationProblem n)
    (x0 : E) {j k : ℕ+} (hjk : j ≤ k) :
    𝓛(problem, x0, j) ≤ 𝓛(problem, x0, k) := by
  -- Unfold the quadratic specialization and use the ambient monotonicity theorem.
  simpa [UnconstrainedQuadraticMinimizationProblem.krylovSubspace] using
    LinearMap.krylovSubspace_mono
      problem.A.toEuclideanLin (∇ problem.objective x0) hjk

end UnconstrainedQuadraticMinimizationProblem

namespace UnconstrainedQuadraticMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Helper for Definition 1.9.2: the gradient of the quadratic objective is the matrix action on
the displacement from the minimizer. -/
private lemma gradient_eq_apply_sub_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    ∇ problem.objective x = problem.A.toEuclideanLin (x - problem.minimizer) := by
  have hsymm : problem.A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
  have hgrad :
      ∇ problem.objective x = problem.a + problem.A.toEuclideanLin x := by
    -- Rewrite the objective gradient using the earlier symmetric quadratic formula.
    simpa [UnconstrainedQuadraticMinimizationProblem.objective] using
      congrFun (quadraticObjective_gradient_eq problem.α problem.a problem.A hsymm) x
  have hmin : problem.A.toEuclideanLin problem.minimizer = -problem.a :=
    apply_matrix_to_minimizer_eq_neg_linear_coefficient problem
  have ha : problem.a = -problem.A.toEuclideanLin problem.minimizer := by
    simpa using (congrArg Neg.neg hmin).symm
  -- Replace `a` by `-A x*` and package the result as `A (x - x*)`.
  calc
    ∇ problem.objective x = problem.a + problem.A.toEuclideanLin x := hgrad
    _ = -problem.A.toEuclideanLin problem.minimizer + problem.A.toEuclideanLin x := by
          rw [ha]
    _ = problem.A.toEuclideanLin x - problem.A.toEuclideanLin problem.minimizer := by
          abel
    _ = problem.A.toEuclideanLin (x - problem.minimizer) := by
          simp [sub_eq_add_neg, map_add, map_neg]

/-- Helper for Definition 1.9.2: matrix powers transport to powers of the induced Euclidean linear
map. -/
private lemma matrix_pow_toEuclideanLin_apply
    (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (x : E) :
    (A ^ m).toEuclideanLin x = (A.toEuclideanLin ^ m) x := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hpow :
      (A ^ m).toEuclideanLin = (A.toEuclideanLin ^ m : E →ₗ[ℝ] E) := by
    -- Move to the coordinate-basis `toLin` model, where matrix powers are already registered.
    change Matrix.toLin b b (A ^ m) = (Matrix.toLin b b A) ^ m
    rw [Matrix.toLin_pow]
  exact congrArg (fun T : E →ₗ[ℝ] E ↦ T x) hpow

/-- Expanding `𝓛(problem, x₀, k)` recovers the textbook positive-iterate span
`span {A (x₀ - x*), ..., Aᵏ (x₀ - x*)}`. -/
-- Proof sketch: rewrite the seed vector as the initial gradient `A (x₀ - x*)`, then identify the
-- iterates of the linear map `problem.A.toEuclideanLin` with the positive powers of `A`.
theorem krylovSubspace_eq_span_positiveIterates
    (problem : UnconstrainedQuadraticMinimizationProblem n)
    (x0 : E) (k : ℕ+) :
    𝓛(problem, x0, k) =
      Submodule.span ℝ
        (Set.range fun i : Fin (k : ℕ) ↦
          (problem.A ^ ((i : ℕ) + 1)).toEuclideanLin (x0 - problem.minimizer)) := by
  let A : E →ₗ[ℝ] E := problem.A.toEuclideanLin
  let displacement : E := x0 - problem.minimizer
  -- Rewrite the Krylov seed as the first positive iterate `A (x₀ - x*)`.
  rw [UnconstrainedQuadraticMinimizationProblem.krylovSubspace, LinearMap.krylovSubspace,
    gradient_eq_apply_sub_minimizer]
  -- Match each owner-side generator with the corresponding positive matrix iterate.
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    calc
      (problem.A ^ ((i : ℕ) + 1)).toEuclideanLin displacement
          = (A ^ ((i : ℕ) + 1)) displacement := by
              exact (matrix_pow_toEuclideanLin_apply problem.A ((i : ℕ) + 1) displacement)
      _ = (A ^ (i : ℕ)) (A displacement) := by
            simp [pow_succ, Module.End.mul_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    calc
      (A ^ (i : ℕ)) (A displacement) = (A ^ ((i : ℕ) + 1)) displacement := by
        simp [pow_succ, Module.End.mul_apply]
      _ = (problem.A ^ ((i : ℕ) + 1)).toEuclideanLin displacement := by
            exact (matrix_pow_toEuclideanLin_apply problem.A ((i : ℕ) + 1) displacement).symm

end UnconstrainedQuadraticMinimizationProblem

/-! ### Definition_1_9_2 (from Items/Chap01) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 1.9.2 lies in the finite-dimensional quadratic / Krylov-subspace domain.

Relevant owner declarations sampled before drafting:
* `LinearMap.krylovSubspace`, the ambient Krylov-space owner for an endomorphism and seed vector;
* `UnconstrainedQuadraticMinimizationProblem.krylovSubspace`, the project owner for the `k`th
  Krylov stage attached to a quadratic problem and an initial point;
* `UnconstrainedQuadraticMinimizationProblem.krylovSubspace_eq_span_positiveIterates`, the bridge
  theorem expanding that owner into the textbook span of positive powers of `A`.

Source/core/bridge triage:
* source-facing: the Krylov subspace `𝓛ₖ` generated by `A (x₀ - x*)`, ..., `Aᵏ (x₀ - x*)`;
* core/canonical: `problem.krylovSubspace x₀ k`;
* bridge/view: the explicit span formula in terms of `problem.A` and `problem.minimizer`.

The exact owner and its textbook expansion already exist in the chapter file, so this item reuses
them directly instead of introducing a parallel local definition. -/

section

variable (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 : E) (k : ℕ+)

/- Definition 1.9.2: for an unconstrained quadratic problem `problem`, a starting point `x₀`, and
`k ≥ 1`, the Krylov subspace `𝓛ₖ` is the chapter owner `problem.krylovSubspace x₀ k`, written on
the source-facing surface as `𝓛(problem, x0, k)`. -/
#check (𝓛(problem, x0, k) : Submodule ℝ E)

/- The owner-side bridge theorem expands `problem.krylovSubspace x₀ k` as the span of
`A (x₀ - x*)`, ..., `Aᵏ (x₀ - x*)`, with `x* = problem.minimizer`. -/
#check
  (show
      𝓛(problem, x0, k) =
        Submodule.span ℝ
          (Set.range fun i : Fin (k : ℕ) ↦
            (problem.A ^ ((i : ℕ) + 1)).toEuclideanLin (x0 - problem.minimizer)) from
    problem.krylovSubspace_eq_span_positiveIterates x0 k)

end

/-! ### Definition_1_9_3 (from Chap01) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 1.9.3 lies in the quadratic / affine-search-space domain.

Sampled owner declarations in this domain:
* `problem.krylovSubspace x₀ k`, the project-level owner for `𝓛ₖ`;
* `AffineSubspace.mk'`, the canonical affine-subspace owner built from a base point and a
  direction;
* `AffineSubspace.mem_mk'`, the owner-side membership characterization;
* `AffineSubspace.direction_mk'`, the owner-side direction computation.

Best owner abstraction:
* the pair `problem.krylovSubspace x₀ k` / `problem.affineKrylovSearchSpace x₀ k`.

Primitive data:
* the quadratic problem `problem`;
* the starting point `x₀`;
* the positive-indexed iterate sequence `xs`.

Derived API:
* the minimizing property of `problem.objective` on `problem.affineKrylovSearchSpace x₀ k`;
* the ambient trajectory obtained by adjoining `x₀` to a positive-indexed sequence.

Source/core/bridge triage:
* source-facing: `problem.affineKrylovSearchSpace x₀ k` and `IsConjugateGradientSequence`;
* core/canonical: `problem.krylovSubspace x₀ k` and `AffineSubspace.mk'`;
* bridge/view: the ambient trajectory `conjugateGradientTrajectory`. -/

namespace UnconstrainedQuadraticMinimizationProblem

/-- The affine Krylov search space `x₀ + 𝓛ₖ` attached to `problem` and the starting point `x₀`. -/
def affineKrylovSearchSpace (problem : UnconstrainedQuadraticMinimizationProblem n)
    (x0 : E) (k : ℕ+) : AffineSubspace ℝ E :=
  AffineSubspace.mk' x0 (𝓛(problem, x0, k))

end UnconstrainedQuadraticMinimizationProblem

/-- Definition 1.9.3: A positive-indexed sequence is generated by the conjugate gradient method
when each iterate `xₖ` minimizes the quadratic objective over the affine space `x₀ + 𝓛ₖ`, where
`𝓛ₖ` is the standard Krylov subspace generated by `A` and the initial seed `A (x₀ - x*)`, with
`x* = -A⁻¹ a`. -/
def IsConjugateGradientSequence (problem : UnconstrainedQuadraticMinimizationProblem n)
    (x0 : E) (xs : ℕ+ → E) : Prop :=
  ∀ k,
    xs k ∈ problem.affineKrylovSearchSpace x0 k ∧
      IsMinOn problem.objective (problem.affineKrylovSearchSpace x0 k : Set E) (xs k)

/-- Every conjugate-gradient iterate lies in the corresponding affine Krylov search space. -/
theorem IsConjugateGradientSequence.mem_affineKrylovSearchSpace
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    xs k ∈ problem.affineKrylovSearchSpace x0 k :=
  (hcg k).1

/-- Every conjugate-gradient iterate minimizes the objective on the corresponding affine Krylov
search set. -/
theorem IsConjugateGradientSequence.isMinOn_affineKrylovSearchSpace
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    IsMinOn problem.objective
      (problem.affineKrylovSearchSpace x0 k : Set E)
      (xs k) :=
  (hcg k).2

section

variable {X : Type*}

/-- The full conjugate-gradient trajectory obtained by adjoining the initial point `x₀` to the
positive-indexed iterate sequence. -/
def conjugateGradientTrajectory (x0 : X) (xs : ℕ+ → X) : ℕ → X
  | 0 => x0
  | k + 1 => xs k.succPNat

/-- The full conjugate-gradient trajectory starts at the prescribed initial point. -/
@[simp] theorem conjugateGradientTrajectory_zero (x0 : X) (xs : ℕ+ → X) :
    conjugateGradientTrajectory x0 xs 0 = x0 :=
  rfl

/-- The full conjugate-gradient trajectory agrees with the positive-indexed iterate sequence at
successor indices. -/
@[simp] theorem conjugateGradientTrajectory_succ (x0 : X) (xs : ℕ+ → X) (k : ℕ) :
    conjugateGradientTrajectory x0 xs (k + 1) = xs k.succPNat :=
  rfl

end

/-! ### Lemma_1_9_4 (from Chap01) -/
open Filter
open scoped Gradient
open scoped Topology

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Lemma 1.9.4 lies in the quadratic/Krylov domain.

Sampled owner declarations in this domain:
* `LinearMap.krylovSubspace`, the ambient Krylov-space owner;
* `LinearMap.map_mem_krylovSubspace_succ`, the owner-side image-to-next-stage theorem;
* `problem.krylovSubspace x0 k`, the project-level owner for `𝓛ₖ`;
* `problem.krylovSubspace_eq_span_positiveIterates`, the canonical positive-iterate expansion;
* `problem.affineKrylovSearchSpace x0 k`, the affine owner for `x₀ + 𝓛ₖ`.

Best owner abstraction:
* the pair `problem.krylovSubspace x0 k` / `problem.affineKrylovSearchSpace x0 k`.

Primitive data:
* `problem : UnconstrainedQuadraticMinimizationProblem n`;
* the initial point `x0`;
* the stage `k : ℕ+`;
* a finite family `points : Fin k → E` together with the stagewise minimizing data on
  `x₀ + 𝓛ᵢ`;
* equivalently, the owner datum `IsConjugateGradientSequence problem x0 xs`.

Derived API:
* `problem.gradient_eq`;
* the owner-side bridge
  `gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace`;
* the owner-side orthogonality bridge
  `gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace`;
* the owner-side inclusion companion
  `span_gradients_le_krylovSubspace_of_mem_affineKrylovSearchSpace`;
* the minimizer-based bridge
  `krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers`;
* the source-facing owner theorem
  `IsConjugateGradientSequence.krylovSubspace_eq_span_gradients`.

Source/core/bridge triage:
* source-facing:
  `IsConjugateGradientSequence.krylovSubspace_eq_span_gradients`;
* core/canonical:
  `LinearMap.krylovSubspace`,
  `LinearMap.map_mem_krylovSubspace_succ`,
  `problem.krylovSubspace x0 k`,
  `problem.krylovSubspace_eq_span_positiveIterates`,
  `problem.affineKrylovSearchSpace x0 k`;
* bridge/view:
  the pointwise lemma `gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace`, the
  owner-side orthogonality bridge
  `gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace`, and the inclusion
  companion
  `span_gradients_le_krylovSubspace_of_mem_affineKrylovSearchSpace`, together with the explicit
  minimizing-data bridge
  `krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers`.
-/

namespace UnconstrainedQuadraticMinimizationProblem

/-- Helper for Lemma 1.9.4: a minimizer on an affine subspace has gradient orthogonal to every
vector in the direction of that affine subspace. -/
private theorem inner_gradient_eq_zero_of_mem_direction_of_affineSubspace_minimizer
    {f : E → ℝ} {x : E} {s : AffineSubspace ℝ E}
    (hf : DifferentiableAt ℝ f x) (hx : x ∈ s) (hmin : IsMinOn f (s : Set E) x)
    {v : E} (hv : v ∈ s.direction) :
    inner ℝ (∇ f x) v = 0 := by
  -- Move both `v` and `-v` into the tangent cone using affine-subspace feasibility along rays.
  have hv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction (s.direction.smul_mem t hv) hx
  have hv_pos :
      v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hv_eventually.frequently
  have hnegv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (-v) ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction
        (s.direction.smul_mem t (Submodule.neg_mem _ hv)) hx
  have hnegv_pos :
      -v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hnegv_eventually.frequently
  -- First-order optimality on the affine subspace kills the directional derivative.
  have hderiv :
      (fderiv ℝ f x : E →L[ℝ] ℝ) v = 0 := by
    exact
      hmin.localize.hasFDerivWithinAt_eq_zero
        hf.hasFDerivAt.hasFDerivWithinAt hv_pos hnegv_pos
  -- Convert the directional derivative back to the inner-product gradient formula.
  simpa [hf.hasGradientAt.fderiv_apply] using hderiv

private theorem span_range_eq_span_range_init_sup_span_last
    {m : ℕ} (xs : Fin (m + 1) → E) :
    Submodule.span ℝ (Set.range xs) =
      Submodule.span ℝ (Set.range (Fin.init xs)) ⊔ ℝ ∙ xs (Fin.last m) := by
  have hset : Set.range xs = insert (xs (Fin.last m)) (Set.range (Fin.init xs)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.lastCases ?_ ?_ i
      · simp
      · intro j
        right
        exact ⟨j, rfl⟩
    · intro hy
      rcases hy with rfl | ⟨j, rfl⟩
      · exact ⟨Fin.last m, rfl⟩
      · exact ⟨j.castSucc, rfl⟩
  rw [hset, Submodule.span_insert, sup_comm]

private theorem krylovSubspace_succ_eq_of_minimizer_mem_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 : E) (k : ℕ+)
    (hmin : problem.minimizer ∈ problem.affineKrylovSearchSpace x0 k) :
    problem.krylovSubspace x0 (k + 1) = problem.krylovSubspace x0 k := by
  let A := problem.A.toEuclideanLin
  let seed := ∇ problem.objective x0
  have hx0min : x0 - problem.minimizer ∈ problem.krylovSubspace x0 k := by
    have hsub : problem.minimizer - x0 ∈ problem.krylovSubspace x0 k := by
      simpa using hmin
    simpa using Submodule.neg_mem (problem.krylovSubspace x0 k) hsub
  have hsucc_le_map :
      problem.krylovSubspace x0 (k + 1) ≤ Submodule.map A (problem.krylovSubspace x0 k) := by
    simpa [UnconstrainedQuadraticMinimizationProblem.krylovSubspace, A, seed] using
      LinearMap.krylovSubspace_succ_le_map_of_preimage_mem A k seed (x0 - problem.minimizer)
        hx0min (by simpa [A, seed] using (problem.gradient_eq x0).symm)
  have hAinj : Function.Injective A := by
    intro u v huv
    have hcoords : problem.A.mulVec u.ofLp = problem.A.mulVec v.ofLp := by
      simpa only [A, Matrix.ofLp_toLpLin] using congrArg (fun z : E ↦ z.ofLp) huv
    have hmulVec_inj : Function.Injective problem.A.mulVec :=
      (Matrix.mulVec_injective_iff_isUnit).2 problem.posDef.isUnit
    have huv' : u.ofLp = v.ofLp := hmulVec_inj hcoords
    exact congrArg (WithLp.toLp 2) huv'
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo A hAinj
  have hmap_finrank :
      Module.finrank ℝ ↥(Submodule.map A (problem.krylovSubspace x0 k)) =
        Module.finrank ℝ ↥(problem.krylovSubspace x0 k) := by
    have h := LinearEquiv.finrank_map_eq e (problem.krylovSubspace x0 k)
    simpa [e] using h
  have hL_le_map :
      problem.krylovSubspace x0 k ≤ Submodule.map A (problem.krylovSubspace x0 k) := by
    exact le_trans
      (problem.krylovSubspace_mono x0
        (show (k : ℕ) ≤ ((k + 1 : ℕ+) : ℕ) by exact Nat.le_succ _))
      hsucc_le_map
  have hL_eq_map :
      problem.krylovSubspace x0 k = Submodule.map A (problem.krylovSubspace x0 k) := by
    exact Submodule.eq_of_le_of_finrank_eq hL_le_map hmap_finrank.symm
  apply le_antisymm
  · rw [← hL_eq_map] at hsucc_le_map
    exact hsucc_le_map
  · exact problem.krylovSubspace_mono x0
      (show (k : ℕ) ≤ ((k + 1 : ℕ+) : ℕ) by exact Nat.le_succ _)

/-- If `x` minimizes the quadratic objective on `x₀ + 𝓛ₖ`, then the gradient at `x` is orthogonal
to `𝓛ₖ`. -/
theorem gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 x : E) (k : ℕ+)
    (hx : x ∈ problem.affineKrylovSearchSpace x0 k)
    (hmin : IsMinOn problem.objective (problem.affineKrylovSearchSpace x0 k : Set E) x) :
    ∇ problem.objective x ∈ (𝓛(problem, x0, k))ᗮ := by
  -- The quadratic objective is differentiable, so first-order optimality on the affine space
  -- turns every search direction into an orthogonality relation with the gradient.
  have hdiff : DifferentiableAt ℝ problem.objective x := by
    have hsymm : problem.A.IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
    simpa [UnconstrainedQuadraticMinimizationProblem.objective] using
      (symmetric_quadratic_contDiff_and_gradient_lipschitz
        problem.α problem.a problem.A hsymm).1.differentiable_one x
  rw [Submodule.mem_orthogonal']
  intro v hv
  exact
    inner_gradient_eq_zero_of_mem_direction_of_affineSubspace_minimizer
      hdiff hx hmin (by
        simpa [UnconstrainedQuadraticMinimizationProblem.affineKrylovSearchSpace] using hv)

/-- If `x ∈ x0 + 𝓛ₖ`, then the gradient at `x` lies in the next Krylov stage `𝓛ₖ₊₁`. -/
-- Proof sketch: write `x = x0 + v` with `v ∈ 𝓛ₖ`. The gradient formula `problem.gradient_eq`
-- identifies `∇ problem.objective x` with the seed `A (x0 - x*)` plus the image `A v`. The first
-- term lies in the first Krylov stage, and the second term is sent into the next stage by the
-- owner-side theorem `LinearMap.map_mem_krylovSubspace_succ`.
theorem gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 x : E) (k : ℕ+)
    (hx : x ∈ problem.affineKrylovSearchSpace x0 k) :
    ∇ problem.objective x ∈ 𝓛(problem, x0, k + 1) := by
  let A := problem.A.toEuclideanLin
  let seed := ∇ problem.objective x0
  have hx' : x - x0 ∈ 𝓛(problem, x0, k) := by
    simpa using hx
  have hxA : x - x0 ∈ A.krylovSubspace k seed := by
    simpa [krylovSubspace, A, seed] using hx'
  have hseed : seed ∈ A.krylovSubspace (k + 1) seed := by
    rw [LinearMap.krylovSubspace]
    exact Submodule.subset_span ⟨0, by simp⟩
  have hmap : A (x - x0) ∈ A.krylovSubspace (k + 1) seed := by
    simpa [A, seed] using LinearMap.map_mem_krylovSubspace_succ A seed hxA
  rw [problem.gradient_eq]
  have hsplit :
      A (x - problem.minimizer) = seed + A (x - x0) := by
    calc
      A (x - problem.minimizer)
          = A ((x0 - problem.minimizer) + (x - x0)) := by
              congr 1
              abel
      _ = A (x0 - problem.minimizer) + A (x - x0) := by simp
      _ = seed + A (x - x0) := by
            rw [show A (x0 - problem.minimizer) = seed by
              simpa [A, seed] using (problem.gradient_eq x0).symm]
  rw [hsplit]
  change seed + A (x - x0) ∈ A.krylovSubspace (k + 1) seed
  exact Submodule.add_mem _ hseed hmap

/-- Under the affine-membership hypotheses, the span of the gradients at
`x₀, x₁, …, xₖ₋₁` lies in the `k`th Krylov space `𝓛ₖ`. This owner-side inclusion is the
companion bridge used by later chapter arguments. -/
-- Proof sketch: the base point contributes `∇ problem.objective x0`, which is the first Krylov
-- generator. For `i > 0`, the hypothesis `xᵢ ∈ x₀ + 𝓛ᵢ` and the pointwise bridge above show that
-- `∇ problem.objective (xᵢ)` lies in `𝓛ᵢ₊₁`; owner-side monotonicity
-- `problem.krylovSubspace_mono x0` then moves this into `𝓛ₖ`, so every spanning gradient belongs
-- to `𝓛ₖ`.
theorem span_gradients_le_krylovSubspace_of_mem_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 : E)
    (k : ℕ+) (points : Fin k → E)
    (hx0 : points 0 = x0)
    (hpoints :
      ∀ i : Fin k, ∀ hi : 0 < i,
        points i ∈ problem.affineKrylovSearchSpace x0 ⟨i, hi⟩) :
    Submodule.span ℝ
      (Set.range fun i : Fin k ↦
        ∇ problem.objective (points i)) ≤
      𝓛(problem, x0, k) := by
  let A := problem.A.toEuclideanLin
  let seed := ∇ problem.objective x0
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rcases eq_or_ne i 0 with rfl | hi
  · have hseed : seed ∈ A.krylovSubspace k seed := by
      rw [LinearMap.krylovSubspace]
      exact Submodule.subset_span ⟨0, by simp⟩
    change ∇ problem.objective (points 0) ∈ A.krylovSubspace k seed
    rw [hx0]
    simpa [seed] using hseed
  · have hi0 : 0 < i := Fin.pos_iff_ne_zero.2 hi
    have hgrad :
        ∇ problem.objective (points i) ∈ 𝓛(problem, x0, Nat.succPNat i) := by
      simpa using
        gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace
          problem x0 (points i) ⟨i, hi0⟩ (hpoints i hi0)
    have hmono :
        𝓛(problem, x0, Nat.succPNat i) ≤ 𝓛(problem, x0, k) := by
      exact problem.krylovSubspace_mono x0 (Nat.succ_le_of_lt i.is_lt)
    exact hmono hgrad

/-- Bridge form of Lemma 1.9.4: if each `xᵢ` with `0 < i < k` lies in and minimizes the quadratic
objective on the affine Krylov search space `x₀ + 𝓛ᵢ`, then `𝓛ₖ` is exactly the span of the
gradients at `x₀, x₁, …, xₖ₋₁`. This is the explicit minimizing-data version of the conjugate-
gradient statement. -/
theorem
    krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 : E)
    (k : ℕ+) (points : Fin k → E)
    (hx0 : points 0 = x0)
    (hpoints :
      ∀ i : Fin k, ∀ hi : 0 < i,
        points i ∈ problem.affineKrylovSearchSpace x0 ⟨i, hi⟩)
    (hmins :
      ∀ i : Fin k, ∀ hi : 0 < i,
        IsMinOn problem.objective
          (problem.affineKrylovSearchSpace x0 ⟨i, hi⟩ : Set E)
          (points i)) :
    𝓛(problem, x0, k) =
      Submodule.span ℝ
        (Set.range fun i : Fin k ↦
          ∇ problem.objective (points i)) := by
  induction k using PNat.recOn with
  | one =>
      have hleft :
          Set.range (fun i : Fin 1 ↦
            (problem.A.toEuclideanLin ^ (i : ℕ)) (∇ problem.objective x0)) =
            {∇ problem.objective x0} := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          have hi : i = 0 := Fin.eq_zero i
          subst hi
          simp
        · rintro rfl
          exact ⟨0, by simp⟩
      have hrange :
          Set.range (fun i : Fin 1 ↦ ∇ problem.objective (points i)) =
            {∇ problem.objective x0} := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          have hi : i = 0 := Fin.eq_zero i
          subst hi
          simpa using congrArg (fun z ↦ ∇ problem.objective z) hx0
        · rintro rfl
          exact ⟨0, by simpa using congrArg (fun z ↦ ∇ problem.objective z) hx0⟩
      rw [UnconstrainedQuadraticMinimizationProblem.krylovSubspace, LinearMap.krylovSubspace]
      simp [hrange]
  | succ k hk =>
      have hprefix :
          𝓛(problem, x0, k) =
            Submodule.span ℝ
              (Set.range fun i : Fin k ↦
                ∇ problem.objective ((Fin.init points) i)) := by
        refine hk (Fin.init points) ?_ ?_ ?_
        · simpa using hx0
        · intro i hi
          simpa using hpoints i.castSucc hi
        · intro i hi
          simpa using hmins i.castSucc hi
      let glast := ∇ problem.objective (points (Fin.last k))
      have hspan :
          Submodule.span ℝ
            (Set.range fun i : Fin (k + 1) ↦
              ∇ problem.objective (points i)) =
              Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) ⊔
                ℝ ∙ glast := by
        simpa [glast, Fin.init] using
          span_range_eq_span_range_init_sup_span_last
            (fun i : Fin ((k + 1 : ℕ+) : ℕ) ↦
              ∇ problem.objective (points i))
      have hlast_pos : 0 < Fin.last k := Fin.pos_iff_ne_zero.mpr (by simp)
      have hlast_mem :
          points (Fin.last k) ∈ problem.affineKrylovSearchSpace x0 k := by
        simpa using hpoints (Fin.last k) hlast_pos
      have hlast_min :
          IsMinOn problem.objective
            (problem.affineKrylovSearchSpace x0 k : Set E)
            (points (Fin.last k)) := by
        simpa using hmins (Fin.last k) hlast_pos
      by_cases hzero : glast = 0
      · have hlast_eq_min : points (Fin.last k) = problem.minimizer := by
          exact problem.eq_minimizer_of_gradient_eq_zero hzero
        have hmin_mem :
            problem.minimizer ∈ problem.affineKrylovSearchSpace x0 k := by
          simpa [hlast_eq_min] using hlast_mem
        calc
          𝓛(problem, x0, k + 1) = 𝓛(problem, x0, k) := by
                  exact
                    krylovSubspace_succ_eq_of_minimizer_mem_affineKrylovSearchSpace
                      problem x0 k hmin_mem
          _ = Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) := hprefix
          _ = Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) ⊔
                ℝ ∙ glast := by simp [hzero]
          _ = Submodule.span ℝ
                (Set.range fun i : Fin (k + 1) ↦
                  ∇ problem.objective (points i)) := hspan.symm
      · have hgrad_mem :
            glast ∈ 𝓛(problem, x0, k + 1) := by
          simpa [glast] using
            gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace
              problem x0 (points (Fin.last k)) k hlast_mem
        have hgrad_orth :
            glast ∈ (𝓛(problem, x0, k))ᗮ := by
          simpa [glast] using
            gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace
              problem x0 (points (Fin.last k)) k hlast_mem hlast_min
        have hgrad_not_mem : glast ∉ 𝓛(problem, x0, k) := by
          intro hgk
          have hself : inner ℝ glast glast = 0 :=
            (Submodule.mem_orthogonal' _ _).1 hgrad_orth glast hgk
          exact hzero (inner_self_eq_zero.mp hself)
        have hsup_le :
            𝓛(problem, x0, k) ⊔ ℝ ∙ glast ≤ 𝓛(problem, x0, k + 1) := by
          refine sup_le ?_ ?_
          · exact problem.krylovSubspace_mono x0
              (show (k : ℕ) ≤ (((k + 1 : ℕ+) : ℕ)) by exact Nat.le_succ _)
          · exact (Submodule.span_singleton_le_iff_mem _ _).2 hgrad_mem
        have hfin_le :
            Module.finrank ℝ ↥(𝓛(problem, x0, k + 1)) ≤
              Module.finrank ℝ ↥(𝓛(problem, x0, k)) + 1 := by
          simpa [UnconstrainedQuadraticMinimizationProblem.krylovSubspace] using
            LinearMap.finrank_krylovSubspace_succ_le
              problem.A.toEuclideanLin k (∇ problem.objective x0)
        have hsup_finrank :
            Module.finrank ℝ ↥(𝓛(problem, x0, k) ⊔ ℝ ∙ glast) =
              Module.finrank ℝ ↥(𝓛(problem, x0, k)) + 1 := by
          exact Submodule.finrank_sup_span_singleton hgrad_not_mem
        have hfin_eq :
            Module.finrank ℝ ↥(𝓛(problem, x0, k) ⊔ ℝ ∙ glast) =
              Module.finrank ℝ ↥(𝓛(problem, x0, k + 1)) := by
          apply le_antisymm
          · exact Submodule.finrank_mono hsup_le
          · calc
              Module.finrank ℝ ↥(𝓛(problem, x0, k + 1))
                  ≤ Module.finrank ℝ ↥(𝓛(problem, x0, k)) + 1 := hfin_le
              _ = Module.finrank ℝ ↥(𝓛(problem, x0, k) ⊔ ℝ ∙ glast) := by
                    rw [hsup_finrank]
        have hsup_eq :
            𝓛(problem, x0, k) ⊔ ℝ ∙ glast =
              𝓛(problem, x0, k + 1) := by
          exact Submodule.eq_of_le_of_finrank_eq hsup_le hfin_eq
        calc
          𝓛(problem, x0, k + 1) = 𝓛(problem, x0, k) ⊔ ℝ ∙ glast := hsup_eq.symm
          _ = Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) ⊔
                ℝ ∙ glast := by rw [hprefix]
          _ = Submodule.span ℝ
                (Set.range fun i : Fin (k + 1) ↦
                  ∇ problem.objective (points i)) := hspan.symm

/-- Lemma 1.9.4: along a conjugate-gradient sequence, the `k`th Krylov space `𝓛ₖ` is exactly the
span of the gradients at the first `k` trajectory points `x₀, x₁, …, xₖ₋₁`. Equivalently, the
nonzero gradients/residuals generated by the minimizing Krylov process span `𝓛ₖ`. -/
theorem IsConjugateGradientSequence.krylovSubspace_eq_span_gradients
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    𝓛(problem, x0, k) =
      Submodule.span ℝ
        (Set.range fun i : Fin k ↦
          ∇ problem.objective (conjugateGradientTrajectory x0 xs i)) := by
  refine
    krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers problem
      x0 k (fun i : Fin k ↦ conjugateGradientTrajectory x0 xs i) ?_ ?_ ?_
  · simp
  · intro i hi
    rcases i with ⟨i, hik⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    simpa [conjugateGradientTrajectory] using hcg.mem_affineKrylovSearchSpace j.succPNat
  · intro i hi
    rcases i with ⟨i, hik⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    simpa [conjugateGradientTrajectory] using hcg.isMinOn_affineKrylovSearchSpace j.succPNat

end UnconstrainedQuadraticMinimizationProblem

/-! ### Lemma_1_9_5 (from Chap01) -/
open Filter
open scoped Topology
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- 
Lemma 1.9.5 lies in first-order optimality over affine search spaces in a real Hilbert space.

Sampled owner declarations in this domain:
* `posTangentConeAt` and `mem_posTangentConeAt_of_frequently_mem`;
* `AffineSubspace.vadd_mem_of_mem_direction`;
* `gradientMethod`, whose chapter owner abstraction already lives on a real inner-product space;
* `gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet`, which exposes the same first-order
  optimality pattern with only pointwise differentiability;
* `IsLocalMinOn.hasFDerivWithinAt_eq_zero`;
* `AffineSubspace.mk'` and `AffineSubspace.direction_mk'`.

Best owner abstraction:
* an affine subspace `s : AffineSubspace ℝ E` together with its direction `s.direction`,
  viewed through the canonical tangent-cone/Fermat optimality API.

Primitive data:
* the objective `f` and the trajectory `x`;
* differentiability of `f` at the iterates where the displayed gradients occur;
* for each positive stage `k`, the feasibility/minimizer datum on the affine search space.

Derived API:
* the owner-side fact that `∇ f (x k)` is orthogonal to every vector in the direction of the
  stage-`k` affine search space;
* the source-facing pairwise orthogonality of distinct trajectory gradients.

Source/core/bridge triage:
* source-facing: pairwise orthogonality of distinct gradients along the trajectory;
* core/canonical: first-order optimality on an affine subspace `s` via `posTangentConeAt`, and
  the owner theorem for a family `searchSpace : ℕ → AffineSubspace ℝ E`;
* bridge/view: specialization of the owner statement to the textbook search space
  `x₀ + span {∇ f(x₀), …, ∇ f(xₖ₋₁)}`.
-/

/-- If `x` minimizes `f` on an affine subspace `s`, then the gradient at `x` is orthogonal to
every vector in the direction of `s`. -/
theorem inner_gradient_eq_zero_of_mem_direction_of_isMinOn_affineSubspace
    {f : E → ℝ} {x : E} {s : AffineSubspace ℝ E}
    (hf : DifferentiableAt ℝ f x) (hx : x ∈ s) (hmin : IsMinOn f (s : Set E) x)
    {v : E} (hv : v ∈ s.direction) :
    inner ℝ (∇ f x) v = 0 := by
  have hv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction (s.direction.smul_mem t hv) hx
  have hv_pos :
      v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hv_eventually.frequently
  have hnegv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (-v) ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction
        (s.direction.smul_mem t (Submodule.neg_mem _ hv)) hx
  have hnegv_pos :
      -v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hnegv_eventually.frequently
  have hderiv :
      (fderiv ℝ f x : E →L[ℝ] ℝ) v = 0 := by
    exact
      hmin.localize.hasFDerivWithinAt_eq_zero
        hf.hasFDerivAt.hasFDerivWithinAt hv_pos hnegv_pos
  simpa [hf.hasGradientAt.fderiv_apply] using hderiv

/-- If each positive stage `x k` minimizes `f` on an affine search space `searchSpace k`, and
every earlier gradient lies in the direction of every later search space, then gradients at
distinct stages are orthogonal. -/
-- Proof sketch: for `a < b`, apply first-order optimality on the stage-`b` affine subspace to the
-- direction vector `∇ f (x a)`. The reverse order is the same identity after commuting the real
-- inner product.
theorem gradients_pairwise_orthogonal_of_isMinOn_affineSearchSpaces
    (f : E → ℝ) (x : ℕ → E) (searchSpace : ℕ → AffineSubspace ℝ E)
    (hdiff : ∀ k : ℕ, DifferentiableAt ℝ f (x k))
    (hdir : ∀ {a b : ℕ}, a < b → ∇ f (x a) ∈ (searchSpace b).direction)
    (hmin : ∀ k : ℕ, 0 < k →
      x k ∈ searchSpace k ∧ IsMinOn f (searchSpace k : Set E) (x k))
    {k i : ℕ} (hki : k ≠ i) :
    inner ℝ (∇ f (x k)) (∇ f (x i)) = 0 := by
  have hlt : ∀ {a b : ℕ}, a < b → inner ℝ (∇ f (x b)) (∇ f (x a)) = 0 := by
    intro a b hab
    have hbmin := hmin b (Nat.zero_lt_of_lt hab)
    exact
      inner_gradient_eq_zero_of_mem_direction_of_isMinOn_affineSubspace
        (hdiff b) hbmin.1 hbmin.2 (hdir hab)
  rcases lt_or_gt_of_ne hki with hki | hki
  · simpa [real_inner_comm] using hlt hki
  · exact hlt hki

/-- Lemma 1.9.5: if each iterate `xₖ` with `k > 0` lies in and minimizes `f` on the affine
subspace `x₀ + span {∇ f(x₀), …, ∇ f(xₖ₋₁)}`, then the gradients at distinct iterates are
orthogonal. -/
-- Proof sketch: specialize
-- `gradients_pairwise_orthogonal_of_isMinOn_affineSearchSpaces` to the textbook search space
-- `x₀ + span {∇ f(x₀), …, ∇ f(xₖ₋₁)}`, where membership of earlier gradients in the later search
-- directions is the tautological `Submodule.subset_span` fact.
theorem gradients_pairwise_orthogonal_of_isMinOn_affineSpan_gradients
    (f : E → ℝ) (x : ℕ → E)
    (hdiff : ∀ k : ℕ, DifferentiableAt ℝ f (x k))
    (hmin : ∀ k : ℕ, 0 < k →
      let searchSpace : AffineSubspace ℝ E :=
        AffineSubspace.mk' (x 0)
          (Submodule.span ℝ (Set.range fun j : Fin k ↦ ∇ f (x j)))
      x k ∈ searchSpace ∧ IsMinOn f (searchSpace : Set E) (x k))
    {k i : ℕ} (hki : k ≠ i) :
    inner ℝ (∇ f (x k)) (∇ f (x i)) = 0 := by
  let searchSpace : ℕ → AffineSubspace ℝ E := fun k ↦
      AffineSubspace.mk' (x 0)
        (Submodule.span ℝ (Set.range fun j : Fin k ↦ ∇ f (x j)))
  have hdir : ∀ {a b : ℕ}, a < b → ∇ f (x a) ∈ (searchSpace b).direction := by
    intro a b hab
    simpa [searchSpace] using
      (Submodule.subset_span ⟨⟨a, hab⟩, rfl⟩ :
        ∇ f (x a) ∈ Submodule.span ℝ (Set.range fun j : Fin b ↦ ∇ f (x j)))
  have hmin' : ∀ k : ℕ, 0 < k →
      x k ∈ searchSpace k ∧ IsMinOn f (searchSpace k : Set E) (x k) := by
    intro k hk
    simpa [searchSpace] using hmin k hk
  exact
    gradients_pairwise_orthogonal_of_isMinOn_affineSearchSpaces
      f x searchSpace hdiff hdir hmin' hki

/-! ### Corollary_1_9_6 (from Chap01) -/
open scoped Gradient
open UnconstrainedQuadraticMinimizationProblem.IsConjugateGradientSequence

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace IsConjugateGradientSequence

/-
Corollary 1.9.6 is a source-facing finite-dimensional consequence of the owner-side conjugate-
gradient datum `IsConjugateGradientSequence problem x0 xs`.

* primitive data: the quadratic problem, the initial point, the positive-indexed iterate sequence,
  and the owner hypothesis `hcg`;
* derived API: the full trajectory `conjugateGradientTrajectory x0 xs`, the owner-side span theorem
  `krylovSubspace_eq_span_gradients hcg`, the affine-span orthogonality theorem
  `gradients_pairwise_orthogonal_of_isMinOn_affineSpan_gradients`, and the quadratic objective
  `problem.objective`;
* finite-dimensional owner step: the mathlib facts
  `linearIndependent_of_ne_zero_of_inner_eq_zero` and
  `LinearIndependent.fintype_card_le_finrank`.

Accordingly, the corollary is stated directly as an owner-side consequence of `hcg`, not as a
parallel free-standing wrapper around the same data.
-/

/-- Corollary 1.9.6: a conjugate-gradient trajectory for problem `(1.3.2)` is finite in the sense
that some iterate among the first `n + 1` points of the full trajectory has vanishing gradient. -/
-- Proof sketch: rewrite each affine Krylov search space as the affine span of the earlier
-- trajectory gradients, then feed the resulting stagewise minimizer data into Lemma 1.9.5.
-- This makes the first `n + 1` trajectory gradients pairwise orthogonal, so finite-dimensional
-- linear algebra in `ℝⁿ` forces one of them to be zero.
theorem zero_gradient_within_dimension
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∃ k ≤ n,
      ∇ problem.objective (conjugateGradientTrajectory x0 xs k) = 0 := by
  let trajectory : ℕ → E := conjugateGradientTrajectory x0 xs
  let gradient : ℕ → E := fun k ↦ ∇ problem.objective (trajectory k)
  -- The quadratic objective is differentiable at every trajectory point.
  have hdiff : ∀ k : ℕ, DifferentiableAt ℝ problem.objective (trajectory k) := by
    intro k
    have hsymm : problem.A.IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
    simpa [UnconstrainedQuadraticMinimizationProblem.objective] using
      (symmetric_quadratic_contDiff_and_gradient_lipschitz
        problem.α problem.a problem.A hsymm).1.differentiable_one (trajectory k)
  -- Rewrite each positive-stage affine Krylov search space into the affine span format required
  -- by Lemma 1.9.5.
  have hmin :
      ∀ k : ℕ, 0 < k →
        let searchSpace : AffineSubspace ℝ E :=
          AffineSubspace.mk' (trajectory 0)
            (Submodule.span ℝ (Set.range fun j : Fin k ↦ gradient j))
        trajectory k ∈ searchSpace ∧
          IsMinOn problem.objective (searchSpace : Set E) (trajectory k) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    let stage : ℕ+ := j.succPNat
    have hmem :
        trajectory (j + 1) ∈ problem.affineKrylovSearchSpace x0 stage := by
      simpa [trajectory, conjugateGradientTrajectory] using hcg.mem_affineKrylovSearchSpace stage
    have hmin_stage :
        IsMinOn problem.objective (problem.affineKrylovSearchSpace x0 stage : Set E)
          (trajectory (j + 1)) := by
      simpa [trajectory, conjugateGradientTrajectory] using
        hcg.isMinOn_affineKrylovSearchSpace stage
    simpa [stage, trajectory, gradient,
      UnconstrainedQuadraticMinimizationProblem.affineKrylovSearchSpace,
      krylovSubspace_eq_span_gradients hcg stage] using
      And.intro hmem hmin_stage
  -- Lemma 1.9.5 makes distinct trajectory gradients orthogonal, and hence every prefix is a
  -- pairwise orthogonal finite family.
  have horth :
      Pairwise fun i j : Fin (n + 1) ↦ inner ℝ (gradient i) (gradient j) = 0 := by
    intro i j hij
    exact
      gradients_pairwise_orthogonal_of_isMinOn_affineSpan_gradients
        problem.objective trajectory hdiff hmin (by
          intro h
          exact hij (Fin.ext h))
  -- If all of these gradients were nonzero, they would be linearly independent, contradicting the
  -- ambient dimension bound `finrank ℝ E = n`.
  by_contra hzero
  have hz : ∀ i : Fin (n + 1), gradient i ≠ 0 := by
    intro i hi
    exact hzero ⟨i, Nat.le_of_lt_succ i.is_lt, hi⟩
  let gradients : Fin (n + 1) → E := fun i ↦ gradient i
  have hlin : LinearIndependent ℝ gradients :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hz horth
  have hcard : n + 1 ≤ n := by
    simpa using hlin.fintype_card_le_finrank
  exact (Nat.not_succ_le_self n) hcard

end IsConjugateGradientSequence

/-! ### Corollary_1_9_7 (from Chap01) -/
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- 
Corollary 1.9.7 is a source-facing consequence of the owner-side conjugate-gradient datum
`IsConjugateGradientSequence problem x0 xs`.

* primitive data: the quadratic problem `problem`, the initial point `x0`, the positive-indexed
  iterate sequence `xs`, the owner hypothesis `hcg`, and the stage `k`;
* owner abstraction: the canonical Krylov space `problem.krylovSubspace x0 k`;
* derived API: the owner-side orthogonality bridge
  `problem.gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace`.

Accordingly, the corollary is stated directly as an owner-side theorem on
`IsConjugateGradientSequence`, not as a parallel free-standing wrapper around the same data.
-/

/-- Corollary 1.9.7: in the conjugate-gradient method for an unconstrained quadratic problem, the
gradient at the `k`th iterate lies in the orthogonal complement of the `k`th Krylov subspace
`𝓛ₖ`. -/
-- Proof sketch: `hcg.isMinOn_affineKrylovSearchSpace k` says that `xs k` minimizes the quadratic
-- objective on the owner affine space `x₀ + 𝓛ₖ`. First-order optimality on an affine subspace
-- therefore makes `∇ problem.objective (xs k)` orthogonal to every vector in the direction of
-- that affine space. Since the direction of `problem.affineKrylovSearchSpace x0 k` is exactly
-- `problem.krylovSubspace x0 k`, the gradient lies in `𝓛ₖᗮ`.
theorem IsConjugateGradientSequence.gradient_mem_krylovSubspace_orthogonal
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    ∇ problem.objective (xs k) ∈ (𝓛(problem, x0, k))ᗮ := by
  -- The conjugate-gradient iterate lies in the affine Krylov search space at stage `k`.
  have hx_mem : xs k ∈ problem.affineKrylovSearchSpace x0 k := by
    simpa using hcg.mem_affineKrylovSearchSpace k
  -- The same iterate minimizes the quadratic objective on that affine search space.
  have hx_min :
      IsMinOn problem.objective (problem.affineKrylovSearchSpace x0 k : Set E) (xs k) := by
    simpa using hcg.isMinOn_affineKrylovSearchSpace k
  -- First-order optimality on the affine Krylov space yields orthogonality to its direction space.
  simpa using
    problem.gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace
      x0 (xs k) k
      hx_mem
      hx_min
