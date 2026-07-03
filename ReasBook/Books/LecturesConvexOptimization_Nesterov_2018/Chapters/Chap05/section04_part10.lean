import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_4_8_17 (from Chap05) -/
open scoped BigOperators
open scoped EuclideanOrthant
open EuclideanSpace (positiveOrthant)

noncomputable section

/-
Definition 5.4.8.17 lies in the Chapter 5 geometric-programming / positive-orthant domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the project owner for the strict positive orthant `ℝⁿ₊₊`;
* `LagrangianProblem` and `LagrangianProblem.mem_feasibleSet_iff` from
  `Chap01/Definition_1_10_2`, the canonical owner for an objective together with `≤ 0`
  constraints;
* `SeparableOptimizationProblem.toLagrangianProblem` and
  `SeparableOptimizationProblem.feasibleSet` from `Chap05/Definition_5_4_8_1`, the local Chapter 5
  source-facing pattern of keeping primitive source data while routing feasibility through the
  Chapter 1 owner.

Best owner abstraction:
* source-facing: `GeometricOptimizationProblem n m`, whose primitive data are the block sizes,
  positive coefficients, and exponent vectors defining the posynomials;
* core/canonical: `LagrangianProblem (ℝ₊₊^n) m`;
* bridge/view: `qFunction`, `objective`, `constraintFunction`, and `toLagrangianProblem`.

Primitive data:
* `blockSize`;
* `coefficient`;
* `exponent`.

Derived API:
* the posynomials `qFunction`;
* the objective `q₀` and the constraint family `qᵢ`, `i = 1, ..., m`;
* the canonical Chapter 1 bridge `toLagrangianProblem`;
* the feasible-set rewrite `mem_feasibleSet_iff`.

The previous version duplicated both the strict-orthant owner and the feasible-set owner pattern.
This refinement keeps the source-facing geometric-program data, reuses `ℝ₊₊^n` as the domain,
and derives feasibility through the canonical `LagrangianProblem` bridge.
-/

/-- Definition 5.4.8.17: a geometric optimization problem on the strict positive orthant
`\mathbb{R}^n_{++}` is specified by block sizes `m₀, …, mₘ`, positive coefficients `αᵢⱼ`,
and exponent vectors `σᵢⱼ ∈ ℝⁿ`, yielding the posynomials
`qᵢ(x) = \sum_{j=1}^{mᵢ} αᵢⱼ \prod_{k=1}^n (x^(k))^(σᵢⱼ^(k))`; the problem is to minimize
`q₀(x)` subject to the constraints `qᵢ(x) ≤ 1` for `i = 1, …, m`. -/
structure GeometricOptimizationProblem (n m : ℕ) where
  /-- The number `mᵢ` of monomial terms in the posynomial `qᵢ`. -/
  blockSize : Fin (m + 1) → ℕ
  /-- The strictly positive coefficients `αᵢⱼ` multiplying the monomial terms. -/
  coefficient (i : Fin (m + 1)) (j : Fin (blockSize i)) : Set.Ioi (0 : ℝ)
  /-- The exponent vectors `σᵢⱼ ∈ ℝⁿ` of the monomial terms. -/
  exponent (i : Fin (m + 1)) (j : Fin (blockSize i)) (k : Fin n) : ℝ

namespace GeometricOptimizationProblem

variable {n m : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => ℝ₊₊^n

/-- The `i`-th posynomial `qᵢ` of a geometric optimization problem, defined on the strict positive
orthant `\mathbb{R}^n_{++}`. -/
def qFunction (problem : GeometricOptimizationProblem n m) (i : Fin (m + 1)) :
    Xₙ → ℝ :=
  fun x ↦
    ∑ j : Fin (problem.blockSize i), (problem.coefficient i j : ℝ) *
      ∏ k : Fin n, Real.rpow ((x : Eₙ) k) (problem.exponent i j k)

/-- The objective posynomial `q₀` of a geometric optimization problem. -/
abbrev objective (problem : GeometricOptimizationProblem n m) : Xₙ → ℝ :=
  problem.qFunction 0

/-- The `i`-th inequality-constraint posynomial `q_{i+1}`. -/
abbrev constraintFunction (problem : GeometricOptimizationProblem n m) (i : Fin m) :
    Xₙ → ℝ :=
  problem.qFunction i.succ

def toLagrangianProblem (problem : GeometricOptimizationProblem n m) : LagrangianProblem Xₙ m where
  objective := problem.objective
  constraints := fun i x ↦ problem.constraintFunction i x - 1

/-- A geometric optimization problem coerces to its canonical Chapter 1 Lagrangian owner. -/
instance : Coe (GeometricOptimizationProblem n m) (LagrangianProblem Xₙ m) where
  coe := toLagrangianProblem

/-- A geometric optimization problem can be used as its objective posynomial `q₀` on the strict
positive orthant. -/
instance : CoeFun (GeometricOptimizationProblem n m) (fun _ ↦ Xₙ → ℝ) where
  coe problem := problem.objective

/-- The Chapter 1 Lagrangian owner evaluates to the source-facing objective `q₀`. -/
@[simp] theorem toLagrangianProblem_apply
    (problem : GeometricOptimizationProblem n m) (x : Xₙ) :
    problem.toLagrangianProblem x = problem.objective x :=
  rfl

/-- Evaluating a geometric optimization problem returns the source-facing objective `q₀`. -/
@[simp] theorem coe_apply
    (problem : GeometricOptimizationProblem n m) (x : Xₙ) :
    problem x = problem.objective x :=
  rfl

@[simp] theorem toLagrangianProblem_constraints_apply
    (problem : GeometricOptimizationProblem n m) (i : Fin m) (x : Xₙ) :
    (problem : LagrangianProblem Xₙ m).constraints i x =
      problem.constraintFunction i x - 1 :=
  rfl

/-- The feasible set of a geometric optimization problem consists of the strictly positive vectors
`x` satisfying `qᵢ(x) ≤ 1` for every constraint index `i = 1, …, m`. -/
def feasibleSet (problem : GeometricOptimizationProblem n m) : Set Xₙ :=
  problem.toLagrangianProblem.feasibleSet

/-- Expanding `qFunction` recovers the defining posynomial formula
`qᵢ(x) = \sum_j αᵢⱼ \prod_k (x^(k))^(σᵢⱼ^(k))`. -/
theorem qFunction_apply
    (problem : GeometricOptimizationProblem n m) (i : Fin (m + 1)) (x : Xₙ) :
    problem.qFunction i x =
      ∑ j : Fin (problem.blockSize i), (problem.coefficient i j : ℝ) *
        ∏ k : Fin n, Real.rpow ((x : Eₙ) k) (problem.exponent i j k) :=
  rfl

/-- Membership in the feasible set is equivalent to satisfying all geometric-program inequality
constraints `qᵢ(x) ≤ 1` for `i = 1, …, m`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : GeometricOptimizationProblem n m) (x : Xₙ) :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraintFunction i x ≤ (1 : ℝ) := by
  rw [feasibleSet]
  constructor
  · intro hx i
    exact sub_nonpos.mp ((problem.toLagrangianProblem.mem_feasibleSet_iff).1 hx i)
  · intro hx
    exact (problem.toLagrangianProblem.mem_feasibleSet_iff).2
      (fun i ↦ sub_nonpos.mpr (hx i))

end GeometricOptimizationProblem

end

/-! ### Definition_5_4_8_18 (from Chap05) -/
open scoped EuclideanOrthant

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-
Definition 5.4.8.18 lies in the Chapter 5 geometric-programming / positive-orthant
logarithmic-coordinate domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the project owner for the
  strict positive orthant `ℝⁿ₊₊`;
* `EuclideanSpace.mem_positiveOrthant_iff` from `Chap01/Definition_1_10_2`, the coordinatewise
  membership bridge for that owner;
* `relativeDirection` and `relativeDirection_apply` from `Definition_5_4_7_14`, the nearby
  Chapter 5 precedent for using `positiveOrthant n` as the owner carrier and `WithLp.toLp` as the
  canonical ambient vector constructor;
* `standardLogarithmicBarrier_apply` from `Definition_5_4_3_2`, the canonical coordinatewise
  logarithmic formula already attached upstream to the same strict-orthant owner.

Best owner abstraction:
* source-facing: `logarithmicSubstitution`, the coordinatewise logarithm on `ℝⁿ₊₊`;
* core/canonical: the Chapter 1 strict-orthant owner `positiveOrthant n` together with
  `WithLp.toLp` for ambient `EuclideanSpace` vectors;
* bridge/view: the coordinate evaluation lemma and its exponential restatement.

Primitive data:
* a point `x : ℝ₊₊^n`.

Derived API:
* the owner map `logarithmicSubstitution`;
* the coordinate formula `logarithmicSubstitution_apply`;
* the exponential inverse relation `logarithmicSubstitution_spec`.

The previous version duplicated the strict-orthant owner with a local subtype alias. This
refinement reuses the Chapter 1 owner directly, uses the existing orthant notation on the theorem
surface, and keeps only the actual source-facing map together with its derived coordinate lemmas.
-/

/-- Definition 5.4.8.18: the logarithmic substitution sends a strictly positive vector
`x ∈ \mathbb{R}^n_{++}` to the vector `y ∈ \mathbb{R}^n` with coordinates
`y^(k) = log x^(k)`. -/
def logarithmicSubstitution (x : ℝ₊₊^n) : Eₙ :=
  WithLp.toLp 2 fun k ↦ Real.log ((x : Eₙ) k)

/-- The logarithmic substitution is the coordinatewise real logarithm. -/
@[simp] theorem logarithmicSubstitution_apply (x : ℝ₊₊^n) (k : Fin n) :
    logarithmicSubstitution x k = Real.log ((x : Eₙ) k) :=
  rfl

/-- Exponentiating the logarithmic substitution recovers the original strictly positive
coordinate. -/
-- Proof sketch: use `logarithmicSubstitution_apply` and then apply `Real.exp_log` to the
-- positive coordinate `x k`, whose positivity is part of the subtype data.
theorem logarithmicSubstitution_spec (x : ℝ₊₊^n) (k : Fin n) :
    (x : Eₙ) k = Real.exp (logarithmicSubstitution x k) := by
  rw [logarithmicSubstitution_apply, Real.exp_log]
  simpa using x.2 k

end

/-! ### Definition_5_4_8_19 (from Chap05) -/
open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ}

/-
Definition 5.4.8.19 lies in the Chapter 5 finite exponential-sum / separable-convex domain.

Sampled owner declarations:
* `SeparableOptimizationProblem.qFunction` from `Definition_5_4_8_1`, the chapter owner for
  finite positive weighted sums of scalar functions along affine maps;
* `SeparableOptimizationProblem.qFunction_apply` from `Definition_5_4_8_1`, the canonical
  expansion bridge for that owner;
* `logSumExp` from `Definition_5_4_7_11`, the nearby finite exponential-family owner in the same
  domain, but with an additional outer logarithm;
* `smoothMaxInnerApproximation` from `Chap07/Definition_7_42`, another project function built from
  exponentials of inner products.

Best owner abstraction:
* source-facing: `sumOfExponentials`;
* core/canonical: `SeparableOptimizationProblem.qFunction`;
* bridge/view: `sumOfExponentialsSeparableProblem` and `sumOfExponentials_eq_separableProblem`;
* derived theorem layer: `sumOfExponentials_convex`.

Primitive data:
* the real coefficient family `α₁, …, αᵣ`;
* the vectors `a₁, …, aᵣ` in a real inner product space.

Derived API:
* the source-facing function `sumOfExponentials`;
* the defining expansion `sumOfExponentials_apply`;
* the positive-weight bridge owner `sumOfExponentialsSeparableProblem`;
* the positive-weight bridge equality `sumOfExponentials_eq_separableProblem`;
* the nonnegative-coefficient convexity theorem `sumOfExponentials_convex`.

The previous version duplicated the chapter owner for finite weighted affine-composition sums as a
raw standalone formula while also exposing a coercion parameter in the source-facing function
owner. This refinement keeps the textbook function name on the primitive real coefficient data
`α : Fin r → ℝ`, and uses the existing owner `SeparableOptimizationProblem.qFunction` only on the
positive-weight bridge layer where that hypothesis is mathematically relevant. The ambient owner is
the intrinsic real inner product space carrying the inner products `⟪aⱼ, y⟫`; specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation.
-/

/-- For strictly positive coefficients, the exponential sum determines a canonical separable
optimization problem with one block and no inequality constraints. -/
def sumOfExponentialsSeparableProblem (α : Fin r → Set.Ioi (0 : ℝ)) (a : Fin r → E) :
    SeparableOptimizationProblem E 0 where
  blockSize _ := r
  weight _ j := α j
  weight_pos _ j := (α j).2
  affineMap _ j := ((innerSL ℝ (a j)).toLinearMap).toAffineMap
  scalarFunction _ _ := Real.exp
  scalarFunction_convex _ _ := by
    simpa using convexOn_exp
  constraintBound := Fin.elim0

/-- Definition 5.4.8.19: for coefficients `α₁, …, αᵣ` read in `ℝ` and vectors `a₁, …, aᵣ` in a
real inner product space `E`, the exponential sum with coefficients `α` and vectors `a` is the
function `g(y) = \sum_{j=1}^r αⱼ \exp(\langle aⱼ, y \rangle)`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` formula. -/
def sumOfExponentials (α : Fin r → ℝ) (a : Fin r → E) : E → ℝ :=
  fun y ↦ ∑ j : Fin r, α j * Real.exp ⟪a j, y⟫

/-- Evaluating `sumOfExponentials α a` at `y` recovers the defining textbook formula
`g(y) = \sum_{j=1}^r αⱼ \exp(\langle aⱼ, y \rangle)`. -/
@[simp] theorem sumOfExponentials_apply (α : Fin r → ℝ) (a : Fin r → E) (y : E) :
    sumOfExponentials α a y = ∑ j : Fin r, α j * Real.exp ⟪a j, y⟫ :=
  rfl

/-- For strictly positive coefficients, the exponential sum obtained by reading `α` as a real
coefficient family is exactly the objective function of the canonical separable owner
`sumOfExponentialsSeparableProblem α a`. -/
theorem sumOfExponentials_eq_separableProblem
    (α : Fin r → Set.Ioi (0 : ℝ)) (a : Fin r → E) :
    sumOfExponentials (fun j ↦ α j) a = sumOfExponentialsSeparableProblem α a := by
  funext y
  rw [SeparableOptimizationProblem.coe_apply]
  rw [(sumOfExponentialsSeparableProblem α a).qFunction_apply 0 y]
  rfl

/-- If all coefficients are nonnegative, then `sumOfExponentials α a` is convex on the whole
ambient space. -/
theorem sumOfExponentials_convex
    (α : Fin r → ℝ) (hα : ∀ j, 0 ≤ α j) (a : Fin r → E) :
    ConvexOn ℝ Set.univ (sumOfExponentials α a) := by
  classical
  let term : Fin r → E → ℝ := fun j y ↦ α j * Real.exp ⟪a j, y⟫
  have hterm : ∀ j : Fin r, ConvexOn ℝ Set.univ (term j) := by
    intro j
    have hcomp : ConvexOn ℝ Set.univ (fun y : E ↦ Real.exp ⟪a j, y⟫) := by
      simpa using
        (convexOn_exp.comp_affineMap (((innerSL ℝ (a j)).toLinearMap).toAffineMap))
    simpa [term] using ConvexOn.smul (hα j) hcomp
  have hsum :
      ∀ s : Finset (Fin r),
        ConvexOn ℝ Set.univ (fun y ↦ s.sum (fun j ↦ term j y)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
    · intro j s hj hs
      simpa [Finset.sum_insert hj] using (hterm j).add hs
  simpa [sumOfExponentials, term] using hsum Finset.univ

end

/-! ### Definition_5_4_8_2 (from Chap05) -/
open scoped BigOperators

namespace SeparableOptimizationProblem

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}
variable (problem : SeparableOptimizationProblem E m)

/-
Definition 5.4.8.2 lies in the separable optimization / finite additive aggregation domain.

Sampled owner declarations:
- `SeparableOptimizationProblem` in `Definition_5_4_8_1`, the chapter owner of the separable
  problem data;
- `SeparableOptimizationProblem.blockSize` in `Definition_5_4_8_1`, the source-facing field
  recording the block counts `mᵢ`;
- `Finset.sum`, the canonical owner for finite additive aggregation;
- `Fin.sum_univ_eq_sum_range` and `Fin.sum_univ_succ`, the standard bridges from a `Fin`-indexed
  sum to textbook range and head-tail presentations.

Best owner abstraction:
- source-facing: the textbook quantity `M = \sum_{i=0}^m mᵢ` attached to
  `problem : SeparableOptimizationProblem E m`;
- core/canonical: the block-count field `problem.blockSize` together with the canonical sum
  `∑ i, problem.blockSize i`;
- bridge/view: `Fin.sum_univ_eq_sum_range` and `Fin.sum_univ_succ`.

Primitive data:
- `problem : SeparableOptimizationProblem E m`.

Derived API:
- `problem.blockSize : Fin (m + 1) → ℕ`;
- the canonical total block count `∑ i, problem.blockSize i`;
- the standard range and successor decompositions of that same finite sum.

Source/core/bridge triage:
- source-facing: the total number `M` of univariate terms in the separable problem;
- core/canonical: the chapter owner `SeparableOptimizationProblem` and its field `blockSize`;
- bridge/view: the generic `Fin`-sum decomposition lemmas.

This file therefore does not keep a free-standing family of counts. Definition 5.4.8.2 is read
through the chapter owner `problem : SeparableOptimizationProblem E m`, and the textbook quantity
`M` is expressed directly as `∑ i, problem.blockSize i`.
-/

/- Definition 5.4.8.2 recalls the chapter owner field for the block counts `mᵢ`. -/
#check SeparableOptimizationProblem.blockSize

/- Definition 5.4.8.2 recalls the canonical finite-sum owner and its standard `Fin` bridges. -/
recall Finset.sum
recall Fin.sum_univ_eq_sum_range
recall Fin.sum_univ_succ

/- Definition 5.4.8.2 expresses the total number of univariate terms as the canonical sum
`M = \sum_{i=0}^m mᵢ` attached to `problem`. -/
#check ∑ i, problem.blockSize i

end SeparableOptimizationProblem

/-! ### Definition_5_4_8_20 (from Chap05) -/
open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

/-
Definition 5.4.8.20 lies in the Chapter 5 `ℓ_p` approximation / separable-convex domain.

Sampled owner declarations:
- `SeparableOptimizationProblem.qFunction` in `Definition_5_4_8_1`, the chapter owner for finite
  positive weighted sums of scalar functions along affine maps;
- `SeparableOptimizationProblem.qFunction_apply` in `Definition_5_4_8_1`, the canonical
  expansion bridge for that owner;
- `sumOfExponentials` in `Definition_5_4_8_19`, the neighboring chapter pattern for a
  source-facing objective defined through `SeparableOptimizationProblem.qFunction`;
- `LpApproximationBoxProblem.toSetConstrainedMinimizationProblem` in `Definition_5_4_9_1`, the
  later box-constrained bridge that should reuse this owner directly rather than through a second
  local objective wrapper.

Best owner abstraction:
- source-facing: `lpApproximationObjective`, the textbook residual objective
  `x ↦ ∑ i, |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p`;
- core/canonical: `SeparableOptimizationProblem.qFunction`;
- bridge/view: `lpApproximationSeparableProblem` and
  `lpApproximationObjective_eq_qFunction`.

Primitive data:
- the exponent `p`;
- the vectors `a₁, …, aₘ` in a real inner product space;
- the scalar targets `b⁽¹⁾, …, b⁽ᵐ⁾`.

Derived API:
- the source-facing objective `lpApproximationObjective`;
- the evaluation lemma `lpApproximationObjective_apply`;
- for `p ≥ 1`, the canonical separable-problem bridge `lpApproximationSeparableProblem` and the
  identification of the objective with its `q₀` block.

Source/core/bridge triage:
- source-facing: Definition 5.4.8.20's `ℓ_p` residual objective;
- core/canonical: the chapter owner `SeparableOptimizationProblem.qFunction`;
- bridge/view: the `SeparableOptimizationProblem E 0` realization below.

The previous version merely recalled a Euclidean raw formula owner from a later theorem file.
This refinement restores Definition 5.4.8.20 as the owner file, moves the objective to the
intrinsic real inner-product-space level, and makes the Chapter 5 separable-objective owner
explicit instead of treating the box-constrained `ℝⁿ` presentation as the core abstraction.
-/

/-- Definition 5.4.8.20: for vectors `a₁, …, aₘ` in a real inner product space `E`, targets
`b⁽¹⁾, …, b⁽ᵐ⁾ ∈ ℝ`, and exponent `p`, the `ℓ_p` approximation objective is the residual sum
`x ↦ \sum_{i=1}^m |\langle a_i, x \rangle - b^{(i)}|^p`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation. -/
def lpApproximationObjective (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) : E → ℝ :=
  fun x ↦ ∑ i : Fin m, |⟪a i, x⟫ - b i| ^ p

/-- Evaluating `lpApproximationObjective p a b` at `x` recovers the defining finite sum
`\sum_{i=1}^m |\langle a_i, x \rangle - b^{(i)}|^p`. -/
@[simp] theorem lpApproximationObjective_apply
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (x : E) :
    lpApproximationObjective p a b x = ∑ i : Fin m, |⟪a i, x⟫ - b i| ^ p :=
  rfl

/-- For `p ≥ 1`, the `ℓ_p` approximation objective is the objective block `q₀` of a canonical
separable optimization problem with one block and no inequality constraints. -/
def lpApproximationSeparableProblem (p : Set.Ici (1 : ℝ)) (a : Fin m → E) (b : Fin m → ℝ) :
    SeparableOptimizationProblem E 0 where
  blockSize _ := m
  weight _ _ := 1
  weight_pos _ _ := zero_lt_one
  affineMap _ i := ((innerSL ℝ (a i)).toLinearMap).toAffineMap + AffineMap.const ℝ E (-b i)
  scalarFunction _ _ := fun t ↦ |t| ^ (p : ℝ)
  scalarFunction_convex _ _ := by
    have habs : ConvexOn ℝ Set.univ (fun t : ℝ ↦ |t|) := by
      simpa [Real.norm_eq_abs] using
        (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))
    have habs_image : (fun t : ℝ ↦ |t|) '' (Set.univ : Set ℝ) = Set.Ici 0 := by
      ext t
      constructor
      · rintro ⟨x, -, rfl⟩
        exact abs_nonneg x
      · intro ht
        refine ⟨t, Set.mem_univ t, ?_⟩
        simp [abs_of_nonneg (show 0 ≤ t from ht)]
    have hpow :
        ConvexOn ℝ ((fun t : ℝ ↦ |t|) '' (Set.univ : Set ℝ)) (fun t : ℝ ↦ t ^ (p : ℝ)) := by
      simpa [habs_image] using
        (convexOn_rpow p.2 : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ t ^ (p : ℝ)))
    have hmono :
        MonotoneOn (fun t : ℝ ↦ t ^ (p : ℝ)) ((fun t : ℝ ↦ |t|) '' (Set.univ : Set ℝ)) := by
      have hp0 : 0 ≤ (p : ℝ) := le_trans zero_lt_one.le p.2
      simpa [habs_image] using
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp0 :
          MonotoneOn (fun t : ℝ ↦ t ^ (p : ℝ)) (Set.Ici 0))
    simpa using hpow.comp habs hmono
  constraintBound := Fin.elim0

/-- For `p ≥ 1`, the source-facing `ℓ_p` residual objective is exactly the `q₀` block of the
canonical separable owner `lpApproximationSeparableProblem`. -/
theorem lpApproximationObjective_eq_qFunction
    (p : Set.Ici (1 : ℝ)) (a : Fin m → E) (b : Fin m → ℝ) :
    lpApproximationObjective (p : ℝ) a b =
      (lpApproximationSeparableProblem p a b).qFunction 0 := by
  funext x
  rw [lpApproximationObjective_apply, (lpApproximationSeparableProblem p a b).qFunction_apply]
  simp [lpApproximationSeparableProblem, sub_eq_add_neg]
  rfl

end

/-! ### Definition_5_4_8_21 (from Chap05) -/
/-
Definition 5.4.8.21 lies in the Chapter 5 box-constrained `ℓ_p` approximation epigraph domain.

Sampled owner declarations:
- `LpApproximationEpigraphPoint` in `Theorem_5_4_8_9`, the chapter owner for the lifted
  epigraph decision variable `(x, τ⁽⁰⁾, τ⁽¹⁾, ..., τ⁽ᵐ⁾)`;
- `LpApproximationEpigraphPoint.objectiveSlack` in `Theorem_5_4_8_9`, the canonical projection to
  the scalar slack `τ⁽⁰⁾`;
- `lpApproximationEpigraphProblem` in `Theorem_5_4_8_9`, the chapter owner for the epigraph
  reformulation;
- `mem_lpApproximationEpigraphProblem_feasibleSet_iff` in `Theorem_5_4_8_9`, the atomic
  membership view of that owner feasible set.

Best owner abstraction:
- source-facing: the textbook epigraph reformulation of the box-constrained `ℓ_p`
  approximation problem;
- core/canonical: `LpApproximationEpigraphPoint` and `lpApproximationEpigraphProblem`;
- bridge/view: the evaluation and membership lemmas expanding those owners to the displayed
  inequalities.

Primitive data:
- the lifted decision-variable type `LpApproximationEpigraphPoint n m`.

Derived API:
- the objective projection `LpApproximationEpigraphPoint.objectiveSlack`;
- the epigraph owner `lpApproximationEpigraphProblem p a b α β`;
- the companion lemmas `lpApproximationEpigraphProblem_apply` and
  `mem_lpApproximationEpigraphProblem_feasibleSet_iff`.

Source/core/bridge triage:
- source-facing: Definition 5.4.8.21's epigraph standard-form variables and inequalities;
- core/canonical: the existing chapter owner declarations from `Theorem_5_4_8_9`;
- bridge/view: the companion expansion lemmas for objective evaluation and feasible-set
  membership.

This item therefore deletes the duplicate local structure
`LpApproximationEpigraphDecisionVariable`, the duplicate feasible-set definition
`lpApproximationEpigraphStandardForm`, and the duplicate objective alias. The existing chapter
owner API should be used directly.
-/

recall LpApproximationEpigraphPoint
recall LpApproximationEpigraphPoint.objectiveSlack
recall lpApproximationEpigraphProblem
recall mem_lpApproximationEpigraphProblem_feasibleSet_iff
recall lpApproximationEpigraphProblem_apply

/- Definition 5.4.8.21 recalls the chapter owner for the `ℓ_p` approximation epigraph decision
variables. -/
#check LpApproximationEpigraphPoint

/- Definition 5.4.8.21 recalls the coordinate projection to the epigraph objective slack. -/
#check LpApproximationEpigraphPoint.objectiveSlack

/- Definition 5.4.8.21 recalls the chapter owner for the corresponding epigraph reformulation. -/
#check lpApproximationEpigraphProblem

/-! ### Definition_5_4_8_3 (from Chap05) -/
namespace SeparableOptimizationProblem

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/- Definition 5.4.8.3 lies in the separable optimization / standard-form epigraph domain.

Sampled owner-style declarations:
- `SeparableOptimizationProblem` from `Definition_5_4_8_1`, the source-facing owner of the block
  data `mᵢ`, affine functionals `ℓᵢⱼ`, and scalar functions `fᵢⱼ`;
- `StandardFormDecisionVariable` from `Theorem_5_4_8_1`, the chapter's owner for the standard-form
  variables `(x, τ, t)`;
- `StandardFormDecisionVariable.epigraphSlack`, the canonical projection exposing the slack family
  `τ : Fin (m + 1) → ℝ`;
- `StandardFormDecisionVariable.termSlack`, the canonical projection exposing the block family
  `t_{i,j}`.

Best owner abstraction:
- source-facing: the textbook slack coordinates `τ` and `t_{i,j}` of a standard-form decision
  variable;
- core/canonical: `StandardFormDecisionVariable problem`;
- bridge/view: the projections `epigraphSlack` and `termSlack`.

Primitive data:
- the original point `x`;
- the slack family `τ`;
- the block family `t`.

Derived API:
- `decision.epigraphSlack : Fin (m + 1) → ℝ`;
- `decision.termSlack i : Fin (problem.blockSize i) → ℝ`.

Source/core/bridge triage:
- source-facing: the slack-coordinate surface `(τ, t)` appearing in the standard-form variables;
- core/canonical: `StandardFormDecisionVariable problem`;
- bridge/view: its coordinate projections.

This numbered item therefore does not keep a second owner for `(τ, t)`: the slack variables are
recalled through the canonical owner `StandardFormDecisionVariable problem`, and only their
coordinate projections are exposed on the public surface. The `τ` surface is still read through
the weaker finite-family type `Fin (m + 1) → ℝ` rather than the over-concrete model
`EuclideanSpace ℝ (Fin (m + 1))`. -/

/- Definition 5.4.8.3 recalls the canonical owner whose projections supply the slack variables. -/
recall StandardFormDecisionVariable

/- Definition 5.4.8.3 uses the canonical slack-coordinate projections. -/
recall StandardFormDecisionVariable.epigraphSlack
recall StandardFormDecisionVariable.termSlack

end SeparableOptimizationProblem

/-! ### Definition_5_4_8_4 (from Chap05) -/
namespace SeparableOptimizationProblem

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/- Definition 5.4.8.4 lies in the separable convex optimization / standard-form epigraph domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with its objective;
- `SeparableOptimizationProblem` in `Definition_5_4_8_1`, the source-facing owner of the
  separable coefficient data and affine-function block structure;
- `StandardFormDecisionVariable` in `Theorem_5_4_8_1`, the canonical decision-variable type for
  the variables `(x, τ, t)`;
- `standardFormOptimizationProblem` in `Theorem_5_4_8_1`, the canonical Chapter 1 constrained
  problem attached to that reformulation.

Best owner abstraction:
- source-facing: the textbook standard-form variables `(x, τ, t)` and the epigraph reformulation
  attached to `problem : SeparableOptimizationProblem E m`;
- core/canonical:
  `SetConstrainedMinimizationProblem (StandardFormDecisionVariable problem)`;
- bridge/view: the exact objective-evaluation and feasible-set-membership theorems already owned
  by `standardFormOptimizationProblem`.

Primitive data:
- the original separable problem `problem : SeparableOptimizationProblem E m`.

Derived API:
- `StandardFormDecisionVariable problem`;
- `standardFormOptimizationProblem problem`;
- `standardFormOptimizationProblem_apply`;
- `mem_standardFormOptimizationProblem_feasibleSet_iff`.

Source/core/bridge triage:
- source-facing: the textbook variables `(x, τ, t)` and the standard-form minimization problem;
- core/canonical: the Chapter 1 owner `SetConstrainedMinimizationProblem`;
- bridge/view: the companion evaluation and membership lemmas for the standard-form owner.

This file therefore reuses the chapter's canonical decision-variable owner
`StandardFormDecisionVariable problem` directly, rather than rebuilding a second wrapper for the
slack variables. The recalled constrained problem is expressed over that reused owner. -/

/- Definition 5.4.8.4 recalls the canonical standard-form decision-variable owner. -/
recall StandardFormDecisionVariable

/- Definition 5.4.8.4 recalls the canonical standard-form epigraph reformulation of a separable
optimization problem. -/
recall standardFormOptimizationProblem
recall standardFormOptimizationProblem_apply
recall mem_standardFormOptimizationProblem_feasibleSet_iff

end SeparableOptimizationProblem

/-! ### Definition_5_4_8_5 (from Chap05) -/
/- Definition 5.4.8.5 lies in the chapter's real epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a feasible set;
- `strictConstrainedEpigraph` from `Chap05/Theorem_5_3_5`, the strict-epigraph companion in the
  same chapter API;
- mathlib `ConvexOn.convex_epigraph`, the standard convex-epigraph owner theorem;
- mathlib `LowerSemicontinuous.isClosed_epigraph`, the standard closed-epigraph owner theorem.

Best owner abstraction:
- core/canonical:
  `constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))`.

Primitive data:
- the positive half-line `(0, ∞)`;
- the function `x ↦ -log x`.

Derived API:
- the epigraph set itself;
- its specialized membership expansion.

Source/core/bridge triage:
- source-facing: the textbook set `Q₁`;
- core/canonical: the chapter epigraph owner `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.

This item therefore deletes the parallel local set `q1NegativeLogEpigraph` and reuses the chapter
epigraph owner directly. -/

/- Definition 5.4.8.5 recalls the chapter epigraph owner specialized to `x ↦ -log x` on
`(0, ∞)`. -/
#check constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))

/-- Membership in the canonical epigraph expression for Definition 5.4.8.5 means that `x > 0`
and `t ≥ -log x`. -/
theorem mem_constrainedEpigraph_negLog_iff {x t : ℝ} :
    (x, t) ∈ constrainedEpigraph (Set.Ioi (0 : ℝ))
      (fun y : ℝ ↦ (-Real.log y : WithTop ℝ)) ↔
      0 < x ∧ t ≥ -Real.log x := by
  rw [mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt

/-! ### Definition_5_4_8_6 (from Chap05) -/
/-
Definition 5.4.8.6 lies in the Chapter 5 strict-epigraph logarithmic-barrier domain.

Sampled owner declarations:
* `epigraphLogBarrier` from `Theorem_5_3_5`, the chapter owner for raw-pair epigraph
  logarithmic barriers;
* `epigraphLogBarrier_apply` from `Theorem_5_3_5`, the canonical evaluation bridge for that
  owner;
* `strictConstrainedEpigraph` from `Theorem_5_3_5`, the matching strict-epigraph domain owner;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the closed-epigraph owner whose interior
  is the source domain for this barrier.

Best owner abstraction:
* core/canonical: `epigraphLogBarrier (fun x : ℝ ↦ -Real.log x)`.

Primitive data:
* the base function `x ↦ -Real.log x`.

Derived API:
* the source-facing barrier `F₁`;
* its textbook coordinate formula, obtained from `epigraphLogBarrier_apply`.

Source/core/bridge triage:
* source-facing: the textbook barrier `F₁`;
* core/canonical: `epigraphLogBarrier`;
* bridge/view: the specialized evaluation of that owner at `(x, t)`.

This item adds no new owner beyond the chapter epigraph-barrier API, so the parallel local alias
`separableLogBarrierF1` is deleted. Downstream files should use
`epigraphLogBarrier (fun x : ℝ ↦ -Real.log x)` directly.
-/

/- Definition 5.4.8.6 recalls the canonical epigraph logarithmic barrier specialized to
`x ↦ -log x`. -/
#check (epigraphLogBarrier (fun x : ℝ ↦ -Real.log x) : ℝ × ℝ → ℝ)

/-- The textbook coordinate formula for Definition 5.4.8.6 is the specialized evaluation of the
canonical epigraph logarithmic barrier owner. -/
theorem epigraphLogBarrier_negLog_apply (x t : ℝ) :
    epigraphLogBarrier (fun y : ℝ ↦ -Real.log y) (x, t) =
      -Real.log x - Real.log (Real.log x + t) := by
  rw [epigraphLogBarrier_apply]
  simp [sub_eq_add_neg, add_comm]

/-! ### Definition_5_4_8_7 (from Chap05) -/
/- Definition 5.4.8.7 is a recall-only item in the Chapter 5 exponential-epigraph domain.

Primary domain:
- the exponential epigraph in `ℝ × ℝ`.

Sampled owner declarations:
- `exponentialEpigraphQ2` from `Theorem_5_4_8_3`, the existing chapter source-facing owner for the
  textbook set `Q₂`;
- `mem_exponentialEpigraphQ2_iff` from `Theorem_5_4_8_3`, the canonical companion theorem for the
  defining inequality;
- `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter core epigraph owner underlying
  this example;
- `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the generic membership expansion
  for that core owner.

Best owner abstraction:
- source-facing owner for this numbered item: `exponentialEpigraphQ2`;
- deeper core/canonical bridge: `constrainedEpigraph (Set.univ : Set ℝ)
  (fun x : ℝ ↦ (Real.exp x : WithTop ℝ))`.

Primitive data:
- none in this file; the source-facing owner is already defined upstream in the chapter.

Derived API:
- the owner declaration `exponentialEpigraphQ2`;
- the defining membership theorem `mem_exponentialEpigraphQ2_iff`.

Source/core/bridge triage:
- source-facing: `exponentialEpigraphQ2`, the textbook set `Q₂`;
- core/canonical: the constrained-epigraph expression specialized to `x ↦ exp x`;
- bridge/view: the identification already supplied upstream by
  `mem_exponentialEpigraphQ2_iff`.

The previous version duplicated the chapter source-facing owner by making the deeper epigraph
bridge the main public surface and adding a second membership theorem for the same set. This file
now reuses the existing owner directly and leaves the canonical epigraph expression as background
structure rather than as a competing public API. -/

/- Definition 5.4.8.7 recalls the existing chapter owner for the textbook exponential epigraph
`Q₂`. -/
recall exponentialEpigraphQ2 : Set (ℝ × ℝ)

/- The defining inequality for `Q₂` is recalled through its canonical companion theorem. -/
recall mem_exponentialEpigraphQ2_iff {x t : ℝ} :
    (x, t) ∈ exponentialEpigraphQ2 ↔ t ≥ Real.exp x

/-! ### Definition_5_4_8_8 (from Chap05) -/
/- Definition 5.4.8.8 is a recall-only item in the Chapter 5 exponential-epigraph barrier domain.

Primary domain:
- logarithmic barriers for the exponential epigraph in `ℝ × ℝ`.

Sampled owner-style declarations:
- `exponentialEpigraphBarrierF2` from `Theorem_5_4_8_3`
- `exponentialEpigraphBarrierF2_apply` from `Theorem_5_4_8_3`
- `exponentialEpigraphQ2` from `Theorem_5_4_8_3`
- `epigraphLogBarrier` from `Theorem_5_3_5`

Best owner abstraction:
- the existing chapter source-facing owner `exponentialEpigraphBarrierF2`

Primitive data:
- none; this numbered item introduces no new primitive object beyond the existing owner.

Derived API:
- the owner declaration `exponentialEpigraphBarrierF2`
- the defining evaluation lemma `exponentialEpigraphBarrierF2_apply`

Source/core/bridge triage:
- source-facing: the textbook function `F₂(x, t) = -log t - log (log t - x)`
- core/canonical: `exponentialEpigraphBarrierF2`
- bridge/view: the evaluation theorem `exponentialEpigraphBarrierF2_apply`

The previous version introduced a second public owner `separableLogBarrierF2` for exactly the
same function already exposed upstream. This file now reuses the existing chapter owner directly,
in line with the chapter's recall-only pattern for numbered items that add no new API. -/

/- Definition 5.4.8.8 recalls the existing chapter owner for the textbook barrier `F₂`. -/
recall exponentialEpigraphBarrierF2 : ℝ × ℝ → ℝ

/- The textbook coordinate formula is recalled through the canonical companion theorem. -/
recall exponentialEpigraphBarrierF2_apply (x t : ℝ) :
    exponentialEpigraphBarrierF2 (x, t) = -Real.log t - Real.log (Real.log t - x)

/-! ### Definition_5_4_8_9 (from Chap05) -/
/- Definition 5.4.8.9 lies in the chapter's real epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a feasible set;
- `mem_constrainedEpigraph_negLog_iff` from `Definition_5_4_8_5`, the nearby chapter pattern for
  specializing this owner to a one-variable barrier epigraph;
- `ConvexOn.convex_epigraph`, the standard convex-epigraph owner theorem;
- `LowerSemicontinuous.isClosed_epigraph`, the standard closed-epigraph owner theorem.

Best owner abstraction:
- core/canonical:
  `constrainedEpigraph (Set.Ici (0 : ℝ))
    (fun x : ℝ ↦ ((x * Real.log x : ℝ) : WithTop ℝ))`.

Primitive data:
- the nonnegative half-line `[0, ∞)`;
- the function `x ↦ x log x`.

Derived API:
- the specialized epigraph expression itself;
- its membership expansion.

Source/core/bridge triage:
- source-facing: the textbook set `Q₃`;
- core/canonical: the chapter epigraph owner `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.

This item therefore keeps the source-facing owner `Q₃` while realizing it directly through the
chapter epigraph owner, deleting the parallel local set `qThreeEpigraph`. -/

/-- Definition 5.4.8.9: the set `Q₃`, namely the epigraph of `x ↦ x log x` on `[0, ∞)`. -/
abbrev Q₃ : Set (ℝ × ℝ) :=
  constrainedEpigraph (Set.Ici (0 : ℝ))
    (fun x : ℝ ↦ ((x * Real.log x : ℝ) : WithTop ℝ))

/-- Membership in `Q₃` means exactly that `x ≥ 0` and `t ≥ x log x`. -/
@[simp] theorem mem_Q₃_iff {x t : ℝ} :
    (x, t) ∈ Q₃ ↔ 0 ≤ x ∧ t ≥ x * Real.log x := by
  rw [Q₃, mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    have hxt' : x * Real.log x ≤ t := by
      exact_mod_cast hxt
    simpa [ge_iff_le] using hxt'
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    have hxt' : x * Real.log x ≤ t := by
      simpa [ge_iff_le] using hxt
    exact_mod_cast hxt'

/-! ### Theorem_5_4_8_1 (from Chap05) -/
noncomputable section

universe u

open scoped BigOperators

namespace SeparableOptimizationProblem

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/- Theorem 5.4.8.1 lies in the separable optimization / standard-form epigraph domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` from
  `Chap01/Definition_1_3_7`, the Chapter 1 owner for feasible-set / objective minimization;
- `LagrangianProblem.toSetConstrainedMinimizationProblem` from `Chap01/Definition_1_10_2`, the
  inherited Chapter 1 owner bridge reached from the source-facing map
  `SeparableOptimizationProblem.toLagrangianProblem`;
- `functionalConstraintStandardFormProblem` from `Proposition_5_3_6_1`, the chapter's standard
  pattern for expressing lifted reformulations directly as a `SetConstrainedMinimizationProblem`
  over raw product data rather than through an extra wrapper structure.

Best owner abstraction:
- source-facing: `problem : SeparableOptimizationProblem E m` together with the textbook
  standard-form variables `(x, τ, t)`;
- core/canonical: `SetConstrainedMinimizationProblem`;
- bridge/view: `StandardFormDecisionVariable problem` and
  `standardFormOptimizationProblem problem`.

Primitive data:
- the base point `x : E`;
- the slack family `τ : Fin (m + 1) → ℝ`;
- the blockwise epigraph family `t`.

Derived API:
- the projection helpers `point`, `epigraphSlack`, and `termSlack`;
- the standard-form Chapter 1 owner `standardFormOptimizationProblem`;
- its objective-evaluation and feasible-set-membership lemmas.

The previous version used a dedicated wrapper structure for the triple `(x, τ, t)`. The chapter's
owner style for standard-form lifts is lighter: keep the Chapter 1 minimization owner primary and
expose the raw lifted data through a thin reusable alias plus projection helpers. The public names
stay the same, but the duplicate wrapper layer is removed. -/

/-- A decision variable of the standard-form epigraph reformulation consists of the original point
`x ∈ E`, slack variables `τ₀, …, τₘ`, and blockwise epigraph variables `tᵢⱼ`. -/
abbrev StandardFormDecisionVariable (problem : SeparableOptimizationProblem E m) :=
  E × (Fin (m + 1) → ℝ) × ((i : Fin (m + 1)) → Fin (problem.blockSize i) → ℝ)

namespace StandardFormDecisionVariable

/-- The original optimization variable `x ∈ E`. -/
abbrev point
    {problem : SeparableOptimizationProblem E m}
    (decision : StandardFormDecisionVariable problem) : E :=
  decision.1

/-- The slack variables `τ₀, …, τₘ` controlling the weighted block sums. -/
abbrev epigraphSlack
    {problem : SeparableOptimizationProblem E m}
    (decision : StandardFormDecisionVariable problem) :
    Fin (m + 1) → ℝ :=
  decision.2.1

/-- The epigraph variables `tᵢⱼ` dominating the scalar convex terms. -/
abbrev termSlack
    {problem : SeparableOptimizationProblem E m}
    (decision : StandardFormDecisionVariable problem)
    (i : Fin (m + 1)) :
    Fin (problem.blockSize i) → ℝ :=
  decision.2.2 i

end StandardFormDecisionVariable

open StandardFormDecisionVariable

/-- The standard-form epigraph reformulation minimizes `τ₀` over the triples `(x, τ, t)`
satisfying the weighted block inequalities `∑ⱼ αᵢⱼ tᵢⱼ ≤ τᵢ`, the side constraints
`τᵢ ≤ βᵢ` for `i = 1, …, m`, and the epigraph inequalities
`fᵢⱼ(ℓᵢⱼ(x)) ≤ tᵢⱼ`. -/
def standardFormOptimizationProblem
    (problem : SeparableOptimizationProblem E m) :
    SetConstrainedMinimizationProblem (StandardFormDecisionVariable problem) where
  feasibleSet := {decision |
    (∀ i : Fin (m + 1),
      ∑ j : Fin (problem.blockSize i), problem.weight i j * decision.termSlack i j ≤
        decision.epigraphSlack i) ∧
      (∀ i : Fin m, decision.epigraphSlack i.succ ≤ problem.constraintBound i) ∧
      ∀ i : Fin (m + 1), ∀ j : Fin (problem.blockSize i),
        problem.scalarFunction i j (problem.affineMap i j decision.point) ≤ decision.termSlack i j}
  objective := fun decision ↦ decision.epigraphSlack 0

/-- Evaluating the standard-form objective returns the zeroth slack variable `τ₀`. -/
@[simp] theorem standardFormOptimizationProblem_apply
    (problem : SeparableOptimizationProblem E m)
    (decision : StandardFormDecisionVariable problem) :
    standardFormOptimizationProblem problem decision = decision.epigraphSlack 0 :=
  rfl

/-- Membership in the feasible set of the standard-form reformulation is exactly the conjunction
of the displayed block-sum, side, and epigraph inequalities. -/
@[simp] theorem mem_standardFormOptimizationProblem_feasibleSet_iff
    (problem : SeparableOptimizationProblem E m)
    (decision : StandardFormDecisionVariable problem) :
    decision ∈ (standardFormOptimizationProblem problem).feasibleSet ↔
      (∀ i : Fin (m + 1),
        ∑ j : Fin (problem.blockSize i), problem.weight i j * decision.termSlack i j ≤
          decision.epigraphSlack i) ∧
        (∀ i : Fin m, decision.epigraphSlack i.succ ≤ problem.constraintBound i) ∧
        ∀ i : Fin (m + 1), ∀ j : Fin (problem.blockSize i),
          problem.scalarFunction i j (problem.affineMap i j decision.point) ≤
            decision.termSlack i j :=
  Iff.rfl

-- Proof sketch: lift each feasible `x` for the inherited Chapter 1 owner
-- `(problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem` to the standard-form
-- decision variable with `tᵢⱼ = fᵢⱼ(ℓᵢⱼ(x))` and
-- `τᵢ = ∑ⱼ αᵢⱼ tᵢⱼ`, which preserves the objective value. Conversely, project any feasible
-- standard-form decision variable to its `x`-component; positivity of the weights and the
-- epigraph inequalities imply that the original objective value is bounded by `τ₀`. Comparing
-- the two induced Chapter 1 optimal values yields equality.
/-- Theorem 5.4.8.1: the original separable optimization problem and its standard-form epigraph
reformulation have the same canonical Chapter 1 optimal value. -/
theorem separableOptimizationProblem_optimalValue_eq_standardFormOptimalValue
    (problem : SeparableOptimizationProblem E m) :
    (problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem.optimalValue =
      (standardFormOptimizationProblem problem).optimalValue := by
  let originalProblem : SetConstrainedMinimizationProblem E :=
    (problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem
  let standardProblem := standardFormOptimizationProblem problem
  apply le_antisymm
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨decision, hdecision, rfl⟩
    rw [mem_standardFormOptimizationProblem_feasibleSet_iff] at hdecision
    rcases hdecision with
      ⟨hweighted, hbound, hepigraph⟩
    have hpoint_problem :
        decision.point ∈ problem.feasibleSet := by
      rw [mem_feasibleSet_iff]
      intro i
      calc
        problem.qFunction i.succ decision.point =
            ∑ j : Fin (problem.blockSize i.succ),
              problem.weight i.succ j *
                problem.scalarFunction i.succ j (problem.affineMap i.succ j decision.point) := by
              rw [qFunction_apply]
        _ ≤ ∑ j : Fin (problem.blockSize i.succ),
              problem.weight i.succ j * decision.termSlack i.succ j := by
              refine Finset.sum_le_sum fun j _ ↦ ?_
              exact mul_le_mul_of_nonneg_left (hepigraph i.succ j)
                (le_of_lt (problem.weight_pos i.succ j))
        _ ≤ decision.epigraphSlack i.succ := hweighted i.succ
        _ ≤ problem.constraintBound i := hbound i
    have hpoint : decision.point ∈ originalProblem.feasibleSet := by
      simpa [originalProblem, SeparableOptimizationProblem.feasibleSet] using hpoint_problem
    have horiginal :
        originalProblem.optimalValue ≤ (originalProblem decision.point : EReal) :=
      originalProblem.optimalValue_le_of_mem_feasibleSet hpoint
    have hvalue :
        (originalProblem decision.point : EReal) ≤ (decision.epigraphSlack 0 : EReal) := by
      have hvalue' : problem decision.point ≤ decision.epigraphSlack 0 := by
        calc
          problem decision.point = problem.qFunction 0 decision.point := by simp
          _ =
              ∑ j : Fin (problem.blockSize 0),
                problem.weight 0 j *
                  problem.scalarFunction 0 j (problem.affineMap 0 j decision.point) := by
                rw [qFunction_apply]
          _ ≤ ∑ j : Fin (problem.blockSize 0),
                problem.weight 0 j * decision.termSlack 0 j := by
                refine Finset.sum_le_sum fun j _ ↦ ?_
                exact mul_le_mul_of_nonneg_left (hepigraph 0 j)
                  (le_of_lt (problem.weight_pos 0 j))
          _ ≤ decision.epigraphSlack 0 := hweighted 0
      exact_mod_cast hvalue'
    simpa [originalProblem, standardProblem] using horiginal.trans hvalue
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    let decision : StandardFormDecisionVariable problem :=
      (x,
        fun i ↦
          ∑ j : Fin (problem.blockSize i),
            problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x),
        fun i j ↦ problem.scalarFunction i j (problem.affineMap i j x))
    have hx_problem : x ∈ problem.feasibleSet := by
      simpa [originalProblem, SeparableOptimizationProblem.feasibleSet] using hx
    have hfeasible :
        decision ∈ standardProblem.feasibleSet := by
      rw [mem_standardFormOptimizationProblem_feasibleSet_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        simp [decision]
      · intro i
        exact (mem_feasibleSet_iff problem x).mp hx_problem i
      · intro i j
        simp [decision]
    have hstandard :
        standardProblem.optimalValue ≤ (standardProblem decision : EReal) :=
      standardProblem.optimalValue_le_of_mem_feasibleSet hfeasible
    simpa [originalProblem, standardProblem, decision, qFunction_apply] using hstandard

end SeparableOptimizationProblem

end

/-! ### Theorem_5_4_8_2 (from Chap05) -/
noncomputable section

/- Theorem 5.4.8.2 lies in the chapter's logarithmic-barrier / epigraph-lifting domain.

Sampled owner declarations:
* `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` in `Example_5_3_1_3`, the scalar owner
  for the base barrier `x ↦ -log x`;
* `epigraphLogBarrier_isSelfConcordantBarrierOnWith` in `Theorem_5_3_5`, the chapter owner for
  lifting a barrier to the strict epigraph on the canonical `WithLp 2 (E × ℝ)` product;
* mathlib `WithLp 2 (ℝ × ℝ)` together with `WithLp.ofLp`, the canonical `L²` ambient owner and
  the public bridge back to the textbook raw pairs;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` in `Chap03/Definition_3_3`, the
  chapter owner for the closed epigraph from Definition 5.4.8.5;
* `strictConstrainedEpigraph` and `epigraphLogBarrier` in `Theorem_5_3_5`, the source-facing
  strict-epigraph and lifted-barrier owners reused by the specialization below.

Best owner abstraction:
* source-facing: the interior of the closed epigraph from Definition 5.4.8.5;
* core/canonical: the lifted barrier owner
  `epigraphLogBarrier_isSelfConcordantBarrierOnWith`;
* bridge/view: the interior-identification theorem below, which rewrites the closed epigraph
  interior as the corresponding strict epigraph.

Primitive data:
* the base logarithmic barrier `x ↦ -Real.log x`;
* the closed epigraph owner
  `constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))`.

Derived API:
* the source-facing interior membership theorem;
* the specialized lifted barrier statement for the canonical epigraph logarithmic barrier.

The file therefore keeps the source-facing interior statement, but the barrier theorem is intended
to be a thin specialization of the chapter owners for the scalar `-log` barrier and epigraph
lifting, rather than a second local barrier construction. -/

local notation "Z" => WithLp 2 (ℝ × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → ℝ × ℝ)
local notation "Q₁" =>
  constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))

-- Proof sketch: the interior of the canonical closed epigraph from Definition 5.4.8.5 is
-- obtained by replacing the boundary inequality `t ≥ -\log x` with the strict inequality
-- `t > -\log x` while keeping `x > 0`.
/-- A point lies in the interior of the canonical epigraph for Definition 5.4.8.5 exactly when
`x > 0` and `t > -\log x`. -/
theorem mem_interior_constrainedEpigraph_negLog_iff {x t : ℝ} :
    (x, t) ∈ interior Q₁ ↔ 0 < x ∧ t > -Real.log x := sorry

-- Proof sketch: first rewrite the interior of the canonical closed epigraph from
-- Definition 5.4.8.5 as the strict epigraph of `x ↦ -\log x` via
-- `mem_interior_constrainedEpigraph_negLog_iff`. Then specialize the scalar owner
-- `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` and the canonical epigraph-lifting owner
-- `epigraphLogBarrier_isSelfConcordantBarrierOnWith`; since the scalar barrier parameter is `1`,
-- the lifted epigraph barrier has the exact source parameter `1 + 1 = 2`.
/-- Theorem 5.4.8.2: the canonical epigraph logarithmic barrier specialized to `x ↦ -\log x`,
namely `F₁(x, t) = -\log x - \log (\log x + t)`, is a `2`-self-concordant barrier for the
canonical epigraph of Definition 5.4.8.5, viewed on the canonical `L²` product owner
`Z = WithLp 2 (ℝ × ℝ)` through `z ↦ z.ofLp`. -/
theorem epigraphLogBarrier_negLog_is_two_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior Q₁)
      (2 : NNReal)
      (epigraphLogBarrier (fun x : ℝ ↦ -Real.log x) ∘ ofZ) := by
  have hQ₁ :
      interior Q₁ = strictConstrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := by
    ext z
    rcases z with ⟨x, t⟩
    rw [mem_strictConstrainedEpigraph_iff]
    simpa [gt_iff_lt] using
      (show (x, t) ∈ interior Q₁ ↔ 0 < x ∧ t > -Real.log x from
        mem_interior_constrainedEpigraph_negLog_iff)
  have hν : (1 : NNReal) + 1 = 2 := by
    norm_num
  simpa [hQ₁, hν] using
    (epigraphLogBarrier_isSelfConcordantBarrierOnWith
      negLog_isSelfConcordantBarrierOnWith_nonnegativeRay)

/-! ### Theorem_5_4_8_3 (from Chap05) -/
noncomputable section

/-
Theorem 5.4.8.3 lies in the Chapter 5 self-concordant-barrier / exponential-epigraph domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for closed epigraphs and their membership expansion;
* `epigraphLogBarrier_negLog_is_two_selfConcordantBarrier` from `Theorem_5_4_8_2`, the chapter
  owner for the already-established `2`-self-concordant barrier on the `-log` epigraph;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the owner-level
  affine-pullback theorem for self-concordant barriers;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the canonical owner for logarithmic barrier factors
  of the form `x ↦ -log (β - f x)`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for quantitative
  self-concordant barriers;
* mathlib `WithLp 2 (ℝ × ℝ)` from `ProdL2`, together with `WithLp.ofLp`, the canonical `L²`
  ambient owner and the public bridge back to raw pairs.

Best owner abstraction:
* source-facing: the textbook exponential epigraph `Q₂` and barrier `F₂`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical product owner
  `WithLp 2 (ℝ × ℝ)`;
* bridge/view: the raw-pair owners `exponentialEpigraphQ2` and `exponentialEpigraphBarrierF2`,
  together with the affine pullback `(x, t) ↦ (t, -x)` from the `-log` epigraph of
  Theorem 5.4.8.2.

Primitive data:
* the closed epigraph inequality `t ≥ exp x`;
* the canonical `-\log` epigraph barrier owner from Theorem 5.4.8.2;
* the affine involution `(x, t) ↦ (t, -x)`.

Derived API:
* the source-facing owner `exponentialEpigraphQ2`;
* the source-facing owner `exponentialEpigraphBarrierF2`;
* the companion lemmas expanding these owners into textbook formulas;
* the affine bridge to the `-log` epigraph barrier from Theorem 5.4.8.2.

This refinement keeps the source-facing names `Q₂` and `F₂`, deletes the duplicate raw
set-builder and duplicate raw logarithmic-body definition in favor of the chapter owners
`constrainedEpigraph` and `epigraphLogBarrier`, and refines the barrier theorem itself to the
correct thin affine-pullback bridge from the earlier canonical `2`-barrier result instead of
introducing a new owner-level `3`-barrier statement. -/

/-- The exponential epigraph `Q₂ = {(x, t) ∈ ℝ² | t ≥ e^x}`. -/
def exponentialEpigraphQ2 : Set (ℝ × ℝ) :=
  constrainedEpigraph (Set.univ : Set ℝ) (fun x : ℝ ↦ (Real.exp x : WithTop ℝ))

-- Proof sketch: expand the specialized constrained epigraph owner. The feasible-set clause is
-- vacuous because the base set is `Set.univ`, so only the defining inequality remains.
/-- A pair `(x, t)` lies in `exponentialEpigraphQ2` exactly when `t ≥ e^x`. -/
theorem mem_exponentialEpigraphQ2_iff {x t : ℝ} :
    (x, t) ∈ exponentialEpigraphQ2 ↔ t ≥ Real.exp x :=
  by simp [exponentialEpigraphQ2]

/-- The function `F₂(x, t) = -log t - log (log t - x)`, defined as the affine pullback of the
canonical `-\log` epigraph barrier from Theorem 5.4.8.2. -/
def exponentialEpigraphBarrierF2 : ℝ × ℝ → ℝ :=
  fun p ↦ epigraphLogBarrier (fun y : ℝ ↦ -Real.log y) (p.2, -p.1)

/-- Evaluating `exponentialEpigraphBarrierF2` at `(x, t)` recovers
`F₂(x, t) = -log t - log (log t - x)`. -/
theorem exponentialEpigraphBarrierF2_apply (x t : ℝ) :
    exponentialEpigraphBarrierF2 (x, t) = -Real.log t - Real.log (Real.log t - x) :=
  by
    simp [exponentialEpigraphBarrierF2, epigraphLogBarrier, sublevelLogBarrier,
      sub_eq_add_neg, add_comm, add_left_comm]

local notation "Z" => WithLp 2 (ℝ × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → ℝ × ℝ)
local notation "Q₁" =>
  constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))

private def exponentialEpigraphAffine : Z →ᴬ[ℝ] Z :=
  (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toContinuousLinearMap)) :
      Z →L[ℝ] Z).toContinuousAffineMap

@[simp] theorem exponentialEpigraphAffine_apply (z : Z) :
    (exponentialEpigraphAffine z).ofLp = (z.ofLp.2, -z.ofLp.1) := by
  simp [exponentialEpigraphAffine]

/-- A pair `(x, t)` lies in the interior of `exponentialEpigraphQ2` exactly when `t > e^x`. -/
theorem mem_interior_exponentialEpigraphQ2_iff {x t : ℝ} :
    (x, t) ∈ interior exponentialEpigraphQ2 ↔ t > Real.exp x := by
  constructor
  · intro h
    have hmem : (x, t) ∈ exponentialEpigraphQ2 := interior_subset h
    have hge : Real.exp x ≤ t := mem_exponentialEpigraphQ2_iff.mp hmem
    by_contra hnot
    have ht : t = Real.exp x := le_antisymm (not_lt.mp hnot) hge
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h) with ⟨ε, hε, hεball⟩
    have hball : (x, t - ε / 2) ∈ Metric.ball (x, t) ε := by
      have hhalf : ε / 2 < ε := by
        linarith
      have hhalf_nonneg : 0 ≤ ε / 2 := by
        linarith
      change max (dist x x) (dist (t - ε / 2) t) < ε
      rw [dist_self, Real.dist_eq, sub_sub_cancel_left, abs_of_nonpos (by linarith)]
      simpa [max_eq_right hhalf_nonneg] using hhalf
    have hmem' : (x, t - ε / 2) ∈ exponentialEpigraphQ2 := hεball hball
    have hge' : Real.exp x ≤ t - ε / 2 := mem_exponentialEpigraphQ2_iff.mp hmem'
    linarith
  · intro h
    let S : Set (ℝ × ℝ) := {p | Real.exp p.1 < p.2}
    have hSopen : IsOpen S :=
      isOpen_lt (Real.continuous_exp.comp continuous_fst) continuous_snd
    have hSsubset : S ⊆ exponentialEpigraphQ2 := by
      intro p hp
      exact mem_exponentialEpigraphQ2_iff.mpr hp.le
    have hSin : (x, t) ∈ S := h
    exact mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset (IsOpen.mem_nhds hSopen hSin) hSsubset

/-- The source-facing barrier `F₂` is the pullback of the `-\log` epigraph barrier along
`(x, t) ↦ (t, -x)`. -/
theorem exponentialEpigraphBarrierF2_eq_epigraphLogBarrier_negLog_comp (x t : ℝ) :
    exponentialEpigraphBarrierF2 (x, t) =
      epigraphLogBarrier (fun y : ℝ ↦ -Real.log y) (t, -x) := by
  rfl

/-- Pulling back the `-\log` epigraph domain along `(x, t) ↦ (t, -x)` recovers the exponential
epigraph domain. -/
theorem preimage_negLogEpigraphBarrierDomain_eq_exponentialEpigraphBarrierDomain :
    exponentialEpigraphAffine ⁻¹' (ofZ ⁻¹' interior Q₁) =
      ofZ ⁻¹' interior exponentialEpigraphQ2 := by
  ext z
  change (exponentialEpigraphAffine z).ofLp ∈ interior Q₁ ↔ z.ofLp ∈ interior exponentialEpigraphQ2
  rw [exponentialEpigraphAffine_apply, mem_interior_constrainedEpigraph_negLog_iff,
    mem_interior_exponentialEpigraphQ2_iff]
  constructor
  · rintro ⟨ht, hx⟩
    have hxt : z.ofLp.1 < Real.log z.ofLp.2 := by linarith
    exact (Real.lt_log_iff_exp_lt ht).mp hxt
  · intro h
    have ht : 0 < z.ofLp.2 := lt_trans (Real.exp_pos z.ofLp.1) h
    have hxt : z.ofLp.1 < Real.log z.ofLp.2 := (Real.lt_log_iff_exp_lt ht).mpr h
    constructor
    · exact ht
    · linarith

-- Proof sketch: apply the owner affine-pullback theorem from Theorem 5.3.3 to the established
-- `2`-self-concordant barrier for the `-\log` epigraph from Theorem 5.4.8.2 using the affine
-- involution `(x, t) ↦ (t, -x)`. The domain bridge identifies the pulled-back `-\log` epigraph
-- interior with `interior exponentialEpigraphQ2`, and the barrier bridge identifies the pulled-
-- back barrier with `exponentialEpigraphBarrierF2`.
/-- Theorem 5.4.8.3: the function `F₂(x, t) = -log t - log (log t - x)` is a
`2`-self-concordant barrier for the exponential epigraph
`Q₂ = {(x, t) ∈ ℝ² | t ≥ e^x}`, viewed on the canonical `L²` product owner
`Z = WithLp 2 (ℝ × ℝ)` through `z ↦ z.ofLp`. This is the affine pullback of
Theorem 5.4.8.2 along `(x, t) ↦ (t, -x)`. -/
theorem exponentialEpigraphBarrierF2_is_two_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior exponentialEpigraphQ2)
      (2 : NNReal)
      (fun z : Z ↦ exponentialEpigraphBarrierF2 z.ofLp) := by
  simpa [Function.comp,
    preimage_negLogEpigraphBarrierDomain_eq_exponentialEpigraphBarrierDomain]
    using
      epigraphLogBarrier_negLog_is_two_selfConcordantBarrier.comp_continuousAffineMap
        exponentialEpigraphAffine

/-! ### Theorem_5_4_8_4 (from Chap05) -/
noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

/- Theorem 5.4.8.4 lies in the Chapter 5 self-concordant-barrier / epigraph domain for
`x ↦ x log x`.

Sampled owner declarations:
* `entropyEpigraphCone`, `entropyEpigraphConeBarrier`, and
  `entropyEpigraphConeBarrier_is_three_self_concordant_barrier` from `Theorem_5_4_7_6`, the
  upstream Chapter 5 owner/view for the entropy-epigraph cone and its canonical `3`-barrier;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the chapter
  owner theorem for affine pullbacks of self-concordant barriers;
* `Q₃` and `mem_Q₃_iff` from `Definition_5_4_8_9`, the source-facing owner/view for the textbook
  epigraph;
* `separableLogBarrierF3` and `separableLogBarrierF3_apply` from `Definition_5_4_8_10`, the
  source-facing owner/view for `F₃`.

Best owner abstraction:
* source-facing: the textbook epigraph `Q₃` and barrier `F₃`;
* core/canonical: `entropyEpigraphConeBarrier_is_three_self_concordant_barrier` together with
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`;
* bridge/view: the affine slice `((x, 1), t)` identifying `Q₃` and `F₃` with the upstream cone
  and barrier owners.

Primitive data:
* the canonical source-facing owners `Q₃` and `F₃`;
* the upstream cone/barrier owners from `Theorem_5_4_7_6`.

Derived API:
* the slice-domain bridge `((x, 1), t) ∈ interior entropyEpigraphCone ↔ (x, t) ∈ interior Q₃`;
* the direct slice identity `F₃ (x, t) = entropyEpigraphConeBarrier ((x, 1), t)`;
* the source-facing `3`-self-concordant-barrier theorem for `F₃`, obtained as an affine pullback.

This file therefore keeps `Q₃` and `F₃` source-facing, but removes the impression of a second
independent owner-level barrier theorem by presenting them through the `x₂ = 1` affine slice of
the upstream entropy-epigraph cone barrier. -/

local notation "F₃" => separableLogBarrierF3

-- Proof sketch: `interior entropyEpigraphCone` is the strict version of the entropy-epigraph
-- cone inequalities. On the slice `x₂ = 1`, this becomes `x > 0` and `t > x log x`, which is
-- exactly `interior Q₃`.
/-- On the affine slice `((x, 1), t)`, membership in `interior entropyEpigraphCone` is exactly
membership in `interior Q₃`. -/
theorem mem_interior_entropyEpigraphCone_secondUnitSlice_iff (x t : ℝ) :
    ((x, 1), t) ∈ interior entropyEpigraphCone ↔ (x, t) ∈ interior Q₃ := sorry

-- Proof sketch: the interior of the canonical closed epigraph from Definition 5.4.8.9 is
-- obtained by replacing the boundary inequalities `x ≥ 0` and `t ≥ x log x` with the strict
-- inequalities `x > 0` and `t > x log x`.
/-- A pair `(x, t)` lies in the interior of the canonical epigraph for Definition 5.4.8.9
exactly when `x > 0` and `t > x log x`. -/
theorem mem_interior_constrainedEpigraph_xlogx_iff {x t : ℝ} :
    (x, t) ∈ interior Q₃ ↔
      0 < x ∧ t > x * Real.log x := sorry

-- Proof sketch: identify the interior of the canonical closed epigraph from
-- Definition 5.4.8.9 with the affine slice `x₂ = 1` of the canonical entropy-epigraph cone
-- from Theorem 5.4.7.6. The upstream barrier theorem pulls back along the affine map
-- `p ↦ ((p.1, 1), p.2)`, and the slice-domain bridge together with the defining slice formula
-- for `F₃` identify the result with the source-facing owners `Q₃` and `F₃`.
/-- Theorem 5.4.8.4: the function `F₃(x, t) = -\log x - \log (t - x \log x)` is a
`3`-self-concordant barrier for the epigraph
`Q₃ = {(x, t) ∈ \mathbb{R}^2 \mid x ≥ 0,\ t ≥ x \log x}` of `x \log x`, with the convention
`0 \log 0 = 0`. -/
theorem separableLogBarrierF3_is_three_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith (interior Q₃) (3 : NNReal) F₃ := by
  let g : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).toContinuousAffineMap +ᵥ
      ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (1 : ℝ)), (0 : ℝ))
  have hg_apply (p : ℝ × ℝ) : g p = ((p.1, 1), p.2) := by
    simp [g]
  let hslice :
      IsSelfConcordantBarrierOnWith
        (g ⁻¹' interior entropyEpigraphCone)
        (3 : NNReal)
        (entropyEpigraphConeBarrier ∘ g) :=
    entropyEpigraphConeBarrier_is_three_self_concordant_barrier.comp_continuousAffineMap
      g
  have hdom : g ⁻¹' interior entropyEpigraphCone = interior Q₃ := by
    ext p
    change g p ∈ interior entropyEpigraphCone ↔ p ∈ interior Q₃
    rw [hg_apply]
    simpa using mem_interior_entropyEpigraphCone_secondUnitSlice_iff p.1 p.2
  have hfun : entropyEpigraphConeBarrier ∘ g = F₃ := by
    funext p
    change entropyEpigraphConeBarrier (g p) = F₃ p
    rw [hg_apply]
    change separableLogBarrierF3 p = separableLogBarrierF3 p
    rfl
  simpa [hdom, hfun] using hslice
