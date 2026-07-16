import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Algorithm_7_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics Filter

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.17 lies in Chapter 7's finite max-absolute-linear / ellipsoidal-rounding
complexity domain.

Sampled owner-style declarations:
- `CentralSymmetryRoundingAlgorithm` in `Algorithm_7_6`, the Chapter 7 source-facing owner of the
  finite-family iterative rounding run attached to `a₁, …, aₘ`;
- `CentralSymmetricRoundingMethod.stoppingIndex_isLeast` in `Algorithm_7_5`, the canonical
  first-hit stopping owner for the underlying centrally symmetric rounding method;
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- `IsEllipsoidalRounding` in `Definition_7_29`, the chapter owner for centered
  `γ √n`-ellipsoidal roundings;
- `convexHull_range_union_neg_eq_absConvexHull_range` in `Proposition_7_12`, the bridge from the
  textbook symmetric hull `conv {± aᵢ}` to the canonical owner `absConvexHull ℝ (Set.range a)`.

Best owner abstraction:
- source-facing: a run of `CentralSymmetryRoundingAlgorithm` on the finite family
  `a₁, …, aₘ`;
- core/canonical: `IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G` together with the
  first-hit stopping owner of the underlying Chapter 7 method;
- bridge/view: a first-hit witness, the stopping matrix, the explicit stopping-index bound, and
  the total arithmetic-work expression attached to the displayed explicit bound and its
  `O(n² (n + m) log m)` consequence.

Primitive data:
- the family `a : Fin m → E`;
- the admissibility data `1 ≤ n` and positive definiteness of the initial Gram matrix
  `centralSymmetryGramMatrix a`;
- a Chapter 7 run `algorithm : CentralSymmetryRoundingAlgorithm m n`;
- the identification of the run's internal stopping parameter with the textbook parameter `γ`;
- a canonical termination witness for the underlying centrally symmetric rounding method.

Derived API:
- the explicit stopping-index bound
  `maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ`;
- the explicit arithmetic-work bound
  `maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ`;
- the canonical first-hit owner data
  `algorithm.toCentralSymmetricRoundingMethod.Terminates` and
  `algorithm.toCentralSymmetricRoundingMethod.stoppingIndex hTerminate`;
- the stopping matrix
  `algorithm.toCentralSymmetricRoundingMethod
    (algorithm.toCentralSymmetricRoundingMethod.stoppingIndex hTerminate)`;
- the canonical `=O` corollary for the explicit arithmetic-work bound on the admissible domain
  `m ≥ 2`.
- the existence theorem and the asymptotic corollary.

Source/core/bridge triage:
- source-facing: Proposition 7.17's existence claim for a terminating Algorithm 7.6 run on the
  given family `a₁, …, aₘ`;
- core/canonical: `CentralSymmetryRoundingAlgorithm`, `absConvexHull`, and
  `CentralSymmetricRoundingMethod.stoppingIndex_isLeast`, `IsEllipsoidalRounding`, and
  `Asymptotics.IsBigO`;
- bridge/view: the terminal matrix `method (method.stoppingIndex hTerminate)`, the explicit
  stopping-index bound, and the displayed work bound.
-/

/-- The explicit stopping-index upper bound
`(γ² / (γ - 1)²) log m` for the canonical first accepted iterate of the Chapter 7 centrally
symmetric rounding method attached to Proposition 7.17. -/
def maxAbsLinearSubdifferentialRoundingStoppingIndexBound
    (m : ℕ+) (γ : ℝ) : ℝ :=
  (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * Real.log (m : ℝ)

/-- Expanding `maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ` recovers the displayed
stopping-index expression `(γ² / (γ - 1)²) log m`. -/
theorem maxAbsLinearSubdifferentialRoundingStoppingIndexBound_eq
    (m : ℕ+) (γ : ℝ) :
    maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ =
      (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * Real.log (m : ℝ) :=
  rfl

/-- The displayed arithmetic-operation bound obtained by adding the preprocessing cost
`n² (n + 6m) / 6` and the rounding cost
`(γ² / (γ - 1)²) n² (2m + 3n) log m`. -/
def maxAbsLinearSubdifferentialRoundingArithmeticWorkBound
    (m : ℕ+) (n : ℕ) (γ : ℝ) : ℝ :=
  ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
    maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ * (n : ℝ) ^ (2 : ℕ) *
      (2 * (m : ℝ) + 3 * (n : ℝ))

-- Proof sketch: unfold
-- `maxAbsLinearSubdifferentialRoundingArithmeticWorkBound`; the right-hand side is exactly the
-- displayed sum of the preprocessing and rounding contributions.
/-- Expanding `maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ` recovers the explicit
operation-count formula from Proposition 7.17. -/
theorem maxAbsLinearSubdifferentialRoundingArithmeticWorkBound_eq
    (m : ℕ+) (n : ℕ) (γ : ℝ) :
    maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ =
      ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
        (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * (n : ℝ) ^ (2 : ℕ) *
          (2 * (m : ℝ) + 3 * (n : ℝ)) * Real.log (m : ℝ) :=
  by
    simp [maxAbsLinearSubdifferentialRoundingArithmeticWorkBound,
      maxAbsLinearSubdifferentialRoundingStoppingIndexBound, mul_assoc, mul_left_comm, mul_comm]

-- Proof sketch: apply the canonical stopping-index bound for the underlying Chapter 7 method,
-- expressed at the owner-level first accepted iterate `s = method.stoppingIndex hTerminate`,
-- and then use the canonical stopping matrix `method s` as the claimed `γ √n`-ellipsoidal
-- rounding of `absConvexHull ℝ (Set.range a)`.
/-- Proposition 7.17, stopping-index form: in positive dimension, if the Gram matrix
`(1 / m) ∑ᵢ aᵢ aᵢᵀ` of the family `a₁, …, aₘ ∈ ℝⁿ` is positive definite, then the associated
max-absolute-value objective admits a Chapter 7 Algorithm 7.6 run with internal threshold
parameter `γ` whose underlying method terminates, whose canonical first stopping matrix is a
`γ √n`-ellipsoidal rounding of `absConvexHull ℝ (Set.range a)`, and whose canonical first
stopping index is bounded above by `(γ² / (γ - 1)²) log m`. -/
theorem exists_centralSymmetryRoundingAlgorithm_of_maxAbsLinearSubdifferential_stoppingIndex_le
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E) (hn : 1 ≤ n) (hγ : 1 < γ)
    (hGram : (centralSymmetryGramMatrix a).PosDef) :
    ∃ algorithm : CentralSymmetryRoundingAlgorithm (m : ℕ) n,
      let method := algorithm.toCentralSymmetricRoundingMethod
      algorithm.vectors = a ∧
        method.gamma = γ ∧
          ∃ hTerminate : method.Terminates,
            let s := method.stoppingIndex hTerminate
            IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ (method s) ∧
              (s : ℝ) ≤ maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ := sorry

-- Proof sketch: combine the preprocessing bound `n² (n + 6m) / 6` for the quantities defining
-- the subdifferential `∂f(0) = conv {± aᵢ}` with the central-symmetry rounding complexity bound
-- `(γ² / (γ - 1)²) n² (2m + 3n) log m`, and realize the result by a terminating
-- `CentralSymmetryRoundingAlgorithm` with threshold parameter `γ`; termination is expressed on
-- the canonical `CentralSymmetricRoundingMethod.Terminates` surface, and the rounded matrix is
-- evaluated at the canonical first stopping index.
/-- Proposition 7.17: in positive dimension, if the Gram matrix
`(1 / m) ∑ᵢ aᵢ aᵢᵀ` of the family `a₁, …, aₘ ∈ ℝⁿ` is positive definite, then the associated
max-absolute-value objective, whose subdifferential at the origin is the symmetric convex hull
`conv {± aᵢ}`, admits a Chapter 7 Algorithm 7.6 run with internal threshold parameter `γ` whose
underlying Chapter 7 method terminates, whose canonical first stopping index yields a
`γ √n`-ellipsoidal rounding matrix for `absConvexHull ℝ (Set.range a)`, and whose stopping-time
arithmetic-work bound at that canonical first stopping index is at most
`n² (n + 6m) / 6 + (γ² / (γ - 1)²) n² (2m + 3n) log m`
arithmetic operations. -/
theorem exists_centralSymmetryRoundingAlgorithm_of_maxAbsLinearSubdifferential
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E) (hn : 1 ≤ n) (hγ : 1 < γ)
    (hGram : (centralSymmetryGramMatrix a).PosDef) :
    ∃ algorithm : CentralSymmetryRoundingAlgorithm (m : ℕ) n,
      let method := algorithm.toCentralSymmetricRoundingMethod
      algorithm.vectors = a ∧
        method.gamma = γ ∧
          ∃ hTerminate : method.Terminates,
            let s := method.stoppingIndex hTerminate
            IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ (method s) ∧
            ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
                (s : ℝ) * (n : ℝ) ^ (2 : ℕ) *
                  (2 * (m : ℝ) + 3 * (n : ℝ)) ≤
              maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ := sorry

-- Proof sketch: for fixed `γ > 1`, the factor `γ² / (γ - 1)²` is a constant depending only on
-- `γ`. The polynomial factors satisfy
-- `n² (n + 6m) = O(n² (n + m))` and `n² (2m + 3n) = O(n² (n + m))`, so the explicit bound is
-- controlled by `n² (n + m) log m` on the admissible domain `m ≥ 2`; this is stated directly on
-- mathlib's canonical `=O[l]` surface with `l = principal { (m, n) | 2 ≤ m }`.
/-- The explicit arithmetic bound from Proposition 7.17 has growth
`O(n² (n + m) log m)` on the domain `m ≥ 2`, expressed on the canonical `Asymptotics.IsBigO`
surface. -/
theorem maxAbsLinearSubdifferentialRoundingArithmeticWorkBound_isBigO_n_sq_mul_n_add_m_log
    {γ : ℝ} (hγ : 1 < γ) :
    (fun dims : ℕ+ × ℕ ↦
      maxAbsLinearSubdifferentialRoundingArithmeticWorkBound dims.1 dims.2 γ) =O[
        principal (setOf fun dims : ℕ+ × ℕ ↦ 2 ≤ (dims.1 : ℕ))]
      (fun dims ↦
        (dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)) := sorry

end
