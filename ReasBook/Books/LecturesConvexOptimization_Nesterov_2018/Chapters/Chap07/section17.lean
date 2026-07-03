import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_17 (from Chap07) -/
noncomputable section

open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

variable {n : ℕ}

/- Definition 7.17 lies in Chapter 7's symmetric-matrix spectral-radius domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, the chapter owner for real symmetric matrices;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the derived ordered-eigenvalue API on `𝕊^n`;
- mathlib `spectralRadius`, the canonical spectral-radius owner;
- mathlib `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, the Hermitian-to-eigenvalue
  bridge behind the source-facing formula.

Best owner abstraction:
- source-facing: the real-valued spectral radius of a symmetric matrix;
- core/canonical: `spectralRadius`;
- bridge/view: the eigenvalue-supremum theorem below, expressed through the chapter owner
  `eigenvalues`.

Primitive data:
- `X : 𝕊^n`

Derived API:
- the source-facing notation `ρ(X)` for the real-valued spectral radius
- the ordered eigenvalue family `eigenvalues X`

Source/core/bridge triage:
- source-facing: Definition 7.17's real-valued spectral-radius surface on `𝕊^n`;
- core/canonical: `spectralRadius`;
- bridge/view: `realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues`.

This file therefore removes the duplicate public alias `symmetricMatrixSpectralRadius`, keeps the
canonical owner `spectralRadius`, and adds the textbook source-facing notation `ρ(X)` on the
chapter carrier `𝕊^n`. The eigenvalue formula remains expressed via the existing Chapter 5 owner
`eigenvalues`.
-/

scoped[RealSymmetricMatrixSpace] notation "ρ(" X ")" =>
  ENNReal.toReal (spectralRadius ℝ (Subtype.val X))

section

variable (n : ℕ)

/- Definition 7.17: for `X ∈ 𝕊^n`, the spectral radius is the real number `ρ(X)`. -/
#check (fun X : 𝕊^n ↦ ρ(X))

end

-- Proof sketch: the Hermitian spectral theorem identifies the real spectrum of a symmetric
-- matrix with its ordered eigenvalues, and the spectral radius is the supremum of the absolute
-- values of spectral points.
/-- The spectral radius of a real symmetric matrix is the maximum absolute value of its
eigenvalues, written as a supremum over the finite index type `Fin n`. -/
theorem realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues
    (X : 𝕊^n) :
    ρ(X) = ⨆ i : Fin n, |eigenvalues X i| := by
  sorry

/-! ### Lemma_7_17 (from Chap07) -/
noncomputable section

open scoped SupportFunction

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 7.17 lies in the chapter's support-function / subdifferential positivity domain.

Mandatory domain-style sampling before refinement:
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`, the chapter owner for support
  functions of sets;
- `supportFunction_dom_eq_univ_of_nonempty_bounded` in `Chap03/Proposition_3_11`, the bounded-set
  finiteness theorem for that owner;
- `ConvexBody.supportFunctionReal` in `Chap07/Definition_7_24`, the convex-body `toReal` bridge
  showing that Chapter 7 treats real-valued support functions through the Chapter 3 owner;
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the source-facing positivity predicate for
  real-valued functions.

Best owner abstraction:
- source-facing: Lemma 7.17 as a `StrictlyPositiveOn` statement for a centrally symmetric support
  function;
- core/canonical: the chapter support-function owner `ξ[S]`;
- bridge/view: the real-valued support-function surface `fun x ↦ (ξ[S] x).toReal`.

Primitive data:
- a set `S : Set E`;
- nonemptiness, boundedness, and central symmetry of `S`.

Derived API:
- the real-valued support function `fun x ↦ (ξ[S] x).toReal`, justified by
  `supportFunction_dom_eq_univ_of_nonempty_bounded`;
- the `StrictlyPositiveOn` conclusion on `Set.univ`.

The previous version stated the support function through a raw `sSup ((fun s ↦ ⟪s, x⟫) '' S)`
formula even though the chapter already owns this notion as `ξ[S]` and Chapter 7 already uses the
`toReal` bridge for real-valued support functions. This refinement keeps the source-facing
positivity theorem but moves it to the canonical owner surface, drops the redundant closedness
hypothesis from the public API, and replaces the over-concrete `EuclideanSpace ℝ (Fin n)` ambient
model by the standard real inner-product-space layer. The `.toReal` bridge is kept only under the
finite-value hypothesis supplied by nonemptiness together with boundedness.
-/

-- Proof sketch: let `f x = (ξ[S] x).toReal`. For `g ∈ ∂ f(x)`, use the subgradient inequality at
-- `y` together with the support-function subgradient characterization to identify `g` with a
-- support point of `S` at `x`. Central symmetry gives `-g ∈ S`, hence
-- `f y = (ξ[S] y).toReal ≥ ⟪-g, y⟫`. Rearranging yields
-- `0 ≤ f y + f x + ⟪g, y - x⟫`.
/-- Lemma 7.17: the real-valued support-function surface `x ↦ (ξ[S] x).toReal` of a nonempty
bounded centrally symmetric set is strictly positive on the whole space in the sense of
Definition 7.81. At this owner level, closedness is redundant because the support function depends
only on the closed convex hull of `S`, while nonemptiness is essential to keep the `.toReal`
bridge faithful. -/
theorem supportFunction_strictlyPositiveOn_univ_of_nonempty_bounded_centrallySymmetric
    (S : Set E) (hS_nonempty : S.Nonempty) (hS_bounded : Bornology.IsBounded S)
    (hS_centrallySymmetric : ∀ ⦃s : E⦄, s ∈ S → -s ∈ S) :
    StrictlyPositiveOn Set.univ (fun x ↦ (ξ[S] x).toReal) := sorry

end

/-! ### Proposition_7_17 (from Chap07) -/
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

/-! ### Theorem_7_17 (from Chap07) -/
open scoped BigOperators

noncomputable section

universe u

section

variable {X : Type u}

/- Theorem 7.17 lies in the Chapter 7 finite-horizon geometric-mean / barrier-rate bridge
domain.

Mandatory domain-style sampling:
- `dynamicStrategyAverageRateOfGrowth` in `Chap07/Definition_7_74`, the source-facing owner for
  the realized dynamic geometric mean along a finite horizon;
- `staticProductionAverageEfficiency` in `Chap07/Definition_7_73`, the chapter owner for the
  static geometric mean on the same horizon;
- `positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate` in
  `Chap07/Theorem_7_16`, the canonical exponentiation bridge from a logarithmic average estimate
  to a geometric-mean lower bound;
- `barrierSubgradientRelativeAccuracyDelta` in `Chap07/Theorem_7_16`, the owner of the explicit
  Chapter 7 rate term.

Best owner abstraction:
- source-facing: the dynamic-vs-static finite-horizon comparison from Theorem 7.17;
- core/canonical: `dynamicStrategyAverageRateOfGrowth`, `staticProductionAverageEfficiency`, and
  the generic bridge theorem
  `positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate`;
- bridge/view: the conversion between the chapter's finite-horizon `Fin`-indexed trace and the
  generic `ℕ`-indexed geometric-mean bridge, together with the asymptotic theorem for
  `barrierSubgradientRelativeAccuracyDelta`.

Primitive data:
- the feasible subtype `P`;
- the horizon `N`;
- the positive outputs `ψ`;
- the realized dynamic trace `x`;
- the comparison static point `xStatic`.

Derived API:
- the dynamic geometric mean `dynamicStrategyAverageRateOfGrowth ψ x`;
- the static geometric mean `staticProductionAverageEfficiency ψ xStatic`;
- the explicit error rate `barrierSubgradientRelativeAccuracyDelta`.

Source/core/bridge triage:
- source-facing: `dynamicStrategyAverageRateOfGrowth_ge_optimalStaticEfficiency_mul_exp_neg_delta`,
  which compares the dynamic owner to the canonical optimal static efficiency;
- core/canonical: `IsMaxOn`, `sSup`, and the generic theorem from `Theorem_7_16`;
- bridge/view:
  `dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap`
  and the asymptotic vanishing statement for the explicit rate.
-/

-- Proof sketch: rewrite the logarithmic average of the dynamic outputs as the logarithm of
-- `dynamicStrategyAverageRateOfGrowth ψ x`, then exponentiate the assumed logarithmic comparison
-- with the static average efficiency at the supplied comparison point.
/-- Exponentiating a logarithmic comparison estimate at a fixed static strategy `xStatic` yields
the corresponding geometric-mean lower bound for the dynamic strategy. This is the bridge/view
step used in Theorem `7.17` after choosing an optimal static strategy via Definition `7.73`. -/
theorem dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P)
    (xStatic : P)
    {ν : ℝ}
    (hlog_rate :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ)) / ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N) :
    dynamicStrategyAverageRateOfGrowth ψ x ≥
      staticProductionAverageEfficiency ψ xStatic *
        Real.exp (-barrierSubgradientRelativeAccuracyDelta ν N) := by
  let outputs : Fin (N + 1) → {r : ℝ // 0 < r} := fun k ↦ ψ k (x k)
  let indices : ℕ → Fin (N + 1) := fun i ↦ ⟨i % (N + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hStaticPos : 0 < staticProductionAverageEfficiency ψ xStatic := by
    rw [staticProductionAverageEfficiency_def, staticProductionTotalOutput_def]
    exact Real.rpow_pos_of_pos (Finset.prod_pos fun k _ ↦ (ψ k xStatic).property) _
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun i ↦ Real.log (outputs (indices i) : ℝ)) =
        ∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun i ↦ Real.log (outputs (indices i) : ℝ))
          = ∑ k : Fin (N + 1), Real.log (outputs (indices k) : ℝ) := by
              simpa using
                (Fin.sum_univ_eq_sum_range (fun i ↦ Real.log (outputs (indices i) : ℝ))
                  (N + 1)).symm
      _ = ∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        simp [outputs, indices, Nat.mod_eq_of_lt k.2]
  have hprod :
      (∏ k : Fin (N + 1), (ψ k (x k) : ℝ)) =
        Finset.prod (Finset.range (N + 1)) (fun i ↦ (outputs (indices i) : ℝ)) := by
    calc
      (∏ k : Fin (N + 1), (ψ k (x k) : ℝ))
          = ∏ k : Fin (N + 1), (outputs (indices k) : ℝ) := by
              refine Finset.prod_congr rfl fun k _ ↦ ?_
              simp [outputs, indices, Nat.mod_eq_of_lt k.2]
      _ = Finset.prod (Finset.range (N + 1)) (fun i ↦ (outputs (indices i) : ℝ)) := by
        simpa using
          (Fin.prod_univ_eq_prod_range (fun i ↦ (outputs (indices i) : ℝ)) (N + 1))
  have hlog_rate' :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (Finset.sum (Finset.range (N + 1)) fun i ↦ Real.log (outputs (indices i) : ℝ)) /
            ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N := by
    simpa [hsum] using hlog_rate
  have hbridge :=
    positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate
      outputs
      indices
      ⟨staticProductionAverageEfficiency ψ xStatic, hStaticPos⟩
      N
      hlog_rate'
  have hdynamic :
      dynamicStrategyAverageRateOfGrowth ψ x =
        Real.rpow
          (Finset.prod (Finset.range (N + 1)) fun i ↦ (outputs (indices i) : ℝ))
          ((1 : ℝ) / (N + 1 : ℝ)) := by
    rw [dynamicStrategyAverageRateOfGrowth_def, ← hprod]
  rw [positiveIterateGeometricMean_def] at hbridge
  simpa [hdynamic] using hbridge

/-- If `xStatic` maximizes the static cumulative output from Definition `7.73`, then it also
maximizes the derived static geometric-mean efficiency. -/
theorem staticProductionAverageEfficiency_isMaxOn_of_staticProductionTotalOutput_isMaxOn
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic) :
    IsMaxOn (staticProductionAverageEfficiency ψ) Set.univ xStatic := by
  rw [isMaxOn_univ_iff] at hoptimal ⊢
  intro y
  rw [staticProductionAverageEfficiency_def, staticProductionAverageEfficiency_def]
  have hy_nonneg : 0 ≤ staticProductionTotalOutput ψ y := by
    rw [staticProductionTotalOutput_def]
    exact le_of_lt (Finset.prod_pos fun k _ ↦ (ψ k y).property)
  exact Real.rpow_le_rpow
    hy_nonneg
    (hoptimal y)
    (by positivity)

/-- An optimal static strategy realizes the canonical optimal static efficiency, expressed as the
supremum of all static geometric-mean efficiencies over the feasible subtype `P`. -/
theorem staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic) :
    sSup (Set.range (staticProductionAverageEfficiency ψ)) =
      staticProductionAverageEfficiency ψ xStatic := by
  have hoptimalEfficiency :
      IsMaxOn (staticProductionAverageEfficiency ψ) Set.univ xStatic :=
    staticProductionAverageEfficiency_isMaxOn_of_staticProductionTotalOutput_isMaxOn ψ xStatic
      hoptimal
  have hne : (Set.range (staticProductionAverageEfficiency ψ)).Nonempty :=
    ⟨_, xStatic, rfl⟩
  have hbdd : BddAbove (Set.range (staticProductionAverageEfficiency ψ)) := by
    refine ⟨staticProductionAverageEfficiency ψ xStatic, ?_⟩
    rintro y ⟨z, rfl⟩
    exact (isMaxOn_univ_iff.mp hoptimalEfficiency z)
  apply le_antisymm
  · refine csSup_le hne ?_
    rintro y ⟨z, rfl⟩
    exact (isMaxOn_univ_iff.mp hoptimalEfficiency z)
  · exact le_csSup hbdd ⟨xStatic, rfl⟩

-- Proof sketch: use Definition `7.73` to identify the comparison point with an optimal static
-- strategy, rewrite its efficiency as the canonical supremum of all static efficiencies, and then
-- apply the one-point exponentiation bridge above.
/-- Theorem 7.17: if `xStatic` is an optimal static strategy in the sense of Definition `7.73`
and the barrier-subgradient logarithmic comparison estimate is available at that optimizer, then
the dynamic average rate of growth is at least the canonical optimal static efficiency times
`exp (-δ_N)`. -/
theorem dynamicStrategyAverageRateOfGrowth_ge_optimalStaticEfficiency_mul_exp_neg_delta
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P)
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic)
    {ν : ℝ}
    (hlog_rate :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ)) / ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N) :
    dynamicStrategyAverageRateOfGrowth ψ x ≥
      sSup (Set.range (staticProductionAverageEfficiency ψ)) *
        Real.exp (-barrierSubgradientRelativeAccuracyDelta ν N) := by
  rw [staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy ψ xStatic hoptimal]
  exact
    dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap
      ψ x xStatic hlog_rate

-- Proof sketch: use that both `(N + 1)⁻¹/²` and `(N + 1)⁻¹` tend to `0` as `N → ∞`, the
-- logarithmic factor grows only like `log (√N)`, and then combine these asymptotics in the
-- owner `barrierSubgradientRelativeAccuracyDelta ν N`.
/-- The explicit barrier-subgradient relative-accuracy term tends to `0` as the horizon tends to
infinity. -/
theorem barrierSubgradientRelativeAccuracyDelta_tendsto_zero
    (ν : NNReal) :
    Filter.Tendsto
      (fun N : ℕ ↦ barrierSubgradientRelativeAccuracyDelta (ν : ℝ) N)
      Filter.atTop (nhds 0) := sorry

end
