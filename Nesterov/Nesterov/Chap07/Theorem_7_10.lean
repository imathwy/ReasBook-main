import Mathlib
import Nesterov.Chap07.Definition_7_35
import Nesterov.Chap07.Lemma_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ} {m : ℕ+}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMatₙ" => { G : Matₙ // Matrix.PosDef G }

/- Theorem 7.10 lies in Chapter 7's sign-invariant diagonal-rounding / stopping-time domain.

Sampled owner-style declarations:
- `signSymmetricConvexHull` and `averageDiagonalSquare` in `Definition_7_35.lean`, the Chapter 7
  owners for the source hull `Conv ⋃ᵢ B(aᵢ)` and its canonical diagonal initialization;
- `ellipsoidBoxInterpolationMatrix` and `ellipsoidBoxLogVolumePotential` in
  `Definition_7_34.lean`, the source-facing one-step matrix update and its logarithmic potential;
- `ellipsoidBoxAlphaStar`, `ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison`, and
  `ellipsoidBoxGammaComparison_neg` in `Lemma_7_7.lean`, the canonical Chapter 7 step-size and
  potential-comparison API;
- `CentralSymmetricRoundingMethod` in `Algorithm_7_5.lean` and
  `CentralSymmetricRoundingMethod.stoppingIndex_le` in `Theorem_7_6.lean`, the nearby owner-level
  pattern where the algorithm object carries the primitive iteration data and the stopping time is
  derived canonically as a first-hit index.

Best owner abstraction:
- source-facing: the sign-invariant rounding method itself, with the canonical initialization
  `D₀ = averageDiagonalSquare a` and the recursive update scheme `(7.2.18)`;
- core/canonical: `signSymmetricConvexHull`, `averageDiagonalSquare`,
  `ellipsoidBoxInterpolationMatrix`, `ellipsoidBoxAlphaStar`, and
  `ellipsoidBoxLogVolumePotential`;
- bridge/view: the potential-drop comparison from Lemma 7.7, applied along the continuing
  iterations of the method.

Primitive data:
- the generating family `a₁, …, aₘ`;
- the current-state dual-norm maximizer choice on positive-definite matrices;
- the positivity of the canonical initial matrix and of each recursive update step.

Derived API:
- the recursive positive-definite orbit `D₀, D₁, …` with
  `D₀ = averageDiagonalSquare a` and
  `Dₖ₊₁ = ellipsoidBoxInterpolationMatrix Dₖ gₖ αₖ`;
- the chosen points `gₖ`;
- the dual radius `rₖ = max {‖g‖*_{Dₖ} | g ∈ signSymmetricConvexHull a}` realized by `gₖ`;
- the step size `αₖ = ellipsoidBoxAlphaStar Dₖ gₖ`;
- the one-step logarithmic drop `ellipsoidBoxLogVolumePotential Dₖ gₖ αₖ`;
- the stopping criterion `rₖ ≤ γ √n` and its canonical first stopping time.

The previous version used a public wrapper whose primitive fields were arbitrary sequences. This
refinement follows the Chapter 7 iterate-owner pattern instead: the public owner is the recursive
sign-invariant algorithm itself, the maximizer property is primitive owner data rather than a
downstream theorem hypothesis, and the matrix/radius/stopping-time API is derived canonically from
that recursion.
-/

section PotentialDrop

variable {potential : ℕ → ℝ}

-- Proof sketch: iterate `hstep` to obtain
-- `potential k ≤ potential 0 - k * drop` for every `k ≤ Nat.find hTerminate`. The defining
-- property of `Nat.find hTerminate` supplies the first nonpositive index, and minimality excludes
-- earlier stopping. Combine this with the initial bound `potential 0 ≤ B`, the nonnegativity
-- `0 ≤ B`, and divide by `drop > 0`.
/-- A potential sequence that starts below an explicit nonnegative bound `B` and decreases by at
least a fixed positive amount `δ` at every continuing step must terminate after at most `δ⁻¹ B`
steps. -/
theorem stoppingTime_le_of_positive_drop
    (hTerminate : ∃ k : ℕ, potential k ≤ 0)
    (B drop : ℝ)
    (hdrop : 0 < drop)
    (hinitial : potential 0 ≤ B)
    (hB : 0 ≤ B)
    (hstep :
      ∀ k : ℕ, k < Nat.find hTerminate →
        potential (k + 1) ≤ potential k - drop) :
    (Nat.find hTerminate : ℝ) ≤ drop⁻¹ * B := sorry

end PotentialDrop

/-- A sign-invariant diagonal rounding algorithm for the family `a₁, …, aₘ` is determined by the
canonical initial matrix `D₀ = averageDiagonalSquare a`, a choice of a current dual-norm
maximizer `gₖ ∈ signSymmetricConvexHull a` from each positive-definite matrix state, and the
requirement that the Chapter 7 update `(7.2.18)` stays positive definite. The actual orbit
`D₀, D₁, …`, the chosen points `g₀, g₁, …`, and the stopping time for the radius threshold are
derived recursively from this source-facing owner.
-/
structure SignInvariantRoundingAlgorithm where
  /-- The generating family `a₁, …, aₘ`. -/
  vectors : Fin (m : ℕ) → EuclideanSpace ℝ (Fin n)
  /-- The canonical initial matrix `D₀ = averageDiagonalSquare a` is positive definite. -/
  initial_posDef : (averageDiagonalSquare vectors).PosDef
  /-- The current-state choice of the point `gₖ ∈ signSymmetricConvexHull a`. -/
  selectMaximizer : PosMatₙ → Eₙ
  /-- Every chosen point lies in the generated sign-symmetric hull and maximizes the current
  `G`-dual norm there. -/
  selectMaximizer_spec :
    ∀ G : PosMatₙ,
      selectMaximizer G ∈ signSymmetricConvexHull vectors ∧
        IsMaxOn (fun g : Eₙ ↦ ‖g‖[G,*]) (signSymmetricConvexHull vectors) (selectMaximizer G)
  /-- The recursive update `(7.2.18)` remains positive definite at every positive-definite state.
  -/
  step_posDef :
    ∀ G : PosMatₙ,
      (ellipsoidBoxInterpolationMatrix G.1 (selectMaximizer G)
        (ellipsoidBoxAlphaStar G.1 G.2 (selectMaximizer G))).PosDef

namespace SignInvariantRoundingAlgorithm

local notation "SignAlg" => @SignInvariantRoundingAlgorithm n m

/-- The sign-symmetric hull generated by the input family `a₁, …, aₘ`. -/
def generatedSet (algorithm : SignAlg) : Set Eₙ :=
  signSymmetricConvexHull algorithm.vectors

/-- The current positive-definite matrix owner at stage `0`. -/
def initialMatrix (algorithm : SignAlg) : PosMatₙ :=
  ⟨averageDiagonalSquare algorithm.vectors, algorithm.initial_posDef⟩

/-- The Chapter 7 step size `α*(D, g)` attached to a positive-definite matrix state `D` and its
selected maximizer `g`. -/
def stepAlpha
    (algorithm : SignAlg) (G : PosMatₙ) : ℝ :=
  ellipsoidBoxAlphaStar G.1 G.2 (algorithm.selectMaximizer G)

/-- The one-step recursive update `(7.2.18)` on positive-definite matrix states. -/
def step
    (algorithm : SignAlg) (G : PosMatₙ) : PosMatₙ :=
  ⟨ellipsoidBoxInterpolationMatrix G.1 (algorithm.selectMaximizer G) (algorithm.stepAlpha G),
    algorithm.step_posDef G⟩

/-- The recursive positive-definite matrix orbit `D₀, D₁, D₂, ...` generated by the sign-
invariant rounding update. -/
def currentMatrix
    (algorithm : SignAlg) : ℕ → PosMatₙ :=
  fun k ↦ (algorithm.step^[k]) (algorithm.initialMatrix)

/-- A sign-invariant rounding algorithm can be used as its underlying matrix orbit
`D₀, D₁, D₂, ...`. -/
instance : CoeFun SignAlg (fun _ ↦ ℕ → Matₙ) where
  coe algorithm k := (algorithm.currentMatrix k).1

/-- The algorithm starts from the canonical Chapter 7 initialization
`D₀ = averageDiagonalSquare a`. -/
@[simp] theorem matrix_zero
    (algorithm : SignAlg) :
    algorithm 0 = averageDiagonalSquare algorithm.vectors :=
  rfl

/-- The recursive orbit at stage `0` is the canonical initial positive-definite matrix owner. -/
@[simp] theorem currentMatrix_zero
    (algorithm : SignAlg) :
    algorithm.currentMatrix 0 = algorithm.initialMatrix :=
  rfl

/-- The chosen point `gₖ` at stage `k` is the state-dependent maximizer selected from `Dₖ`. -/
def maximizer (algorithm : SignAlg) (k : ℕ) : Eₙ :=
  algorithm.selectMaximizer (algorithm.currentMatrix k)

/-- Every chosen point belongs to the generated sign-symmetric hull. -/
theorem maximizer_mem_generatedSet
    (algorithm : SignAlg) (k : ℕ) :
    algorithm.maximizer k ∈ generatedSet algorithm :=
  (algorithm.selectMaximizer_spec (algorithm.currentMatrix k)).1

/-- At stage `k`, the chosen point maximizes the current dual norm on the generated
sign-symmetric hull. -/
theorem maximizer_isMaxOn_generatedSet
    (algorithm : SignAlg) (k : ℕ) :
    IsMaxOn
      (fun g : Eₙ ↦ ‖g‖[algorithm.currentMatrix k,*])
      (generatedSet algorithm)
      (algorithm.maximizer k) :=
  (algorithm.selectMaximizer_spec (algorithm.currentMatrix k)).2

/-- The recursive matrix orbit satisfies the Chapter 7 successor update `(7.2.18)`. -/
theorem matrix_succ
    (algorithm : SignAlg) (k : ℕ) :
    algorithm (k + 1) =
      ellipsoidBoxInterpolationMatrix (algorithm k) (algorithm.maximizer k)
        (algorithm.stepAlpha (algorithm.currentMatrix k)) := by
  simpa [currentMatrix, step, stepAlpha, maximizer] using
    congrArg Subtype.val
      (Function.iterate_succ_apply' algorithm.step k algorithm.initialMatrix)

/-- The positive-definite matrix owner at stage `k + 1` is obtained by one application of the
recursive update step. -/
theorem currentMatrix_succ
    (algorithm : SignAlg) (k : ℕ) :
    algorithm.currentMatrix (k + 1) = algorithm.step (algorithm.currentMatrix k) := by
  simpa [currentMatrix] using
    Function.iterate_succ_apply' algorithm.step k algorithm.initialMatrix

/-- The Chapter 7 step size `αₖ = α*(Dₖ, gₖ)`. -/
def alpha (algorithm : SignAlg) (k : ℕ) : ℝ :=
  algorithm.stepAlpha (algorithm.currentMatrix k)

/-- The maximal dual radius `rₖ = max {‖g‖*_{Dₖ} | g ∈ signSymmetricConvexHull a}` realized by
the chosen maximizer `gₖ`. -/
def radius (algorithm : SignAlg) (k : ℕ) : ℝ :=
  ‖algorithm.maximizer k‖[algorithm.currentMatrix k,*]

/-- Every point of the generated sign-symmetric hull has current dual norm at most the stage-`k`
radius. -/
theorem dualNorm_le_radius
    (algorithm : SignAlg) (k : ℕ) {g : Eₙ}
    (hg : g ∈ generatedSet algorithm) :
    ‖g‖[algorithm.currentMatrix k,*] ≤ algorithm.radius k :=
  (algorithm.maximizer_isMaxOn_generatedSet k) hg

/-- The one-step logarithmic potential contribution at stage `k`. -/
def potentialStep (algorithm : SignAlg) (k : ℕ) : ℝ :=
  ellipsoidBoxLogVolumePotential (algorithm k) (algorithm.maximizer k) (algorithm.alpha k)

/-- The remaining logarithmic-volume budget
`B - (log det Dₖ - log det D₀)` at stage `k`, measured against the canonical matrix orbit of the
sign-invariant rounding algorithm. -/
def remainingLogVolumeBudget
    (algorithm : SignAlg) (B : ℝ) (k : ℕ) : ℝ :=
  B - (Real.log (Matrix.det (algorithm k)) - Real.log (Matrix.det (algorithm 0)))

/-- At stage `0`, the remaining logarithmic-volume budget is exactly the initial budget `B`. -/
@[simp] theorem remainingLogVolumeBudget_zero
    (algorithm : SignAlg) (B : ℝ) :
    algorithm.remainingLogVolumeBudget B 0 = B := by
  simp [remainingLogVolumeBudget]

/-- Advancing one sign-invariant rounding step decreases the remaining logarithmic-volume budget by
exactly the Chapter 7 one-step potential `ellipsoidBoxLogVolumePotential Dₖ gₖ αₖ`. -/
theorem remainingLogVolumeBudget_succ
    (algorithm : SignAlg) (B : ℝ) (k : ℕ) :
    algorithm.remainingLogVolumeBudget B (k + 1) =
      algorithm.remainingLogVolumeBudget B k + algorithm.potentialStep k := sorry

/-- The stopping criterion from Theorem 7.10: the stage-`k` dual radius is at most `γ √n`. -/
def stoppingCriterion (algorithm : SignAlg) (γ : ℝ) (k : ℕ) : Prop :=
  algorithm.radius k ≤ γ * Real.sqrt (n : ℝ)

/-- The algorithm terminates once some iterate satisfies the radius threshold `rₖ ≤ γ √n`. -/
def Terminates (algorithm : SignAlg) (γ : ℝ) : Prop :=
  ∃ k : ℕ, algorithm.stoppingCriterion γ k

/-- The canonical stopping time is the first iterate satisfying the stopping criterion
`rₖ ≤ γ √n`. -/
noncomputable def stoppingTime
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) : ℕ := by
  classical
  exact Nat.find hTerminate

/-- The first stopping time is least with respect to the radius threshold. -/
theorem stoppingTime_isLeast
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) :
    IsLeast {k : ℕ | algorithm.stoppingCriterion γ k} (algorithm.stoppingTime hTerminate) := by
  classical
  simpa [stoppingTime, Terminates] using Nat.isLeast_find hTerminate

/-- The stopping test succeeds at the canonical stopping time. -/
theorem stoppingTime_spec
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) :
    algorithm.stoppingCriterion γ (algorithm.stoppingTime hTerminate) :=
  (algorithm.stoppingTime_isLeast hTerminate).1

/-- No earlier stage satisfies the stopping criterion. -/
theorem stoppingTime_min
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    ¬ algorithm.stoppingCriterion γ k := by
  exact fun hkStop ↦
    (not_le_of_gt hk) ((algorithm.stoppingTime_isLeast hTerminate).2 hkStop)

/-- Before the canonical stopping time, the current dual radius is strictly larger than
`γ √n`. -/
theorem threshold_lt_radius_of_lt_stoppingTime
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    γ * Real.sqrt (n : ℝ) < algorithm.radius k := by
  exact lt_of_not_ge <| by
    simpa [stoppingCriterion] using algorithm.stoppingTime_min hTerminate hk

-- Proof sketch: apply the abstract helper `stoppingTime_le_of_positive_drop` to the canonical
-- remaining logarithmic-volume budget
-- `B - (log det Dₖ - log det D₀)` with
-- `B = n (log n + 2 log m)`. At the canonical stopping time, use
-- `hremaining_nonpos_of_stopping`; before that time, positivity comes from
-- `hremaining_pos_of_continuing` together with
-- `threshold_lt_radius_of_lt_stoppingTime`. The recursion step for the remaining budget is
-- `remainingLogVolumeBudget_succ`, and the one-step drop is bounded above by
-- `ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison` on continuing iterates. Combining
-- this with `ellipsoidBoxGammaComparison_neg` yields the uniform positive decrease
-- `((γ² - 1) / γ² - log (1 + (γ² - 1) / γ²))`. The initial budget at stage `0` is exactly `B`,
-- and `0 ≤ B` follows from `hn` and `m.2`.
/-- Theorem 7.10: if a sign-invariant recursive rounding algorithm `(7.2.18)` has the Chapter 7
remaining logarithmic-volume budget
`n (log n + 2 log m) - (log det Dₖ - log det D₀)`, if that canonical budget is positive at every
genuinely continuing iterate `rₖ > γ √n` and nonpositive at every iterate satisfying the
threshold `rₖ ≤ γ √n`, and if the continuing steps satisfy the Chapter 7 potential comparison
with parameter `γ ≥ √(1 + 1 / √n)`, then the canonical first stopping time for the threshold
`rₖ ≤ γ √n` is at most
`[(γ² - 1) / γ² - log (1 + (γ² - 1) / γ²)]⁻¹ n (log n + 2 log m)` steps. -/
theorem stoppingTime_le
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    (hTerminate : algorithm.Terminates γ)
    (hremaining_pos_of_continuing :
      ∀ k : ℕ,
        γ * Real.sqrt (n : ℝ) < algorithm.radius k →
          0 < algorithm.remainingLogVolumeBudget
            ((n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))) k)
    (hremaining_nonpos_of_stopping :
      ∀ k : ℕ,
        algorithm.stoppingCriterion γ k →
          algorithm.remainingLogVolumeBudget
            ((n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))) k ≤ 0) :
    (algorithm.stoppingTime hTerminate : ℝ) ≤
      (((γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
          Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)))⁻¹ *
        (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))) := sorry

end SignInvariantRoundingAlgorithm

end
