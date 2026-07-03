import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_12 (from Chap07) -/
noncomputable section

open Matrix
open Seminorm
open scoped BigOperators

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 7.12 lies in the chapter's dual-norm / pullback-seminorm domain.

Sampled owner-style declarations:
- project `Seminorm.dualNorm`
- project `Seminorm.dualNorm_apply`
- mathlib `Seminorm.comp`
- mathlib `normSeminorm`

Best owner abstraction:
- source-facing: `matrixInducedEuclideanSeminorm A`
- core/canonical: `Seminorm.comp (normSeminorm ℝ Eₘ) A.toEuclideanLin`
- bridge/view: `matrixInducedEuclideanSeminorm_apply`,
  `matrixInducedEuclideanSeminorm_isNorm`

Primitive data:
- a matrix `A : Matrix (Fin m) (Fin n) ℝ`

Derived API:
- pointwise evaluation as `x ↦ ‖A x‖`
- the `Seminorm.IsNorm` instance under injectivity of `A.toEuclideanLin`
- the dual norm formula under an explicit full-column-rank hypothesis, through the chapter owner
  `Seminorm.dualNorm`

Source/core/bridge triage:
- source-facing: the seminorm induced on `ℝⁿ` by the Euclidean norm on `ℝᵐ`
- core/canonical: pullback of `normSeminorm` along `A.toEuclideanLin`
- bridge/view: Gram-form and row-pairing formulas, plus the dual-norm formula

This refinement removes the duplicate local `vectorDualNorm` owner and exposes the matrix-induced
object at the canonical seminorm layer. The textbook function `x ↦ ‖A x‖` is now the evaluation
surface of that owner, while duality uses the existing project owner `Seminorm.dualNorm`.
-/

/-- Definition 7.12: the Euclidean seminorm on `ℝⁿ` induced by a matrix `A ∈ ℝ^(m × n)`, namely
the pullback of the Euclidean norm on `ℝᵐ` along `A.toEuclideanLin`. When `A` has full column
rank, the derived theorem `matrixInducedEuclideanSeminorm_isNorm` upgrades this seminorm to the
textbook norm `x ↦ ‖A x‖`. -/
def matrixInducedEuclideanSeminorm (A : Matrix (Fin m) (Fin n) ℝ) : Seminorm ℝ Eₙ :=
  Seminorm.comp (normSeminorm ℝ Eₘ) A.toEuclideanLin

/-- Evaluating the induced seminorm recovers the textbook formula `x ↦ ‖A x‖`. -/
theorem matrixInducedEuclideanSeminorm_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x = ‖A.toEuclideanLin x‖ :=
  rfl

/-- If `A` has full column rank, the induced Euclidean seminorm is a genuine norm. -/
theorem matrixInducedEuclideanSeminorm_isNorm
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) :
    Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) := by
  refine ⟨?_⟩
  intro x hx
  apply hA
  simpa using norm_eq_zero.mp (by
    simpa [matrixInducedEuclideanSeminorm_apply] using hx)

/-- If `A` has full column rank, then the induced Euclidean seminorm vanishes only at the
origin. -/
theorem matrixInducedEuclideanSeminorm_eq_zero_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) {x : Eₙ} :
    matrixInducedEuclideanSeminorm A x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact (matrixInducedEuclideanSeminorm_isNorm A hA).eq_zero_of_map_eq_zero hx
  · rintro rfl
    simp [matrixInducedEuclideanSeminorm_apply]

-- Proof sketch: unfold `matrixInducedEuclideanSeminorm`, rewrite `‖A x‖^2` as
-- `⟪A x, A x⟫`, and identify this with the Gram quadratic form for `Aᵀ A`.
/-- The induced Euclidean seminorm is the square root of the quadratic form associated to the
Gram matrix `G = Aᵀ A`. -/
theorem matrixInducedEuclideanSeminorm_eq_sqrt_gram
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x =
      Real.sqrt (inner ℝ ((A.transpose * A).toEuclideanLin x) x) := sorry

-- Proof sketch: expand the Euclidean norm of `A x` as the sum of the squares of its coordinates;
-- these coordinates are the pairings with the rows of `A`, equivalently the columns of `Aᵀ`.
/-- The induced Euclidean seminorm is the square root of the sum of the squared pairings with the
columns of `Aᵀ`, i.e. the rows of `A`. -/
theorem matrixInducedEuclideanSeminorm_eq_sqrt_sum_row_pairings
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x =
      Real.sqrt (∑ i : Fin m, (A i ⬝ᵥ x.ofLp) ^ (2 : ℕ)) := sorry

/-- If `A` has full column rank, then the dual norm of the induced Euclidean seminorm is
`g ↦ √⟪g, (Aᵀ A)⁻¹ g⟫`. -/
theorem dualNorm_matrixInducedEuclideanSeminorm_eq_sqrt_inverse_gram
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) (g : Eₙ) :
    by
      let _ : Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) :=
        matrixInducedEuclideanSeminorm_isNorm A hA
      exact (matrixInducedEuclideanSeminorm A).dualNorm g =
        Real.sqrt (inner ℝ g (((A.transpose * A)⁻¹).toEuclideanLin g)) := by
  sorry

end

/-! ### Lemma_7_12 (from Chap07) -/
noncomputable section

open scoped BigOperators

universe u v

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [AddCommGroup U] [Module ℝ U]

/- Lemma 7.12 lies in the barrier-subgradient / saddle-representation / Jensen-averaging domain.

Mandatory domain-style sampling:
- `Finset.centerMass` in mathlib, the canonical owner for normalized finite weighted averages;
- `ConcaveOn.le_map_centerMass` and `ConvexOn.map_centerMass_le` in mathlib, the canonical Jensen
  inequalities for passing between averaged points and averaged values;
- `SaddlePointRepresentation` in `Definition_7_59`, the Chapter 7 owner of the saddle data
  `(f, Ψ)`;
- `maximalValueOn` in `Definition_7_56`, the Chapter 7 `EReal` owner for maximization over a
  feasible set;
- `barrierSubgradientWeightSum` and `barrierSubgradientMaximalGap` in `Definition_7_57`, the
  Chapter 7 owners for `S_k` and `ℓ_k⋆`.

Best owner abstraction:
- source-facing: the averaged duality-gap estimate of Lemma 7.12;
- core/canonical: `SaddlePointRepresentation`, `Finset.centerMass`, `maximalValueOn`,
  `barrierSubgradientWeightSum`, and `barrierSubgradientMaximalGap`;
- bridge/view: the textbook symbols `\bar x_k`, `\bar w_k`, and `η`, which here are only views of
  those owners, not separate public declarations.

Primitive data:
- the feasible set `P`, an ambient objective extension `f`, the saddle representation owner
  `representation`, and a minimizing branch `w`;
- the iterate family `x`, chosen subgradients, weights `λ`, and index `k`.

Derived API:
- the primal and dual averages as direct `Finset.centerMass` expressions;
- the dual value as direct use of `maximalValueOn`.

The previous file exposed raw parameters `f`, `Ψ`, and `w` even though Definition 7.59 already
introduced the chapter owner surface for the saddle data. This refinement keeps only the ambient
objective extension `f : E → ℝ` needed to state concavity on the feasible set `P ⊆ E`, moves the
saddle data itself to `SaddlePointRepresentation`, removes the redundant standalone convexity
hypothesis because `ConcaveOn ℝ P f` already contains that convexity, and removes the redundant
owner-level minimizer-selection hypothesis because this averaged-gap estimate uses `w` only
through the assumed model inequality and the resulting weighted averages.
-/

-- Proof sketch: for each iterate `x_i`, use the assumed linearization inequality
-- `Ψ(y, w(x_i)) - f(x_i) ≤ ⟪g_i, y - x_i⟫`, weight by `λ_i`, sum over `i = 0, …, k`,
-- and divide by `S_k`. Then use convexity of the slices `Ψ(y, ·)` to pass from the weighted
-- average of the values `Ψ(y, w(x_i))` to `Ψ(y, \bar w_k)`, identify the resulting supremum with
-- `η(\bar w_k)`, and finally apply concavity of `f` on `P` to bound the weighted average of the
-- primal values by `f(\bar x_k)`.
/-- Lemma 7.12: with the canonical weighted averages
`\bar w_k = (1 / S_k) ∑_{i=0}^k λ_i w(x_i)` and
`\bar x_k = (1 / S_k) ∑_{i=0}^k λ_i x_i`, one has
`η(\bar w_k) - f(\bar x_k) ≤ (1 / S_k) ℓ_k^⋆`. -/
theorem barrierSubgradientAverageDualityGap_le_maximalGap
    {P : Set E} {f : E → ℝ} {representation : SaddlePointRepresentation ↥P U} {w : P → U}
    (hobjective_eq : ∀ y : P, representation y = f y)
    (hf_concave : ConcaveOn ℝ P f)
    (hsaddle_convex : ∀ y : P, ConvexOn ℝ Set.univ (representation.saddleFunction y))
    (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ)
    (hlam_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ lam i)
    (hlam_sum_pos : 0 < barrierSubgradientWeightSum lam k)
    (hsubgradient_model :
      ∀ i ∈ Finset.range (k + 1), ∀ y : P,
        representation.saddleFunction y (w (x i)) - representation (x i) ≤
          inner ℝ (subgradient i) ((y : E) - (x i : E))) :
    maximalValueOn (Set.univ : Set ↥P)
        (fun y ↦
          representation.saddleFunction y
            ((Finset.range (k + 1)).centerMass lam fun i ↦ w (x i))) -
        f ((Finset.range (k + 1)).centerMass lam fun i ↦ (x i : E)) ≤
      barrierSubgradientMaximalGap x subgradient lam k / barrierSubgradientWeightSum lam k := sorry

end

/-! ### Proposition_7_12 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction

universe u v

section Family

variable {ι : Type u}

/- Proposition 7.12 lies in the chapter's symmetric-hull / support-function / finite
max-absolute-linear domain.

Sampled owner-style declarations:
- mathlib `absConvexHull` and `convexHull_union_neg_eq_absConvexHull`;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `ξ[Q]` and `supportFunction_convexHull_eq` in `Chap03/Definition_3_9`.

Best owner abstraction:
- source-facing: the symmetric hull `conv {±aᵢ}` and the finite objective `x ↦ maxᵢ |⟪aᵢ, x⟫|`;
- core/canonical: `absConvexHull ℝ (Set.range a)`, `maxTypeObjective`, and the Chapter 3 support
  function `ξ[Q]`;
- bridge/view: the theorem identifying `conv {±aᵢ}` with `absConvexHull ℝ (Set.range a)` and the
  support-function identity relating the finite max to that canonical hull.

Primitive data:
- a family `a : ι → E`;
- a finite nonempty index type `[Fintype ι] [Nonempty ι]` for the finite max owner.

Derived API:
- the source-facing specialization of mathlib's canonical symmetric-hull bridge
  `convexHull ℝ (Set.range a ∪ Set.range (fun i ↦ -a i)) = absConvexHull ℝ (Set.range a)`;
- the canonical owner evaluation theorem `maxTypeObjective_apply`, specialized to
  `fun i x ↦ |⟪aᵢ, x⟫|`;
- the support-function bridge below.
-/

section Hull

variable {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- The textbook symmetric hull `conv {±aᵢ}` of a family `a` is exactly the canonical absolutely
convex hull of its range. This is the `Set.range` specialization of mathlib's owner theorem
`convexHull_union_neg_eq_absConvexHull`. -/
theorem convexHull_range_union_neg_eq_absConvexHull_range (a : ι → E) :
    convexHull ℝ (Set.range a ∪ Set.range (fun i ↦ -a i)) =
      absConvexHull ℝ (Set.range a) := by
  simpa [Set.neg_range] using
    (convexHull_union_neg_eq_absConvexHull :
      convexHull ℝ (Set.range a ∪ -Set.range a) = absConvexHull ℝ (Set.range a))

end Hull

section Support

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FiniteFamily

variable [Fintype ι] [Nonempty ι]

/-- Companion bridge: the Chapter 3 support function of the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)` is exactly the finite max of the absolute pairings. -/
theorem supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner
    (a : ι → E) (x : E) :
    (ξ[absConvexHull ℝ (Set.range a)] x).toReal =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := sorry

/-- Proposition 7.12 (2): the support function of the symmetric hull `conv {±aᵢ}` is exactly the
finite maximum of the absolute pairings `maxᵢ |⟪aᵢ, x⟫|`. -/
theorem supportFunction_convexHull_range_union_neg_toReal_eq_maxTypeObjective_absInner
    (a : ι → E) (x : E) :
    (ξ[convexHull ℝ (Set.range a ∪ Set.range fun i : ι ↦ -a i)] x).toReal =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  simpa [convexHull_range_union_neg_eq_absConvexHull_range] using
    supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner a x

end FiniteFamily

end Support

end Family

section Ellipsoid

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

-- Proof sketch: Proposition 7.12 is the support-function sandwich induced by the centered
-- ellipsoidal-rounding owner, then rewritten through the symmetric-hull bridge
-- `convexHull_range_union_neg_eq_absConvexHull_range`.
/-- Companion bridge: the lower ellipsoidal bound written for the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)`. -/
theorem ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding_absConvexHull
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    ‖x‖[⟨G, hrounding.posDef⟩] ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  sorry

/-- Proposition 7.12 (1): if the symmetric hull `conv {±aᵢ}` admits a `γ √n`-ellipsoidal
rounding with shape matrix `G`, then `maxᵢ |⟪aᵢ, x⟫|` bounds the `G`-norm of `x` from below. -/
theorem ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun i : Fin (m : ℕ) ↦ -a i)) γ G) :
    ‖x‖[⟨G, hrounding.posDef⟩] ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  have hrounding' : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G := by
    simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hrounding
  simpa using
    ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding_absConvexHull a x
      hrounding'

/- Proposition 7.12 (2) is exactly
`supportFunction_convexHull_range_union_neg_toReal_eq_maxTypeObjective_absInner`. -/

-- Proof sketch: combine the support-function identity
-- `supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner` with the outer
-- inclusion from `hrounding`, then evaluate the support function of the centered ellipsoid
-- `W[(γ * √n)](G)` via the dual norm `‖·‖[⟨G, hrounding.posDef⟩]`.
/-- Companion bridge: the upper ellipsoidal bound written for the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)`. -/
theorem maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  sorry

/-- Proposition 7.12 (3): if the symmetric hull `conv {±aᵢ}` admits a `γ √n`-ellipsoidal
rounding with shape matrix `G`, then `maxᵢ |⟪aᵢ, x⟫|` is bounded above by `γ √n ‖x‖_G`. -/
theorem maxTypeObjective_absInner_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun i : Fin (m : ℕ) ↦ -a i)) γ G) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  have hrounding' : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G := by
    simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hrounding
  simpa using
    maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull a x hrounding'

/-- Companion bridge: the support function of `absConvexHull ℝ (Set.range a)` satisfies the same
upper bound because it is exactly the finite max of the absolute pairings in real form. -/
theorem supportFunction_absConvexHull_range_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    (ξ[absConvexHull ℝ (Set.range a)] x).toReal ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  rw [supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner]
  exact maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull a x hrounding

-- Proof sketch: each generator `a_i` belongs to the symmetric hull `conv {±aᵢ}`, so the outer
-- inclusion from `hrounding` places `a_i` inside `W[(γ * √n)](G)`. Rewriting membership in this
-- centered ellipsoid by `mem_centeredMatrixEllipsoid_iff_dualNorm_le` gives the claimed
-- dual-norm bound.
/-- Each generator `a_i` lies in the outer centered ellipsoid coming from the rounding
hypothesis. Equivalently, its `G`-dual norm is at most `γ √n`. -/
theorem generator_ellipsoidalDualNorm_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (i : Fin (m : ℕ))
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun j : Fin (m : ℕ) ↦ -a j)) γ G) :
    ‖a i‖[⟨G, hrounding.posDef⟩,*] ≤ γ * Real.sqrt (n : ℝ) := by
  sorry

end Ellipsoid

end

/-! ### Theorem_7_12 (from Chap07) -/
noncomputable section

open scoped MatrixGameRelativeScaleNotation StandardSimplex

variable {m n : ℕ+}

local notation "Δₙ" => Δ[(n : ℕ)]
local notation "PosMat" => { G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // Matrix.PosDef G }
local notation "DiagPosMat" =>
  { G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // Matrix.IsDiag G ∧ Matrix.PosDef G }
local notation "Solver" =>
  (Δₙ → ℝ) → ℝ → Set Δₙ → PosMat → Δₙ → ℕ → Δₙ

/- Theorem 7.12 lies in Chapter 7's nonnegative matrix-game / relative-scale outer-iteration
domain.

Sampled owner-style declarations:
- `Δ[n]` in `Chap06/Definition_6_11.lean`, the chapter simplex owner for finite matrix-game
  iterates;
- `matrixGameRelativeScaleIterate`, `matrixGameRelativeScaleTerminates`,
  `matrixGameRelativeScaleStoppingTime`, and `matrixGameRelativeScaleStoppingTime_min` in
  `Algorithm_7_10.lean`, the canonical owner API for the outer orbit and first accepted stage;
- `matrixGameRelativeScaleBlockLength` in `Algorithm_7_10.lean`, the canonical per-stage
  lower-level budget;
- `iterativeSmoothingTotalLowerLevelSteps` and the split statement surface in
  `Theorem_7_11.lean`, the nearby Chapter 7 pattern for stopping-time and total-work bounds;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for terminal relative-value
  accuracy.

Best owner abstraction:
- source-facing: Theorem 7.12's stopping-time, terminal-value, and total-work bounds for the
  nonnegative matrix-game relative-scale method;
- core/canonical: the Algorithm 7.10 owners
  `matrixGameRelativeScaleIterate m S f fμ D δ`,
  `matrixGameRelativeScaleStoppingTime hTerminate`,
  `matrixGameRelativeScaleOutputPoint hTerminate`, and
  `matrixGameRelativeScaleBlockLength m n δ`;
- bridge/view: the derived total lower-level work
  `matrixGameRelativeScaleTotalLowerLevelSteps hTerminate`.

Primitive data:
- the objective `f`, smoothing family `fμ`, diagonal positive-definite matrix data `D`,
  parameter `δ`, lower-level solver `S`, and canonical termination witness `hTerminate`;
- feasibility of the generated orbit, the feasible-set lower bound for `fStar`, the positivity
  regimes `0 < fStar` and `0 < δ`, the initial-value bound, and the terminal relative-gap
  estimate.

Derived API:
- the generated points `\hat x_t`;
- the stopping time `T`;
- the accepted output point `\hat x_T`;
- the total lower-level work up to `T`;
- the optional `IsRelativeAccuracy` packaging of the terminal-value conclusion.

Source/core/bridge triage:
- source-facing: the three atomic theorem clauses below;
- core/canonical: the Algorithm 7.10 orbit, stopping-time, and block-length owners;
- bridge/view: `matrixGameRelativeScaleTotalLowerLevelSteps`.
-/

/-- The total number of lower-level steps used by Algorithm 7.10 up to its canonical stopping
time, assuming that each outer stage uses the canonical block length
`matrixGameRelativeScaleBlockLength m n δ`. -/
def matrixGameRelativeScaleTotalLowerLevelSteps
    {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat} {δ : ℝ}
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ) : ℕ :=
  matrixGameRelativeScaleStoppingTime hTerminate *
    matrixGameRelativeScaleBlockLength m n δ

-- Proof sketch: unfold `matrixGameRelativeScaleTotalLowerLevelSteps`.
/-- Expanding `matrixGameRelativeScaleTotalLowerLevelSteps hTerminate` gives the product of the
canonical stopping time and the canonical per-stage lower-level work budget. -/
theorem matrixGameRelativeScaleTotalLowerLevelSteps_def
    {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat} {δ : ℝ}
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ) :
    matrixGameRelativeScaleTotalLowerLevelSteps hTerminate =
      matrixGameRelativeScaleStoppingTime hTerminate *
        matrixGameRelativeScaleBlockLength m n δ := sorry

section Complexity

variable
  {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat}
  {δ fStar : ℝ} {feasibleSet : Set Δₙ}

local notation "x̂" => x̂[m; S; f; fμ; D | δ]

-- Proof sketch: use `matrixGameRelativeScaleStoppingTime_min hTerminate` to get geometric decay
-- before the accepted stage, evaluate feasibility at the generated points via
-- `hGenerated_feasible`, compare `f*` with the preterminal objective value, and combine this
-- with the initial estimate `f (x̂ 0) ≤ 2 √n fStar`.
/-- Theorem 7.12 (1): if every generated point `\hat x_t` is feasible, feasible points have
objective value at least `f*`, and the initial value satisfies `f(\hat x_0) ≤ 2 √n f*`, then
the stopping time satisfies `T ≤ 1 + log (2 √n)`. -/
theorem matrixGameRelativeScale_stoppingTime_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : Δₙ) (_hx : x ∈ feasibleSet), fStar ≤ f x)
    (hfStar_pos : 0 < fStar)
    (hInitial_value_le :
      f (x̂ 0) ≤ 2 * Real.sqrt (n : ℝ) * fStar) :
    (matrixGameRelativeScaleStoppingTime hTerminate : ℝ) ≤
      1 + Real.log (2 * Real.sqrt (n : ℝ)) := sorry

-- Proof sketch: multiply the terminal relative-gap estimate by `1 + δ`, use `0 < 1 + δ`, and
-- rearrange the resulting inequality to isolate `f x̂T`.
/-- Theorem 7.12 (2): the accepted output point satisfies
`f(\hat x_T) ≤ (1 + δ) f*` once `δ > 0` and the terminal relative-gap estimate from the
relative-scale analysis is available. -/
theorem matrixGameRelativeScale_outputPoint_value_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hδ : 0 < δ)
    (hTerminal_relative_gap :
      f (matrixGameRelativeScaleOutputPoint hTerminate) - fStar ≤
        (δ / (1 + δ)) * f (matrixGameRelativeScaleOutputPoint hTerminate)) :
    f (matrixGameRelativeScaleOutputPoint hTerminate) ≤ (1 + δ) * fStar := sorry

-- Proof sketch: combine Theorem 7.12 (1) with the definition of
-- `matrixGameRelativeScaleTotalLowerLevelSteps` as the product of the canonical stopping time and
-- the canonical block length, then expand the block-length formula.
/-- Theorem 7.12 (3): the total number of lower-level steps does not exceed
`4 e (1 + log (2 √n)) √(2 n log m) (1 + 1 / δ)` under the same feasibility and initial-value
hypotheses together with `δ > 0`. -/
theorem matrixGameRelativeScale_totalLowerLevelSteps_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hδ : 0 < δ)
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : Δₙ) (_hx : x ∈ feasibleSet), fStar ≤ f x)
    (hfStar_pos : 0 < fStar)
    (hInitial_value_le :
      f (x̂ 0) ≤ 2 * Real.sqrt (n : ℝ) * fStar) :
    (matrixGameRelativeScaleTotalLowerLevelSteps hTerminate : ℝ) ≤
      4 * Real.exp 1 * (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
        Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ) := sorry

-- Proof sketch: package the lower and upper bounds on `f x̂T` together with `0 < fStar` into the
-- three conjuncts defining `IsRelativeAccuracy`.
/-- If the optimal value `f*` is positive and the accepted output value is already known to lie
between `f*` and `(1 + δ) f*`, then the output value in Theorem 7.12 has relative accuracy `δ`
in the sense of Definition 7.1. -/
theorem matrixGameRelativeScale_outputPoint_isRelativeAccuracy
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hfStar_pos : 0 < fStar)
    (hOutput_value_ge : fStar ≤ f (matrixGameRelativeScaleOutputPoint hTerminate))
    (hOutput_value_le :
      f (matrixGameRelativeScaleOutputPoint hTerminate) ≤ (1 + δ) * fStar) :
    IsRelativeAccuracy fStar δ (f (matrixGameRelativeScaleOutputPoint hTerminate)) := sorry

end Complexity
