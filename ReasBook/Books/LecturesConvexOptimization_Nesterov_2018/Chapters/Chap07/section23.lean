import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_23 (from Chap07) -/
noncomputable section

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 7.23 lies in the positive-definite matrix / induced-norm domain.

Sampled owner-style declarations:
- `LinearMap.BilinForm.primalSeminorm` in `Chap04/Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm` in `Chap04/Definition_4_3_4`
- `Matrix.toEuclideanLin` in mathlib
- `Matrix.toBilin'` in mathlib, for the coordinate-space matrix bilinear-form owner
- `Matrix.PosDef.toQuadraticForm'` in mathlib

Best owner abstraction:
- source-facing: the norm induced on `ℝⁿ` by a positive-definite matrix `G`
- core/canonical: the Chapter 4 bilinear-form owner
  `LinearMap.BilinForm.primalSeminorm B`
- bridge/view: the canonical Euclidean-space bilinear form induced by `Matrix.toEuclideanLin G`

Primitive data:
- a matrix `G : Matrix (Fin n) (Fin n) ℝ`
- its positive-definiteness proof `hG : G.PosDef`

Derived API:
- the source-facing seminorm owner `positiveDefMatrixNorm G hG`
- the source-facing notation `‖x‖[⟨G, hG⟩]`
- the canonical dual notation `‖s‖[⟨G, hG⟩,*]`
- the inverse-matrix formula `√⟪s, G⁻¹ s⟫`

Source/core/bridge triage:
- source-facing: Definition 7.23's matrix-induced norm
- core/canonical: `LinearMap.BilinForm.primalSeminorm` and `Seminorm.dualNorm`
- bridge/view: the bilinear form attached to `Matrix.toEuclideanLin`

This refinement removes the duplicate public matrix-to-bilinear-form owner and the notation-only
wrapper abbrevs. The source-facing matrix object remains a `Seminorm`, defined directly from the
canonical Euclidean linear operator attached to the matrix, and the dual norm is reused from the
Chapter 2 owner
`Seminorm.dualNorm`.
-/

private def matrixBilin (G : Matrix (Fin n) (Fin n) ℝ) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (Matrix.toEuclideanLin G).toContinuousLinearMap).toBilinForm

private theorem matrixToBilinForm_isSymm_of_posDef
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (matrixBilin G).IsSymm := by
  sorry

private theorem matrixToBilinForm_posDef_of_posDef
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (matrixBilin G).toQuadraticMap.PosDef := by
  sorry

/-- Definition 7.23 in owner form: a positive-definite matrix `G` induces the canonical seminorm
`x ↦ √⟪Gx, x⟫` on `ℝⁿ`. -/
def positiveDefMatrixNorm
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    Seminorm ℝ E :=
  LinearMap.BilinForm.primalSeminorm
    (matrixBilin G)
    (matrixToBilinForm_posDef_of_posDef G hG)

instance positiveDefMatrixNorm_isNorm
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (positiveDefMatrixNorm G hG).IsNorm :=
  by
    simpa [positiveDefMatrixNorm] using
      (LinearMap.BilinForm.primalSeminorm_isNorm
        (matrixBilin G)
        (matrixToBilinForm_posDef_of_posDef G hG))

namespace PositiveDefMatrixNorm

/- Lean notation for the primal norm induced by a positive-definite matrix. -/
scoped notation:max "‖" x "‖[" G "]" =>
  positiveDefMatrixNorm (Subtype.val G) (Subtype.property G) x

/- Lean notation for the dual norm induced by a positive-definite matrix. -/
scoped notation:max "‖" s "‖[" G ",*]" =>
  Seminorm.dualNorm (positiveDefMatrixNorm (Subtype.val G) (Subtype.property G)) s

end PositiveDefMatrixNorm

open scoped PositiveDefMatrixNorm

-- Proof sketch: `positiveDefMatrixNorm G hG` is the Chapter 4 bilinear-form-induced seminorm for
-- the Euclidean bilinear form associated with `Matrix.toEuclideanLin G`, whose pointwise formula
-- is exactly `√⟪Gx, x⟫`.
/-- Evaluating `positiveDefMatrixNorm G hG` recovers the textbook formula `√⟪Gx, x⟫`. -/
theorem positiveDefMatrixNorm_def
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x : E) :
    ‖x‖[G] =
      Real.sqrt (inner ℝ ((Matrix.toEuclideanLin G.1) x) x) := by
  sorry

-- Proof sketch: the dual norm is the chapter owner `Seminorm.dualNorm`, so its defining
-- support-function formula is the canonical theorem `Seminorm.dualNorm_apply`.
/-- The dual norm of `positiveDefMatrixNorm G hG` is the support function of the `G`-unit ball. -/
theorem positiveDefMatrixNorm_dualNorm_apply
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    ‖s‖[G,*] =
      sSup ((fun x : E ↦ inner ℝ s x) '' {x | ‖x‖[G] ≤ 1}) := by
  sorry

-- Proof sketch: compare the Chapter 2 support-function definition of
-- `(positiveDefMatrixNorm G hG).dualNorm` with the Chapter 4 strong-dual owner for the bilinear
-- form induced by `Matrix.toEuclideanLin G`, then evaluate that owner by the inverse-matrix
-- formula.
/-- The dual norm of `positiveDefMatrixNorm G hG` is `√⟪s, G⁻¹ s⟫`. -/
theorem positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    ‖s‖[G,*] =
      Real.sqrt (inner ℝ s ((Matrix.toEuclideanLin G.1⁻¹) s)) := by
  sorry

end

/-! ### Lemma_7_23 (from Chap07) -/
open scoped BigOperators

/-
Lemma 7.23 lies in the scalar recurrence / partial-sum accumulation domain.

Sampled owner-style declarations:
* current mathlib's ordered-field scalar bundle `[Field α] [LinearOrder α]
  [IsStrictOrderedRing α]`, which replaces the old bundled `LinearOrderedField` owner in this
  environment and is the canonical scalar layer for the recurrence and `nlinarith` step;
* mathlib `Finset.sum_range_zero`, the canonical base-case owner for sums over `Finset.range 0`;
* mathlib `Finset.sum_range_succ`, the canonical step decomposition of a partial sum on
  `Finset.range`;
* project `estimating_function_le_weighted_transformed_objective_add_initial` in `Lemma_7_21`,
  the nearby Chapter 7 recurrence-accumulation pattern;
* project `accumulatedWeights` in `Chap06/Definition_6_53`, the chapter owner for inclusive
  accumulated sums.

Best owner abstraction:
* source-facing: the lower recursion for the optimal values `ψ_k^*`;
* core/canonical: the current mathlib ordered-field scalar bundle together with the `Finset.range`
  partial-sum API;
* bridge/view: `accumulatedWeights (fun i ↦ a i * hatF i)` is the natural chapter bridge for
  inclusive sums, but it is not the main owner here because the textbook statement is intrinsically
  the source-facing predecessor partial sum `∑_{i=0}^{k-1} a_i \hat f(x_i)`.

Primitive data:
* the scalar sequences `ψStar`, `a`, `hatF`, and `dualGradNormSq`;
* the initial lower bound `0 ≤ ψStar 0`;
* the one-step recursion and progress identity.

Derived API:
* the accumulated lower bound for `ψ_k^*`.

No upstream project theorem has this exact stage-dependent lower-recursion interface, so the file
keeps the source-facing statement and uses the canonical `Finset.range` owner directly rather than
introducing a parallel wrapper.
-/

-- Proof sketch: argue by induction on `k`. The base case is `hzero`, since the sum over
-- `Finset.range 0` is zero. For the induction step, apply `hupdate` at stage `k`, substitute the
-- progress identity `hprogress k` to rewrite the quadratic loss term as `δ a_k \hat f(x_k)`, and
-- then combine the inductive lower bound with the decomposition of the sum over
-- `Finset.range (k + 1)`.
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Lemma 7.23: if the optimal values `ψStar k = ψ_k^*` of the quasi-Newton estimating functions
satisfy the one-step lower recursion induced by the update `(7.4.12)` and the progress identity
`(7.4.15)`, then
`ψ_k^* ≥ (1 - δ) * ∑_{i=0}^{k-1} a_i \hat f(x_i)`. Here `hatF k` abbreviates `\hat f(x_k)` and
`dualGradNormSq k` abbreviates `(\| \hat g(x_k) \|_{G_{k+1}}^*)^2`. -/
theorem quasiNewtonEstimatingOptimalValue_lower_bound
    (ψStar a hatF dualGradNormSq : ℕ → α) (δ : α)
    (hzero : 0 ≤ ψStar 0)
    (hupdate :
      ∀ k : ℕ,
        ψStar (k + 1) ≥
          ψStar k + a k * hatF k - (1 / 2 : α) * (a k) ^ (2 : ℕ) * dualGradNormSq k)
    (hprogress :
      ∀ k : ℕ,
        (1 / 2 : α) * (a k) ^ (2 : ℕ) * dualGradNormSq k = δ * a k * hatF k)
    (k : ℕ) :
    ψStar k ≥ (1 - δ) * (∑ i ∈ Finset.range k, a i * hatF i) := by
  induction k with
  | zero =>
      simpa using hzero
  | succ k ih =>
      have hstep :
          ψStar (k + 1) ≥ ψStar k + (1 - δ) * (a k * hatF k) := by
        have hupdate' := hupdate k
        rw [hprogress k] at hupdate'
        nlinarith
      have hsum :
          ψStar (k + 1) ≥
            (1 - δ) * (∑ i ∈ Finset.range k, a i * hatF i) + (1 - δ) * (a k * hatF k) := by
        nlinarith
      simpa [Finset.sum_range_succ, mul_add, add_comm, add_left_comm, add_assoc] using hsum

/-! ### Proposition_7_23 (from Chap07) -/
noncomputable section

universe u

section

variable {X : Type u}

/- Proposition 7.23 lies in Chapter 7's relative-accuracy / constrained-optimal-value transfer
domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  real-valued objective on a feasible set;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  constrained optimal-value owner;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_7`,
  the defining bridge to the infimum of the feasible value image in `EReal`;
- `inducedObjectiveInf` and `inducedRadiusInf` in `Chap07/Proposition_7_22`, the nearby chapter
  pattern using the same owner together with a `.toReal` bridge back to textbook real inequalities.

Best owner abstraction:
- source-facing: transfer of a relative-accuracy bound from the smoothed objective `f_p` to the
  original objective `φ` on the same feasible set;
- core/canonical: `(.mk Q f : SetConstrainedMinimizationProblem X).optimalValue`;
- bridge/view: the pointwise sandwich between `φ` and `f_p`.

Primitive data:
- a feasible set `Q : Set X`;
- the two objectives `φ` and `f_p`;
- a positive smoothing order `p : ℕ+`;
- the candidate point `yBar ∈ Q`;
- the feasible-set nonnegativity of `φ`;
- the pointwise lower and upper comparisons between `φ` and `f_p` on `Q`.

Derived API:
- the constrained optimization owners `(.mk Q φ : SetConstrainedMinimizationProblem X)` and
  `(.mk Q f_p : SetConstrainedMinimizationProblem X)`;
- the textbook real surfaces `((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal`
  and `((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal`;
- the relative-accuracy inequalities stated using those owners.

This refinement removes the duplicate local real-valued optimal-value wheel from the public
surface. The constrained minima of `φ` and `f_p` are canonically owned by
`SetConstrainedMinimizationProblem.optimalValue`; the proposition uses only the minimal `.toReal`
bridge needed to recover the textbook real inequalities from those owner values.
-/

-- Proof sketch: combine the feasible-set nonnegativity of `φ` with the pointwise bounds to get
-- `φ yBar ≤ sqrt (2 * f_p yBar)` and
-- `sqrt (2 * ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal) ≤
--   r^(1 / (2p)) * ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal`,
-- then use
-- `f_p yBar ≤ (1 + δ) *
--   ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal`.
-- The condition
-- `((1 + δ) / δ) * log r ≤ p` implies `r^(1 / (2p)) ≤ sqrt (1 + δ)` when `r > 1`; for `r ≤ 1`,
-- the factor `r^(1 / (2p))` only decreases the right-hand side, so the same conclusion is easier.
-- Thus
-- `φ yBar / ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal ≤
--   r^(1 / (2p)) * sqrt (1 + δ) ≤ 1 + δ`.
/-- Proposition 7.23: if `p` is a positive smoothing order, `f_p` lies between
`(1 / 2) φ^2` and `(1 / 2) r^(1 / p) φ^2` on the feasible set `Q`, and `yBar ∈ Q` is
`(1 + δ)`-optimal for `f_p`, then `yBar` is also `(1 + δ)`-optimal for `φ`, with both optimal
values read from the canonical Chapter 1 constrained optimization owner and projected back to `ℝ`
via `.toReal`. -/
theorem relative_accuracy_transfer_from_fp_to_phi
    (Q : Set X) (φ f_p : X → ℝ) (δ r : ℝ) (p : ℕ+) (yBar : X)
    (hyBar_mem : yBar ∈ Q)
    (hδ : 0 < δ)
    (hφ_nonneg : ∀ y ∈ Q, 0 ≤ φ y)
    (h_lower : ∀ y ∈ Q, (1 / 2 : ℝ) * φ y ^ (2 : ℕ) ≤ f_p y)
    (h_upper : ∀ y ∈ Q,
      f_p y ≤ (1 / 2 : ℝ) * Real.rpow r (1 / (p : ℝ)) * φ y ^ (2 : ℕ))
    (hp : ((1 + δ) / δ) * Real.log r ≤ (p : ℝ))
    (hyBar :
      f_p yBar ≤
        (1 + δ) * ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal) :
    φ yBar ≤
      (1 + δ) * ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal := sorry

end
