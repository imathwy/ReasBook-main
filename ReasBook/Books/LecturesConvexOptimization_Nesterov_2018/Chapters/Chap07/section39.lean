import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_39 (from Chap07) -/
noncomputable section

open scoped Gradient PositiveDefMatrixNorm SmoothConvex

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 7.39 lies in constrained smooth convex minimization on `ℝⁿ` with a weighted
Euclidean norm.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for the
  primitive feasible-set and objective data;
- `ConvexC1SeminormSmooth` in `Chap02/Theorem_2_5`, the canonical owner for convex `C¹`
  objectives with a gradient-Lipschitz bound relative to a seminorm and its dual norm;
- `positiveDefMatrixNorm` in `Chap07/Definition_7_23`, the source-facing weighted seminorm
  attached to a positive-definite matrix;
- `Definition_3_64`, which keeps the feasible-set side on the ambient constrained owner rather
  than duplicating that data inside a second objective wrapper.

Best owner abstraction:
- source-facing: `CompositeSmoothConvexMinimizationProblem`;
- core/canonical: `SetConstrainedMinimizationProblem E` for `Q` and `φ`, together with
  `ConvexC1SeminormSmooth (positiveDefMatrixNorm G hG) L φ`;
- bridge/view: the notations `‖·‖[G]` and `‖·‖[G,*]` supplied by `positiveDefMatrixNorm`.

Primitive data:
- the feasible set and objective, owned by `SetConstrainedMinimizationProblem E`;
- a positive-definite matrix `G`;
- a positive Lipschitz constant encoded canonically by `NNRealˣ`;
- nonemptiness, closedness, and convexity of the feasible set;
- the single smoothness owner witness for the objective.

Derived API:
- whole-space convexity of the objective;
- whole-space differentiability of the objective;
- the weighted dual-norm gradient-Lipschitz inequality.

The previous version stored the objective-side convexity, differentiability, and
gradient-Lipschitz properties as separate primitive fields. This refinement keeps the
source-facing problem structure, but moves the ambient problem data onto
`SetConstrainedMinimizationProblem` and the smoothness package onto the canonical Chapter 2 owner
`ConvexC1SeminormSmooth`. -/

/-- Definition 7.39: a composite smooth convex minimization problem consists of a nonempty closed
convex feasible set `Q ⊆ ℝⁿ`, a convex differentiable objective `φ : ℝⁿ → ℝ`, a positive-definite
matrix `G` defining the weighted norm `‖·‖_G`, and a positive constant `L` such that
`‖∇φ(x) - ∇φ(y)‖*_G ≤ L ‖x - y‖_G` for all `x, y ∈ ℝⁿ`. The feasible-set and objective pair is
owned canonically by `SetConstrainedMinimizationProblem`, and the objective-side smoothness data
is owned by `ConvexC1SeminormSmooth` for the weighted seminorm from Definition 7.23. -/
structure CompositeSmoothConvexMinimizationProblem (n : ℕ)
    extends SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  /-- The positive-definite matrix defining the weighted norm `‖·‖_G`. -/
  metricMatrix : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}
  /-- The Lipschitz constant `L > 0`, encoded canonically as a positive nonnegative real. -/
  lipschitzConstant : NNRealˣ
  /-- The feasible set `Q` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The objective belongs to the weighted smooth-convex class
  `𝓕[(L : NNReal), positiveDefMatrixNorm G]¹¹`. -/
  objective_smooth :
    ConvexC1SeminormSmooth
      (positiveDefMatrixNorm metricMatrix.1 metricMatrix.2)
      (lipschitzConstant : NNReal)
      objective

namespace CompositeSmoothConvexMinimizationProblem

variable {n : ℕ}

/-- A composite smooth convex minimization problem can be used as its underlying objective
function. -/
instance : CoeFun (CompositeSmoothConvexMinimizationProblem n)
    (fun _ ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

@[simp] theorem coe_apply
    (problem : CompositeSmoothConvexMinimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n)) :
    problem x = problem.objective x :=
  rfl

/-- The objective lies in the weighted smooth-convex class attached to `problem.metricMatrix`
with constant `problem.lipschitzConstant`. -/
theorem objective_mem_F11
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    problem.objective ∈
      𝓕[(problem.lipschitzConstant : NNReal),
        positiveDefMatrixNorm problem.metricMatrix.1 problem.metricMatrix.2]¹¹ := by
  simpa [mem_F11_iff] using problem.objective_smooth

/-- The objective of a composite smooth convex minimization problem is convex on all of `ℝⁿ`. -/
theorem objective_convex
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    ConvexOn ℝ Set.univ problem.objective :=
  problem.objective_smooth.convexOn

/-- The objective of a composite smooth convex minimization problem is differentiable on all of
`ℝⁿ`. -/
theorem objective_differentiable
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    Differentiable ℝ problem.objective :=
  let hcontDiff : ContDiff ℝ 1 problem.objective := problem.objective_smooth.contDiff
  hcontDiff.differentiable_one

/-- The weighted smoothness constant is strictly positive because it is encoded by `NNRealˣ`. -/
theorem lipschitzConstant_pos
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    0 < (problem.lipschitzConstant : ℝ) := by
  exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero problem.lipschitzConstant))

/-- The gradient of the objective is `(problem.lipschitzConstant)`-Lipschitz from the weighted
norm `‖·‖[problem.metricMatrix]` to the dual norm `‖·‖[problem.metricMatrix,*]`. -/
theorem gradient_lipschitz
    (problem : CompositeSmoothConvexMinimizationProblem n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖∇ problem.objective x - ∇ problem.objective y‖[problem.metricMatrix,*] ≤
      (problem.lipschitzConstant : ℝ) * ‖x - y‖[problem.metricMatrix] := by
  simpa using problem.objective_smooth.dualNorm_gradient_sub_le x y

end CompositeSmoothConvexMinimizationProblem

/-! ### Proposition_7_39 (from Chap07) -/
universe u

section

variable {X : Type u}

/- Proposition 7.39 lies in Chapter 7's relative-scale / scalar iteration-bound domain.

Mandatory domain-style sampling before refinement:
- `relativeScaleIterationBound` in `Proposition_7_40`, the Chapter 7 owner of the logarithmic
  threshold `R_n(δ)`;
- `relativeScaleIterationBound_def` in `Proposition_7_40`, the canonical bridge from the owner to
  the textbook logarithmic formula;
- `relativeScaleIterationBound_lt_uniformBound` in `Proposition_7_40`, the sibling scalar theorem
  in the same domain using the same positivity structure;
- `IsRelativeAccuracy` in `Definition_7_1`, the chapter owner for two-sided relative accuracy.

Best owner abstraction:
- source-facing: Proposition 7.39's upper bound `f(x_k^*) ≤ (1 + δ) f^*` under the mixed scalar
  estimate and the iteration threshold;
- core/canonical: the scalar threshold owner `relativeScaleIterationBound`;
- bridge/view: `relativeScaleIterationBound_def`.

Primitive data:
- the objective `f`, the best point `xkStar`, the positive dimension `n : ℕ+`, and the scalars
  `δ`, `L`, `R`, `fStar`, `k`;
- the source estimate `hEstimate`.

Derived API:
- the owner-level lower bound `relativeScaleIterationBound n δ L R fStar ≤ k`;
- the induced exponential lower bound on
  `Real.exp (δ * (k + 1) / n) - 1`.

The target theorem is source-facing rather than a new owner: it proves only the upper relative
bound and does not carry the lower bound `fStar ≤ f xkStar` needed for the chapter owner
`IsRelativeAccuracy`. The refinement therefore keeps the source theorem surface, reuses the owner
`relativeScaleIterationBound` directly, and avoids reintroducing the raw logarithmic formula as a
parallel local declaration.
-/

-- Proof sketch: use the lower bound on `k` to show that the exponential remainder term in the
-- mixed bound is at most `δ * (1 - δ / 2) * fStar²`, so together with the term
-- `δ * (1 / 2) * fStar²` the right-hand side of `hEstimate` is bounded by
-- `δ * (1 - δ) * fStar²`. After dividing by the positive factor `(1 - δ) * fStar`, this yields
-- `f xkStar - fStar ≤ δ * fStar`, hence `f xkStar ≤ (1 + δ) * fStar`.
/-- Proposition 7.39: if `δ ∈ (0, 1 / 2)`, the quasi-Newton best point `x_k^*` satisfies the
estimate
`(1 - δ) (f(x_k^*) - f^*) f^* ≤ δ \hat f(x^*) + L² R² / (2 n (e^{δ (k + 1) / n} - 1))`
with `\hat f(x^*) = (1 / 2) (f^*)²`, and the iteration index `k` is at least
`R_n(δ) = (n / δ) log (1 + L² R² / (n δ (1 - 2δ) (f^*)²))`, then
`f(x_k^*) ≤ (1 + δ) f^*`. -/
theorem quasiNewton_bestPoint_relative_accuracy_of_iterationBound
    (f : X → ℝ) (xkStar : X) (n : ℕ+) (δ L R fStar : ℝ) (k : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hfStar : 0 < fStar)
    (hEstimate :
      (1 - δ) * (f xkStar - fStar) * fStar ≤
        δ * ((1 / 2 : ℝ) * fStar ^ (2 : ℕ)) +
          (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
            (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)))
    (hk : relativeScaleIterationBound n δ L R fStar ≤ (k : ℝ)) :
    f xkStar ≤ (1 + δ) * fStar := by
  let x : ℝ :=
    ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
      (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ)
  let e : ℝ := Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have h_one_sub_δ : 0 < 1 - δ := by
    linarith [hδ.2]
  have h_one_sub_two_δ : 0 < 1 - 2 * δ := by
    linarith [hδ.2]
  have hfStar_sq_pos : 0 < fStar ^ (2 : ℕ) := by
    positivity
  have hscale_pos : 0 < δ * (1 - 2 * δ) * fStar ^ (2 : ℕ) := by
    exact mul_pos (mul_pos hδ.1 h_one_sub_two_δ) hfStar_sq_pos
  have hk_log : Real.log (1 + x) ≤ δ * (k : ℝ) / (n : ℝ) := by
    have hratio_pos : 0 < (n : ℝ) / δ := by
      exact div_pos hn hδ.1
    rw [relativeScaleIterationBound_def] at hk
    have hk_mul : Real.log (1 + x) * ((n : ℝ) / δ) ≤ (k : ℝ) := by
      simpa [x, mul_comm, mul_left_comm, mul_assoc] using hk
    have hk_div : Real.log (1 + x) ≤ (k : ℝ) / ((n : ℝ) / δ) := by
      exact (le_div_iff₀ hratio_pos).2 hk_mul
    have hδ_ne : δ ≠ 0 := hδ.1.ne'
    have hn_ne : (n : ℝ) ≠ 0 := hn.ne'
    have hdiv_eq : (k : ℝ) / ((n : ℝ) / δ) = δ * (k : ℝ) / (n : ℝ) := by
      field_simp [hδ_ne, hn_ne]
    simpa [hdiv_eq] using hk_div
  have hk_step : δ * (k : ℝ) / (n : ℝ) ≤ δ * (((k + 1 : ℕ) : ℝ)) / (n : ℝ) := by
    have hk_cast : (k : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.le_succ k
    have hδn_nonneg : 0 ≤ δ / (n : ℝ) := by
      exact (div_pos hδ.1 hn).le
    have hmul := mul_le_mul_of_nonneg_left hk_cast hδn_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hlog_arg_pos : 0 < 1 + x := by
    linarith
  have hx_le_e : x ≤ e := by
    have h_exp_bound : 1 + x ≤ Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      refine (Real.log_le_iff_le_exp hlog_arg_pos).1 ?_
      exact hk_log.trans hk_step
    linarith [h_exp_bound]
  have he_pos : 0 < e := by
    have harg_pos : 0 < δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
      have hk1_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
        positivity
      exact div_pos (mul_pos hδ.1 hk1_pos) hn
    have hexp_gt_one : 1 < Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      exact (Real.one_lt_exp_iff).2 harg_pos
    linarith
  have hscaled_le :
      (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
          (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ)) ≤
        (n : ℝ) * e := by
    have hx_mul :
        (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
            (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ)) ≤
          e * (n : ℝ) := by
      exact (div_le_iff₀ hn).1 (by
        simpa [x, e, mul_comm, mul_left_comm, mul_assoc] using hx_le_e)
    simpa [mul_comm] using hx_mul
  have hnum_le :
      L ^ (2 : ℕ) * R ^ (2 : ℕ) ≤
        (n : ℝ) * e * (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ)) := by
    exact (div_le_iff₀ hscale_pos).1 hscaled_le
  have hremainder :
      (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * e) ≤
        δ * (1 - 2 * δ) * fStar ^ (2 : ℕ) / 2 := by
    have hden_pos : 0 < 2 * (n : ℝ) * e := by
      exact mul_pos (by positivity) he_pos
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith [hnum_le]
  have hmain :
      (1 - δ) * (f xkStar - fStar) * fStar ≤
        δ * (1 - δ) * fStar ^ (2 : ℕ) := by
    have hEstimate' :
        (1 - δ) * (f xkStar - fStar) * fStar ≤
          δ * ((1 / 2 : ℝ) * fStar ^ (2 : ℕ)) +
            (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * e) := by
      simpa [e] using hEstimate
    have hsum :
        δ * ((1 / 2 : ℝ) * fStar ^ (2 : ℕ)) +
            (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * e) ≤
          δ * (1 - δ) * fStar ^ (2 : ℕ) := by
      nlinarith [hremainder]
    exact hEstimate'.trans hsum
  have hfactor_pos : 0 < (1 - δ) * fStar := by
    exact mul_pos h_one_sub_δ hfStar
  have hgap_div :
      f xkStar - fStar ≤
        (δ * (1 - δ) * fStar ^ (2 : ℕ)) / ((1 - δ) * fStar) := by
    refine (le_div_iff₀ hfactor_pos).2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  have hgap : f xkStar - fStar ≤ δ * fStar := by
    have h_one_sub_δ_ne : 1 - δ ≠ 0 := h_one_sub_δ.ne'
    have hfStar_ne : fStar ≠ 0 := hfStar.ne'
    have hdiv_eq :
        (δ * (1 - δ) * fStar ^ (2 : ℕ)) / ((1 - δ) * fStar) = δ * fStar := by
      field_simp [h_one_sub_δ_ne, hfStar_ne]
    simpa [hdiv_eq] using hgap_div
  nlinarith [hgap]

end
