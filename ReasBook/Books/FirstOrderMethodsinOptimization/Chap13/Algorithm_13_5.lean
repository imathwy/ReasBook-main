import Mathlib
import FirstOrderMethodsinOptimization.Chap08.Definition_8_2
import FirstOrderMethodsinOptimization.Chap01.Definition_1_31
import FirstOrderMethodsinOptimization.Chap13.Definition_13_6
import FirstOrderMethodsinOptimization.Chap13.Definition_13_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

/- `prompt_add/` is absent in this workspace, so the statement design is checked against the
nearby Chapter 13 owners. Domain sampling for Algorithm 13.5 uses:

- `polytope_quadratic_objective`, `polytope_quadratic_problem`, and
  `polytope_quadratic_feasible_set` from Definition 13.10 as the `core/canonical` quadratic
  model `f_q`, constrained problem `(13.32)`, and feasible polytope `Ω` on the canonical
  Chapter 13 owner `Fin n → ℝ`;
- `positiveDefiniteMatrices n` from Definition 1.31 as the canonical owner for the textbook
  regime `Q ∈ 𝕊_{++}^n`, used only in the bridge and optimality theorems that need the
  positive-definite quadratic geometry behind equation `(13.34)`;
- `unconstrained_problem_solutions` from Chapter 8 as the canonical owner for the finite
  vertex-index argmin set, together with `IsMinOn` for the corresponding minimizer
  characterization and the induced linearized conditional-gradient subproblem on
  `Ω = conv{a₁, …, a_l}`;
- `conditional_gradient_exact_line_search_stepsizes` from Definition 13.6 as the chapter owner
  for exact line search on a segment, with the clipped quadratic ratio from equation `(13.34)`
  treated below as a source-facing bridge into that owner rather than as a second owner;
- the project's set-valued one-step algorithm pattern from Algorithm 11.2 and Algorithm 13.1.

This item is `source-facing`: it chooses a minimizing vertex index, defines the search direction
and the exact-line-search scalar explicitly, and then either stops on the sign test
`⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0` or updates to the next iterate. The helper owners below therefore use the
primitive matrix/point data already sufficient to define their formulas, while the
positive-definite and feasibility assumptions are kept only on the bridge and optimality theorems
that need them. The public API is therefore a small family of concrete helpers together with a
set-valued one-step owner, while optimality of the stopping branch is kept as a separate theorem
rather than primitive algorithmic data. The bridge/view `EuclideanSpace ℝ (Fin n) ≃ Fin n → ℝ`
is not exposed here: Algorithm 13.5 now lives directly on the chapter's quadratic owner type. -/

/-- The vertex-selection objective in Algorithm 13.5, namely
`i ↦ a_iᵀ (Q xᵏ + b)`, equivalently `i ↦ ⟪a_i, ∇ f_q(xᵏ)⟫` in the textbook
positive-definite quadratic setting. -/
def polytope_quadratic_vertex_linear_objective
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) : Fin l → ℝ :=
  fun i ↦ dotProduct (a i) (Q *ᵥ xk + b)

-- Proof sketch: unfold `polytope_quadratic_vertex_linear_objective`; evaluation at `i` is exactly
-- the displayed linearization value `a_iᵀ (Q xᵏ + b)`.
/-- Evaluating the vertex-selection objective at `i` gives `a_iᵀ (Q xᵏ + b)`. -/
@[simp] theorem polytope_quadratic_vertex_linear_objective_apply
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_vertex_linear_objective Q b a xk i =
      dotProduct (a i) (Q *ᵥ xk + b) :=
  rfl

/-- Every vertex `a_i` belongs to the feasible polytope `Ω = conv{a₁, …, a_l}`. -/
theorem polytope_quadratic_vertex_mem_feasible_set
    (a : Fin l → E) (i : Fin l) :
    a i ∈ polytope_quadratic_feasible_set a := by
  exact subset_convexHull ℝ (Set.range a) (Set.mem_range_self i)

-- Proof sketch: a linear functional attains the same minimum on a convex hull as on the
-- generating vertices. Therefore a minimizing vertex index produces a canonical `IsMinOn`
-- witness for the linearized subproblem over `Ω`.
/-- A minimizing vertex index in Algorithm 13.5 yields a canonical minimizer of the linearized
objective over the full feasible polytope `Ω = conv{a₁, …, a_l}`. -/
theorem polytope_quadratic_linearized_isMinOn_feasible_set_of_mem_vertex_argmin
    {Q : Matrix (Fin n) (Fin n) ℝ} {b : E} {a : Fin l → E} {xk : E} {i : Fin l}
    (hi :
      i ∈ unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a xk)) :
    IsMinOn (fun y ↦ dotProduct y (Q *ᵥ xk + b)) (polytope_quadratic_feasible_set a) (a i) := by
  let S : Set E := {y | dotProduct (a i) (Q *ᵥ xk + b) ≤ dotProduct y (Q *ᵥ xk + b)}
  -- First rewrite the discrete argmin certificate as pointwise inequalities on all vertices.
  have hvertices :
      Set.range a ⊆ S := by
    rw [mem_unconstrained_problem_solutions_iff_forall_le] at hi
    intro y hy
    rcases hy with ⟨j, rfl⟩
    simpa [S, polytope_quadratic_vertex_linear_objective_apply] using hi j
  -- Then extend the linear inequality from the vertices to their convex hull.
  have hconvex : Convex ℝ S := by
    intro x hx y hy t₁ t₂ ht₁ ht₂ hsum
    simp only [S, Set.mem_setOf_eq] at hx hy ⊢
    calc
      dotProduct (a i) (Q *ᵥ xk + b) =
          (t₁ + t₂) * dotProduct (a i) (Q *ᵥ xk + b) := by rw [hsum, one_mul]
      _ ≤ t₁ * dotProduct x (Q *ᵥ xk + b) + t₂ * dotProduct y (Q *ᵥ xk + b) := by
        nlinarith
      _ = dotProduct (t₁ • x + t₂ • y) (Q *ᵥ xk + b) := by
        simp [add_dotProduct, smul_dotProduct, dotProduct_add]
        ring
  have hfeasible_subset : polytope_quadratic_feasible_set a ⊆ S := by
    simpa [polytope_quadratic_feasible_set, S] using convexHull_min hvertices hconvex
  rw [isMinOn_iff]
  intro y hy
  exact hfeasible_subset hy

/-- The search direction `dᵏ = a_{i_k} - xᵏ` from Algorithm 13.5. -/
def polytope_quadratic_conditional_gradient_direction
    (a : Fin l → E) (xk : E) (i : Fin l) : E :=
  a i - xk

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_direction`; the result is exactly
-- the difference `a_{i_k} - xᵏ`.
/-- Expanding the search direction gives `a_{i_k} - xᵏ`. -/
@[simp] theorem polytope_quadratic_conditional_gradient_direction_eq
    (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_conditional_gradient_direction a xk i = a i - xk :=
  rfl

/-- The stopping test in Algorithm 13.5 is the directional derivative
`(dᵏ)ᵀ (Q xᵏ + b)` along the chosen vertex direction, equivalently
`⟪dᵏ, ∇ f_q(xᵏ)⟫` in the positive-definite quadratic setting. -/
def polytope_quadratic_conditional_gradient_directional_derivative
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) : ℝ :=
  dotProduct (polytope_quadratic_conditional_gradient_direction a xk i)
    (Q *ᵥ xk + b)

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_directional_derivative`; this is
-- exactly `(dᵏ)ᵀ (Q xᵏ + b)`.
/-- Expanding the stopping test gives `(dᵏ)ᵀ (Q xᵏ + b)`. -/
@[simp] theorem polytope_quadratic_conditional_gradient_directional_derivative_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i =
      dotProduct (polytope_quadratic_conditional_gradient_direction a xk i)
        (Q *ᵥ xk + b) :=
  rfl

/-- The unclipped ratio from equation `(13.34)`,
`λ_k = -⟪dᵏ, ∇ f_q(xᵏ)⟫ / ((dᵏ)^T Q dᵏ)` attached to a matrix `Q`, current point `xᵏ`, and
direction `dᵏ`. On the nonterminal branch of Algorithm 13.5 in the positive-definite quadratic
regime, this is the exact-line-search candidate later clipped to `[0, 1]`. -/
def polytope_quadratic_exact_line_search_ratio
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (xk d : E) : ℝ :=
  -dotProduct d (Q *ᵥ xk + b) / dotProduct d (Q *ᵥ d)

-- Proof sketch: unfold `polytope_quadratic_exact_line_search_ratio`; the declaration is exactly
-- the quotient displayed in equation `(13.34)`.
/-- Expanding `polytope_quadratic_exact_line_search_ratio Q b xᵏ dᵏ` gives the scalar
`-⟪dᵏ, ∇ f_q(xᵏ)⟫ / ((dᵏ)^T Q dᵏ)`. -/
@[simp] theorem polytope_quadratic_exact_line_search_ratio_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (xk d : E) :
    polytope_quadratic_exact_line_search_ratio Q b xk d =
      -dotProduct d (Q *ᵥ xk + b) / dotProduct d (Q *ᵥ d) :=
  rfl

/-- The nonterminal-branch update formula `xᵏ + t_k dᵏ` from Algorithm 13.5, expressed using the
clipped ratio attached to the chosen vertex direction. In Algorithm 13.5 this formula is used on
the branch `⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0`, later specialized to feasible iterates and positive-definite
quadratic data. -/
def polytope_quadratic_conditional_gradient_update
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) : E :=
  let d := polytope_quadratic_conditional_gradient_direction a xk i
  xk + min (polytope_quadratic_exact_line_search_ratio Q b xk d) 1 • d

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_update`; it is definitionally the
-- update `xᵏ + t_k dᵏ` with `dᵏ = a_{i_k} - xᵏ` and `t_k = min {λ_k, 1}`.
/-- Expanding the nonterminal update gives `xᵏ + t_k dᵏ` with the exact-line-search stepsize
attached to the chosen direction `dᵏ = a_{i_k} - xᵏ`. -/
theorem polytope_quadratic_conditional_gradient_update_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_conditional_gradient_update Q b a xk i =
      let d := polytope_quadratic_conditional_gradient_direction a xk i
      xk + min (polytope_quadratic_exact_line_search_ratio Q b xk d) 1 • d :=
  rfl

/-- Helper for Algorithm 13.5: positive definiteness makes the quadratic cross term symmetric. -/
lemma positiveDefinite_dotProduct_mulVec_swap
    {Q : positiveDefiniteMatrices n} (x y : E) :
    dotProduct x (Q *ᵥ y) = dotProduct y (Q *ᵥ x) := by
  have htranspose : ((Q : Matrix (Fin n) (Fin n) ℝ)ᵀ) = Q := by
    simpa using Q.2.1.eq
  -- Move the transpose to the first vector, then use symmetry of `Q`.
  rw [Matrix.dotProduct_mulVec]
  rw [← htranspose]
  rw [Matrix.vecMul_transpose]
  rw [htranspose, dotProduct_comm]

/-- Helper for Algorithm 13.5: the quadratic objective restricts to a scalar quadratic along every
line through a point. -/
lemma polytope_quadratic_objective_add_smul_direction_eq
    {Q : positiveDefiniteMatrices n} {b x d : E} {t : ℝ} :
    polytope_quadratic_objective Q b (x + t • d) =
      polytope_quadratic_objective Q b x +
        t * dotProduct d (Q *ᵥ x + b) +
        ((t ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) := by
  -- Expand the quadratic and linear parts using bilinearity and the symmetry cross term.
  rw [polytope_quadratic_objective_apply, polytope_quadratic_objective_apply]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [positiveDefinite_dotProduct_mulVec_swap (Q := Q) x d]
  rw [dotProduct_comm b d]
  ring

/-- Helper for Algorithm 13.5: clipping the exact quadratic ratio to `[0, 1]` minimizes the
scalar quadratic restriction on the unit interval. -/
lemma clipped_quadratic_ratio_isMinOn_unit_interval
    {α κ : ℝ} (hκ : 0 < κ) :
    IsMinOn (fun t : ℝ ↦ t * α + ((t ^ (2 : ℕ)) / 2) * κ)
      (Set.Icc (0 : ℝ) 1) (min (-α / κ) 1) := by
  let f : ℝ → ℝ := fun t ↦ t * α + ((t ^ (2 : ℕ)) / 2) * κ
  let lam : ℝ := -α / κ
  have hκne : κ ≠ 0 := ne_of_gt hκ
  rw [isMinOn_iff]
  intro t ht
  by_cases hlam : lam ≤ 1
  · have hdiff : f t - f lam = (κ / 2) * (t - lam) ^ (2 : ℕ) := by
        dsimp [f, lam]
        field_simp [hκne]
        ring
    have hnonneg : 0 ≤ (κ / 2) * (t - lam) ^ (2 : ℕ) := by
      exact mul_nonneg (by positivity) (sq_nonneg (t - lam))
    have hmin : f lam ≤ f t := by
      linarith
    have hclip : min lam 1 = lam := min_eq_left hlam
    simpa [f, lam, hclip] using hmin
  · have hlam_ge : 1 ≤ lam := le_of_not_ge hlam
    have hακ : α + κ ≤ 0 := by
      have hκle : κ ≤ -α := by
        have := (le_div_iff₀ hκ).mp hlam_ge
        simpa [lam] using this
      linarith
    have hfactor_nonpos : α + (κ / 2) * (t + 1) ≤ 0 := by
      have hterm : (κ / 2) * (t + 1) ≤ κ := by
        nlinarith [ht.2, hκ.le]
      linarith
    have hdiff : f t - f 1 = (t - 1) * (α + (κ / 2) * (t + 1)) := by
      dsimp [f]
      ring
    have hnonneg : 0 ≤ (t - 1) * (α + (κ / 2) * (t + 1)) := by
      refine mul_nonneg_of_nonpos_of_nonpos ?_ hfactor_nonpos
      linarith [ht.2]
    have hmin : f 1 ≤ f t := by
      linarith
    have hclip : min lam 1 = 1 := min_eq_right hlam_ge
    simpa [f, lam, hclip] using hmin

-- Proof sketch: for a positive-definite quadratic objective, the one-dimensional restriction to
-- the segment from `xᵏ` to `a_{i_k}` is minimized on `[0, 1]` by the clipped ratio
-- `min {λ_k, 1}` from equation `(13.34)` once the Algorithm 13.5 update branch
-- `⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0` ensures that the unclipped ratio is nonnegative.
/-- On the nonterminal branch of Algorithm 13.5, where the chosen direction satisfies
`⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0`, the clipped ratio from equation `(13.34)` belongs to the canonical
Chapter 13 exact-line-search set on the segment from `xᵏ` to the chosen vertex `a_{i_k}`. This
is the `bridge/view` from the explicit quadratic ratio to the owner
`conditional_gradient_exact_line_search_stepsizes`. -/
theorem polytope_quadratic_ratio_clip_mem_conditional_gradient_exact_line_search_stepsizes
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E} {xk : E} {i : Fin l}
    (hderiv :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0) :
    min
        (polytope_quadratic_exact_line_search_ratio Q b xk
          (polytope_quadratic_conditional_gradient_direction a xk i))
        1 ∈
      conditional_gradient_exact_line_search_stepsizes
        (polytope_quadratic_objective Q b).toEReal
        xk (a i) := by
  let d : E := polytope_quadratic_conditional_gradient_direction a xk i
  let α : ℝ := dotProduct d (Q *ᵥ xk + b)
  let κ : ℝ := dotProduct d (Q *ᵥ d)
  let lam : ℝ := polytope_quadratic_exact_line_search_ratio Q b xk d
  have hα : α < 0 := by
    simpa [d, α] using hderiv
  have hd : d ≠ 0 := by
    intro hd
    have : ¬ α < 0 := by
      simp [α, hd]
    exact this hα
  have hκ : 0 < κ := by
    simpa [d, κ] using Q.2.dotProduct_mulVec_pos hd
  have hlamdef : lam = -α / κ := by
    simp [lam, α, κ, d, polytope_quadratic_exact_line_search_ratio_eq]
  have hmem : min lam 1 ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨?_, min_le_right _ _⟩
    rw [hlamdef]
    exact le_min (div_nonneg (by linarith : 0 ≤ -α) hκ.le) zero_le_one
  have hscalar :
      IsMinOn (fun t : ℝ ↦ t * α + ((t ^ (2 : ℕ)) / 2) * κ)
        (Set.Icc (0 : ℝ) 1) (min lam 1) := by
    simpa [hlamdef] using
      clipped_quadratic_ratio_isMinOn_unit_interval (α := α) (κ := κ) hκ
  rw [mem_conditional_gradient_exact_line_search_stepsizes_iff]
  refine ⟨?_, ?_⟩
  · change min lam 1 ∈ Set.Icc (0 : ℝ) 1
    exact hmem
  · rw [isMinOn_iff]
    intro u hu
    have hquad := (isMinOn_iff.mp hscalar) u hu
    -- Rewrite the one-dimensional restriction explicitly, then cast the resulting real inequality
    -- to `EReal` for the exact-line-search owner.
    change
      ((polytope_quadratic_objective Q b (xk + min lam 1 • d) : EReal) ≤
        polytope_quadratic_objective Q b (xk + u • d))
    have hshift :
        polytope_quadratic_objective Q b (xk + min lam 1 • d) ≤
          polytope_quadratic_objective Q b (xk + u • d) := by
      have hquad' :
          min lam 1 * dotProduct d (Q *ᵥ xk + b) +
              (((min lam 1) ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) ≤
            u * dotProduct d (Q *ᵥ xk + b) +
              ((u ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) := by
        simpa [α, κ] using hquad
      rw [polytope_quadratic_objective_add_smul_direction_eq
          (Q := Q) (b := b) (x := xk) (d := d) (t := min lam 1)]
      rw [polytope_quadratic_objective_add_smul_direction_eq
          (Q := Q) (b := b) (x := xk) (d := d) (t := u)]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hquad' (polytope_quadratic_objective Q b xk)
    exact_mod_cast hshift

/-- Algorithm 13.5: the admissible next iterates from `xᵏ` are obtained by choosing a vertex
index `i_k` minimizing `⟪a_i, ∇ f_q(xᵏ)⟫`, setting `dᵏ = a_{i_k} - xᵏ`, and then either stopping
when `⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0` (encoded here by the stationary outcome `xᵏ⁺¹ = xᵏ`), or updating by
`xᵏ⁺¹ = xᵏ + t_k dᵏ` with `t_k = min {λ_k, 1}` and
`λ_k = -⟪dᵏ, ∇ f_q(xᵏ)⟫ / ((dᵏ)^T Q dᵏ)`, for a feasible iterate `xᵏ ∈ Ω` in the
positive-definite quadratic regime `Q ∈ 𝕊_{++}^n`. -/
def polytope_quadratic_conditional_gradient_one_step
    (Q : positiveDefiniteMatrices n) (b : E) (a : Fin l → E)
    (xk : polytope_quadratic_feasible_set a) : Set E :=
  {xNext : E |
      ∃ i ∈
          unconstrained_problem_solutions
            (polytope_quadratic_vertex_linear_objective Q b a xk),
        ((0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i ∧
            xNext = (xk : E)) ∨
          (polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0 ∧
            xNext = polytope_quadratic_conditional_gradient_update Q b a xk i))}

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_one_step`; the resulting set
-- comprehension is exactly the stop-or-update alternative from Algorithm 13.5.
/-- Expanding `polytope_quadratic_conditional_gradient_one_step Q b a xᵏ` yields the set of
points produced by a minimizing vertex index `i_k`, together with the stopping-or-update
alternative from Algorithm 13.5. -/
theorem polytope_quadratic_conditional_gradient_one_step_def
    (Q : positiveDefiniteMatrices n) (b : E) (a : Fin l → E)
    (xk : polytope_quadratic_feasible_set a) :
    polytope_quadratic_conditional_gradient_one_step Q b a xk =
      {xNext : E |
          ∃ i ∈
          unconstrained_problem_solutions
                (polytope_quadratic_vertex_linear_objective Q b a xk),
            ((0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i ∧
                xNext = (xk : E)) ∨
              (polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0 ∧
                xNext = polytope_quadratic_conditional_gradient_update Q b a xk i))} :=
  rfl

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_one_step`; membership is exactly
-- the displayed stop-or-update alternative.
/-- A point `xᵏ⁺¹` belongs to `polytope_quadratic_conditional_gradient_one_step Q b a xᵏ` exactly
when it arises from a minimizing vertex index `i_k`, with either the stopping certificate
`⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0` and `xᵏ⁺¹ = xᵏ`, or the nonterminal update
`xᵏ⁺¹ = xᵏ + t_k dᵏ`. -/
@[simp] theorem mem_polytope_quadratic_conditional_gradient_one_step_iff
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
    {xk : polytope_quadratic_feasible_set a} {xNext : E} :
    xNext ∈ polytope_quadratic_conditional_gradient_one_step Q b a xk ↔
      ∃ i ∈
          unconstrained_problem_solutions
            (polytope_quadratic_vertex_linear_objective Q b a xk),
        ((0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i ∧
            xNext = (xk : E)) ∨
          (polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0 ∧
            xNext = polytope_quadratic_conditional_gradient_update Q b a xk i)) :=
  Iff.rfl

-- Proof sketch: from `hi`, the chosen vertex `a_i` minimizes the linearization over all vertices,
-- hence over the feasible polytope `Ω = conv{a₁, …, a_l}` by convexity of the linear
-- functional. The feasible hypothesis `hxk` upgrades the nonnegative directional derivative at
-- `dᵏ = a_i - xᵏ` to the first-order optimality condition for the convex quadratic objective on
-- `Ω`, which is exactly `IsMinOn` for the constrained problem `(13.32)`.
/-- If the minimizing vertex direction in Algorithm 13.5 satisfies the stopping test
`⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0` at a feasible point `xᵏ ∈ Ω`, then `xᵏ` solves the constrained quadratic
problem `(13.32)`. This is the optimality theorem attached to the stopping branch, not part of
the one-step data itself. -/
theorem polytope_quadratic_isMinOn_of_nonneg_directional_derivative
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E} {xk : E} {i : Fin l}
    (hxk : xk ∈ polytope_quadratic_feasible_set a)
    (hi :
      i ∈ unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a xk))
    (hderiv : 0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i) :
    IsMinOn (polytope_quadratic_problem Q b a) Set.univ xk := by
  let v : E := Q *ᵥ xk + b
  have hlin :
      IsMinOn (fun y ↦ dotProduct y v) (polytope_quadratic_feasible_set a) (a i) :=
    polytope_quadratic_linearized_isMinOn_feasible_set_of_mem_vertex_argmin hi
  rw [isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ polytope_quadratic_feasible_set a
  · have hai_le : dotProduct (a i) v ≤ dotProduct y v := (isMinOn_iff.mp hlin) y hy
    have hxk_le_ai : dotProduct xk v ≤ dotProduct (a i) v := by
      have hderiv' : 0 ≤ dotProduct (a i - xk) v := by
        simpa [polytope_quadratic_conditional_gradient_directional_derivative,
          polytope_quadratic_conditional_gradient_direction_eq, v] using hderiv
      exact sub_nonneg.mp (by simpa [sub_dotProduct] using hderiv')
    have hdir : 0 ≤ dotProduct (y - xk) v := by
      have : dotProduct xk v ≤ dotProduct y v := le_trans hxk_le_ai hai_le
      simpa [sub_dotProduct] using sub_nonneg.mpr this
    have hcurv :
        0 ≤ dotProduct (y - xk) (Q *ᵥ (y - xk)) := by
      simpa using Q.2.posSemidef.dotProduct_mulVec_nonneg (y - xk)
    have hobj :
        polytope_quadratic_objective Q b xk ≤ polytope_quadratic_objective Q b y := by
      have hexpand :
          polytope_quadratic_objective Q b y =
            polytope_quadratic_objective Q b xk +
              dotProduct (y - xk) v +
              (((1 : ℝ) ^ (2 : ℕ)) / 2) * dotProduct (y - xk) (Q *ᵥ (y - xk)) := by
        -- Specialize the line-restriction formula at `t = 1` and rewrite `xk + (y - xk)` to `y`.
        have hy_eq : xk + (1 : ℝ) • (y - xk) = y := by
          simp [sub_eq_add_neg]
        rw [← hy_eq]
        rw [polytope_quadratic_objective_add_smul_direction_eq
            (Q := Q) (b := b) (x := xk) (d := y - xk) (t := (1 : ℝ))]
        simp [v, one_smul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      rw [hexpand]
      nlinarith
    have hobjEReal :
        (polytope_quadratic_objective Q b xk : EReal) ≤ polytope_quadratic_objective Q b y := by
      exact_mod_cast hobj
    rw [polytope_quadratic_problem_of_mem Q b a hxk, polytope_quadratic_problem_of_mem Q b a hy]
    exact hobjEReal
  · rw [polytope_quadratic_problem_of_mem Q b a hxk, polytope_quadratic_problem_of_not_mem Q b a hy]
    simp

end
