import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_9_8 (from Chap09) -/
universe u

open InnerProductSpace (toDualMap)
open WithLp (toLp)

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δ" => (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) : Set E)
local notation "ω" => (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2)

/- Text 9.8 is `source-facing`: the textbook specializes mirror descent on the simplex to the
Euclidean distance-generating function `ω(x) = ‖x‖₂² / 2`, initialized at the uniform point
`(1 / n) e`. The `core/canonical` owner for this rate statement is therefore the Chapter 9
trajectory predicate `is_mirror_descent_trajectory` together with the fixed-horizon rate theorem
`mirror_descent_best_value_gap_le_one_div_sqrt_of_constant_stepsizes`; the Euclidean
projected-subgradient formulation is only a `bridge/view`, supplied by Text 9.5. In the current
project the ambient Euclidean owner is `EuclideanSpace ℝ (Fin n)`, the simplex is the transported
set `toLp 2 '' stdSimplex ℝ (Fin n)`, and the uniform initial point is the transport of the
canonical simplex barycenter. -/

-- The coordinate-side owner is `stdSimplex.barycenter`; `uniform_simplex_point` is only its
-- Euclidean transported view in the image simplex `Δ`.
/-- The canonical uniform initial point `x⁰ = (1 / n) e` in the Euclidean simplex
`toLp 2 '' stdSimplex ℝ (Fin n)`, obtained by transporting `stdSimplex.barycenter`, for
`n > 0`. -/
abbrev uniform_simplex_point (hn : 0 < n) : Δ :=
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  ⟨toLp 2 (stdSimplex.barycenter : stdSimplex ℝ (Fin n)),
    ⟨stdSimplex.barycenter, stdSimplex.barycenter.2, rfl⟩⟩

-- Proof sketch: `stdSimplex.barycenter` has every coordinate equal to `(Fintype.card (Fin n))⁻¹`,
-- i.e. `1 / n`, and `uniform_simplex_point` is exactly its `toLp 2` transport into the ambient
-- Euclidean space.
/-- Coercing the uniform simplex point to the ambient Euclidean space gives the transported
constant vector with coordinates `1 / n`. -/
theorem coe_uniform_simplex_point (hn : 0 < n) :
    ((uniform_simplex_point hn : Δ) : E) = toLp 2 (fun _ : Fin n ↦ 1 / (n : ℝ)) := sorry

/-- The Euclidean mirror map `ω(x) = ‖x‖² / 2` is a Bregman potential with modulus `1` on the
transported simplex `Δ`. -/
theorem half_squared_norm_isBregmanPotentialOn_simplex :
    IsBregmanPotentialOn ω Δ 1 := sorry

-- Proof sketch: for the Euclidean mirror map, the Bregman distance is
-- `(1 / 2) ‖x - x₀‖²`. Two points of the simplex lie in the unit `ℓ₂` ball and differ by at most
-- `√2`, so the resulting Bregman diameter from the uniform initialization is at most `1`.
/-- On the simplex, the Euclidean Bregman distance to the uniform initialization `x⁰ = (1 / n)e`
is bounded by `1`. This is the simplex specialization of the textbook constant `Θ₀ = 1`. -/
theorem half_squared_norm_bregman_le_one_of_mem_simplex
    (hn : 0 < n) {x : E} (hx : x ∈ Δ) :
    B[(ω : E → ℝ)] x ((uniform_simplex_point hn : Δ) : E) ≤ 1 := sorry

section Rate

variable {f : E → EReal} {XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f Δ)

-- Proof sketch: apply Theorem 9.16 to the Euclidean mirror map `ω(x) = ‖x‖² / 2` on the simplex
-- `Δ`, use `half_squared_norm_isBregmanPotentialOn_simplex` for the Bregman-potential owner, and
-- bound the initial Bregman term by `1` via
-- `half_squared_norm_bregman_le_one_of_mem_simplex` at the optimal point `xStar ∈ XStar ⊆ Δ`.
-- With `σ = 1`, `Θ₀ = 1`, and the constant stepsize
-- `t_k = √2 / (L_{f,2} √(N + 1))`, Theorem 9.16 reduces exactly to the displayed estimate.
/-- Text 9.8: for mirror descent on the Euclidean simplex with mirror map
`ω(x) = ‖x‖₂² / 2`, uniform initialization `x⁰ = (1 / n)e`, and constant stepsizes
`t_k = √2 / (L_{f,2} √(N + 1))` on the first `N + 1` iterations, the running-best objective gap
is bounded by `√2 L_{f,2} / √(N + 1)`, with `L_{f,2}` represented here by `h_bound.L_f`. -/
theorem euclidean_simplex_mirror_descent_best_value_gap_le
    (hn : 0 < n) {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj : is_mirror_descent_trajectory (fun y ↦ (f y).toReal) ω Δ x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (hx0 : x 0 = ((uniform_simplex_point hn : Δ) : E))
    {N : ℕ}
    (h_stepsize :
      ∀ k : Fin (N + 1),
        t k = Real.sqrt 2 / (h_bound.L_f * Real.sqrt (N + 1 : ℝ))) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      Real.sqrt 2 * h_bound.L_f / Real.sqrt (N + 1 : ℝ) := sorry

section Bridge

variable (hn : 0 < n)
variable (g : ℕ → Δ → E) (t : ℕ → ℝ)

local notation "x[" k "]" =>
  projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t (uniform_simplex_point hn) k

-- Proof sketch: feasibility of each iterate is automatic because `projected_subgradient_method`
-- is `Δ`-valued, the strong-dual subgradient hypothesis rewrites to the Euclidean subgradient
-- clause in `is_mirror_descent_trajectory`, `h_stepsize_pos` supplies positivity, and Text 9.5
-- identifies the projected-subgradient minimization with the Euclidean mirror-descent one-step
-- minimization.
/-- The projected-subgradient iterates on the Euclidean simplex, started at the uniform point,
form the specialized mirror-descent trajectory for `ω(x) = ‖x‖₂² / 2`. This is the explicit
Text 9.5 bridge between the Chapter 8 recursive iterates and the Chapter 9 owner
`is_mirror_descent_trajectory`. -/
theorem projected_subgradient_method_is_mirror_descent_trajectory
    (h_subgrad :
      ∀ k,
        toDualMap ℝ E (g k (x[k])) ∈ strongDualSubdifferential f (x[k] : E))
    (h_stepsize_pos : ∀ k, 0 < t k) :
    is_mirror_descent_trajectory
      (fun y ↦ (f y).toReal)
      ω
      Δ
      (fun k ↦ (x[k] : E))
      (fun k ↦ g k (x[k]))
      t := sorry

end Bridge

end Rate

end

/-! ### Theorem_9_8 (from Chap09) -/
universe u

section

/-
Theorem 9.8 is a `source-facing` constrained specialization of the Chapter 9 owner theorem
`existsUnique_composite_minimizer_mem_domains`. Its primitive mathematical data are the feasible
set `C`, the dual linear perturbation `a`, and the Bregman potential hypothesis on `ω`; the
constrained formulation over `C` is derived by taking `ψ = ((a · : ℝ) : EReal) + δ_C`.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {ω : E → EReal} {σ : ℝ}

-- Proof sketch: apply Lemma 9.7 to
-- `ψ(x) = ((a x : ℝ) : EReal) + extendedIndicator C x`. The indicator of a nonempty closed convex
-- set is proper, closed, and convex, and adding the linear functional preserves those properties.
-- Then translate the resulting global minimizer statement back to minimization over `C`.
/-- Theorem 9.8: if `C` is nonempty, closed, and convex and `ω` is a Bregman potential on `C`,
then for every dual vector `a`, the constrained problem
`min_{x ∈ C} {⟨a, x⟩ + ω(x)}` has a unique minimizer, and that minimizer lies in
`C ∩ dom(∂ ω)`. -/
theorem existsUnique_mirror_descent_problem_minimizer_mem_domains
    (a : StrongDual ℝ E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hω : IsBregmanPotentialOn ω C σ) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + ω x) C xStar ∧
        xStar ∈ C ∩ subdifferential_domain ω := sorry

end
