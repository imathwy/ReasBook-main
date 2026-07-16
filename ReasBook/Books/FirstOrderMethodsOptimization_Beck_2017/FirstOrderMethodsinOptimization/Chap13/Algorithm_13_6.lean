import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap13.Algorithm_13_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap13.Assumption_13_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

/- `prompt_add/` is absent in this workspace, so the statement design is checked against the
nearby Chapter 13 owners. This item is `source-facing`: it records the data produced by the
initialization procedure used before the convergence statements.

Domain sampling identifies the relevant owners already present upstream:
- `polytope_quadratic_feasible_set` and `polytope_quadratic_objective` from Definition 13.10 for
  the finite-hull quadratic model on a vertex family `a : Fin l → E`;
- `polytope_quadratic_conditional_gradient_one_step` and
  `polytope_quadratic_vertex_mem_feasible_set` from Algorithm 13.5 for the trial conditional-
  gradient step from the minimizing vertex;
- `IsStrictVertexSublevelInitialPoint` from Assumption 13.18 for the final strict-simplex output.

The `core/canonical` owner in this part of the chapter is the vertex family `a`, not a concrete
matrix whose columns realize that family. Matrix identities such as `x = A *ᵥ v` are therefore
demoted to the usual bridge `a := A.col`, while the public Algorithm 13.6 API records barycentric
equalities directly as weighted sums `∑ i, v i • a i`. The trial step is not stored through a
second local wrapper: it is primitive data only as membership in the existing Algorithm 13.5
one-step owner. -/

/-- Algorithm 13.6, step 4: if the trial simplex coordinates `ṽ⁰` are already strictly positive,
the algorithm keeps `(x̃⁰, ṽ⁰)`. Otherwise it chooses strictly positive simplex coordinates `v⁰`
sufficiently close to `ṽ⁰` so that the strict inequality
`f_q(∑ i, v i • a_i) < f_q(a_p)` still holds at `v = v⁰`. -/
def algorithm_13_6_step4_output
    (f_q : E → ℝ) (a : Fin l → E)
    (p : Fin l) (xTilde0 x0 : E)
    (vTilde0 v0 : stdSimplex ℝ (Fin l)) : Prop :=
  (((vTilde0 : Fin l → ℝ) ∈ positiveOrthant l) ∧ v0 = vTilde0 ∧ x0 = xTilde0) ∨
    (¬ ((vTilde0 : Fin l → ℝ) ∈ positiveOrthant l) ∧
      x0 = ∑ i, v0 i • a i ∧
      (v0 : Fin l → ℝ) ∈ positiveOrthant l ∧
      ∃ ε > 0,
        ‖(v0 : Fin l → ℝ) - vTilde0‖ < ε ∧
          ∀ w : stdSimplex ℝ (Fin l),
            ‖(w : Fin l → ℝ) - vTilde0‖ < ε →
              f_q (∑ i, w i • a i) < f_q (a p))

/-- Algorithm 13.6: `p` minimizes the vertex values `f_q(a_i)`, the point `x̃⁰` is produced by
one Algorithm 13.5 conditional-gradient step from the feasible vertex `a_p` and strictly improves
the objective, `ṽ⁰ ∈ Δ_l` represents `x̃⁰`, and step 4 then either keeps `(x̃⁰, ṽ⁰)` when
`ṽ⁰ ∈ ℝ^l_{++}` or replaces it by a strictly positive simplex point `v⁰` chosen sufficiently
close to `ṽ⁰` so that the strict inequality persists for
`x⁰ = ∑ i, v⁰_i • a_i`. The final output is exposed canonically through
`IsStrictVertexSublevelInitialPoint`. -/
class algorithm_13_6_initialization
    (Q : positiveDefiniteMatrices n) (b : E) (a : Fin l → E)
    (p : Fin l) (xTilde0 x0 : E)
    (vTilde0 v0 : stdSimplex ℝ (Fin l)) : Prop where
  minimizing_vertex :
    IsMinOn (fun i : Fin l ↦ polytope_quadratic_objective Q b (a i)) Set.univ p
  trial_step :
    xTilde0 ∈ polytope_quadratic_conditional_gradient_one_step Q b a
      ⟨a p, polytope_quadratic_vertex_mem_feasible_set a p⟩
  trial_improves :
    polytope_quadratic_objective Q b xTilde0 <
      polytope_quadratic_objective Q b (a p)
  trial_eq_weighted_sum :
    xTilde0 = ∑ i, vTilde0 i • a i
  step4 :
    algorithm_13_6_step4_output (polytope_quadratic_objective Q b) a p xTilde0 x0 vTilde0 v0

variable {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
variable {p : Fin l} {xTilde0 x0 : E} {vTilde0 v0 : stdSimplex ℝ (Fin l)}

namespace algorithm_13_6_initialization

set_option linter.unusedVariables false in
/-- An Algorithm 13.6 initialization canonically yields Assumption 13.18 for the final output
`(x⁰, v⁰)`. This is the chapter-level `bridge/view` from the procedural initialization data to the
source-facing strict-vertex-sublevel owner. -/
theorem toIsStrictVertexSublevelInitialPoint
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) :
    IsStrictVertexSublevelInitialPoint (polytope_quadratic_objective Q b) a x0 v0 where
  objective_lt_vertex i :=
    let hp : ∀ j : Fin l,
        polytope_quadratic_objective Q b (a p) ≤
          polytope_quadratic_objective Q b (a j) := isMinOn_univ_iff.mp h.minimizing_vertex
    match h.step4 with
    | .inl ⟨_, _, hx0⟩ =>
        have hltp :
            polytope_quadratic_objective Q b x0 < polytope_quadratic_objective Q b (a p) :=
          hx0 ▸ h.trial_improves
        lt_of_lt_of_le hltp (hp i)
    | .inr ⟨_, hx0, _, _, _, hv0_near, hnear⟩ =>
        have hltp :
            polytope_quadratic_objective Q b x0 < polytope_quadratic_objective Q b (a p) :=
          hx0 ▸ hnear v0 hv0_near
        lt_of_lt_of_le hltp (hp i)
  eq_weighted_sum :=
    match h.step4 with
    | .inl ⟨_, hv0, hx0⟩ => hv0 ▸ hx0 ▸ h.trial_eq_weighted_sum
    | .inr ⟨_, hx0, _, _, _, _, _⟩ => hx0
  weights_mem_positiveOrthant :=
    match h.step4 with
    | .inl ⟨hvTilde0, hv0, _⟩ => hv0 ▸ hvTilde0
    | .inr ⟨_, _, hv0, _, _, _, _⟩ => hv0

/-- An Algorithm 13.6 initialization canonically yields Assumption 13.18 for the final output
`(x⁰, v⁰)`. This is the chapter-level `bridge/view` from the procedural initialization data to the
source-facing strict-vertex-sublevel owner. -/
instance instIsStrictVertexSublevelInitialPoint
    [algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0] :
    IsStrictVertexSublevelInitialPoint (polytope_quadratic_objective Q b) a x0 v0 :=
  toIsStrictVertexSublevelInitialPoint inferInstance

set_option linter.unusedVariables false in
/-- In Algorithm 13.6, the final output has objective value strictly below every vertex value. -/
theorem objective_lt_vertex
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) (i : Fin l) :
    polytope_quadratic_objective Q b x0 < polytope_quadratic_objective Q b (a i) :=
  (toIsStrictVertexSublevelInitialPoint h).objective_lt_vertex i

set_option linter.unusedVariables false in
/-- In Algorithm 13.6, the final output keeps the barycentric representation `x⁰ = ∑ i, v⁰_i a_i`.
-/
theorem eq_weighted_sum
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) :
    x0 = ∑ i, v0 i • a i :=
  (toIsStrictVertexSublevelInitialPoint h).eq_weighted_sum

set_option linter.unusedVariables false in
/-- In Algorithm 13.6, the final simplex coordinates are strictly positive. -/
theorem weights_mem_positiveOrthant
    (h : algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0) :
    (v0 : Fin l → ℝ) ∈ positiveOrthant l :=
  (toIsStrictVertexSublevelInitialPoint h).weights_mem_positiveOrthant

end algorithm_13_6_initialization

/-- An Algorithm 13.6 initialization canonically exposes feasibility of the final point `x⁰`. -/
instance instFactAlgorithm136InitializationOutputMemFeasible
    [algorithm_13_6_initialization Q b a p xTilde0 x0 vTilde0 v0] :
    Fact (x0 ∈ polytope_quadratic_feasible_set a) where
  out :=
    let hstrict :
        IsStrictVertexSublevelInitialPoint (polytope_quadratic_objective Q b) a x0 v0 :=
      inferInstance
    hstrict.mem_feasible_set

end
