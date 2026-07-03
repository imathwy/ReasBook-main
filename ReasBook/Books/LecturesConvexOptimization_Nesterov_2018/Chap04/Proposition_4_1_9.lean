import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_14
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_15
import LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_9_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped CubicRegularizedDiagonalInvariants

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.9 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalMinimum`, `cubicRegularizedMinimalDiagonalIndices`, and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal owners of
  `H_min`, `I*`, and `G²`;
* `quadraticObjective` in `Chap01/Definition_1_9_1` and
  `UnconstrainedQuadraticMinimizationProblem.minimizer_unique` in
  `Chap01/Proposition_1_9_11`, the core owner / uniqueness API for the shifted quadratic
  subproblem.

Best owner abstraction:
* source-facing: the diagonal nondegenerate `G² > 0` closed-form dual formula and the resolvent
  minimizer statements from the source;
* core/canonical: `cubicRegularizedQuadraticDualFunction`, `cubicRegularizedQuadraticDualDomain`,
  `quadraticObjective`, and `IsMinOn`;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag` together with the diagonal
  invariants `H_min`, `I*`, and `G²`.

Primitive data:
* the gradient `g`, diagonal data `Hdiag`, cubic parameter `M`, and the diagonal matrix
  `H = Matrix.diagonal Hdiag`;
* the canonical diagonal invariants `H_min`, `I*`, and `G²`.

Derived API:
* the dual-domain identity for `dom ψ`;
* the closed formula for `ψ(λ)` on that domain;
* the owner-level minimizer theorem for the shifted diagonal quadratic;
* the uniqueness corollary identifying every minimizer with the same resolvent point.

This file therefore keeps the source-facing Proposition 4.1.9 statements, but states them
directly in terms of the chapter owners `ψ` and `dom ψ` rather than forcing the long raw owner
names on the theorem surface. It also exposes the shifted-quadratic minimizer statement here as
the canonical upstream owner, with uniqueness kept only as the thin corollary attached to that
owner. -/

section

variable (g : EuclideanSpace ℝ (Fin n)) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Irest" => Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag]

/-- Helper for Proposition 4.1.9: the shifted diagonal matrix `H + λ I`. -/
abbrev shiftedDiagonalMatrix (lam : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Helper for Proposition 4.1.9: the shifted quadratic objective `q_λ`. -/
abbrev shiftedQuadraticObjective (lam : ℝ) : E → ℝ :=
  quadraticObjective 0 g (shiftedDiagonalMatrix (Hdiag := Hdiag) lam)

/-- Helper for Proposition 4.1.9: the canonical diagonal resolvent point `-(H + λ I)⁻¹ g`. -/
abbrev diagonalResolventPoint (lam : ℝ) : E :=
  (-Matrix.toEuclideanLin ((shiftedDiagonalMatrix (Hdiag := Hdiag) lam)⁻¹) g : E)

local notation "Ashift" => shiftedDiagonalMatrix (Hdiag := Hdiag)
local notation "qShift" => shiftedQuadraticObjective (g := g) (Hdiag := Hdiag)
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "dom " "ψ" => cubicRegularizedQuadraticDualDomain g H M
local notation "resolventPoint" => diagonalResolventPoint (g := g) (Hdiag := Hdiag)

/-- Helper for Proposition 4.1.9: shifting the diagonal matrix by `λ I` is still diagonal, with
entries `H_i + λ`. -/
lemma diagonal_shift_eq_diagonal_add_scalar
    (lam : ℝ) :
    Ashift lam = Matrix.diagonal (fun i ↦ Hdiag i + lam) := by
  -- Compare entries directly: diagonal entries gain `λ`, off-diagonal entries stay zero.
  ext i j
  by_cases hij : i = j
  · subst hij
    dsimp [shiftedDiagonalMatrix]
    simp [Matrix.diagonal]
  · dsimp [shiftedDiagonalMatrix]
    simp [Matrix.diagonal, hij]

/-- Helper for Proposition 4.1.9: every diagonal entry lies above the minimum diagonal value
`H_min`. -/
lemma diagonalMinimum_le_entry
    (i : Fin n) :
    H_min[Hdiag] ≤ Hdiag i := by
  -- `H_min` was defined as the infimum of the finite range of `Hdiag`.
  exact csInf_le (Set.Finite.bddBelow (Set.finite_range Hdiag))
    (show Hdiag i ∈ Set.range Hdiag from ⟨i, rfl⟩)

/-- Helper for Proposition 4.1.9: if `G² > 0`, then some active index carries a nonzero
gradient coordinate. -/
lemma active_index_exists_of_activeGradientSquare_pos
    (hGpos : 0 < G²[g;Hdiag]) :
    ∃ i, i ∈ I*[Hdiag] ∧ g i ≠ 0 := by
  -- A positive finite sum of squares must contain a nonzero summand.
  have hsum_ne : G²[g;Hdiag] ≠ 0 := by
    linarith
  rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne with ⟨i, hi, hineq⟩
  refine ⟨i, hi, ?_⟩
  intro hgi
  simp [hgi] at hineq

/-- Helper for Proposition 4.1.9: restricting `q_λ` to a coordinate line gives the displayed
one-variable quadratic. -/
lemma quadraticObjective_single_eq
    (lam t : ℝ) (k : Fin n) :
    qShift lam (EuclideanSpace.single k t) =
      g k * t + (1 / 2 : ℝ) * (Hdiag k + lam) * t ^ (2 : ℕ) := by
  -- On a coordinate line, only the `k`-th diagonal entry contributes to the quadratic term.
  -- TODO: finish the coordinate-line evaluation by rewriting `quadraticObjective` with
  -- `quadraticObjective_zero_eq_dotProduct` and simplifying the diagonal action on
  -- `EuclideanSpace.single k t`.
  sorry

/-- Helper for Proposition 4.1.9: a one-variable quadratic with negative leading coefficient is
unbounded below. -/
lemma not_bddBelow_negative_quadratic_line
    (a b : ℝ) (ha : a < 0) :
    ¬BddBelow (Set.range fun t : ℝ ↦ (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + b * t) := by
  -- Choose a large positive `t` so that the negative quadratic term dominates the linear term.
  intro hbb
  rcases hbb with ⟨m, hm⟩
  let t : ℝ := 2 * (|b| + |m| + 1) / (-a) + 1
  have hta : 0 < -a := by
    linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_one : 1 ≤ t := by
    dsimp [t]
    have : 0 ≤ 2 * (|b| + |m| + 1) / (-a) := by
      positivity
    linarith
  have hdom : |b| + |m| + 1 < (-a / 2) * t := by
    dsimp [t]
    field_simp [ha.ne]
    nlinarith [abs_nonneg b, abs_nonneg m]
  have hb : b * t ≤ |b| * t := by
    have habs : |b * t| = |b| * |t| := by
      rw [abs_mul]
    rw [abs_of_pos ht_pos] at habs
    have hbt : b * t ≤ |b * t| := le_abs_self _
    nlinarith
  have hm' : -(|m| + 1) * t < m := by
    have hnonneg : 0 ≤ |m| + 1 := by
      positivity
    have h1 : -(|m| + 1) * t ≤ -(|m| + 1) := by
      nlinarith [ht_one]
    have h2 : -(|m| + 1) < -|m| := by
      nlinarith
    have h3 : -|m| ≤ m := by
      simpa using neg_abs_le m
    linarith
  have hvalue :
      (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + b * t < m := by
    have hmain :
        (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + |b| * t < -(|m| + 1) * t := by
      nlinarith [hdom, ht_pos]
    linarith
  have hq := hm ⟨t, rfl⟩
  linarith

/-- Helper for Proposition 4.1.9: a nonzero linear function on `ℝ` is unbounded below. -/
lemma not_bddBelow_nonzero_linear_line
    (b : ℝ) (hb : b ≠ 0) :
    ¬BddBelow (Set.range fun t : ℝ ↦ b * t) := by
  -- Evaluate the line at `t = -( |m| + 1 ) / b` to force the value below any lower bound `m`.
  intro hbb
  rcases hbb with ⟨m, hm⟩
  let t : ℝ := -(|m| + 1) / b
  have hvalue : b * t < m := by
    dsimp [t]
    have h1 : b * (-(|m| + 1) / b) = -(|m| + 1) := by
      field_simp [hb]
    rw [h1]
    have h2 : -(|m| + 1) < -|m| := by
      nlinarith
    have h3 : -|m| ≤ m := by
      simpa using neg_abs_le m
    linarith
  have hq := hm ⟨t, rfl⟩
  linarith

/-- Helper for Proposition 4.1.9: the value of `q_λ` at the diagonal resolvent is the full
diagonal reciprocal sum. -/
lemma quadraticObjective_resolvent_eq_diagonal_sum
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) :
    qShift lam (resolventPoint lam) =
      -((1 / 2 : ℝ) * Finset.sum Finset.univ
        (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam))) := by
  -- The inverse of a shifted diagonal matrix is diagonal again, so the objective simplifies
  -- coordinatewise at the explicit minimizer.
  -- TODO: evaluate the resolvent coordinates explicitly and then simplify the quadratic value to
  -- the diagonal reciprocal sum.
  sorry

/-- Helper for Proposition 4.1.9: the active part of the diagonal reciprocal sum collapses to
`G² / (H_min + λ)`. -/
lemma active_diagonal_sum_eq_minimalGradientSquare_div
    (lam : ℝ) :
    Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) =
      G²[g;Hdiag] / (H_min[Hdiag] + lam) := by
  -- On `I*`, every denominator is the same because `Hdiag i = H_min`.
  unfold cubicRegularizedMinimalDiagonalGradientSquare
  calc
    Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam))
        =
          Finset.sum (I*[Hdiag])
            (fun i ↦ (g i) ^ (2 : ℕ) / (H_min[Hdiag] + lam)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi' : Hdiag i = H_min[Hdiag] :=
              (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag i).mp hi
            simp [hi']
    _ = Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ)) / (H_min[Hdiag] + lam) := by
          rw [Finset.sum_div]

/-- Helper for Proposition 4.1.9: eliminating `τ` rewrites the scalar dual value as the infimum
of the shifted quadratic minus the cubic penalty. -/
lemma cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic_local
    (hM : 0 < M) (lam : ℝ) :
    ψ lam =
      sInf (Set.range fun h : E ↦
        ((qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal)) := by
  rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
  let τ := cubicRegularizedQuadraticTauMinimizer M lam
  -- TODO: finish the `τ`-elimination argument by combining the owner-side scalar minimizer
  -- theorem with the explicit minimizing value of the scalar objective.
  sorry

/-- Helper for Proposition 4.1.9: when `λ > -H_min`, the diagonal resolvent is the global
minimizer of the shifted quadratic. -/
lemma diagonalResolvent_isMinOn_aux
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) :
    IsMinOn (qShift lam) Set.univ (resolventPoint lam) := by
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := 0
      a := g
      A := Ashift lam
      posDef := by
        -- Positivity of every shifted diagonal entry gives positive definiteness.
        rw [diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam]
        exact Matrix.PosDef.diagonal (n := Fin n) (R := ℝ)
          (d := fun i ↦ Hdiag i + lam) (by
            intro i
            have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
              diagonalMinimum_le_entry (Hdiag := Hdiag) i
            linarith) }
  -- The quadratic owner theorem identifies the canonical minimizer with the resolvent.
  simpa [problem, UnconstrainedQuadraticMinimizationProblem.minimizer] using
    (UnconstrainedQuadraticMinimizationProblem.minimizer_isMinOn problem)

-- Proof sketch: under `G² > 0`, the singular direction corresponding to `H_min` makes the dual
-- value equal to `-∞` exactly when `λ ≤ -H_min`, while `hGpos` forces `I*` nonempty and hence
-- rules out the vacuous `n = 0` case. Therefore `λ > -H_min` makes `H + λ I` positive definite
-- and the infimum finite.
/-- If `G² > 0`, then the dual domain is exactly the open half-line `(-H_min, ∞)`. -/
theorem cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
      (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) :
    dom ψ = Set.Ioi (-H_min[Hdiag]) := by
  -- TODO: combine the bounded-below owner characterization of `dom ψ` with the active-direction
  -- obstruction on the coordinate line through an active index.
  sorry

-- Proof sketch: combine the `τ`-elimination formula from
-- `cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic` with the domain
-- characterization from `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos`
-- to identify the admissible `λ`, evaluate the unique minimizer of `q_λ` at
-- `-(H + λ I)⁻¹ g`, and split the sum into the active part `G² / (H_min + λ)` and the inactive
-- complementary sum.
/-- Proposition 4.1.9: if `M > 0` and `G² > 0`, then for every `λ` in
`dom ψ = {μ : ℝ | μ > -H_min}` the dual
function has the closed form
`ψ(λ) = -(1 / 2) G² / (H_min + λ) - (1 / 2) ∑_{i ∉ I*} (g^(i))² / (H_i + λ) - (2 / (3 M²)) |λ|³`.
The companion statements around it record the domain identity, expose the owner-level minimizer
theorem for `q_λ`, and add the matching owner-level uniqueness statement. -/
theorem cubicRegularizedQuadraticDualFunction_eq_closedForm_of_activeGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) (lam : ℝ)
    (hlam : lam ∈ dom ψ) :
    ψ lam =
      ((-(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lam) -
        (1 / 2 : ℝ) * Finset.sum Irest (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) -
        (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) : ℝ) : EReal) := by
  -- TODO: once the local `τ`-elimination and the resolvent-value identity are available, replace
  -- the infimum by the minimizing quadratic value and split the full diagonal sum into active and
  -- inactive parts.
  sorry

-- Proof sketch: `-H_min < λ` is exactly the intrinsic diagonal positivity condition for
-- `H + λ I`. The shifted quadratic owner `q_λ` then has the canonical Euclidean-space
-- resolvent minimizer `resolvent λ`, whose coordinate formula is recorded downstream in
-- `Proposition_4_1_10`.
/-- If `λ > -H_min`, then the canonical diagonal resolvent point `resolvent λ` minimizes the
shifted quadratic `q_λ`. -/
theorem cubicRegularizedDiagonalResolvent_isMinOn
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) :
    IsMinOn (qShift lam) Set.univ (resolventPoint lam) := by
  -- This source-facing theorem is the public wrapper around the earlier owner-level helper.
  exact diagonalResolvent_isMinOn_aux (g := g) (Hdiag := Hdiag) lam hlam

-- Proof sketch: package `q_λ` as an `UnconstrainedQuadraticMinimizationProblem`, use the
-- Chapter 1 owner theorem `minimizer_unique`, and compare the given minimizer with the canonical
-- resolvent minimizer above.
/-- If `λ > -H_min`, then every global minimizer of the shifted diagonal quadratic `q_λ`
coincides with the canonical diagonal resolvent point `resolvent λ`. -/
theorem cubicRegularizedDiagonalResolvent_unique
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam)
    (h : E)
    (hh : IsMinOn (qShift lam) Set.univ h) :
    h = resolventPoint lam := by
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := 0
      a := g
      A := Ashift lam
      posDef := by
        -- This is the same positive-definite shifted quadratic packaged in owner form.
        rw [diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam]
        exact Matrix.PosDef.diagonal (n := Fin n) (R := ℝ)
          (d := fun i ↦ Hdiag i + lam) (by
            intro i
            have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
              diagonalMinimum_le_entry (Hdiag := Hdiag) i
            linarith) }
  -- The Chapter 1 uniqueness theorem identifies every minimizer with `problem.minimizer`.
  simpa [problem, UnconstrainedQuadraticMinimizationProblem.minimizer, shiftedQuadraticObjective,
    diagonalResolventPoint] using
    (UnconstrainedQuadraticMinimizationProblem.minimizer_unique problem hh)

end

end
