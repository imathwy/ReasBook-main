import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_1_9 (from Chap04) -/
open scoped Gradient
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.1.9 lies in the gradient-domination / global-minimization domain on a real
inner-product space. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`.

Sampled owner-style declarations:
* `IsMinOn` in mathlib, the canonical fixed-point minimizer predicate on a feasible set;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for minimizer sets on a feasible set;
* `gradientWithin`, `HasGradientWithinAt`, and `UniqueDiffOn` in mathlib / Chapter 2, the
  canonical constrained first-order owner layer when within derivatives are required to be
  intrinsic on a feasible set;
* `StarConvexFunction` in `Chap04/Definition_4_1_7`, which keeps a source-facing optimization
  property while exposing the minimizer layer through the canonical owner data;
* `HasGloballyNondegenerateOptimalSet` in `Chap04/Definition_4_1_8`, which likewise treats the
  optimal set as derived canonical API rather than duplicating a local wrapper.

Best owner abstraction:
* source-facing: `GradientDominatedOn p 𝓕 f`;
* core/canonical: `DifferentiableOn ℝ f 𝓕`, `UniqueDiffOn ℝ 𝓕`, `gradientWithin f 𝓕`,
  `argmin[𝓕] f`, and `IsMinOn f 𝓕 xStar`;
* bridge/view: `GradientDominatedOn.UsesConstant` and
  `GradientDominatedOn.exists_usesConstant_of_mem_argmin`.

Primitive data:
* a feasible set `𝓕 : Set E`;
* a differentiable objective `f : E → ℝ` on `𝓕`;
* a unique-differentiability hypothesis on `𝓕`, making `gradientWithin f 𝓕` intrinsic;
* a degree `p ∈ [1, 2]`;
* existence of a feasible global minimizer and a positive domination constant.

Derived API:
* nonemptiness of the canonical optimal set `argmin[𝓕] f`;
* the constrained gradient map `gradientWithin f 𝓕`, now used only on the intrinsic
  `UniqueDiffOn ℝ 𝓕` layer;
* the bridge predicate `GradientDominatedOn.UsesConstant p 𝓕 f xStar τf`;
* transport of one domination constant to any canonical minimizer in `argmin[𝓕] f`.

This refinement keeps the source-facing owner `GradientDominatedOn`, upgrades the minimizer field
to the canonical owner `argmin[𝓕] f`, and records the minimal `UniqueDiffOn ℝ 𝓕` hypothesis
needed for `gradientWithin f 𝓕` to be a canonical first-order datum rather than an arbitrary
chosen `fderivWithin` witness. On open feasible sets, and in particular for `𝓕 = Set.univ`, the
resulting bound reduces to the textbook ambient-gradient form.
-/

namespace GradientDominatedOn

/-- `UsesConstant p 𝓕 f xStar τf` packages the unique differentiability of the feasible set, the
canonical `argmin` membership of `xStar`, and the positive domination constant `τf` used in the
source-facing gradient-domination bound. -/
def UsesConstant (p : ℝ) (𝓕 : Set E) (f : E → ℝ) (xStar : E) (τf : ℝ) : Prop :=
  UniqueDiffOn ℝ 𝓕 ∧ xStar ∈ argmin[𝓕] f ∧ 0 < τf ∧
    ∀ ⦃x : E⦄, x ∈ 𝓕 → f x - f xStar ≤ τf * Real.rpow ‖gradientWithin f 𝓕 x‖ p

end GradientDominatedOn

/-- Definition 4.1.9: a differentiable function `f` on a uniquely differentiable feasible set
`𝓕 ⊆ ℝⁿ` is gradient dominated of degree `p ∈ [1, 2]` when it has a global minimizer `xStar` on
`𝓕` and a positive constant `τf` such that
`f x - f xStar ≤ τf * ‖gradientWithin f 𝓕 x‖^p` for every `x ∈ 𝓕`. On open feasible sets, and in
particular for `𝓕 = Set.univ`, this agrees with the textbook ambient-gradient form. -/
class GradientDominatedOn (p : ℝ) (𝓕 : Set E) (f : E → ℝ) : Prop where
  /-- The function is differentiable on the feasible set. -/
  differentiableOn : DifferentiableOn ℝ f 𝓕
  /-- The degree of domination lies in the interval `[1, 2]`. -/
  degree_mem_Icc : p ∈ Set.Icc (1 : ℝ) 2
  /-- The canonical minimizer set `argmin[𝓕] f` is nonempty, and one minimizer carries the
  unique-differentiability and positive-constant data needed for the source-facing
  gradient-domination inequality. -/
  exists_usesConstant :
    ∃ xStar τf, GradientDominatedOn.UsesConstant p 𝓕 f xStar τf

namespace GradientDominatedOn

variable {p : ℝ} {𝓕 : Set E} {f : E → ℝ}

theorem uniqueDiffOn (hf : GradientDominatedOn p 𝓕 f) :
    UniqueDiffOn ℝ 𝓕 := by
  rcases hf.exists_usesConstant with ⟨xStar, τf, hτf⟩
  exact hτf.1

/-- A `GradientDominatedOn p 𝓕 f` hypothesis canonically supplies the differentiability of `f` on
`𝓕`, the intrinsic within-gradient layer on `𝓕`, and the admissible degree range
`p ∈ [1, 2]`. -/
instance {p : ℝ} {𝓕 : Set E} {f : E → ℝ} [hf : GradientDominatedOn p 𝓕 f] :
    Fact (DifferentiableOn ℝ f 𝓕 ∧ UniqueDiffOn ℝ 𝓕 ∧ p ∈ Set.Icc (1 : ℝ) 2) where
  out := ⟨hf.differentiableOn, hf.uniqueDiffOn, hf.degree_mem_Icc⟩

theorem UsesConstant.uniqueDiffOn
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) :
    UniqueDiffOn ℝ 𝓕 :=
  hτf.1

theorem UsesConstant.mem_argmin
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) :
    xStar ∈ argmin[𝓕] f :=
  hτf.2.1

theorem UsesConstant.pos
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) :
    0 < τf :=
  hτf.2.2.1

theorem UsesConstant.bound
    {xStar : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf) {x : E} (hx : x ∈ 𝓕) :
    f x - f xStar ≤ τf * Real.rpow ‖gradientWithin f 𝓕 x‖ p :=
  hτf.2.2.2 hx

/-- On an open feasible set, the within-gradient bound from `UsesConstant` is exactly the
textbook ambient-gradient bound. -/
theorem UsesConstant.bound_eq_gradient_of_isOpen
    {xStar x : E} {τf : ℝ}
    (hτf : UsesConstant p 𝓕 f xStar τf)
    (hf : DifferentiableOn ℝ f 𝓕) (h𝓕_open : IsOpen 𝓕) (hx : x ∈ 𝓕) :
    f x - f xStar ≤ τf * Real.rpow ‖∇ f x‖ p := by
  have hgrad : gradientWithin f 𝓕 x = ∇ f x := by
    rw [gradientWithin, gradient]
    congr
    exact fderivWithin_eq_fderiv (h𝓕_open.uniqueDiffWithinAt hx)
      ((hf x hx).differentiableAt (h𝓕_open.mem_nhds hx))
  simpa [hgrad] using hτf.bound hx

/-- Any point of the canonical minimizer set can be paired with some positive domination
constant. -/
theorem exists_usesConstant_of_mem_argmin
    (hf : GradientDominatedOn p 𝓕 f) {xStar : E} (hxStar : xStar ∈ argmin[𝓕] f) :
    ∃ τf, UsesConstant p 𝓕 f xStar τf := by
  rcases hf.exists_usesConstant with ⟨yStar, τf, hyStar⟩
  have hxStar_mem : xStar ∈ argmin[𝓕] f := hxStar
  have hyStar_mem : yStar ∈ argmin[𝓕] f := hyStar.mem_argmin
  rw [mem_constrainedArgmin_iff] at hxStar hyStar_mem
  have hfxStar : f xStar = f yStar := by
    exact le_antisymm (hxStar.2 hyStar_mem.1) (hyStar_mem.2 hxStar.1)
  refine ⟨τf, ⟨hyStar.uniqueDiffOn, hxStar_mem, hyStar.pos, ?_⟩⟩
  intro x hx
  simpa [hfxStar] using hyStar.bound hx

end GradientDominatedOn

/-- A gradient-dominated function has a nonempty canonical minimizer set on its feasible set. -/
theorem GradientDominatedOn.argmin_nonempty
    {p : ℝ} {𝓕 : Set E} {f : E → ℝ} (hf : GradientDominatedOn p 𝓕 f) :
    (argmin[𝓕] f).Nonempty := by
  rcases hf.exists_usesConstant with ⟨xStar, τf, hτf⟩
  exact ⟨xStar, hτf.mem_argmin⟩

/-! ### Lemma_4_1_9 (from Chap04) -/
noncomputable section

universe u

open scoped LevelSetNotation

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 4.1.9 lies in the nonlinear change-of-variables / convex sublevel-set domain.

Sampled owner declarations:
* project `𝓛[f](a)` / `mem_levelSet_iff` in `Chap01/Definition_1_4_8`, the chapter owner for
  sublevel sets
* mathlib `Equiv.symm_apply_apply` and `Equiv.apply_symm_apply`
* mathlib `ConvexOn.convex_le`
* mathlib `Convex.norm_image_sub_le_of_norm_fderivWithin_le`
* the core canonical sublevel-set expression `(f ⁻¹' Set.Iic a : Set E)`

Source/core/bridge triage:
* source-facing: the distortion estimate on a transformed sublevel set
* core/canonical: an invertible map `u : E ≃ E`, a convex function `φ`, the transformed objective
  `φ ∘ u`, and the chapter owner surface `𝓛[φ](φ (u x0))` and `𝓛[φ ∘ u]((φ ∘ u) x0)`
* bridge/view: the raw preimage forms `φ ⁻¹' Set.Iic (φ (u x0))` and
  `(φ ∘ u) ⁻¹' Set.Iic ((φ ∘ u) x0)`, together with the textbook set-builder forms
  `{z | φ z ≤ φ (u x0)}` and
  `{x | φ (u x) ≤ φ (u x0)}`

Best owner abstraction:
* the previous local structure `NonlinearConvexTransformationCore` was a duplicate wheel
* the mathematically primitive owner layer for this lemma is `u : E ≃ E`, not a bespoke wrapper
* the stronger chapter structure `NonlinearConvexTransformation` packages extra data for later
  results, so using it as the main parameter here would over-strengthen the source lemma

Primitive data:
* `u : E ≃ E`, `φ : E → ℝ`, and `x0 : E`
* whole-space convexity `ConvexOn ℝ Set.univ φ`
* differentiability of `u.symm` on the image-side level set `𝓛[φ](φ (u x0))`
* the derivative-within-set bound
  `‖fderivWithin ℝ u.symm (𝓛[φ](φ (u x0))) z‖ ≤ σ`
  on that same image-side level set

Derived API:
* the x-side transformed level set is `𝓛[φ ∘ u]((φ ∘ u) x0)`
* membership in that level set is exactly the textbook inequality `φ (u x) ≤ φ (u x0)`

The refinement therefore deletes the wrapper structure and its local duplicate objective/sublevel
definitions, keeps the primitive equivalence-level source semantics, and states the item on the
chapter owner layer `𝓛[·](·)` rather than on the raw preimage bridge. -/

section

variable (u : E ≃ E) (φ : E → ℝ) (x0 : E)

local notation "S" => (𝓛[φ]((φ (u x0))) : Set E)
local notation "T" => (𝓛[(φ ∘ u)](((φ ∘ u) x0)) : Set E)

-- Proof sketch: write `x = u.symm (u x)` and `y = u.symm (u y)` using the inverse identities. The
-- image points `u x` and `u y` lie in the convex level set `𝓛[φ](φ (u x0))`, so the whole segment
-- between them stays in that set. Apply the convex mean-value inequality to `u.symm` within this
-- image-side sublevel set and use the uniform within-set derivative bound there.
/-- Lemma 4.1.9: if `φ ∘ u` is obtained from a nonlinear change of variables with convex `φ`, and
`‖fderivWithin ℝ u.symm (𝓛[φ](φ (u x0))) z‖ ≤ σ` on the image-side level set
`𝓛[φ](φ (u x0))`, then any two points of the transformed level set
`𝓛[φ ∘ u]((φ ∘ u) x0)` satisfy
`‖x - y‖ ≤ σ ‖u x - u y‖`. -/
theorem norm_sub_le_sigma_mul_norm_image_sub
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hdiff : DifferentiableOn ℝ u.symm S)
    (σ : ℝ)
    (hσ :
      ∀ ⦃z : E⦄, z ∈ S → ‖fderivWithin ℝ u.symm S z‖ ≤ σ)
    {x y : E}
    (hx : x ∈ T)
    (hy : y ∈ T) :
    ‖x - y‖ ≤ σ * ‖u x - u y‖ := by
  have hs : Convex ℝ S := by
    change Convex ℝ (𝓛[φ]((φ (u x0))) : Set E)
    simpa [Function.comp, Set.preimage, Set.mem_Iic, Set.sep_univ] using
      hφ_convex.convex_le ((φ ∘ u) x0)
  have hxS : u x ∈ S := by
    change φ (u x) ≤ (φ ∘ u) x0
    simpa [Function.comp] using hx
  have hyS : u y ∈ S := by
    change φ (u y) ≤ (φ ∘ u) x0
    simpa [Function.comp] using hy
  simpa using hs.norm_image_sub_le_of_norm_fderivWithin_le hdiff hσ hyS hxS

end

/-! ### Proposition_4_1_9 (from Chap04) -/
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

/-! ### Theorem_4_1_9 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.1.9 lies in the nonlinear-transformation / strong-convex cubic-regularization rate
domain.

Sampled owner declarations:
* `NonlinearConvexTransformation` in `Definition_4_1_10`, the source-facing owner for the
  transformed objective, transported minimizer, and level-set constants `σ` and `D`;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the chapter owner for the iterate sequence
  and regularization schedule;
* `HessianLipschitzOn` in `Definition_4_1_2`, the canonical chapter owner for local convex
  Hessian-Lipschitz control on a comparison set;
* `CubicRegularizationMethod.objective_succ_le_feasibleComparison` in `Theorem_4_1_8`, the
  owner-level one-step feasible comparison estimate used by the transformed cubic-rate bounds.

Source/core/bridge triage:
* source-facing: the first-phase decay, termination, and second-phase superlinear estimates for a
  strongly convex transformed objective;
* core/canonical: `NonlinearConvexTransformation`, `CubicRegularizationMethod`, and
  `StrongConvexOn Set.univ μ problem.φ`;
* bridge/view: the scalar threshold `\tilde ω`.

Primitive data:
* the transformed problem `problem`;
* the comparison set `𝓕` together with the sublevel containment hypothesis from Theorem 4.1.8;
* the canonical smoothness owner `HessianLipschitzOn L 𝓕 problem.objective`;
* the cubic-regularization method `method`;
* the strong-convexity parameter `μ > 0`.

Derived API:
* the threshold `\tilde ω = 2 L σ^3 / μ^(3/2)`;
* the objective gaps `f(x_k) - f(x*)`;
* the owner-level one-step feasible comparison estimate from
  `CubicRegularizationMethod.objective_succ_le_feasibleComparison`;
* the phase-wise gap estimates below.

The monotonicity needed to keep the trajectory inside the initial sublevel set is already derived
from the chapter owner `CubicRegularizationMethod`, and Theorem 4.1.8 already upgrades the
one-step feasible comparison estimate to the owner theorem
`CubicRegularizationMethod.objective_succ_le_feasibleComparison`. This refinement therefore keeps
the Theorem 4.1.8 comparison-set hypotheses explicit, preserves the source-facing theorem family
semantics, and derives the one-step feasible comparison bound from the method owner rather than
keeping it as parallel public data. -/

/-- The threshold `\tilde ω = 2 L σ^3 / μ^(3/2)` governing the two-phase convergence estimate for
cubic regularization after a nonlinear transformation of a strongly convex function. -/
abbrev nonlinearTransformationStrongConvexCubicThreshold
    (L σ μ : ℝ) : ℝ :=
  (2 * L * σ ^ (3 : ℕ)) / Real.rpow μ (3 / 2 : ℝ)

/-- Expanding `nonlinearTransformationStrongConvexCubicThreshold L σ μ` recovers the textbook
formula `\tilde ω = 2 L σ^3 / μ^(3/2)`. -/
@[simp]
theorem nonlinearTransformationStrongConvexCubicThreshold_def
    (L σ μ : ℝ) :
    nonlinearTransformationStrongConvexCubicThreshold L σ μ =
      (2 * L * σ ^ (3 : ℕ)) / Real.rpow μ (3 / 2 : ℝ) :=
  rfl

section NonlinearTransformationStrongConvexCubicRate

variable (problem : NonlinearConvexTransformation E)
variable (𝓕 : Set E) (μ : ℝ) {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal}
variable
  (method :
    CubicRegularizationMethod
      problem
      stepMap
      L0 (L : ℝ) problem.x0)

local notation "f" => problem
local notation "𝓛₀" => f ⁻¹' Set.Iic (f problem.x0)
local notation "ω̃" =>
  nonlinearTransformationStrongConvexCubicThreshold (L : ℝ) problem.sigma μ
local notation "Δ" => fun k : ℕ ↦ f (method k) - f problem.xStar

variable
  (hlevel_subset : 𝓛₀ ⊆ 𝓕)
  [HessianLipschitzOn L 𝓕 problem]
  (hμ : 0 < μ)
  (hphi_strong : StrongConvexOn Set.univ μ problem.φ)

-- Proof sketch: apply
-- `method.objective_succ_le_feasibleComparison hlevel_subset`
-- from Theorem 4.1.8 at the comparison point `v (α • u* + (1 - α) • u (x_k))`, then use
-- convexity of `φ` and strong convexity at `u*` to bound the objective and distance terms.
-- Rewrite the resulting scalar recursion in terms of
-- `\tilde ω = nonlinearTransformationStrongConvexCubicThreshold L σ μ`, and iterate the same
-- first-phase argument as in the star-convex model case.
/-- Theorem 4.1.9 (1): under the nonlinear-transformation assumptions from Theorem 4.1.8, if
`φ` is `μ`-strongly convex and the initial gap is at least `(4 / 9) * \tilde ω`, then every
iterate whose gap is still above that threshold satisfies the fourth-root decay bound. -/
theorem nonlinearTransformation_cubicRegularization_firstPhase_gap_bound
    (hgap0 :
      Δ 0 ≥ (4 / 9 : ℝ) * ω̃)
    (k : ℕ)
    (hk : Δ k ≥ (4 / 9 : ℝ) * ω̃) :
    Δ k ≤
      (Real.rpow (Δ 0) (1 / 4 : ℝ) -
        ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ)) ^
        (4 : ℕ) := sorry

-- Proof sketch: apply the first-phase scalar recursion from the previous theorem to the
-- normalized gaps `Δ_k = (f(x_k) - f(x*)) / \tilde ω`. The same argument as in the first phase
-- shows that this recursion cannot remain forever in the regime `Δ_k > 4 / 9`, so some iterate
-- must cross the threshold.
/-- Theorem 4.1.9 (2): under the same assumptions, the first phase ends at some index `k₀` where
`f(x_{k₀}) - f(x^*) ≤ (4 / 9) * \tilde ω`. -/
theorem nonlinearTransformation_cubicRegularization_firstPhase_terminates
    (hgap0 :
      Δ 0 ≥ (4 / 9 : ℝ) * ω̃) :
    ∃ k0 : ℕ,
      Δ k0 ≤ (4 / 9 : ℝ) * ω̃ := sorry

-- Proof sketch: once `f(x_k) - f(x*) ≤ (4 / 9) * \tilde ω`, the scalar upper bound obtained from
-- the comparison points
-- `v (α • u* + (1 - α) • u (x_k))` is minimized at `α = 1`, giving
-- `Δ_{k+1} ≤ (1 / 2) Δ_k^(3/2)` for `Δ_k = (f(x_k) - f(x*)) / \tilde ω`. Rewriting this bound
-- in terms of the original objective values yields the displayed superlinear recurrence.
/-- Theorem 4.1.9 (3): once an iterate reaches the threshold `(4 / 9) * \tilde ω`, every later
iterate satisfies the superlinear estimate
`f(x_{k+1}) - f(x^*) ≤ (1 / 2) (f(x_k) - f(x^*)) * sqrt ((f(x_k) - f(x^*)) / \tilde ω)`. -/
theorem nonlinearTransformation_cubicRegularization_secondPhase_gap_le_superlinear
    (k0 : ℕ)
    (hk0 : Δ k0 ≤ (4 / 9 : ℝ) * ω̃)
    (k : ℕ)
    (hk : k0 ≤ k) :
    Δ (k + 1) ≤
      (1 / 2 : ℝ) * Δ k * Real.sqrt (Δ k / ω̃) := sorry

end NonlinearTransformationStrongConvexCubicRate

/-! ### Definition_4_1_10 (from Chap04) -/
noncomputable section

universe u

open scoped LevelSetNotation

/-
Definition 4.1.10 lies in the nonlinear change-of-variables domain for convex minimization.

Sampled owner-style declarations:
* project `𝓛[f](a)` / `mem_levelSet_iff` in `Chap01/Definition_1_4_8`, the chapter owner for
  sublevel sets;
* project `norm_sub_le_sigma_mul_norm_image_sub` in `Chap04/Lemma_4_1_9`, which uses the same
  controlling level set and the derivative bound needed downstream;
* project `modifiedGaussNewtonLocalModel` in `Chap04/Definition_4_4_11`, which treats a
  pointwise Jacobian family as primitive data via the canonical owner `HasFDerivAt`;
* mathlib `IsMinOn f Set.univ xStar`, the canonical owner of the chosen minimizer relation.

Best owner abstraction:
* source-facing: the nonlinear convex transformation together with the chosen minimizer `uStar`
  and the textbook constants `σ` and `D`;
* core/canonical: the equivalence `u : E ≃ E`, the potential `φ`, the chapter level-set owner
  `𝓛[φ](φ (u x0))`, and pointwise differentiability of `u.symm` together with its canonical
  derivative `fderiv ℝ u.symm` on that level set;
* bridge/view: the transformed objective `φ ∘ u`, the transported minimizer `xStar`, and the
  derived within-set differentiability used by later mean-value estimates.

Primitive data:
* the equivalence `u`, the convex potential `φ`, the base point `x0`;
* pointwise differentiability of `u.symm` on the controlling level set;
* the chosen minimizer `uStar` of `φ`;
* the constants `σ` and `D` recorded by their attained-maximum properties on the controlling
  level set.

Derived API:
* the transformed objective `objective`;
* the transported minimizer `xStar = u.symm uStar`;
* the within-set differentiability and derivative-norm bounds needed by the distortion lemma.

This file therefore keeps the source-facing owner `NonlinearConvexTransformation`, but reuses the
chapter sublevel-set owner directly and records `σ` using the ordinary derivative data of
`u.symm`, not the proof-oriented within derivative. -/

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 4.1.10: a nonlinear transformation of a convex objective consists of an
invertible map `u : E → E`, a convex function `φ`, a starting point `x₀`, differentiability of
`u⁻¹` on the controlling level set `𝓛[φ]((φ (u x₀)))`, a chosen minimizer `u*` of `φ`, and the
corresponding constants `σ` and `D`. The transformed objective is `f = φ ∘ u`, the transported
minimizer is `x* = u⁻¹(u*)`, and the constants `σ` and `D` are the maxima of
`‖(u⁻¹)'(z)‖` and `‖z - u*‖` on `𝓛[φ]((φ (u x₀)))`. -/
structure NonlinearConvexTransformation where
  /-- The nonlinear change of variables `u`. -/
  u : E ≃ E
  /-- The convex potential `φ`. -/
  φ : E → ℝ
  /-- The starting point `x₀`. -/
  x0 : E
  /-- The potential `φ` is convex on the whole space. -/
  φ_convex : ConvexOn ℝ Set.univ φ
  /-- The inverse map `u⁻¹` is differentiable at every point of the controlling level set
  `𝓛[φ]((φ (u x₀)))`. -/
  u_symm_differentiableAt_controllingLevelSet
    {z : E} (hz : z ∈ (𝓛[φ]((φ (u x0))) : Set E)) : DifferentiableAt ℝ u.symm z
  /-- The chosen global minimizer `u*` of `φ`. -/
  uStar : E
  /-- The chosen point `u*` minimizes `φ` globally. -/
  isMinOn_uStar : IsMinOn φ Set.univ uStar
  /-- The constant `σ`, defined as the maximum of `‖fderiv ℝ u.symm z‖` on the controlling
  level set. -/
  sigma : ℝ
  /-- The displayed value `σ` is the maximum of `‖fderiv ℝ u.symm z‖` on the controlling level
  set. -/
  sigma_isGreatest :
    IsGreatest
      ((fun z : E ↦ ‖fderiv ℝ u.symm z‖) '' (𝓛[φ]((φ (u x0))) : Set E))
      sigma
  /-- The constant `D`, defined as the maximum distance from `u*` on the controlling level set. -/
  D : ℝ
  /-- The displayed value `D` is the maximum of `‖z - u*‖` on the controlling level set. -/
  D_isGreatest :
    IsGreatest
      ((fun z : E ↦ ‖z - uStar‖) '' (𝓛[φ]((φ (u x0))) : Set E))
      D

namespace NonlinearConvexTransformation

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The transformed objective `f(x) = φ(u(x))`. -/
def objective (problem : NonlinearConvexTransformation E) : E → ℝ :=
  problem.φ ∘ problem.u

/-- A nonlinear convex transformation can be used as its transformed objective `f = φ ∘ u`. -/
instance : CoeFun (NonlinearConvexTransformation E) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

/-- Evaluating the transformed objective recovers `φ (u x)`. -/
@[simp] theorem objective_apply (problem : NonlinearConvexTransformation E) (x : E) :
    problem.objective x = problem.φ (problem.u x) :=
  rfl

/-- A nonlinear convex transformation evaluates as its transformed objective. -/
@[simp] theorem coe_apply (problem : NonlinearConvexTransformation E) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The inverse map `u⁻¹` is differentiable on the controlling level set
`𝓛[φ]((φ (u x₀)))`. -/
theorem u_symm_differentiableOn_controllingLevelSet
    (problem : NonlinearConvexTransformation E) :
    DifferentiableOn ℝ problem.u.symm
      (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E) := by
  intro z hz
  exact (problem.u_symm_differentiableAt_controllingLevelSet hz).differentiableWithinAt

/-- On the controlling level set, the ordinary derivative norm of `u⁻¹` is bounded by `σ`. -/
theorem norm_fderiv_u_symm_le_sigma
    (problem : NonlinearConvexTransformation E)
    {z : E}
    (hz : z ∈ (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)) :
    ‖fderiv ℝ problem.u.symm z‖ ≤ problem.sigma := by
  exact
    problem.sigma_isGreatest.2
      (Set.mem_image_of_mem (fun z : E ↦ ‖fderiv ℝ problem.u.symm z‖) hz)

/-- Every point of the controlling level set lies at distance at most `D` from `u*`. -/
theorem norm_sub_uStar_le_D
    (problem : NonlinearConvexTransformation E)
    {z : E}
    (hz : z ∈ (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)) :
    ‖z - problem.uStar‖ ≤ problem.D := by
  exact problem.D_isGreatest.2 (Set.mem_image_of_mem (fun z : E ↦ ‖z - problem.uStar‖) hz)

/-- The point `x* = u⁻¹(u*)` corresponding to the chosen minimizer `u*` of `φ`. -/
def xStar (problem : NonlinearConvexTransformation E) : E :=
  problem.u.symm problem.uStar

/-- The point `x* = u⁻¹(u*)` is a global minimizer of the transformed objective `f = φ ∘ u`. -/
theorem isMinOn_xStar (problem : NonlinearConvexTransformation E) :
    IsMinOn problem Set.univ problem.xStar := by
  have hphi : IsMinOn problem.φ Set.univ (problem.u problem.xStar) := by
    simpa [xStar] using problem.isMinOn_uStar
  simpa [objective] using hphi.on_preimage problem.u

end NonlinearConvexTransformation

/-! ### Proposition_4_1_10 (from Chap04) -/
noncomputable section
open scoped CubicRegularizedDiagonalInvariants

variable {n : ℕ} [NeZero n]

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.10 belongs to the diagonal quadratic-minimization interface.

Sampled owner declarations:
* `quadraticObjective` for the shifted quadratic `q_λ`;
* `UnconstrainedQuadraticMinimizationProblem.minimizer` and
  `UnconstrainedQuadraticMinimizationProblem.minimizer_unique` for the canonical quadratic
  minimizer / uniqueness owner;
* `cubicRegularizedDiagonalMinimum`, `cubicRegularizedMinimalDiagonalIndices`, and
  `cubicRegularizedMinimalDiagonalGradientSquare` for `H_min`, `I*`, and `G²`;
* `cubicRegularizedDiagonalResolvent_isMinOn` in `Proposition_4_1_9`, the upstream owner-level
  minimizer theorem for the diagonal resolvent point.

Source/core/bridge triage:
* source-facing: the coordinate description of the minimizer of `q_λ` in the degenerate case
  `G² = 0`;
* core/canonical: the shifted diagonal quadratic together with its resolvent point
  `-(diag(Hdiag + λ))⁻¹ g`;
* bridge/view: the coordinate formula for that resolvent and the equivalence between being a
  minimizer and satisfying the textbook coordinate formula.

Primitive data:
* the diagonal data `Hdiag`, gradient `g`, and shift `λ`;
* the strict interior inequality `λ > -H_min`.

Derived API:
* the coordinate formula for the diagonal resolvent point;
* the upstream owner-level minimizer theorem for that resolvent;
* the source-facing `iff` statement in the degenerate case `G² = 0`.

This file therefore keeps Proposition 4.1.10 as a source-facing bridge theorem, but exposes the
canonical diagonal resolvent minimizer through the upstream owner theorem in
`Proposition_4_1_9` instead of owning a second copy here. -/

section

variable (g : E) (Hdiag : Fin n → ℝ) (lam : ℝ)

local notation "A" => Matrix.diagonal fun i ↦ Hdiag i + lam

/-- Evaluating the diagonal resolvent point `-(diag(Hdiag + λ))⁻¹ g` gives the coordinate formula
`-g i / (H_i + λ)`. -/
theorem cubicRegularizedDiagonalResolvent_apply
    (hlam : -H_min[Hdiag] < lam) (i : Fin n) :
    (-((A)⁻¹).mulVec g) i = -g i / (Hdiag i + lam) := sorry

/- The owner-level minimizer statement for the diagonal resolvent point is already the upstream
theorem `cubicRegularizedDiagonalResolvent_isMinOn`. -/
recall cubicRegularizedDiagonalResolvent_isMinOn

-- Proof sketch: `λ > -H_min` makes the shifted diagonal Hessian strictly positive, so the
-- shifted quadratic has the canonical resolvent minimizer above. The hypothesis `G² = 0`
-- forces `g i = 0` on `I*`, and the resolvent coordinate formula then reduces exactly to the
-- textbook description `h i = 0` on `I*` and `h i = -g i / (H_i + λ)` off `I*`. Uniqueness of
-- the quadratic minimizer supplies the converse direction.
/-- Proposition 4.1.10: if `G² = 0` and `λ > -H_min`, then a vector `h` minimizes the shifted
diagonal quadratic `q_λ` on `ℝⁿ` exactly when its coordinates satisfy
`h i = 0` on `I*` and `h i = -g i / (H_i + λ)` off `I*`. -/
theorem cubicRegularizedDiagonal_isMinOn_iff
    (hG : G²[g;Hdiag] = 0)
    (hlam : -H_min[Hdiag] < lam)
    (h : E) :
    IsMinOn (quadraticObjective 0 g A) Set.univ h ↔
      ∀ i : Fin n,
        h i =
          if i ∈ I*[Hdiag] then
            0
          else
            -g i / (Hdiag i + lam) := sorry

end

/-! ### Theorem_4_1_10 (from Chap04) -/
noncomputable section
open scoped CubicRegularizedDiagonalInvariants

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Domain/API note for this item: the theorem lies in the diagonal cubic-regularized quadratic /
scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Definition_4_1_14`, the chapter owner of the primal
  cubic model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos` in
  `Proposition_4_1_9`, the existing source-facing domain identity in the nondegenerate diagonal
  case;
* `cubicRegularizedDiagonalMinimum` and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal owners of
  `H_min` and `G²`;
* `cubicRegularizedQuadraticTauMinimizer` and
  `cubicRegularizedQuadraticTauMinimizer_def` in `Definition_4_1_14`, the chapter owner and
  defining formula for the slack minimizer `τ(λ)`.

Best owner abstraction:
* source-facing: the diagonal `G² > 0` strong-duality and minimizer statements from the source;
* core/canonical: the generic cubic-regularized quadratic objective, dual function, dual domain,
  and tau minimizer together with the diagonal bounded-below-domain owner;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag`.

Primitive data:
* the gradient `g`, diagonal data `Hdiag`, cubic parameter `M`, and the diagonal matrix
  `H = Matrix.diagonal Hdiag`;
* the canonical diagonal invariants `H_min` and `G²`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `cubicRegularizedQuadraticDualFunction g H M`;
* `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`;
* `IsMaxOn (cubicRegularizedQuadraticDualFunction g H M)
    (cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)) lam`;
* `cubicRegularizedQuadraticTauMinimizer M lam`.

This file therefore keeps the source-facing diagonal theorem family, but removes duplicate local
owners for the primal objective, shifted quadratic form, and dual function. The source domain
clause is reused directly from `Proposition_4_1_9`, while the explicit `τ(λ*)` formula is
reused from the existing owner theorem `cubicRegularizedQuadraticTauMinimizer_def`. -/

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)

/- The nondegenerate diagonal domain identity is already the source-facing proposition
`cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos`. -/
recall cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos

-- Proof sketch: combine the positivity assumption `G² > 0` with the diagonal analysis of the
-- shifted quadratic subproblem to identify the maximizing dual parameter range. Then apply strong
-- duality for the epigraph reformulation to identify the primal infimum with the dual value at a
-- nonnegative dual maximizer.
/-- Theorem 4.1.10: for the diagonal cubic-regularized quadratic model with `H = diag(Hdiag)`,
if `G² = ∑_{i : Hdiag i = H_min} (g i)^2` is positive, then every nonnegative dual maximizer on
`cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici 0` yields strong duality:
the minimum of the primal objective equals the dual value `ψ(λ*)`.
The companion entries in this file record the strong-duality consequences, the explicit primal
minimizer, and the owner-level formula
`cubicRegularizedQuadraticTauMinimizer_def` for the associated slack minimizer `τ(λ*)`. -/
theorem
    cubicRegularizedQuadraticDiagonal_strongDuality_of_dualMaximizer_of_minimalGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar) :
    sInf (Set.range fun h : E ↦
      (cubicRegularizedQuadraticObjective g H M h : EReal)) =
        cubicRegularizedQuadraticDualFunction g H M lamStar := sorry

-- Proof sketch: solve the shifted quadratic subproblem at the maximizing multiplier `λ*`, using
-- the positivity assumption `G² > 0` and the optimality relations from the strong-duality
-- statement to show that the resolvent point minimizes the primal cubic objective.
/-- Under the hypotheses of
`cubicRegularizedQuadraticDiagonal_strongDuality_of_dualMaximizer_of_minimalGradientSquare_pos`,
the primal problem admits the explicit global minimizer
`h* = -(H + λ* I)⁻¹ g`. -/
theorem
    cubicRegularizedQuadraticDiagonal_primalMinimizer_of_dualMaximizer_of_minimalGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar) :
    IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
      (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) := sorry

/- The source formula `τ(λ*) = 4 λ* |λ*| / M²` is already the exact owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`. -/
recall cubicRegularizedQuadraticTauMinimizer_def

end

/-! ### Definition_4_1_11 (from Chap04) -/
noncomputable section

/- Definition 4.1.11 lies in the nonlinear-transformation / triangular-coordinate domain.

Sampled owner declarations:
* project `NonlinearConvexTransformation` in `Definition_4_1_10`, the nearby owner for a
  source-facing change of variables on `EuclideanSpace ℝ (Fin n)`;
* mathlib `Differentiable`, the canonical regularity predicate for the coordinate-correction
  maps `φ₁, …, φₙ₋₁`;
* mathlib `Fin.cons`, the canonical owner API for assembling a `Fin (n + 1)`-tuple from its first
  coordinate and remaining coordinates;
* mathlib subtype indices `{i : Fin (n + 1) // i ≠ 0}`, the canonical way to speak about the
  higher coordinates while keeping the first coordinate separate;
* mathlib `EuclideanSpace.equiv`, the canonical bridge between `EuclideanSpace ℝ (Fin k)` and
  coordinate functions `Fin k → ℝ`.
* mathlib `CoeFun`, the canonical way to expose the resulting transformation as a map
  `ℝⁿ⁺¹ → ℝⁿ⁺¹`.

Best owner abstraction:
* source-facing: the triangular transformation itself;
* core/canonical: the family of differentiable correction maps indexed by the nonzero
  coordinates, each defined on the space of strictly earlier coordinates;
* bridge/view: the prefix-coordinate extraction map and the coordinate formulas for evaluating the
  induced transformation via `Fin.cons`.

Primitive data:
* for each nonzero coordinate `i`, a differentiable map `φᵢ : ℝⁱ → ℝ` on the earlier
  coordinates only.

Derived API:
* the induced map `u : ℝⁿ⁺¹ → ℝⁿ⁺¹`;
* the first-coordinate identity `u¹(x) = x¹`;
* for each nonzero coordinate `i`, the formula `uⁱ(x) = xⁱ + φᵢ(x¹, …, xⁱ⁻¹)`.

This keeps the source-facing owner at the transformation level and avoids a parallel wrapper for
the induced map. -/

/-- The higher coordinates of `ℝⁿ⁺¹`, i.e. all coordinates except the first one. -/
abbrev HigherCoord (n : ℕ) := { i : Fin n.succ // i ≠ 0 }

/-- Definition 4.1.11: a triangular transformation of `ℝⁿ⁺¹` is determined by differentiable
coordinate-correction maps for the higher coordinates, where the correction at coordinate `i`
depends only on the strictly earlier coordinates `0, …, i - 1`. The associated map
`u : ℝⁿ⁺¹ → ℝⁿ⁺¹` is recovered by coercion to a function in the namespace below. -/
structure TriangularTransformation (n : ℕ) where
  /-- The correction term for the higher coordinate `i`, depending only on the earlier
  coordinates. -/
  correction (i : HigherCoord n) : EuclideanSpace ℝ (Fin i.1) → ℝ
  /-- Each coordinate-correction map is differentiable on its natural Euclidean domain. -/
  differentiable_correction (i : HigherCoord n) : Differentiable ℝ (correction i)

namespace TriangularTransformation

/-- The vector of the coordinates of `x` strictly preceding the higher coordinate `i`. -/
def previousCoordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n) :
    EuclideanSpace ℝ (Fin i.1) :=
  (EuclideanSpace.equiv (Fin i.1) ℝ).symm fun j ↦
    x (Fin.castLT j (lt_trans j.2 i.1.2))

/-- Evaluating `previousCoordinates x i` at `j` returns the `j`-th coordinate of `x`. -/
@[simp] theorem previousCoordinates_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ))
    (i : HigherCoord n) (j : Fin i.1) :
    previousCoordinates x i j = x (Fin.castLT j (lt_trans j.2 i.1.2)) := by
  simp [previousCoordinates]

/-- The triangular transformation acts on `x : ℝⁿ⁺¹` by leaving the first coordinate fixed and
adding to each higher coordinate a correction depending only on the earlier coordinates. -/
def toFun {n : ℕ} (u : TriangularTransformation n) :
    EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ) :=
  fun x ↦
    (EuclideanSpace.equiv (Fin n.succ) ℝ).symm <|
      Fin.cons (x 0) fun i ↦
        x i.succ +
          u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
            (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩)

instance {n : ℕ} : CoeFun (TriangularTransformation n)
    (fun _ ↦ EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ)) where
  coe := toFun

/-- The first coordinate of a triangular transformation is unchanged. -/
@[simp] theorem coe_apply_zero {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    u x 0 = x 0 := by
  simp [TriangularTransformation.toFun]

/-- At a higher coordinate `i`, evaluating a triangular transformation adds the corresponding
correction term depending only on the earlier coordinates. -/
@[simp] theorem coe_apply_higherCoord {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n) :
    u x i.1 = x i.1 + u.correction i (previousCoordinates x i) := by
  rcases i with ⟨i, hi⟩
  cases i using Fin.cases with
  | zero => cases (hi rfl)
  | succ i =>
      simp [TriangularTransformation.toFun]

/-- At the higher coordinate `i.succ`, evaluating a triangular transformation adds the
corresponding correction term depending only on the earlier coordinates `0, …, i`. -/
@[simp] theorem coe_apply_succ {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : Fin n) :
    u x i.succ = x i.succ +
      u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
        (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩) := by
  simpa using
    coe_apply_higherCoord u x ⟨i.succ, Fin.succ_ne_zero i⟩

end TriangularTransformation

/-! ### Proposition_4_1_11 (from Chap04) -/
open scoped BigOperators
open scoped CubicRegularizedDiagonalInvariants

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.11 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalResolvent_apply` in `Proposition_4_1_10`, the diagonal coordinate
  formula for the canonical resolvent point;
* `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` in `Proposition_4_1_13`, the
  generic owner theorem equating the resolvent norm with `(2 / M) λ*` at a dual maximizer;
* `cubicRegularizedMinimalDiagonalIndices` and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal source
  invariants `I*` and `G²`.

Best owner abstraction:
* source-facing: the perturbed diagonal model `v_δ(h) = v(h) + δ h^(k)` and the resulting
  boundary equation for an optimal perturbed dual point;
* core/canonical: `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, and `IsMaxOn` for the perturbed dual problem;
* bridge/view: the diagonal resolvent coordinate formula together with the generic dual-maximizer
  norm identity.

Primitive data:
* the diagonal data `Hdiag`, the gradient `g`, the cubic parameter `M`, and the active index
  `k ∈ I*`;
* the source-facing perturbed gradient `g + δ e_k`.

Derived API:
* the scalar dual function and dual domain, already owned upstream;
* the generic resolvent norm identity at a dual maximizer, already owned upstream;
* dual optimality on the nonnegative feasible set `dom ψ ∩ ℝ₊`, which should reuse the chapter
  owner `IsMaxOn` rather than restating feasibility and order as a second local wrapper API.

This file therefore keeps the perturbation owner `cubicRegularizedDiagonalPerturbedGradient`, but
deletes the redundant local diagonal scalar-dual function/domain and the one-off dual-maximizer
wrapper in favor of the existing chapter owners; the main proposition is only the diagonal bridge
expansion of the upstream resolvent norm identity. -/

/-- The perturbed linear term obtained from `g` by adding `δ` to the coordinate `k`, encoding
the textbook objective perturbation `v_δ(h) = v(h) + δ h^(k)`. -/
def cubicRegularizedDiagonalPerturbedGradient
    (g : E) (k : Fin n) (δ : ℝ) : E :=
  g + EuclideanSpace.single k δ

/-- Expanding `cubicRegularizedDiagonalPerturbedGradient` gives the coordinatewise perturbation
`g^(i) + δ` at `i = k` and `g^(i)` elsewhere. -/
-- Proof sketch: unfold `cubicRegularizedDiagonalPerturbedGradient` and split on `i = k`.
@[simp]
theorem cubicRegularizedDiagonalPerturbedGradient_apply
    (g : E) (k i : Fin n) (δ : ℝ) :
    cubicRegularizedDiagonalPerturbedGradient g k δ i =
      g i + if i = k then δ else 0 := by
  simp [cubicRegularizedDiagonalPerturbedGradient]

-- Proof sketch: for `gδ = cubicRegularizedDiagonalPerturbedGradient g k δ`, the perturbed dual
-- maximizer hypothesis is exactly `IsMaxOn ψδ Dplusδ lamDelta`. Because `k ∈ I*`,
-- `cubicRegularizedMinimalDiagonalGradientSquare g Hdiag = 0`, and `δ ≠ 0`, the perturbed active
-- squared mass becomes `δ² > 0`, so the perturbed problem is nondegenerate. Apply the upstream
-- owner theorem
-- `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` to `gδ`, then expand the
-- diagonal resolvent coordinates with `cubicRegularizedDiagonalResolvent_apply`; on `I* \\ {k}`
-- the terms vanish, at `k` the numerator is `δ²`, and off `I*` the numerators remain `(g i)²`.

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus(" g' ")" =>
  cubicRegularizedQuadraticDualDomain g' H M ∩ Set.Ici (0 : ℝ)
variable {δ : ℝ} {k : Fin n}
local notation "gδ" => cubicRegularizedDiagonalPerturbedGradient g k δ
local notation "ψδ" => cubicRegularizedQuadraticDualFunction gδ H M
local notation "Dplusδ" => Dplus(gδ)

/-- Proposition 4.1.11: in the degenerate case `G² = 0`, perturbing the objective by `δ h^(k)`
for `k ∈ I*` and `δ ≠ 0` forces every optimal dual maximizer `λ_δ*` on `dom ψ_δ ∩ ℝ₊` to satisfy
`δ² / (H_min + λ_δ*)² + ∑_{i ∉ I*} (g^(i))² / (H_i + λ_δ*)² = 4 (λ_δ*)² / M²`. -/
theorem perturbedDiagonalDualMaximizer_satisfies_boundaryEquation
    {δ : ℝ} (hM : 0 < M) (hδ : δ ≠ 0) {k : Fin n}
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    {lamDelta : ℝ}
    (hopt_max : IsMaxOn ψδ Dplusδ lamDelta) :
    δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦
            i ∉ I*[Hdiag])
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) =
      (4 : ℝ) * lamDelta ^ (2 : ℕ) / M ^ (2 : ℕ) := sorry

end

/-! ### Theorem_4_1_11 (from Chap04) -/
noncomputable section
open scoped CubicRegularizedDiagonalInvariants

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 4.1.11 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Definition_4_1_14`, the chapter owner for the primal
  cubic model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners for the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticScalarDualDomain_eq` in `Definition_4_1_14`, the bridge from
  `dom ψ` to the bounded-below shifted quadratic form;
* `cubicRegularizedQuadraticTauMinimizer` and `cubicRegularizedQuadraticTauMinimizer_def` in
  `Definition_4_1_14`, the owner and defining formula for the slack minimizer `τ(λ)`.

Best owner abstraction:
* source-facing: the diagonal `G² = 0` strong-duality and primal-minimizer theorems from the
  source;
* core/canonical: the primal objective, scalar dual function/domain, and the owner-level slack
  minimizer `cubicRegularizedQuadraticTauMinimizer`;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag`.

Primitive data:
* `g`, `Hdiag`, `M`, and the induced diagonal matrix `H = Matrix.diagonal Hdiag`;
* the diagonal invariant `cubicRegularizedMinimalDiagonalGradientSquare g Hdiag`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `cubicRegularizedQuadraticDualFunction g H M`;
* `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`;
* `cubicRegularizedQuadraticTauMinimizer M lam` together with
  `cubicRegularizedQuadraticTauMinimizer_def`.

This file therefore keeps the source-facing diagonal theorem family and records the `τ(λ*)`
clause by a labeled recall of the existing owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`, rather than by a duplicate specialized wrapper. -/

/- The cubic objective, scalar dual owner, dual-domain owner, and slack minimizer are already the
upstream declarations from `Definition_4_1_14`. -/
recall cubicRegularizedQuadraticObjective
recall cubicRegularizedQuadraticObjective_apply
recall cubicRegularizedQuadraticScalarLagrangian
recall cubicRegularizedQuadraticDualFunction
recall cubicRegularizedQuadraticDualFunction_eq_sInf
recall cubicRegularizedQuadraticDualDomain
recall mem_cubicRegularizedQuadraticDualDomain_iff
recall cubicRegularizedQuadraticTauMinimizer
recall cubicRegularizedQuadraticTauMinimizer_isMinOn

variable [NeZero n]

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "v" => cubicRegularizedQuadraticObjective g H M
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)

variable {lamStar : ℝ}
variable (hM : 0 < M)
variable (hGzero : G²[g;Hdiag] = 0)
variable (hmax : IsMaxOn ψ Dplus lamStar)
variable (hlam : -H_min[Hdiag] < lamStar)

-- Proof sketch: combine the assumption `G² = 0` with the diagonal analysis of the shifted
-- quadratic subproblem to identify the minimizing `h`-variable for every `λ > -H_min`. Then use
-- the assumed maximality of `λ*` on `dom ψ ∩ ℝ₊` to identify the primal infimum with the dual
-- value `ψ(λ*)`; the auxiliary supremum step is the generic order-theoretic fact obtained from
-- `hmax.isLUB` and `IsLUB.csSup_eq`.
/-- Theorem 4.1.11 (1): for the diagonal cubic-regularized quadratic model with `H = diag(Hdiag)`,
if `G² = 0` and the dual problem admits a maximizer `λ* > -H_min`, then strong duality holds at
that maximizer:
the minimum of the primal objective `v(h)` equals the dual value `ψ(λ*)`. -/
theorem cubicRegularizedQuadraticDiagonal_strongDuality_of_zeroMinimalGradientSquare
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar)
    :
    sInf (Set.range fun h : E ↦
      (v h : EReal)) =
      ψ lamStar := sorry

-- Proof sketch: solve the quadratic `h`-subproblem at the dual maximizer `λ*` using the
-- `G² = 0` diagonal case, and then use the primal-dual optimality relations at the maximizing
-- multiplier `λ*` to show that the resulting resolvent point minimizes the original cubic
-- objective.
/-- Theorem 4.1.11 (2): under the same hypotheses, the primal problem admits the explicit global
minimizer `h* = -(H + λ* I)⁻¹ g`. -/
theorem cubicRegularizedQuadraticDiagonal_primalMinimizer_of_zeroMinimalGradientSquare
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar)
    :
    IsMinOn v Set.univ
      (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) := sorry

/- Theorem 4.1.11 (3): the associated slack minimizer satisfies
`τ(λ*) = 4 λ* |λ*| / M²`; this is exactly the owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`. -/
recall cubicRegularizedQuadraticTauMinimizer_def

end

/-! ### Definition_4_1_12 (from Chap04) -/
/- This item stays in the Chapter 4 cubic-regularized quadratic-subproblem domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the cubic model
  `v`;
* `cubicRegularizedQuadraticObjective_apply` in `Theorem_4_1_11`, the theorem expanding that owner
  to the displayed formula;
* `IsMinOn` in mathlib, the canonical predicate for global minimizers on a set;
* `isMinOn_univ_iff` in mathlib, the bridge from `IsMinOn ... Set.univ ...` to the textbook
  pointwise inequality form.

Best owner abstraction:
* source-facing: `cubicRegularizedQuadraticObjective g H M`;
* core/canonical: `IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ hStar`;
* bridge/view: `isMinOn_univ_iff`.
-/

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (hStar : E)

/- Definition 4.1.12: the cubic-regularized quadratic model
`v(h) = ⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ + (M / 6) ‖h‖^3`
is the existing owner `cubicRegularizedQuadraticObjective`. -/
recall cubicRegularizedQuadraticObjective

/- The owner theorem `cubicRegularizedQuadraticObjective_apply` expands the model to the textbook
formula for `v(h)`. -/
recall cubicRegularizedQuadraticObjective_apply

/- The canonical minimizer owner is `IsMinOn`; the auxiliary minimization problem is its
whole-space specialization to the cubic model. -/
recall IsMinOn

set_option linter.hashCommand false in
#check IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ hStar

/- The textbook inequality form of global minimality over `ℝⁿ` is exactly `isMinOn_univ_iff`. -/
recall isMinOn_univ_iff

set_option linter.hashCommand false in
#check
  (show IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ hStar ↔
      ∀ h : E,
        cubicRegularizedQuadraticObjective g H M hStar ≤
          cubicRegularizedQuadraticObjective g H M h from
    isMinOn_univ_iff)

end
