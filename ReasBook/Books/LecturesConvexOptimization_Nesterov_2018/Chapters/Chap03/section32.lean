import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_32 (from Chap03) -/
open scoped BigOperators

universe u

section

variable {X : Type u}

/-
Definition 3.32 is a recall-only item in the chapter's finite weighted-sum domain.

Primary domain:
- finite weighted sums of sampled scalar values.

Sampled owner-style declarations:
- mathlib `dotProduct`, the canonical owner for finite sums of entrywise products;
- mathlib notation `α ⬝ᵥ fy`, the idiomatic display form of that owner;
- `hatf` in `Chap03/Lemma_3_24`, the local weighted-sum notation built from `dotProduct` for the
  chapter's sampled primal values;
- project `gapFunctionCertificate_apply` in `Chap03/Lemma_3_24`, the nearby textbook-style
  expansion from the `dotProduct` owner back to an explicit finite sum.

Best owner abstraction:
- `dotProduct α (f ∘ y)`, equivalently `α ⬝ᵥ (f ∘ y)`.

Primitive data:
- a horizon `N : ℕ`;
- sample points `y : Fin (N + 1) → X`;
- coefficients `α : Fin (N + 1) → ℝ`;
- the sampled scalar family `f ∘ y : Fin (N + 1) → ℝ`.

Derived API:
- the textbook display `α ⬝ᵥ (f ∘ y) = ∑ k, α k * f (y k)`, which is just the defining expansion
  of `dotProduct`;
- nearby sampled weighted-gap owners built from the same `dotProduct` abstraction.

Source/core/bridge triage:
- source-facing: the textbook quantity `\hat f_N = ∑_{k=0}^N α_k f(y_k)`;
- core/canonical: `dotProduct α (f ∘ y)`;
- bridge/view: the explicit finite-sum display of that dot product.

This file therefore recalls the mathlib owner directly instead of keeping a parallel local
weighted-sum wrapper.
-/

recall dotProduct

section

variable {N : ℕ} (y : Fin (N + 1) → X) (α : Fin (N + 1) → ℝ) (f : X → ℝ)

#check α ⬝ᵥ (f ∘ y)

#check
  (show α ⬝ᵥ (f ∘ y) = ∑ k, α k * f (y k) from by
    simp [dotProduct])

end

end

/-! ### Lemma_3_32 (from Chap03) -/
section

open MeasureTheory

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

open scoped EllipsoidNotation

/- 
Lemma 3.32 is a downstream recall of the chapter's ellipsoid-update owner API.

Sampled owner-style declarations:
- `affineEllipsoid` in `Lemma_3_2_7`, the source-facing owner of the textbook ellipsoid
  `E(H, x̄)`;
- `centerCutEllipsoid` in `Lemma_3_2_7`, the source-facing owner of the center cut `E₊`;
- `updatedEllipsoidCenter` and `updatedEllipsoidMatrix` in `Lemma_3_2_7`, the textbook ellipsoid
  update formulas;
- `centerCutEllipsoid_subset_updatedEllipsoid_and_volume_le` in `Lemma_3_2_7`, the owner theorem
  for the containment and volume decrease.

Best owner abstraction:
- source-facing/core owner: the ellipsoid-update API already introduced in `Lemma_3_2_7`;
- bridge/view: this file is recall-only.

Primitive data:
- `H : Mat`;
- `xBar g : E`;
- the valid-update hypotheses `H.PosDef`, `g ≠ 0`, and `1 < n` for the containment theorem.

Derived API:
- the ellipsoid `affineEllipsoid H xBar`;
- the center cut `centerCutEllipsoid H xBar g`;
- the updated center and shape matrix;
- the canonical containment and volume-decrease theorem.

Source/core/bridge triage:
- source-facing: the textbook ellipsoid update and its containment/volume statement;
- core/canonical: the existing owner declarations from `Lemma_3_2_7`;
- bridge/view: this recall file.

Accordingly, this file no longer keeps parallel local copies of the ellipsoid-update definitions or
their main theorem. The owner objects already live upstream, so this file stays theorem-recall-only
and reuses the canonical containment/volume statement directly.
-/

recall centerCutEllipsoid_subset_updatedEllipsoid_and_volume_le
    (H : Mat) (hH : H.PosDef) (xBar g : E) (hg : g ≠ 0) (hn : 1 < n) :
    E₊(H, xBar, g) ⊆ E(H₊(H, g), x̄₊(H, xBar, g)) ∧
      ((volume (E(H₊(H, g), x̄₊(H, xBar, g)))).toReal ≤
        Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((n : ℝ) / 2) *
          (volume (E(H, xBar))).toReal)

end

/-! ### Proposition_3_32 (from Chap03) -/
noncomputable section

open scoped CoordinateSubspace

variable {k : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin k)

/- Primary domain: the finite-dimensional Nemirovski hard instance on `ℝ^k`, together with the
prefix-coordinate maximum appearing in the early-iterate lower bound.

Sampled owner-style declarations:
* `firstKCoordinateFamily` in `Chap03/Definition_3_35`, the restricted coordinate family behind
  the hard instance;
* `first_k_coordinate_max` in `Chap03/Definition_3_35`, the canonical prefix-maximum owner;
* `f_k` in `Chap03/Definition_3_35`, the source-facing Nemirovski hard-instance objective.

Best owner abstraction:
* source-facing: the early-iterate nonnegativity statement for the actual hard-instance owner
  `f_k`;
* core/canonical: `f_k` and `first_k_coordinate_max`.

Primitive data:
* the hard-instance parameters `μ` and `γ`;
* the iterate sequence `x`;
* the textbook hypothesis `first_k_coordinate_max k k (x i) = 0` for `i ≤ k - 1`.

Derived API:
* the generic lower bound
  `γ * first_k_coordinate_max k k x ≤ f_k k k μ γ x` when `μ ≥ 0`;
* the early-iterate consequence `0 ≤ f_k k k μ γ (x i)`.

Source/core/bridge triage:
* source-facing: `no_decrease_f_k_first_steps`;
* core/canonical: `f_k`, `first_k_coordinate_max`;
* bridge/view: `scaled_first_k_coordinate_max_le_f_k`.

The source proposition does not use the support statement `x i ∈ ℝ^{i,k}` directly. Its displayed
hypothesis is the stronger explicit equality `max_{1 ≤ j ≤ k} x_i^(j) = 0`, represented here by
`first_k_coordinate_max k k (x i) = 0`. This file therefore keeps the textbook owner `f_k` as the
main declaration, uses the canonical prefix-maximum owner from Definition 3.35, and records the
lower bound `f_k(x_i) ≥ γ max_j x_i^(j)` only through the direct formula for `f_k`. -/

/-- Helper for Proposition 3.32 [Chapter3_2.json:70]: the quadratic term in `f_k` is
nonnegative whenever `μ ≥ 0`. -/
-- Proof sketch: `μ / 2` is nonnegative because both `μ` and `2` are nonnegative, and `‖x‖^2`
-- is nonnegative as a square; multiplying the two nonnegative factors preserves nonnegativity.
theorem f_k_quadratic_term_nonneg
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    0 ≤ (μ / 2) * ‖x‖ ^ 2 := by
  -- The scalar coefficient stays nonnegative after division by `2`.
  have hcoeff : 0 ≤ μ / 2 := by
    exact div_nonneg hμ (by norm_num)
  -- The squared norm is nonnegative because it is a square in `ℝ`.
  have hsq : 0 ≤ ‖x‖ ^ 2 := by
    simpa [pow_two] using sq_nonneg ‖x‖
  -- Combine the two nonnegative factors.
  exact mul_nonneg hcoeff hsq

/-- Helper for Proposition 3.32 [Chapter3_2.json:70]: the Nemirovski hard-instance value
dominates the scaled maximum of the first `k`
coordinates whenever the quadratic coefficient `μ` is nonnegative. -/
-- Proof sketch: unfold `f_k`; the quadratic term `(μ / 2) * ‖x‖^2` is nonnegative when `μ ≥ 0`,
-- so `f_k` is bounded below by its `γ * first_k_coordinate_max` summand.
theorem scaled_first_k_coordinate_max_le_f_k
    (μ γ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    γ * first_k_coordinate_max k k x ≤ f_k k k μ γ x := by
  -- Unfold `f_k` so the goal becomes a comparison with an added nonnegative term.
  rw [f_k_def]
  have hquad : 0 ≤ (μ / 2) * ‖x‖ ^ 2 := f_k_quadratic_term_nonneg (μ := μ) hμ x
  -- The added quadratic contribution can only increase the value.
  nlinarith

/-- Helper for Proposition 3.32 [Chapter3_2.json:70]: if the maximum among the first `k`
coordinates of `x` is `0`, then the Nemirovski
hard-instance value at `x` is nonnegative whenever `μ ≥ 0`. -/
-- Proof sketch: combine `scaled_first_k_coordinate_max_le_f_k` with the hypothesis
-- `first_k_coordinate_max k k x = 0` and rewrite the left-hand side to `0`.
theorem f_k_nonneg_of_first_k_coordinate_max_eq_zero
    (μ γ : ℝ) (hμ : 0 ≤ μ) {x : E}
    (hmax : first_k_coordinate_max k k x = 0) :
    0 ≤ f_k k k μ γ x := by
  -- First lower-bound `f_k x` by the scaled prefix maximum.
  have hbound := scaled_first_k_coordinate_max_le_f_k (k := k) μ γ hμ x
  -- The textbook hypothesis identifies that scaled maximum with `0`.
  rw [hmax] at hbound
  simpa using hbound

/-- Proposition 3.32 [Chapter3_2.json:70]: if each iterate `x_i` with `0 ≤ i ≤ k - 1` satisfies
`max_{1 ≤ j ≤ k} x_i^(j) = 0`, then along the first `k - 1` nonzero steps one has
`f_k(x_i) ≥ γ max_{1 ≤ j ≤ k} x_i^(j) = 0`; equivalently, `f_k (x_{i+1}) ≥ 0` for every
`i < k - 1`. -/
-- Proof sketch: for `x (i + 1)`, apply `f_k_nonneg_of_first_k_coordinate_max_eq_zero` using the
-- textbook hypothesis at the index `i + 1`; the required bound follows from
-- `Nat.succ_le_of_lt hi`.
theorem no_decrease_f_k_first_steps
    (μ γ : ℝ) (hμ : 0 ≤ μ) (x : ℕ → E)
    (hmax : ∀ i : ℕ, i ≤ k - 1 → first_k_coordinate_max k k (x i) = 0)
    {i : ℕ} (hi : i < k - 1) :
    0 ≤ f_k k k μ γ (x (i + 1)) := by
  -- The hypothesis applies at the shifted index `i + 1` because `i < k - 1`.
  have hmax_succ : first_k_coordinate_max k k (x (i + 1)) = 0 := by
    exact hmax (i + 1) (Nat.succ_le_of_lt hi)
  -- Specialize the generic nonnegativity lemma to the iterate `x (i + 1)`.
  simpa using
    f_k_nonneg_of_first_k_coordinate_max_eq_zero
      (k := k) (μ := μ) (γ := γ) hμ (x := x (i + 1)) hmax_succ

end

/-! ### Theorem_3_32 (from Chap03) -/
/- Theorem 3.32: (Karush--Kuhn--Tucker) under convexity, differentiability, and a Slater point
for the inequality constraints on `Q`, a point `x*` solves
`min {f₀(x) | x ∈ Q, fᵢ(x) ≤ 0}` if and only if there exists a nonnegative multiplier vector
whose Lagrangian gradient pairing is nonnegative on `Q` and which satisfies complementary
slackness at `x*`.

This numbered item is already formalized on the canonical Chapter 3 owner surface in
`isMinOn_iff_exists_karush_kuhn_tucker_multiplier`, so this file reuses that theorem directly
instead of introducing a parallel local KKT API.
-/
recall isMinOn_iff_exists_karush_kuhn_tucker_multiplier
