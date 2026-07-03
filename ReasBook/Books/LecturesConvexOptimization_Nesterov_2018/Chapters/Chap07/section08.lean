import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_8 (from Chap07) -/
/- Definition 7.8 lies in the nearest-point / norm-minimization domain.

Sampled owner declarations:
* `IsProjectionPointOn` in `Chap07/Definition_7_3`, the project owner of projection-point data;
* `IsProjectionPointOn.iff_isMinOn` in `Chap02/Definition_2_33`, the canonical bridge from that
  owner to minimizing the distance-to-basepoint function on a set;
* mathlib `IsMinOn` and `isMinOn_iff`, the canonical minimizer API on a set.

Source/core/bridge triage:
* source-facing: the textbook notion “projection of the origin onto `Q1`”;
* core/canonical: `IsProjectionPointOn Q1 (0 : E) x0`;
* bridge/view: norm-minimizer and pointwise norm-comparison reformulations.

Accordingly, the main labeled entry directly reuses the existing projection-point owner specialized
to the base point `0`, and the norm formulas are recorded as companion bridge theorems. -/

universe u

section

variable {E : Type u} [NormedAddCommGroup E]
variable (Q1 : Set E) (x0 : E)

set_option linter.hashCommand false in
/- Definition 7.8: the projection of the origin onto `Q1` with respect to the norm is the
existing projection-point predicate specialized to the base point `0`. -/
#check (IsProjectionPointOn Q1 (0 : E) x0 : Prop)

end

section

variable {E : Type u} [NormedAddCommGroup E]

/-- A projection point of the origin onto `Q1` is exactly a feasible minimizer of the norm on
`Q1`. -/
-- Proof sketch: specialize `IsProjectionPointOn.iff_isMinOn` to the base point `0` and simplify
-- `‖x - 0‖` to `‖x‖`.
theorem isProjectionPointOn_origin_iff_isMinOn_norm {Q1 : Set E} {x0 : E} :
    IsProjectionPointOn Q1 (0 : E) x0 ↔
      x0 ∈ Q1 ∧ IsMinOn (fun x ↦ ‖x‖) Q1 x0 := sorry

/-- A point is a projection of the origin onto `Q1` exactly when it lies in `Q1` and its norm is
no larger than the norm of every point of `Q1`. -/
-- Proof sketch: rewrite the `IsMinOn` statement in
-- `isProjectionPointOn_origin_iff_isMinOn_norm` using `isMinOn_iff`.
theorem isProjectionPointOn_origin_iff_forall_norm_le {Q1 : Set E} {x0 : E} :
    IsProjectionPointOn Q1 (0 : E) x0 ↔
      x0 ∈ Q1 ∧ ∀ x ∈ Q1, ‖x0‖ ≤ ‖x‖ := sorry

end

/-! ### Lemma_7_8 (from Chap07) -/
noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction SymmetricBox

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.8 lies in Chapter 7's orthant-box / support-function / diagonal-ellipsoid domain.

Sampled owner-style declarations:
- `ξ[Q]` and `supportFunction_convexHull_eq` in `Chap03/Definition_3_9`, the chapter owner for
  support functions;
- `supportFunction_range_toReal_eq_sSup_inner` in `Chap07/Lemma_7_1`, the finite-range support
  function bridge already available upstream for families `a : Fin m → Eₙ`;
- `signSymmetricConvexHull` in `Chap07/Definition_7_35`, the source-facing Chapter 7 owner for
  the box hull `convexHull ℝ (⋃ i, B(a i))`;
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the canonical orthant owner;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the centered-rounding owner packaging the
  unit and outer ellipsoid containments together with positive definiteness.

Best owner abstraction:
- source-facing: the box hull owner `signSymmetricConvexHull a`;
- core/canonical: `ξ[Q]`, `nonnegativeOrthant`, `IsEllipsoidalRounding`, and the
  positive-definite norm owner `‖x‖[G]`;
- bridge/view: the orthant-restricted identification of `ξ[signSymmetricConvexHull a]` with the
  finite-range support function `ξ[Set.range a]`.

Primitive data:
- a family `a : Fin m → Eₙ`.

Derived API:
- the orthant bridge from the source-facing box-hull owner to the canonical finite-range support
  function;
- the centered rounding datum `IsEllipsoidalRounding (signSymmetricConvexHull a) γ D`;
- the support-function sandwich theorem below, derived from that owner.

Source/core/bridge triage:
- source-facing: the two theorems below about `signSymmetricConvexHull a`;
- core/canonical: `IsEllipsoidalRounding`;
- bridge/view: passing from `hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D`
  to the inner/outer containments with `hrounding.unit_ellipsoid_subset` and
  `hrounding.subset_outer_ellipsoid`.

This refinement deletes the raw-set duplication in the public theorem surface. The box hull is now
named by its Chapter 7 owner `signSymmetricConvexHull`, and the main sandwich theorem is stated
through the centered-rounding owner `IsEllipsoidalRounding` instead of keeping its fields as
parallel hypotheses.
-/

/-- On the nonnegative orthant, the support function of the symmetric box `B(a)` with nonnegative
generator `a` is the linear form `x ↦ ⟪a, x⟫`. -/
theorem supportFunction_symmetricBox_toReal_eq_inner_of_mem_nonnegativeOrthant
    {a x : Eₙ} (ha : a ∈ nonnegativeOrthant n) (hx : x ∈ nonnegativeOrthant n) :
    (ξ[(B(a))] x).toReal = inner ℝ a x := sorry

/-- On the nonnegative orthant, the support function of the Chapter 7 box-hull owner
`signSymmetricConvexHull a` agrees with the canonical finite-range support function
`ξ[Set.range a]`. -/
theorem supportFunction_signSymmetricConvexHull_eq_range_on_nonnegativeOrthant
    (a : Fin m → Eₙ) (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    {x : Eₙ} (hx : x ∈ nonnegativeOrthant n) :
    (ξ[signSymmetricConvexHull a] x).toReal = (ξ[Set.range a] x).toReal := sorry

-- Proof sketch: on the nonnegative orthant, the support function of each coordinate box
-- `coordinateBox (a i)` is `⟪a_i, x⟫` because `a_i` has nonnegative coordinates. Hence the support
-- function of `signSymmetricConvexHull a` agrees with the canonical finite-range owner
-- `ξ[Set.range a]`. Monotonicity of support functions under the inclusions
-- `W[1](D) ⊆ signSymmetricConvexHull a ⊆ W[γ √n](D)` supplied by
-- `hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D` then give the lower and
-- upper bounds, and the support function of `W[ρ](D)` is `ρ * ‖x‖[⟨D, hrounding.posDef⟩]`.
/-- Lemma 7.8: if the convex hull of the boxes `B(a_i)` with nonnegative generators contains
`W₁(D)` and is contained in `W_{γ √n}(D)`, then on the nonnegative orthant the support function of
that box hull is sandwiched between `‖x‖_D` and `γ √n ‖x‖_D`. -/
theorem supportFunction_signSymmetricConvexHull_bounds_on_nonnegativeOrthant
    (a : Fin m → Eₙ) {D : Matₙ} {γ : ℝ}
    (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    (hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D)
    (x : Eₙ) (hx_nonneg : x ∈ nonnegativeOrthant n) :
    ‖x‖[⟨D, hrounding.posDef⟩] ≤
        (ξ[signSymmetricConvexHull a] x).toReal ∧
      (ξ[signSymmetricConvexHull a] x).toReal ≤
        γ * Real.sqrt (n : ℝ) * ‖x‖[⟨D, hrounding.posDef⟩] := sorry

end

/-! ### Proposition_7_8 (from Chap07) -/
noncomputable section

/- Proposition 7.8 lies in the scalar concavity / maximizer layer of the centrally symmetric
rounding argument.

Sampled owner-style declarations:
- mathlib `StrictConcaveOn`, the canonical owner for strict concavity on an interval;
- mathlib `IsMaxOn`, the canonical owner for interval maximizers;
- `rankOneUpdatePotential` in `Lemma_7_4`, the matrix-level specialization whose scalar part is the
  same logarithmic objective with `σ = (1 / n) ‖g‖_{G,*}² - 1`;
- `oneSidedRoundingPotential` in `Lemma_7_5`, a nearby chapter scalar maximizer statement with the
  same `IsMaxOn` owner discipline.

Best owner abstraction:
- source-facing: the scalar objective `V(α)` and its distinguished critical point `α*`;
- core/canonical: mathlib's `StrictConcaveOn` and `IsMaxOn`;
- bridge/view: later matrix-level specializations obtained by substituting a concrete `σ`.

Primitive data:
- the dimension parameter `n`;
- the scalar parameter `σ`;
- the interval variable `α`.

Derived API:
- strict concavity on `Set.Ico 0 1`;
- membership of the explicit critical point in that interval;
- the first-order characterization, maximizer characterization, and closed-form value at `α*`.

The scalar coefficient `n (1 + σ) - 1` is not kept as a separate public owner: it is derived data
inside the objective and critical-point formulas. -/

/-- The scalar objective `V(α)` on `[0, 1)` used in the centrally symmetric rounding estimate. -/
def centralSymmetryRoundingObjective (n : ℕ) (σ : ℝ) (α : ℝ) : ℝ :=
  Real.log (1 + α * ((n : ℝ) * (1 + σ) - 1)) +
    ((n : ℝ) - 1) * Real.log (1 - α)

/-- The explicit critical point `α* = σ / (n (1 + σ) - 1)` of the scalar objective. -/
def centralSymmetryRoundingAlphaStar (n : ℕ) (σ : ℝ) : ℝ :=
  σ / ((n : ℝ) * (1 + σ) - 1)

-- Proof sketch: write `V` as the sum of two logarithmic terms composed with affine maps taking
-- `[0, 1)` into `(0, ∞)`. The hypothesis `-1 ≤ σ` keeps the first logarithmic argument positive on
-- `Set.Ico 0 1`, `1 ≤ n` keeps the second logarithmic coefficient nonnegative, and the extra
-- nonconstancy hypothesis rules out the degenerate constant case. Strict concavity then follows
-- from strict concavity of `Real.log` on `Set.Ioi 0` together with stability under affine
-- reparametrization and addition.
/-- The objective `V` is strictly concave on `[0, 1)` once both logarithmic terms are well defined
and at least one of them is genuinely nonconstant. -/
theorem centralSymmetryRoundingObjective_strictConcaveOn
    {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : -1 ≤ σ)
    (hstrict : ((n : ℝ) * (1 + σ) - 1 ≠ 0) ∨ 1 < n) :
    StrictConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (centralSymmetryRoundingObjective n σ) := sorry

-- Proof sketch: use `2 ≤ n` and `0 ≤ σ` to show
-- `0 ≤ σ / (n (1 + σ) - 1) < 1`, equivalently that the explicit critical point lies in
-- `Set.Ico 0 1`.
/-- The explicit critical point `α*` lies in the interval `[0, 1)`. -/
theorem centralSymmetryRoundingAlphaStar_mem_Ico
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) :
    centralSymmetryRoundingAlphaStar n σ ∈ Set.Ico (0 : ℝ) 1 := sorry

-- Proof sketch: compute `V'(α)` on the genuine logarithmic domain, namely points of `[0, 1)` for
-- which the first logarithmic argument `1 + α (n (1 + σ) - 1)` is positive. On that domain, the
-- critical-point equation reduces to a linear equation in `α`, whose unique solution is
-- `α = σ / (n (1 + σ) - 1)`. The coefficient hypothesis keeps the displayed closed form defined.
/-- On the genuine logarithmic domain inside `[0, 1)`, the first-order condition for `V` is
equivalent to `α = α*`. -/
theorem centralSymmetryRoundingObjective_firstOrderCondition_iff
    {n : ℕ} {σ : ℝ} (hn : 1 ≤ n)
    (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hlog : 0 < 1 + α * ((n : ℝ) * (1 + σ) - 1)) :
    ((n : ℝ) - 1) / (1 - α) =
        (((n : ℝ) * (1 + σ) - 1) / (1 + α * ((n : ℝ) * (1 + σ) - 1))) ↔
      α = centralSymmetryRoundingAlphaStar n σ := sorry

-- Proof sketch: strict concavity gives uniqueness of a feasible maximizer on the convex set
-- `[0, 1)`. The first-order characterization identifies the only critical point with
-- `σ / (n (1 + σ) - 1)`, and the separate membership theorem shows that this point is feasible.
/-- Proposition 7.8: among feasible points `α ∈ [0, 1)`, the scalar objective `V` is maximized
exactly at `α* = σ / (n (1 + σ) - 1)`. -/
theorem centralSymmetryRoundingObjective_isMaxOn_iff
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    IsMaxOn (centralSymmetryRoundingObjective n σ) (Set.Ico (0 : ℝ) 1) α ↔
      α = centralSymmetryRoundingAlphaStar n σ := sorry

-- Proof sketch: substitute `α* = σ / (n (1 + σ) - 1)` into the two logarithmic factors,
-- simplify `1 + α* (n (1 + σ) - 1) = 1 + σ` and
-- `1 - α* = ((n - 1) (1 + σ)) / (n (1 + σ) - 1)`, then evaluate `V(α*)`. Only the
-- nondegeneracy of `n (1 + σ) - 1` is needed for the substitution.
/-- The scalar objective evaluated at `α*` has the closed form stated in the proposition. -/
theorem centralSymmetryRoundingObjective_alphaStar_value
    {n : ℕ} {σ : ℝ} (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) :
    centralSymmetryRoundingObjective n σ (centralSymmetryRoundingAlphaStar n σ) =
      Real.log (1 + σ) +
        ((n : ℝ) - 1) *
          Real.log
            (((n : ℝ) - 1) * (1 + σ) / ((n : ℝ) * (1 + σ) - 1)) := sorry

/-! ### Theorem_7_8 (from Chap07) -/
noncomputable section

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 7.8 lies in the Chapter 7 centered ellipsoid-rounding / sign-invariant convex-set
domain.

Sampled owner-style declarations:
* `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the chapter owner of centered
  `γ √n`-ellipsoidal roundings;
* `IsEllipsoidalRounding.unit_ellipsoid_subset` and
  `IsEllipsoidalRounding.subset_outer_ellipsoid` in `Chap07/Definition_7_29`, the derived inner
  and outer containment API for that owner;
* `IsSignInvariant` in `Chap07/Definition_7_33`, the chapter owner of sign-symmetry;
* `matrixEllipsoid` / `W[r](G)` in `Chap07/Definition_7_26`, reused upstream by
  `IsEllipsoidalRounding`.

Best owner abstraction:
* source-facing: the existence of a diagonal centered ellipsoidal rounding for a sign-invariant
  convex set;
* core/canonical: `IsEllipsoidalRounding C γ D`;
* bridge/view: the extra diagonality condition `D.IsDiag`.

Primitive data:
* a set `C : Set E`;
* a matrix `D : Mat`.

Derived API:
* positive definiteness and the two ellipsoid containments, all supplied by
  `IsEllipsoidalRounding C 1 D`;
* diagonality as the only additional theorem-specific datum.

This refinement deletes the duplicate local wrapper `IsDiagonalEllipsoidalRounding`. The theorem is
source-facing, but its rounding core is already owned by `IsEllipsoidalRounding`; only the extra
diagonality requirement remains outside that owner.
-/

-- Proof sketch: choose a volume-maximizing feasible diagonal matrix among those whose unit
-- ellipsoid lies in `C`, and use the sign-invariant rounding argument from Lemma 7.7 to show that
-- the optimal outer radius is at most `Real.sqrt n`.
/-- Theorem 7.8: every bounded sign-symmetric convex set in `ℝⁿ` with nonempty interior admits a
positive-definite diagonal matrix `D` such that `W_1(D) ⊆ C ⊆ W_(sqrt n)(D)`. -/
theorem exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty_bounded
    {C : Set E} (h_sign : IsSignInvariant C) (h_convex : Convex ℝ C)
    (h_interior : (interior C).Nonempty) (h_bounded : Bornology.IsBounded C) :
    ∃ D : Mat, D.IsDiag ∧ IsEllipsoidalRounding C 1 D := sorry
