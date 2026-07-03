

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_19 (from Chap07) -/
noncomputable section

open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

variable {n : ℕ}

/-- Definition 7.19: `spectral_eigenvalue_l1_unit_ball n` is the set `Q₂` of real symmetric
`n × n` matrices whose ordered eigenvalues satisfy `∑ i, |λ_i(X)| ≤ 1`. -/
def spectral_eigenvalue_l1_unit_ball (n : ℕ) : Set (𝕊^n) :=
  {X | ∑ i : Fin n, |eigenvalues X i| ≤ (1 : ℝ)}

-- Proof sketch: unfold `spectral_eigenvalue_l1_unit_ball`; membership is exactly the displayed
-- eigenvalue `ℓ₁`-bound from the definition of `Q₂`.
/-- Membership in `spectral_eigenvalue_l1_unit_ball n` means that the sum of the absolute values
of the ordered eigenvalues of `X` is at most `1`. -/
theorem mem_spectral_eigenvalue_l1_unit_ball_iff
    (X : 𝕊^n) :
    X ∈ spectral_eigenvalue_l1_unit_ball n ↔
      ∑ i : Fin n, |eigenvalues X i| ≤ (1 : ℝ) :=
  Iff.rfl

/-! ### Lemma_7_19 (from Chap07) -/
universe u

variable {Q : Type u}

-- Proof sketch: evaluate at an arbitrary `x : Q`; from `hf x` we get `0 < f₁ x`, and since
-- `f₁ x ≤ max (f₁ x) (f₂ x)`, transitivity gives positivity of the function-space maximum.
/-- Lemma 7.19: if `f₁` is strictly positive on `Q`, then the pointwise maximum of `f₁` and `f₂`
is strictly positive on `Q`. In particular, this applies when both functions are strictly
positive. -/
theorem StrictlyPositive.max {f₁ : Q → ℝ}
    (hf : StrictlyPositive f₁) (f₂ : Q → ℝ) :
    StrictlyPositive (max f₁ f₂) := by
  intro x
  exact (hf x).trans_le (le_max_left (f₁ x) (f₂ x))

/-! ### Proposition_7_19 (from Chap07) -/
noncomputable section

open scoped SupportFunction

universe u v

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 7.19 lies in Chapter 7's finite-range support-function / log-sum-exp smoothing
domain.

Sampled owner-style declarations:
- `ξ[Q]` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for support
  functions;
- `supportFunction_range_toReal_eq_sSup_inner` in `Chap07/Lemma_7_1`, the nearby finite-range
  evaluation theorem for `ξ[Set.range a]`;
- `smoothMaxInnerApproximation` and `smoothMaxInnerApproximation_apply` in
  `Chap07/Definition_7_42`, the chapter owner for the positive-parameter log-sum-exp smoothing of
  `x ↦ max_i ⟪aᵢ, x⟫`;
- `HasDiagonalOrthantSupportBounds` in `Chap07/Proposition_7_21`, the direct downstream support-
  function surface for the same finite family `a`.

Best owner abstraction:
- source-facing: Proposition 7.19's smoothing bound for the support function of `Set.range a`;
- core/canonical: `ξ[Set.range a]` and `smoothMaxInnerApproximation a μ`;
- bridge/view: the finite-max evaluation
  `maxTypeObjective (fun i y ↦ inner ℝ (a i) y) x = (ξ[Set.range a] x).toReal`.

Primitive data:
- the finite nonempty index type `ι`;
- the vectors `a : ι → E`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the canonical support-function owner `(ξ[Set.range a] x).toReal`;
- the canonical smoothing owner `smoothMaxInnerApproximation a μ`;
- the additive error term `(μ : ℝ) * Real.log (Fintype.card ι)`.

This refinement keeps Proposition 7.19 on the intrinsic Chapter 3 support-function owner instead
of the lower-level finite-max owner. The finite maximum remains only a bridge/view to this support
function surface, matching the surrounding Chapter 7 API in `Lemma_7_1` and `Proposition_7_21`.
-/

/-- Proposition 7.19: for a finite nonempty family `aᵢ` in a real inner product space, the
log-sum-exp smoothing of the support function of `Set.range a` lies between
`(ξ[Set.range a] x).toReal` and the same quantity plus `μ log (Fintype.card ι)` at every point
`x`, for every positive smoothing parameter `μ`. -/
-- Proof sketch: let `M = (ξ[Set.range a] x).toReal`, equivalently
-- `M = max_i ⟪aᵢ, x⟫`. Every summand `exp (⟪aᵢ, x⟫ / μ)` is at most `exp (M / μ)`, so the whole
-- sum is at most `Fintype.card ι * exp (M / μ)`, which gives the upper bound after applying
-- `μ * log`. Since the finite maximum is attained, one summand is exactly `exp (M / μ)`, so the
-- sum is at least that term, yielding the lower bound.
theorem supportFunction_range_toReal_smoothing_bounds
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    (ξ[Set.range a] x).toReal ≤ smoothMaxInnerApproximation a μ x ∧
      smoothMaxInnerApproximation a μ x ≤
        (ξ[Set.range a] x).toReal +
          (μ : ℝ) * Real.log (Fintype.card ι) := sorry

end

/-! ### Theorem_7_19 (from Chap07) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 7.19 lies in the chapter's relative-subgradient / dual-seminorm positivity domain.

Sampled owner-style declarations:
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the source-facing positivity predicate on a
  feasible set written directly with the canonical whole-space subdifferential owner
  `∂[Set.univ] f(x)`;
- `Seminorm.dualNorm` and `Seminorm.dualNorm_apply` in `Chap02/Definition_2_5`, the project owner
  for the dual norm of a separated seminorm;
- `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  chapter owner bridge for real-valued relative subgradients on a feasible set;
- mathlib `ConvexOn.sup`, the canonical convex-max owner for the pointwise maximum of two convex
  functions on the same feasible set.

Best owner abstraction:
- source-facing: Theorem 7.19's strict-positivity claim for the pointwise maximum
  `x ↦ max (φ x) (L * p x)` on `Q`;
- core/canonical: `p : Seminorm ℝ E` together with `[Seminorm.IsNorm p]`, the owner map
  `p.dualNorm`, and the chapter's relative-subdifferential owner `∂[Q] φ(x)`;
- bridge/view: the conclusion `StrictlyPositiveOn Q`, whose defining inequality is phrased with
  whole-space subgradients of the resulting max-function.

Primitive data:
- the feasible set `Q`;
- the convex objective `φ`;
- the separated seminorm `p : Seminorm ℝ E`;
- the scalar bound `L`.

Derived API:
- the dual norm `p.dualNorm`;
- the strict-positivity theorem below for `fun x ↦ max (φ x) (L * p x)`.

The previous version rebuilt a local `VectorNorm` wrapper and a duplicate dual-norm definition with
the exact same mathematical content as the Chapter 2 owner `Seminorm.dualNorm`. This refinement
deletes that duplicate owner, removes the theorem-local max wrapper, and states the subgradient
bound on the canonical relative owner `∂[Q] φ(x)` that matches `ConvexOn ℝ Q φ`.
-/

-- Proof sketch: let `f x = max (φ x) (L * p x)` and verify the defining inequality of
-- `StrictlyPositiveOn`. If `φ x < L * p x`, use a norming functional for `p` at `x` scaled by `L`.
-- If `φ x > L * p x`, use the assumed dual-norm bound on subgradients of `φ` together with the
-- triangle inequality. In the boundary case `φ x = L * p x`, pass to the limit through convex
-- combinations of the first two cases.
/-- Theorem 7.19: if `φ` is convex on `Q` and every subgradient of `φ` on `Q`
has dual norm at most `L`, then the augmented function
`x ↦ max (φ x) (L * p x)` is strictly positive on `Q` in the sense of Definition 7.81. -/
theorem strictlyPositiveOn_max_of_subgradientWithin_dualNorm_le
    (Q : Set E) (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ)
    (hφ_convex : ConvexOn ℝ Q φ) (hL_nonneg : 0 ≤ L)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L) :
    StrictlyPositiveOn Q (fun x ↦ max (φ x) (L * p x)) := sorry
