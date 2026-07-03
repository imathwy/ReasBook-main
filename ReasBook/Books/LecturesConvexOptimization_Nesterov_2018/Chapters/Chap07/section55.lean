

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_55 (from Chap07) -/
noncomputable section

universe u

section

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-
Definition 7.55 lies in Chapter 7's barrier-regularized affine-maximization domain.

Sampled owner-style declarations:
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter owner for `EReal`-valued maximal
  values of real objectives on feasible sets;
- `maximalValueOn_eq_sSup_image` in `Chap07/Definition_7_56`, the canonical expansion theorem for
  that owner;
- `affineBarrierRegularizedPayoff` and `affineBarrierRegularizedPayoff_def` in `Chap07/Lemma_7_11`,
  the source-facing payoff surface specialized by this definition.

Best owner abstraction:
- source-facing: the textbook barrier-regularized value `ℓ⋆(β)`;
- core/canonical: `maximalValueOn`;
- bridge/view: the specialization to `hatP ∩ interior Q` and
  `affineBarrierRegularizedPayoff x0 β ℓ F`, together with the explicit `sSup` formula.

Primitive data:
- the sets `hatP` and `Q`;
- the barrier term `F`, base point `x₀`, affine functional `ℓ`, and parameter `β`.

Derived API:
- the direct specialization of `maximalValueOn` to the barrier-regularized payoff;
- the `sSup` expansion and the two basic comparison lemmas below.

Definition 7.55 does not introduce a second maximal-value owner: the mathematical content is the
existing Chapter 7 owner `maximalValueOn` evaluated at the barrier-regularized affine payoff on
the strict feasible set. The refinement therefore deletes the duplicate wrapper and keeps only the
source-specific companion theorems on that canonical owner.
-/

variable (hatP Q : Set E) (F : E → ℝ) (x0 : E) (ℓ : AffineMap ℝ E ℝ) (β : ℝ)

/- Definition 7.55 uses the Chapter 7 maximal-value owner directly at the barrier-regularized
affine payoff on the strict feasible set `hatP ∩ interior Q`. -/
set_option linter.hashCommand false in
#check maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F)

section

variable {hatP Q : Set E} {F : E → ℝ} {x0 : E} {ℓ : AffineMap ℝ E ℝ} {β : ℝ}

-- Proof sketch: expand `maximalValueOn` by
-- `maximalValueOn_eq_sSup_image` and the payoff by `affineBarrierRegularizedPayoff_def`.
/-- Expanding the canonical maximal-value owner at the barrier-regularized affine payoff gives the
supremum formula defining the textbook value `ℓ⋆(β)` on `P₀`. -/
theorem maximalValueOn_affineBarrierRegularizedPayoff_eq_sSup_image
    (hatP Q : Set E) (F : E → ℝ) (x0 : E) (ℓ : AffineMap ℝ E ℝ) (β : ℝ) :
    maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F) =
      sSup
        ((fun x : E ↦ ((ℓ x - β * (F x - F x0) : ℝ) : EReal)) ''
          (hatP ∩ interior Q)) := sorry

-- Proof sketch: evaluate the defining supremum at the feasible point `x₀`; the barrier term
-- vanishes there because `F x0 - F x0 = 0`.
/-- If the base point `x₀` lies in the strict feasible set `P₀`, then the canonical maximal value
of the barrier-regularized payoff is at least the textbook base value `ℓ₀ = ℓ(x₀)`. -/
theorem baseAffineValue_le_maximalValueOn_affineBarrierRegularizedPayoff
    (hatP Q : Set E) (F : E → ℝ) (x0 : E) (ℓ : AffineMap ℝ E ℝ) (β : ℝ)
    (hx0 : x0 ∈ hatP ∩ interior Q) :
    (ℓ x0 : EReal) ≤
      maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F) := sorry

-- Proof sketch: the `β = 0` specialization of Definition 7.55 is just the ordinary affine
-- objective `ℓ`; then apply `maximalValueOn_eq_of_closure_eq` with `P₀ = hatP ∩ interior Q` and
-- `P = hatP ∩ Q`.
/-- When the regularization parameter is `0`, Definition 7.55 reduces to the ordinary maximal
value of `ℓ`; if `hatP ∩ Q` is the closure of `hatP ∩ interior Q` and `ℓ` is continuous there,
the two owner values coincide. -/
theorem maximalValueOn_affineBarrierRegularizedPayoff_zero
    (hatP Q : Set E) (ℓ : AffineMap ℝ E ℝ)
    (hℓ : ContinuousOn ℓ (hatP ∩ Q))
    (hclosure : closure (hatP ∩ interior Q) = hatP ∩ Q) :
    maximalValueOn (hatP ∩ interior Q) ℓ =
      maximalValueOn (hatP ∩ Q) ℓ := sorry

end

end
