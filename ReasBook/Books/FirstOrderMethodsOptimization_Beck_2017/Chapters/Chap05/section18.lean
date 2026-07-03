

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_5_18 (from Chap05) -/
noncomputable section

open WithLp (ofLp)

section

variable {n : ℕ}

local notation "E₁" => WithLp 1 (Fin n → ℝ)
local notation "Δ₁" => Set.preimage (ofLp : E₁ → Fin n → ℝ) (stdSimplex ℝ (Fin n))

/- Remark 5.18 is `source-facing`: the primitive object is the entropy-shifted simplex function
`x ↦ f(x) - α ‖x‖₁²`. Domain sampling points to Proposition 5.14's entropy owner
`coordinatewise_negative_entropy` and mathlib's canonical real-valued owner `ConvexOn` on the
`WithLp 1` simplex model. The main labeled entry is therefore a convexity statement on `Δ₁`,
while the helper lemmas record the simplex-specific identities `‖x‖₁ = 1` and
`f(x) - α ‖x‖₁² = f(x) - α`. -/

-- Proof sketch: expand `hx : x ∈ Δ₁` as `ofLp x ∈ stdSimplex ℝ (Fin n)`, rewrite the `WithLp 1`
-- norm by the finite `ℓ₁` coordinate formula, then use nonnegativity of simplex coordinates to
-- remove absolute values and the simplex equation `∑ i, ofLp x i = 1`.
/-- Every point of the unit simplex has `ℓ₁`-norm equal to `1` in the canonical `WithLp 1`
model. -/
theorem l1_norm_eq_one_of_mem_stdSimplex {x : E₁} (hx : x ∈ Δ₁) :
    ‖x‖ = 1 := sorry

-- Proof sketch: substitute `‖x‖ = 1` from `l1_norm_eq_one_of_mem_stdSimplex hx`, square this
-- identity, and simplify the scalar expression.
/-- On the unit simplex, subtracting `α ‖x‖₁²` from the negative entropy is the same as
subtracting the constant `α`. -/
theorem negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex
    (α : ℝ) {x : E₁} (hx : x ∈ Δ₁) :
    coordinatewise_negative_entropy (ofLp x) - α * ‖x‖ ^ (2 : ℕ) =
      coordinatewise_negative_entropy (ofLp x) - α := sorry

-- Proof sketch: use Proposition 5.14 to get `1`-strong convexity of
-- `x ↦ coordinatewise_negative_entropy (ofLp x)` on `Δ₁`, lower the modulus to `0` to obtain
-- convexity, and then apply `ConvexOn.add_const (-α)`. The helper lemma
-- `negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex` identifies the source
-- expression with that constant translate on all points of `Δ₁`.
/-- Remark 5.18: for every `α > 0`, the negative entropy on the unit simplex remains convex after
subtracting `α ‖x‖₁²`, because this term is constant on the simplex. -/
theorem negative_entropy_sub_alpha_l1Square_convexOn_stdSimplex (α : ℝ) (hα : 0 < α) :
    ConvexOn ℝ Δ₁
      (fun x : E₁ ↦ coordinatewise_negative_entropy (ofLp x) - α * ‖x‖ ^ (2 : ℕ)) := sorry

-- Proof sketch: the preceding theorem shows that every positive shift parameter still gives a
-- convex function. If the same parameter `α` also yielded `α`-strong convexity for all `α > 0`,
-- then this one simplex entropy profile would admit arbitrarily large strong-convexity moduli up
-- to constant translation, contradicting the finite-curvature geometry alluded to in the remark.
/-- The entropy shift cannot realize the same positive parameter simultaneously as shift size and
strong-convexity modulus for every `α > 0`. -/
theorem not_forall_pos_strongConvexOn_negative_entropy_sub_alpha_l1Square
    (n : ℕ) :
    ¬ ∀ α > 0,
      StrongConvexOn
        (Set.preimage (ofLp : WithLp 1 (Fin n → ℝ) → Fin n → ℝ) (stdSimplex ℝ (Fin n)))
        α
        (fun x : WithLp 1 (Fin n → ℝ) ↦
          coordinatewise_negative_entropy (ofLp x) - α * ‖x‖ ^ (2 : ℕ)) := sorry

end
