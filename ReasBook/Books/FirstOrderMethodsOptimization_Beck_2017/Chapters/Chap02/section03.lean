import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_3 (from Chap02) -/
universe u

variable {α : Type u}

/- Definition 2.3: the project records the textbook notion of lower semicontinuity at a point via
the canonical mathlib owner declaration `LowerSemicontinuousAt`. -/
recall LowerSemicontinuousAt

/- The global notion of lower semicontinuity is the canonical pointwise owner statement
`lowerSemicontinuous_iff`. -/
recall lowerSemicontinuous_iff

/- The liminf formulation used by the textbook is the canonical complete-linear-order
characterization `lowerSemicontinuousAt_iff_le_liminf`. -/
recall lowerSemicontinuousAt_iff_le_liminf

section

variable {f : α → EReal} {a : ℝ} {x : α}

/- The textbook real level-set notation is canonically the preimage `f ⁻¹' Iic (a : EReal)`. -/
#check (f ⁻¹' Set.Iic (a : EReal))

/- Membership in that real sublevel set is definitionally the inequality `f x ≤ a`. -/
#check (show x ∈ f ⁻¹' Set.Iic (a : EReal) ↔ f x ≤ (a : EReal) from Iff.rfl)

end

/-! ### Example_2_3 (from Chap02) -/
noncomputable section

/-- The Example 2.3 family takes the value `α` at `0`, agrees with the identity on `(0, 1]`, and
is `∞` elsewhere. -/
def truncated_identity_with_origin_value (α : ℝ) : ℝ → EReal :=
  fun x ↦ extendedIndicator (Set.Icc (0 : ℝ) 1) x + if x = 0 then (α : EReal) else x

-- Proof sketch: unfold `truncated_identity_with_origin_value` and `effective_domain`, then split
-- into the cases `x = 0`, `0 < x ∧ x ≤ 1`, and the complement. The value at `0` is finite because
-- `α : ℝ`, so the finite-value locus is exactly the interval `[0, 1]`.
/-- The effective domain of `truncated_identity_with_origin_value α` is exactly the interval
`[0, 1]`. -/
theorem truncated_identity_with_origin_value_effective_domain_eq (α : ℝ) :
    effective_domain (truncated_identity_with_origin_value α) = Set.Icc (0 : ℝ) 1 := sorry

-- Proof sketch: the function is continuous on each branch away from `0`. At the origin, the only
-- possible failure of lower semicontinuity comes from approaching through positive points in the
-- domain, where the values converge to `0`, so the lower-semicontinuity condition is exactly
-- `α ≤ 0`.
/-- Example 2.3: the function `truncated_identity_with_origin_value α` is closed, equivalently
lower semicontinuous, if and only if `α ≤ 0`. -/
theorem truncated_identity_with_origin_value_lowerSemicontinuous_iff (α : ℝ) :
    LowerSemicontinuous (truncated_identity_with_origin_value α) ↔ α ≤ 0 := sorry

-- Proof sketch: use `truncated_identity_with_origin_value_effective_domain_eq` to identify the
-- effective domain with `[0, 1]`. Relative continuity is automatic away from `0`, and at `0` the
-- right-hand limit along the domain is `0`, so continuity on the effective domain holds exactly
-- when the value assigned at `0` is also `0`.
/-- The Example 2.3 family is continuous on its effective domain exactly when the origin value is
`0`. -/
theorem truncated_identity_with_origin_value_continuousOn_effective_domain_iff (α : ℝ) :
    ContinuousOn (truncated_identity_with_origin_value α)
      (effective_domain (truncated_identity_with_origin_value α)) ↔ α = 0 := sorry

-- Proof sketch: combine
-- `truncated_identity_with_origin_value_lowerSemicontinuous_iff` and
-- `truncated_identity_with_origin_value_continuousOn_effective_domain_iff` at `α = -1 / 10`.
/-- The parameter choice `α = -1 / 10` gives a closed function that is not continuous on its
effective domain. -/
theorem truncated_identity_with_origin_value_neg_tenth_closed_not_continuousOn_effective_domain :
    LowerSemicontinuous (truncated_identity_with_origin_value (-(1 : ℝ) / 10)) ∧
      ¬ ContinuousOn (truncated_identity_with_origin_value (-(1 : ℝ) / 10))
        (effective_domain (truncated_identity_with_origin_value (-(1 : ℝ) / 10))) := sorry

end

/-! ### Lemma_2_3 (from Chap02) -/
/- Lemma 2.3 is the canonical pointwise-set identity `Set.image_smul`: for a scalar `α ∈ ℝ` and
a set `A ⊆ E`, the pointwise scalar multiple `α • A` is the image of `A` under the map
`a ↦ α • a`, equivalently the set `{α • a | a ∈ A}`. -/
recall Set.image_smul

/-! ### Proposition_2_3 (from Chap02) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: if `y ∈ polar_cone K`, every pairing `y x` with `x ∈ K`
-- is at most `0`, and `0 ∈ K`, so the supremum defining `support_function K y`
-- is exactly `0`. If `y ∉ polar_cone K`, choose `x ∈ K` with `0 < y x`; since
-- `K` is closed under nonnegative scaling, every `t • x` with `t > 0` also lies
-- in `K`, so the support function dominates arbitrarily large real values and
-- therefore equals `⊤`, matching the indicator of the complement of the polar
-- cone.
/-- Proposition 2.3: if `K` is closed under nonnegative scalar multiplication and contains `0`,
then the support function `σ_K` is the indicator function of the polar cone
`Kᵒ = {y | ∀ x ∈ K, y x ≤ 0}`. -/
theorem support_function_eq_indicatorFunction_polarCone
    (K : Set E) (hK : IsCone K) (h0 : (0 : E) ∈ K) :
    support_function K = extendedIndicator (polar_cone K) := sorry

end

/-! ### Theorem_2_3 (from Chap02) -/
universe u

variable {E : Type u} [TopologicalSpace E]

section

-- Proof sketch: prove lower semicontinuity pointwise. On the closed effective domain, continuity
-- gives lower semicontinuity within the domain. Outside the domain the function is identically
-- `⊤` on an open neighborhood, because the complement of a closed effective domain is open.
-- Combine these two cases to obtain lower semicontinuity everywhere.
/-- Theorem 2.3: if an extended-real-valued function is continuous on its effective domain and that
domain is closed, then the function is closed, equivalently lower semicontinuous. -/
theorem lowerSemicontinuous_of_continuousOn_effective_domain (f : E → EReal)
    (h_cont : ContinuousOn f (effective_domain f))
    (h_closed : IsClosed (effective_domain f)) :
    LowerSemicontinuous f := sorry

end
