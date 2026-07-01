import Mathlib
import FirstOrderMethodsinOptimization.Chap12.Algorithm_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal BigOperators

noncomputable section

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 12.8 is `source-facing`: it computes the dual smoothness constant for the specific
diagonal duplication operator `𝒜(z) = (z, …, z)` used to rewrite the block problem in Chapter 12.

Domain sampling against nearby project owners and mathlib points to:
- `dual_based_proximal_gradient_dual_lipschitz_constant` from Algorithm 12.1 as the canonical
  owner for the FDPG parameter `L = ‖𝒜‖² / σ`;
- `PiLp (2 : ENNReal)` as the canonical `L²` block-product owner from Chapter 11;
- `ContinuousLinearMap.pi` together with `PiLp.continuousLinearEquiv` as the canonical realization
  of the diagonal map into the `p`-fold block product.

The public API should therefore expose the actual diagonal continuous linear map and state the
constant formula directly for that canonical owner, rather than through a surrogate package. -/

variable (E) in
/-- The diagonal duplication operator sending `z` to the constant `p`-block vector
`(z, \ldots, z)` in the `L²` block product `PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)`. -/
abbrev dual_block_duplication
    (p : ℕ) : E →L[ℝ] PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) :=
  ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun _ : Fin p ↦ ContinuousLinearMap.id ℝ E)

-- Proof sketch: unfold `dual_block_duplication`; `ContinuousLinearMap.pi` forms the constant
-- function `fun _ ↦ z`, and `PiLp.continuousLinearEquiv` identifies that function with its point in
-- the `L²` block product.
/-- Every block coordinate of the duplicated vector `𝒜(z)` is equal to `z`. -/
@[simp] theorem dual_block_duplication_apply
    (p : ℕ) (z : E) (i : Fin p) :
    dual_block_duplication E p z i = z := by
  simp [dual_block_duplication]

variable (E) in
/-- Helper for Proposition 12.8: the duplicated `L²` block vector has squared norm
`p * ‖z‖²`. -/
lemma dual_block_duplication_norm_sq_apply
    (p : ℕ) (z : E) :
    ‖dual_block_duplication E p z‖ ^ (2 : ℕ) = (p : ℝ) * ‖z‖ ^ (2 : ℕ) := by
  -- Expand the `PiLp` norm into the sum of coordinate squares.
  calc
    ‖dual_block_duplication E p z‖ ^ (2 : ℕ)
        = ∑ i : Fin p, ‖dual_block_duplication E p z i‖ ^ (2 : ℕ) := by
            simpa using
              (PiLp.norm_sq_eq_of_L2 (fun _ : Fin p ↦ E) (dual_block_duplication E p z))
    _ = ∑ i : Fin p, ‖z‖ ^ (2 : ℕ) := by
          simp
    _ = (p : ℝ) * ‖z‖ ^ (2 : ℕ) := by
          simp

variable (E) in
/-- Helper for Proposition 12.8: the duplication map scales every norm by `√p`. -/
lemma dual_block_duplication_norm_apply
    (p : ℕ) (z : E) :
    ‖dual_block_duplication E p z‖ = Real.sqrt (p : ℝ) * ‖z‖ := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  -- Compare squares of the two nonnegative quantities.
  refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp ?_
  rw [dual_block_duplication_norm_sq_apply, mul_pow, Real.sq_sqrt hp_nonneg]

-- Proof sketch: evaluate `‖dual_block_duplication p z‖²` using `PiLp.norm_sq_eq_of_L2`; this gives
-- `∑ i : Fin p, ‖z‖² = p * ‖z‖²`. The upper bound `‖𝒜‖² ≤ p` follows from this identity and
-- `ContinuousLinearMap.opNorm_le_bound`; the matching lower bound is obtained by testing the map on
-- any nonzero vector of norm `1`.
variable [Nontrivial E]

/-- The diagonal duplication operator on the `p`-fold `L²` block product has squared operator norm
`p`. -/
theorem dual_block_duplication_opNorm_sq
    (p : ℕ) :
    ‖dual_block_duplication E p‖ ^ (2 : ℕ) = (p : ℝ) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  have hnorm :
      ‖dual_block_duplication E p‖ = Real.sqrt (p : ℝ) := by
    -- The vectorwise scaling formula identifies the map as a homothety of ratio `√p`.
    simpa using
      (ContinuousLinearMap.homothety_norm (dual_block_duplication E p)
        (dual_block_duplication_norm_apply (E := E) p))
  -- Square the operator-norm identity to recover the textbook constant `‖𝒜‖² = p`.
  calc
    ‖dual_block_duplication E p‖ ^ (2 : ℕ) = (Real.sqrt (p : ℝ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = (p : ℝ) := by
      exact Real.sq_sqrt hp_nonneg

-- Proof sketch: unfold the Chapter 12.1 owner
-- `dual_based_proximal_gradient_dual_lipschitz_constant`, then substitute
-- `dual_block_duplication_opNorm_sq`.
/-- Proposition 12.8: for the diagonal duplication operator `𝒜(z) = (z, \ldots, z)`, the FDPG
parameter from Algorithm 12.1 satisfies `L = ‖𝒜‖² / σ = p / σ`. -/
@[simp]
theorem dual_block_duplication_fdpg_lipschitz_constant_eq
    (σ : PosReal) (p : ℕ) :
    dual_based_proximal_gradient_dual_lipschitz_constant
        (dual_block_duplication E p) σ =
      (p : ℝ) / (σ : ℝ) := by
  rw [dual_based_proximal_gradient_dual_lipschitz_constant_eq, dual_block_duplication_opNorm_sq]

end
