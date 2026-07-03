import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u

/- Proposition 12.7 is `source-facing`: it records the norm, adjoint, and coordinatewise proximal
formula for the block model with diagonal map `z ↦ (z, ..., z)` and separable regularizer
`(y₁, ..., y_p) ↦ ∑ i, g (y_i)`.

Domain sampling identifies the existing owners:
- `core/canonical`: Chapter 6 `prox[...]` and `proximal_objective`;
- `core/canonical`: Chapter 6 `PiLp.separableSum`;
- `core/canonical`: Chapter 12 `dual_block_duplication`;
- `bridge/view`: the constant block family `fun _ : Fin p ↦ g`.

Primitive data are therefore only `g` and the block number `p`; the block regularizer and the
duplication map are derived from those owners rather than defined again locally. -/

section Proposition127Part1

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/- Proposition 12.7 (1) is exactly the owner norm formula for the diagonal duplication map. -/
recall dual_block_duplication_opNorm_sq

end Proposition127Part1

section Proposition127Adjoint

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: use the defining adjoint identity
-- `⟪A z, y⟫ = ⟪z, A† y⟫`, expand the product inner product on `PiLp 2`, and rewrite the left-hand
-- side as `∑ i, ⟪z, y i⟫ = ⟪z, ∑ i, y i⟫`.
/-- Proposition 12.7 (2): the Hilbert adjoint of the diagonal duplication operator sends
`y = (y₁, ..., y_p)` to the block sum `∑ i, y_i`. -/
theorem dual_block_duplication_adjoint_apply
    {p : ℕ} (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    (dual_block_duplication E p).adjoint y =
      ∑ i : Fin p, y i := by
  apply ext_inner_right ℝ
  intro z
  calc
    inner ℝ ((dual_block_duplication E p).adjoint y) z =
        inner ℝ y (dual_block_duplication E p z) := by
      simpa using
        ContinuousLinearMap.adjoint_inner_left (dual_block_duplication E p) z y
    _ = ∑ i : Fin p, inner ℝ (y i) z := by
      simp [PiLp.inner_apply]
    _ = inner ℝ (∑ i : Fin p, y i) z := by
      rw [sum_inner]

end Proposition127Adjoint

section Proposition127Prox

variable {E : Type u} [NormedAddCommGroup E]

-- Proof sketch: specialize the Chapter 6 separable-product theorem
-- to the constant block family `fun _ : Fin p ↦ g`.
/-- Proposition 12.7 (3): for the block-separable regularizer
`(y₁, ..., y_p) ↦ ∑ i, g (y_i)`, the Chapter 6 proximal mapping on the Hilbert product is
coordinatewise, assuming the canonical owner hypothesis
`hg_proper : IsProperExtendedRealFunction g`:
`prox[PiLp.separableSum (fun _ ↦ g)] v = {y | ∀ i, y_i ∈ prox[g] (v_i)}`. -/
theorem prox_block_separable_regularizer_eq_coordinatewise
    {p : ℕ} (g : E → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (v : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    prox[PiLp.separableSum (fun _ : Fin p ↦ g)] v =
      {y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) | ∀ i : Fin p, y i ∈ prox[g] (v i)} := by
  simpa using
    (prox_separableSum_eq_coordinatewise (fun _ : Fin p ↦ g) (fun _ ↦ hg_proper) v)

end Proposition127Prox
