import Nesterov.Chap02.Proposition_2_5
import Nesterov.Chap06.Definition_6_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

/- Definition 6.14 lies in the finite simplex / entropic prox-geometry domain.

Sampled owner declarations:
* project `EuclideanSpace.l1Seminorm`, the canonical coordinate `ℓ₁` seminorm on `ℝⁿ`;
* project `EuclideanSpace.l1Seminorm_apply`, the coordinate formula for that owner;
* project `entropyFunction`, the canonical entropy owner on `Fin n → ℝ`;
* project `entropyFunction_apply`, the coordinate expansion of that owner.

Best owner abstraction:
* source-facing: the normalized entropy prox-function on the simplex `Δ[n]`;
* core/canonical: `EuclideanSpace.l1Seminorm` for the ambient geometry and `entropyFunction` for
  the entropy term;
* bridge/view: restricting `x ↦ log n + entropyFunction n x` to the simplex subtype `Δ[n]`.

Primitive data:
* the positive dimension `n : ℕ+`.

Derived API:
* the pointwise formula for the normalized entropy prox-function on `Δ[n]`;
* the textbook use of `EuclideanSpace.l1Seminorm (n : ℕ)` and
  `EuclideanSpace.l1Seminorm (m : ℕ)` as the ambient norms on `ℝⁿ` and `ℝᵐ`.

Source/core/bridge triage:
* source-facing: `normalizedEntropyProxFunction`;
* core/canonical: `EuclideanSpace.l1Seminorm` and `entropyFunction`;
* bridge/view: this file, which keeps the simplex-subtype prox function but deletes the duplicate
  bundled prox-structure wrapper.
-/

/-- Definition 6.14: on the standard simplex `Δ_n`, the entropy prox-function is
`x ↦ log n + ∑ᵢ xᵢ log xᵢ`; the ambient norm is the canonical coordinate `ℓ₁` seminorm
`EuclideanSpace.l1Seminorm (n : ℕ)`. The same owner specializes to the textbook pair
`(d₁, d₂)` by using the dimensions `n` and `m`. -/
def normalizedEntropyProxFunction (n : ℕ+) : Δ[n] → ℝ :=
  fun x ↦ Real.log (n : ℝ) + entropyFunction (n : ℕ) x

/-- The ambient norm from Definition 6.14 is the canonical coordinate `ℓ₁` seminorm on `ℝⁿ`,
written in textbook form as the sum of the coordinate absolute values. -/
-- Proof sketch: specialize `EuclideanSpace.l1Seminorm_apply` to real coordinates and rewrite
-- `‖x i‖` as `|x i|`.
theorem l1Seminorm_eq_sum_abs (n : ℕ+) (x : EuclideanSpace ℝ (Fin (n : ℕ))) :
    EuclideanSpace.l1Seminorm (n : ℕ) x = ∑ i : Fin (n : ℕ), |x i| := sorry

/-- Evaluating `normalizedEntropyProxFunction n` gives the textbook formula
`log n + ∑ᵢ xᵢ log xᵢ` on `Δ_n`. -/
-- Proof sketch: unfold `normalizedEntropyProxFunction` and then expand `entropyFunction`
-- coordinatewise using `entropyFunction_apply`.
theorem normalizedEntropyProxFunction_apply (n : ℕ+) (x : Δ[n]) :
    normalizedEntropyProxFunction n x =
      Real.log (n : ℝ) + ∑ i : Fin (n : ℕ), x i * Real.log (x i) := sorry
