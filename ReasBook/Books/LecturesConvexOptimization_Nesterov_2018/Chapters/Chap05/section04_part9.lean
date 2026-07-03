import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_4_7_3 (from Chap05) -/
noncomputable section

open scoped PowerConeGeometricMean

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerCone

/- Theorem 5.4.7.3 is a barrier theorem in the Chapter 5 power-cone domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the earlier source-facing owner for `K_α`;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the generic owner for the composed barrier
  used here;
* `power_cone_plus_barrier_apply` from `Theorem_5_4_7_4`, the adjacent bridge theorem evaluating
  the one-sided specialization of the same generic owner shape;
* `ξ[α]`, `powerConeBarrier`, and the swapped-coordinate specialization
  `secondOrderConeBarrier ∘ Prod.swap`, the earlier primitive factor data for the same
  cone-composition construction;
* `powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier` from `Theorem_5_4_7_2`, the
  compatibility theorem feeding the proof route.

Source/core/bridge triage:
* source-facing: the barrier owner `power_cone_barrier α` and the resulting four-self-concordant
  barrier statement on `powerCone α`;
* core/canonical: the earlier owner `coneCompositionBarrier` specialized to the power-cone data;
* bridge/view: the explicit logarithmic evaluation formula below.

Primitive data:
* `powerConeBarrier`;
* `secondOrderConeBarrier ∘ Prod.swap`;
* `ξ[α]`;
* the source-facing cone owner `powerCone α`.

Derived API:
* the source-facing barrier owner `power_cone_barrier α`;
* the pointwise evaluation formula below;
* the resulting `4`-self-concordant barrier statement on `interior (powerCone α)`.

This refinement keeps `coneCompositionBarrier` as the core owner abstraction for the proof route,
but exposes the textbook power-cone barrier itself through the shorter source-facing owner
`power_cone_barrier α`, matching the adjacent chapter API. -/

/-- The logarithmic barrier `Ψ_P` for the symmetric power cone `K_α`, presented as the
source-facing specialization of the chapter's canonical cone-composition barrier owner. -/
def power_cone_barrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (secondOrderConeBarrier ∘ Prod.swap)
    ξ[α]
    1

-- Proof sketch: on the nonnegative orthant, evaluate `power_cone_barrier α` at
-- `((x₁, x₂), z)` using the upstream pointwise formulas for `secondOrderConeBarrier ∘ Prod.swap`,
-- `powerConeBarrier`, and `ξ[α]`, then rewrite the square
-- `(x₁^α x₂^(1 - α))^2` as `x₁^(2 α) x₂^(2 (1 - α))`.
/-- Evaluating `power_cone_barrier α` at `((x₁, x₂), z)` on the nonnegative orthant
reproduces the textbook formula
`-log ((x₁)^(2 α) (x₂)^(2 (1 - α)) - z^2) - log x₁ - log x₂`. -/
theorem power_cone_barrier_apply
    (α x₁ x₂ z : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) :
    power_cone_barrier α ((x₁, x₂), z) =
      -Real.log
          (Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) - z ^ (2 : ℕ)) -
        Real.log x₁ - Real.log x₂ := by
  rw [power_cone_barrier, coneCompositionBarrier_apply, secondOrderConeBarrier_swap_apply,
    powerConeBarrier_apply, powerConeGeometricMean_apply]
  norm_num
  have hx₁_square : Real.rpow x₁ α ^ (2 : ℕ) = Real.rpow x₁ (α * 2) := by
    simpa using (Real.rpow_mul_natCast hx₁ α 2).symm
  have hx₂_square : Real.rpow x₂ (1 - α) ^ (2 : ℕ) = Real.rpow x₂ ((1 - α) * 2) := by
    simpa using (Real.rpow_mul_natCast hx₂ (1 - α) 2).symm
  have hsquare :
      (Real.rpow x₁ α * Real.rpow x₂ (1 - α)) ^ (2 : ℕ) =
        Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) := by
    calc
      (Real.rpow x₁ α * Real.rpow x₂ (1 - α)) ^ (2 : ℕ) =
          (Real.rpow x₁ α) ^ (2 : ℕ) * (Real.rpow x₂ (1 - α)) ^ (2 : ℕ) := by
            ring
      _ = Real.rpow x₁ (α * 2) * Real.rpow x₂ ((1 - α) * 2) := by
        rw [hx₁_square, hx₂_square]
      _ = Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) := by
        congr 1 <;> ring_nf
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    congrArg
      (fun t : ℝ ↦ -Real.log (t - z ^ (2 : ℕ)) + (-Real.log x₁ - Real.log x₂))
      hsquare

-- Proof sketch: apply the cone-composition barrier construction with
-- `Q₁ = ℝ_+²`, `F(x₁, x₂) = -log x₁ - log x₂`, `β = 1`, `ξ(x₁, x₂) = x₁^α x₂^(1 - α)`, and
-- `Φ(y, z) = -log (y^2 - z^2)`. Theorem 5.4.7.2 supplies the `1`-compatibility of `ξ` with
-- `F`, and the planar barrier `Φ` has parameter `μ = 2`; together with `ν = 2` for `F`, the
-- composed barrier has parameter `μ + ν = 4` and specializes to the owner barrier below on the
-- interior of `powerCone α`.
/-- Theorem 5.4.7.3: for `0 < α < 1`, the function
`Ψ_P((x₁, x₂), z) = -log ((x₁)^(2 α) (x₂)^(2 (1 - α)) - z^2) - log x₁ - log x₂`
is a `4`-self-concordant barrier for the power cone `K_α`. -/
theorem power_cone_barrier_is_four_self_concordant_barrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior K_[α])
      (4 : NNReal)
      (power_cone_barrier α) := sorry

/-! ### Theorem_5_4_7_4 (from Chap05) -/
noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerConePlus

/- Theorem 5.4.7.4 lies in the Chapter 5 power-cone / cone-composition barrier domain.

Sampled owner declarations:
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the generic composed-barrier owner;
* `power_cone_plus` from `Definition_5_4_7_4`, the source-facing one-sided power-cone owner;
* `qTwoPlus_sublevelLogBarrier_apply` from `Definition_5_4_7_5`, the recalled planar logarithmic
  barrier specialization used as the outer barrier factor;
* `coneCompositionBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_4_6_13`, the canonical
  composed-barrier owner theorem specialized here to the power-cone data;
* `power_cone_barrier` and `power_cone_barrier_is_four_self_concordant_barrier` from
  `Theorem_5_4_7_3`, the sibling source-facing barrier owner and theorem on the symmetric power
  cone.

Source/core/bridge triage:
* source-facing: the barrier owner `power_cone_plus_barrier α` and the resulting theorem on
  `interior (K_[α]⁺)` for the textbook function `Ψ_P^+((x₁, x₂), z)`;
* core/canonical: the generic owner theorem
  `coneCompositionBarrier_isSelfConcordantBarrierOnWith`;
* bridge/view: the pointwise identity between `power_cone_plus_barrier α` and the textbook
  logarithmic formula.

Primitive data:
* `powerConeBarrier`;
* `sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0`;
* `powerConeGeometricMean α`;
* the source-facing cone owner `K_[α]⁺`.

Derived API:
* the source-facing barrier owner `power_cone_plus_barrier α`;
* the pointwise evaluation formula below;
* the resulting `3`-self-concordant barrier statement directly on
  `interior (K_[α]⁺)`.

This refinement keeps the source-facing cone owner `K_[α]⁺` as the public surface,
introduces the matching source-facing barrier owner `power_cone_plus_barrier α`, and keeps the
pointwise formula as the thin companion bridge to the canonical `coneCompositionBarrier`
specialization. -/

/-- The logarithmic barrier `Ψ_P^+` for the one-sided power cone `K_α^+`, presented as the
source-facing specialization of the chapter's canonical cone-composition barrier owner. -/
def power_cone_plus_barrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0)
    (powerConeGeometricMean α)
    1

-- Proof sketch: evaluate `power_cone_plus_barrier α` at `((x₁, x₂), z)` using the upstream
-- pointwise formulas for `powerConeBarrier`, `sublevelLogBarrier`, and `powerConeGeometricMean`.
/-- Evaluating `power_cone_plus_barrier α` at `((x₁, x₂), z)` gives the textbook formula
`-log (x₁^α x₂^(1 - α) - z) - log x₁ - log x₂`. -/
theorem power_cone_plus_barrier_apply (α x₁ x₂ z : ℝ) :
    power_cone_plus_barrier α ((x₁, x₂), z) =
      -Real.log (Real.rpow x₁ α * Real.rpow x₂ (1 - α) - z) -
        Real.log x₁ - Real.log x₂ := by
  rw [power_cone_plus_barrier, coneCompositionBarrier_apply,
    qTwoPlus_sublevelLogBarrier_apply, powerConeBarrier_apply, powerConeGeometricMean_apply]
  have hβ : (((1 : NNReal) : ℝ) ^ (3 : ℕ)) = 1 := by
    norm_num
  rw [hβ]
  ring

-- Proof sketch: instantiate the general cone-composition barrier theorem with
-- `Q₁ = powerConeQ1`, `K = ConvexCone.positive ℝ ℝ`, `ξ = powerConeGeometricMean α`,
-- `Q₂ = {(y, z) | z ≤ y}`, `Φ = sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0`, and
-- `F = powerConeBarrier`. The compatibility hypothesis is provided by
-- `powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier`, the barrier parameters are `1`
-- for `sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0` and `2` for `powerConeBarrier`, and the
-- resulting source-facing owner `power_cone_plus_barrier α` has total parameter `3`. The bridge
-- lemma `power_cone_plus_barrier_apply` rewrites that owner to the textbook raw-triple
-- logarithmic formula, so the public theorem is stated directly on `interior (K_[α]⁺)`.
/-- Theorem 5.4.7.4: for `0 < α < 1`, the function
`Ψ_P^+((x₁, x₂), z) = -log (x₁^α x₂^(1 - α) - z) - log x₁ - log x₂` is a
`3`-self-concordant barrier for the one-sided power cone `K_α^+`. -/
theorem power_cone_plus_barrier_is_three_self_concordant_barrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior (K_[α]⁺))
      (3 : NNReal)
      (power_cone_plus_barrier α) := sorry

/-! ### Theorem_5_4_7_5 (from Chap05) -/
open scoped EuclideanSpaceLp

/- Theorem 5.4.7.5 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-cone domain.

Sampled owner declarations:
* `EuclideanSpace.LpExponent` from `Definition_3_7`, the project owner for admissible
  finite-dimensional `ℓ_p` exponents `1 ≤ p < ∞`;
* `EuclideanSpace.lpSeminorm` and `EuclideanSpace.lpNorm_eq_sum` from `Definition_3_7`, the
  intrinsic finite-dimensional `ℓ_p` owner and its textbook notation surface `‖z‖_[p]`;
* `lpNormEpigraphCone` and `mem_lpNormEpigraphCone_iff` from `Definition_5_4_7_6`, the
  coordinate-model epigraph bridge sitting underneath the intrinsic norm inequality;
* `lpEpigraphConeLiftDomain` and `mem_lpEpigraphConeLiftDomain_iff` from
  `Definition_5_4_7_7`, the chapter owner for the lifted-domain witness data;
* `WithLp.toLp`, the canonical coordinate norm owner used internally by
  `lpNormEpigraphCone`.

Source/core/bridge triage:
* source-facing: membership of `(τ, z)` in the epigraph owner `lpNormEpigraphCone n p`;
* core/canonical: the owner seminorm `EuclideanSpace.lpSeminorm n p`;
* bridge/view: the coordinate epigraph owner `lpNormEpigraphCone n (p : ENNReal)` and the
  lifted witness
  domain `lpEpigraphConeLiftDomain n (1 / p.toReal)`.

Primitive data:
* the admissible exponent `p : EuclideanSpace.LpExponent`;
* the epigraph point `(τ, z) : ℝ × EuclideanSpace ℝ (Fin n)`.

Derived API:
* the source-facing epigraph membership `(τ, z) ∈ lpNormEpigraphCone n p`;
* the intrinsic inequality bridge `mem_lpNormEpigraphCone_iff`;
* the lifted witness domain `lpEpigraphConeLiftDomain n (1 / p.toReal)`;
* the coordinatewise witness inequalities, recovered from
  `mem_lpEpigraphConeLiftDomain_iff` when needed.

This theorem therefore lives on the Chapter 5 epigraph owner surface `lpNormEpigraphCone`, while
the intrinsic inequality `‖z‖_[p] ≤ τ` is kept only as the upstream bridge
`mem_lpNormEpigraphCone_iff`. The lifted witness set remains a genuine bridge layer rather than a
competing public owner. -/

-- Proof sketch: the main theorem is stated directly on the epigraph owner
-- `lpNormEpigraphCone n p`. For the forward direction, construct a lift `(τ, x, z)` in
-- `lpEpigraphConeLiftDomain n (1 / p.toReal)` by choosing the standard coordinate witness `x`
-- from the finite-dimensional `ℓ_p` norm formula. For the reverse direction, unpack the lift with
-- `mem_lpEpigraphConeLiftDomain_iff`, raise the coordinate inequalities to the power
-- `p.toReal`, sum over `i`, use `∑ i, x i = τ`, and finally read the result back through
-- `mem_lpNormEpigraphCone_iff` when needed.
/-- Theorem 5.4.7.5: a point `(τ, z)` lies in the finite-dimensional `ℓ_p` epigraph cone exactly
when it admits a lift to the chapter’s lifted domain with exponent `1 / p.toReal`. -/
theorem mem_lpNormEpigraphCone_iff_exists_lift
    {n : ℕ} (p : EuclideanSpace.LpExponent) {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)} :
    (τ, z) ∈ lpNormEpigraphCone n p ↔
      ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) :=
  sorry

/-- The intrinsic inequality form of Theorem 5.4.7.5, read through the epigraph-owner bridge
`mem_lpNormEpigraphCone_iff`. -/
theorem lpSeminorm_le_iff_exists_lift
    {n : ℕ} (p : EuclideanSpace.LpExponent) {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)} :
    ‖z‖_[p] ≤ τ ↔
      ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) := by
  rw [← mem_lpNormEpigraphCone_iff]
  exact mem_lpNormEpigraphCone_iff_exists_lift p

/-! ### Theorem_5_4_7_6 (from Chap05) -/
noncomputable section

open scoped EntropyEpigraph

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

/-
Theorem 5.4.7.6 lies in the Chapter 5 entropy-epigraph / cone-composition barrier domain.

Sampled owner declarations:
* `entropyEpigraphCone` from `Definition_5_4_7_8`, the source-facing feasible-set owner;
* `entropyEpigraphRelativeEntropy` and
  `entropyEpigraphQ2_sublevelLogBarrier_apply` from `Definition_5_4_7_9`, the entropy-specific
  map and outer logarithmic barrier factor;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the canonical composed-barrier owner;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for the compatibility
  hypothesis used in clause `(1)`;
* `Chap05RealProdL2` from `RealProdL2`, the chapter owner bridge realizing the raw coordinate
  product types with the Euclidean `L²` ambient structure required by the barrier owners.

Source/core/bridge triage:
* source-facing: `entropyEpigraphConeBarrier` and the four theorem clauses below;
* core/canonical: `coneCompositionBarrier`, `IsBetaCompatibleWith`, and
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: `Chap05RealProdL2`, `entropyEpigraphConeBarrier_apply`, and the
  slice-identification theorems.

Primitive data:
* the orthant barrier `powerConeBarrier`;
* the entropy-specific map `ξ`;
* the half-space barrier factor `sublevelLogBarrier (fun yz ↦ -yz.1 - yz.2) 0`.

Derived API:
* the source-facing barrier owner `entropyEpigraphConeBarrier`;
* the pointwise textbook evaluation formula;
* the compatibility, barrier, and slice theorems.

The owner-level refinement here is to reuse the chapter's canonical composed-barrier owner
directly, instead of storing a parallel explicit raw formula as primitive data. -/

/-- The logarithmic barrier `ψ_E` for the entropy-epigraph cone, presented as the source-facing
specialization of the chapter's canonical cone-composition barrier owner. -/
def entropyEpigraphConeBarrier : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0)
    ξ
    1

-- Proof sketch: evaluate the source-facing owner through the canonical `coneCompositionBarrier`
-- specialization and the upstream pointwise formulas for its three factors.
/-- Evaluating `entropyEpigraphConeBarrier` at `((x₁, x₂), z)` gives the textbook formula
`-\log (z - x^(1) \log (x^(1) / x^(2))) - \log x^(1) - \log x^(2)`. -/
theorem entropyEpigraphConeBarrier_apply (x₁ x₂ z : ℝ) :
    entropyEpigraphConeBarrier ((x₁, x₂), z) =
      -Real.log (z - x₁ * Real.log (x₁ / x₂)) - Real.log x₁ - Real.log x₂ := by
  rw [entropyEpigraphConeBarrier, coneCompositionBarrier_apply,
    entropyEpigraphQ2_sublevelLogBarrier_apply, powerConeBarrier_apply,
    entropyEpigraphRelativeEntropy_apply]
  norm_num
  have harg : -(x₁ * Real.log (x₁ / x₂)) + z = z - x₁ * Real.log (x₁ / x₂) := by ring
  rw [harg]
  ring

-- Proof sketch: compute the second and third directional derivatives of
-- `entropyEpigraphRelativeEntropy`, identify `hessianLocalNorm powerConeBarrier x h` with
-- the Euclidean norm of the scaled direction, and use Cauchy--Schwarz to obtain the coefficient
-- bound required in `IsBetaCompatibleWith` for `β = 1`.
/-- Theorem 5.4.7.6 (1): the relative-entropy map
`ξ(x) = -x^(1) \log (x^(1) / x^(2))` is `1`-compatible with the orthant barrier
`F(x) = -\log x^(1) - \log x^(2)` relative to the scalar cone `ℝ_+`. -/
theorem entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier :
    IsBetaCompatibleWith powerConeQ1 (ConvexCone.positive ℝ ℝ)
      powerConeBarrier (1 : NNReal) ξ := sorry

-- Proof sketch: apply the general cone-composition barrier theorem to
-- `Q₁ = powerConeQ1`, `K = ConvexCone.positive ℝ ℝ`, the entropy-specific map `ξ`,
-- the half-space `Q₂`, `Φ = sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0`, and
-- `F = powerConeBarrier`. Clause `(1)` supplies the compatibility hypothesis, the barrier
-- parameters are `2` and `1`, and the composed barrier simplifies to `entropyEpigraphConeBarrier`.
/-- Theorem 5.4.7.6 (2): the function
`ψ_E((x^(1), x^(2)), z) = -\log (z - x^(1) \log (x^(1) / x^(2))) - \log x^(1) - \log x^(2)` is
a `3`-self-concordant barrier for the entropy-epigraph cone `\mathcal Q`. -/
theorem entropyEpigraphConeBarrier_is_three_self_concordant_barrier :
    IsSelfConcordantBarrierOnWith (interior entropyEpigraphCone) (3 : NNReal)
      entropyEpigraphConeBarrier := sorry

-- Proof sketch: unfold `entropyEpigraphCone` at the point `((1, x₂), z)`, rewrite the defining
-- inequality using `1 * (Real.log 1 - Real.log x₂) = -Real.log x₂`, and keep the positivity of
-- `x₂` explicit because Lean's totalized `Real.log` hides the textbook domain restriction.
/-- Theorem 5.4.7.6 (3): on the affine slice `x^(1) = 1`, the entropy-epigraph cone is exactly
the chapter constrained epigraph of `x^(2) ↦ -\log x^(2)` on `(0, ∞)`, with the positivity
condition on `x^(2)` made explicit. -/
theorem entropyEpigraphCone_unitSlice_eq_logEpigraph :
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
      constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ)) := sorry

-- Proof sketch: start from the description in clause `(3)` and exponentiate the inequality
-- `z ≥ -log x₂`; since `Real.exp (-z)` is always positive, this is equivalent to
-- `x₂ ≥ Real.exp (-z)`.
/-- Theorem 5.4.7.6 (4): on the affine slice `x^(1) = 1`, the entropy-epigraph cone is
equivalently described by the inequality `x^(2) ≥ e^{-z}`. -/
theorem entropyEpigraphCone_unitSlice_eq_expEpigraph :
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
      {yz : ℝ × ℝ | yz.1 ≥ Real.exp (-yz.2)} := sorry

/-! ### Theorem_5_4_7_7 (from Chap05) -/
noncomputable section

open Filter Set Topology
open scoped BigOperators

universe v

variable {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "LPoint" => E × E × ℝ × ℝ

/- Theorem 5.4.7.7 lies in the finite-family lifted log-sum-exp / barrier-function domain.

Sampled owner declarations:
* `liftedConeLogSumExp` from `Definition_5_4_7_12`, the source-facing lifted cone owner `hat Q`;
* `exponentialConeBarrier` from `Definition_5_4_7_10`, the scalar logarithmic barrier summed
  coordinatewise in the lifted construction;
* `AffineSubspace`, the canonical ambient owner for the normalization hyperplane;
* `IsBarrierFunctionOn` from `Chap01/Definition_1_10_18`, the project's canonical barrier owner
  on the intrinsic interior of a closed feasible set.

Source/core/bridge triage:
* source-facing: the hyperplane restriction of the lifted finite-family barrier `Ψ_L`;
* core/canonical: the normalization affine subspace together with `IsBarrierFunctionOn` on the
  closed normalized feasible region in that relative ambient space;
* bridge/view: the carrier inclusion of the normalization hyperplane and the resulting restricted
  barrier maps.

Primitive data:
* the finite-family lifted cone `liftedConeLogSumExp`;
* the scalar barrier owner `exponentialConeBarrier`;
* the normalization equation `∑ i, y i = τ`.

Derived API:
* `liftedConeLogSumExpBarrier`;
* `liftedConeLogSumExpNormalizationHyperplane`;
* `liftedConeLogSumExpRelativeDomain`;
* `liftedConeLogSumExpHyperplaneBarrier`;
* `liftedConeLogSumExpRelativeBarrierMap`.

The owner layer stays at an arbitrary finite index type `ι`, matching
`Definition_5_4_7_11` and `Definition_5_4_7_12`; the textbook `Fin n` presentation is only a
specialization bridge. -/

/-- The ambient logarithmic barrier `Ψ_L(x, y, t, τ)` is the finite sum of the canonical scalar
exponential-cone barriers on the coordinate triples `((x^(i) - t, y^(i)), τ)`. -/
def liftedConeLogSumExpBarrier : LPoint → ℝ :=
  fun p ↦ ∑ i : ι, exponentialConeBarrier ((p.1 i - p.2.2.1, p.2.1 i), p.2.2.2)

-- Proof sketch: unfold `liftedConeLogSumExpBarrier`; evaluating at `(x, y, t, τ)` is a direct
-- substitution into the coordinatewise scalar barrier sum.
/-- Evaluating `liftedConeLogSumExpBarrier` at `(x, y, t, τ)` gives the finite sum of the scalar
exponential-cone barriers on the coordinates `((x^(i) - t, y^(i)), τ)`. -/
@[simp]
theorem liftedConeLogSumExpBarrier_apply
    (x y : E) (t τ : ℝ) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      ∑ i : ι, exponentialConeBarrier ((x i - t, y i), τ) :=
  rfl

-- Proof sketch: rewrite each summand with `exponentialConeBarrier_apply`, use positivity to
-- expand `log (y^(i) / τ) = log y^(i) - log τ`, and then rearrange the logarithmic slack term.
/-- On the positive branch `τ > 0` and `y^(i) > 0`, the lifted barrier expands to the textbook
formula for `Ψ_L(x, y, t, τ)`. -/
theorem liftedConeLogSumExpBarrier_apply_formula
    (x y : E) (t τ : ℝ) (hτ : 0 < τ) (hy : ∀ i : ι, 0 < y i) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      -∑ i : ι,
        (Real.log (t + τ * Real.log (y i) - x i - τ * Real.log τ) +
          Real.log (y i) + Real.log τ) := by
  rw [liftedConeLogSumExpBarrier, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [exponentialConeBarrier_apply]
  have harg :
      τ * Real.log (y i / τ) - (x i - t) =
        t + τ * Real.log (y i) - x i - τ * Real.log τ := by
    rw [Real.log_div (hy i).ne' hτ.ne']
    ring
  rw [harg]
  ring

/-- The linear normalization functional whose kernel cuts out the hyperplane `∑ i, y i = τ`. -/
private def liftedConeLogSumExpNormalizationLinearMap : LPoint →ₗ[ℝ] ℝ where
  toFun := fun p ↦ ∑ i : ι, p.2.1 i - p.2.2.2
  map_add' p q := by
    simp [Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c p := by
    simp only [Prod.smul_snd, Prod.smul_fst, PiLp.smul_apply, smul_eq_mul, Real.ringHom_apply,
      sub_eq_add_neg]
    rw [← Finset.mul_sum]
    ring_nf

/-- The normalization hyperplane `∑ i, y i = τ` on which the relative geometry of `hat Q` is
considered. -/
def liftedConeLogSumExpNormalizationHyperplane : AffineSubspace ℝ LPoint :=
  liftedConeLogSumExpNormalizationLinearMap.ker.toAffineSubspace

local notation "H" => (liftedConeLogSumExpNormalizationHyperplane : AffineSubspace ℝ LPoint)

-- Proof sketch: unfold `liftedConeLogSumExpNormalizationHyperplane`; the defining equation is
-- exactly the displayed normalization identity.
/-- A quadruple `(x, y, t, τ)` belongs to the normalization hyperplane exactly when
`∑ i, y i = τ`. -/
theorem mem_liftedConeLogSumExpNormalizationHyperplane_iff
    {x y : E} {t τ : ℝ} :
    (x, y, t, τ) ∈ liftedConeLogSumExpNormalizationHyperplane ↔ ∑ i, y i = τ := by
  simp [liftedConeLogSumExpNormalizationHyperplane,
    liftedConeLogSumExpNormalizationLinearMap, sub_eq_zero]

/-- The open relative-domain model of `hat Q`, viewed on the carrier of the normalization affine
hyperplane, is the pullback of the ambient lifted cone along the hyperplane inclusion. -/
abbrev liftedConeLogSumExpRelativeDomain : Set H :=
  Subtype.val ⁻¹' liftedConeLogSumExp

local notation "D" => (liftedConeLogSumExpRelativeDomain : Set H)

/-- A point of the normalization affine subspace belongs to `liftedConeLogSumExpRelativeDomain`
exactly when its underlying quadruple belongs to the lifted cone `liftedConeLogSumExp`. -/
theorem mem_liftedConeLogSumExpRelativeDomain_iff
    (p : H) :
    p ∈ liftedConeLogSumExpRelativeDomain ↔ p.1 ∈ liftedConeLogSumExp :=
  Iff.rfl

/-- The restriction of `Ψ_L` to the normalization hyperplane `∑ i, y i = τ`. -/
abbrev liftedConeLogSumExpHyperplaneBarrier : H → ℝ :=
  liftedConeLogSumExpBarrier ∘ Subtype.val

-- Proof sketch: unfold `liftedConeLogSumExpHyperplaneBarrier`; it is defined by evaluating the
-- ambient barrier `liftedConeLogSumExpBarrier` on the underlying quadruple.
/-- Evaluating the restricted barrier on the normalization hyperplane agrees with the ambient
formula `liftedConeLogSumExpBarrier`. -/
theorem liftedConeLogSumExpHyperplaneBarrier_apply
    (p : H) :
    liftedConeLogSumExpHyperplaneBarrier p = liftedConeLogSumExpBarrier p.1 :=
  rfl

/-- The canonical bundled barrier map on the intrinsic interior of the closed normalized lifted
region `closure liftedConeLogSumExpRelativeDomain`, obtained by restricting the hyperplane bridge
once more to the intrinsic interior. -/
abbrev liftedConeLogSumExpRelativeBarrierMap :
    C(interior (closure D), ℝ) where
  toFun := (interior (closure D)).restrict
    liftedConeLogSumExpHyperplaneBarrier
  continuous_toFun := sorry

/-- Evaluating the canonical bundled barrier map agrees with the ambient hyperplane restriction. -/
theorem liftedConeLogSumExpRelativeBarrierMap_apply
    (p : interior (closure D)) :
    liftedConeLogSumExpRelativeBarrierMap p = liftedConeLogSumExpHyperplaneBarrier p.1 :=
  rfl

-- Proof sketch: work in the subtype ambient space cut out by `∑ i, y i = τ`, and take the closed
-- feasible set `closure liftedConeLogSumExpRelativeDomain` so Chapter 1's barrier owner applies
-- in the correct ambient space. Its interior is the relative interior of `hat Q`. The coordinate
-- functions `y i`, `τ`, and
-- `t + τ * log (y i) - x i - τ * log τ = (t - x i) + τ * log (y i / τ)` are positive on the
-- relative interior, making the logarithmic sum continuous there. If a sequence in the relative
-- interior approaches the frontier of the closed normalized region, then either some `y i`, `τ`,
-- or one of the logarithmic slack terms tends to `0`, forcing the corresponding term of `Ψ_L` to
-- diverge to `+∞`.
/-- Theorem 5.4.7.7: restricting `Ψ_L(x, y, t, τ)` to the hyperplane `∑ i, y^(i) = τ` yields a
barrier function on the closed normalized lifted log-sum-exp region
`closure liftedConeLogSumExpRelativeDomain`, viewed in its intrinsic relative ambient space. -/
theorem liftedConeLogSumExpBarrier_restriction_isBarrierFunctionOn :
    IsBarrierFunctionOn
      (closure D)
      liftedConeLogSumExpRelativeBarrierMap := sorry

/-! ### Theorem_5_4_7_8 (from Chap05) -/
open scoped Gradient HessianLocalNorm RelativeDirection
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n
noncomputable local instance : Fintype (Fin n) := Fintype.ofFinite (Fin n)

/- Theorem 5.4.7.8 lies in the Chapter 5 positive-orthant barrier / Hessian-local-norm domain.

Sampled owner declarations:
* `standardLogarithmicBarrierAmbient` in `Definition_5_4_3_2`, the ambient bridge for the
  positive-orthant logarithmic barrier;
* `relativeDirection` in `Definition_5_4_7_14`, the source-facing scaled direction `δ_x(h)`;
* `hessianLocalNorm` and the notation `‖h‖[f; x]` in `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `hessianLocalNorm_def` in `Definition_5_1_1`, the bridge expanding that owner to the raw square
  root of the Hessian quadratic form.

Source/core/bridge triage:
* source-facing: the local norm of the orthant logarithmic barrier at `x` applied to `h`;
* core/canonical: `‖h‖[standardLogarithmicBarrierAmbient n; x]`;
* bridge/view: `hessianLocalNorm_def` together with the coordinate formula for
  `relativeDirection x h`.

The previous version kept the bridge formula
`Real.sqrt (inner ℝ h ((fderiv ℝ (∇ F) x) h))` as the main theorem surface. This refinement keeps
the same mathematics, but moves the statement to the chapter owner `hessianLocalNorm`; the raw
Hessian square root is already canonical derived API via `hessianLocalNorm_def`. -/

private theorem standardLogarithmicBarrierAmbient_hasGradientAt_of_nonzero
    (x : Eₙ) (hx : ∀ i : Fin n, x i ≠ 0) :
    HasGradientAt
      (standardLogarithmicBarrierAmbient n)
      (WithLp.toLp 2 fun i ↦ -(x i)⁻¹)
      x := by
  unfold standardLogarithmicBarrierAmbient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsum :
      HasFDerivAt
        (fun y : Eₙ ↦ ∑ i : Fin n, Real.log (y i))
        (∑ i : Fin n,
          ((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
        x := by
    have hterms :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          HasFDerivAt
            (fun y : Eₙ ↦ Real.log (y i))
            (((x i)⁻¹ : ℝ) •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
            x := by
      intro i hi
      simpa using ((PiLp.hasFDerivAt_apply (2 : ENNReal) x i).log (hx i))
    convert HasFDerivAt.sum hterms using 1
    funext y
    simp
  have hdual :
      (InnerProductSpace.toDual ℝ Eₙ) (WithLp.toLp 2 fun i ↦ -(x i)⁻¹) =
        -(∑ i : Fin n,
          ((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)) := by
    ext h
    change inner ℝ (WithLp.toLp 2 fun i ↦ -(x i)⁻¹) h = _
    rw [PiLp.inner_apply]
    change (∑ i : Fin n, h i * (-(x i)⁻¹)) = _
    simp [ContinuousLinearMap.neg_apply, Finset.sum_apply, mul_comm]
  have hneg :
      HasFDerivAt
        (fun y : Eₙ ↦ -∑ i : Fin n, Real.log (y i))
        (-(∑ i : Fin n,
          ((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)))
        x := by
    convert hsum.neg using 1
  exact hdual.symm ▸ hneg

private theorem standardLogarithmicBarrierAmbient_hasFDerivAt_gradient
    (x : Xₙ) :
    HasFDerivAt
      (∇ (standardLogarithmicBarrierAmbient n))
      ((
        PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)
      ).symm.toContinuousLinearMap.comp
        (show Eₙ →L[ℝ] (Fin n → ℝ) from
          ContinuousLinearMap.pi fun i : Fin n ↦
            ((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)))
      (x : Eₙ) := by
  let G : Eₙ → Eₙ := fun y ↦ WithLp.toLp 2 fun i ↦ -(y i)⁻¹
  let H : Eₙ → Fin n → ℝ := fun y i ↦ -(y i)⁻¹
  let H' : Eₙ →L[ℝ] Fin n → ℝ :=
    show Eₙ →L[ℝ] (Fin n → ℝ) from
      ContinuousLinearMap.pi fun i : Fin n ↦
        ((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)
  have hEq : ∇ (standardLogarithmicBarrierAmbient n) =ᶠ[nhds (x : Eₙ)] G := by
    have hpos : {y : Eₙ | ∀ i : Fin n, 0 < y i} ∈ nhds (x : Eₙ) := by
      have hopen : IsOpen {y : Eₙ | ∀ i : Fin n, 0 < y i} := by
        simpa [Set.setOf_forall] using
          (isOpen_iInter_of_finite fun i ↦
            isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i))
      exact hopen.mem_nhds x.2
    filter_upwards [hpos] with y hy
    exact
      (standardLogarithmicBarrierAmbient_hasGradientAt_of_nonzero
        y
        fun i ↦ ne_of_gt (hy i)).gradient
  have hH : HasFDerivAt H H' (x : Eₙ) := by
    rw [hasFDerivAt_pi]
    intro i
    have hproj :
        HasFDerivAt
          (fun y : Eₙ ↦ y i)
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)
          (x : Eₙ) := by
      simpa using PiLp.hasFDerivAt_apply (2 : ENNReal) (x : Eₙ) i
    have hinv :
        HasFDerivAt
          (fun y : Eₙ ↦ (y i)⁻¹)
          (-((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
          (x : Eₙ) := by
      let L : Eₙ →L[ℝ] ℝ :=
        -((((x : Eₙ) i) ^ (2 : ℕ))⁻¹ : ℝ) •
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ)
      have hcomp :
          HasFDerivAt
            (fun y : Eₙ ↦ (y i)⁻¹)
            (-(((ContinuousLinearMap.mulLeftRight ℝ ℝ) ((x : Eₙ) i)⁻¹) ((x : Eₙ) i)⁻¹).comp
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ))
            (x : Eₙ) := by
        simpa using (hasFDerivAt_inv' (by exact ne_of_gt (x.2 i))).comp (x : Eₙ) hproj
      have hL :
          -(((ContinuousLinearMap.mulLeftRight ℝ ℝ) ((x : Eₙ) i)⁻¹) ((x : Eₙ) i)⁻¹).comp
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : Eₙ →L[ℝ] ℝ) = L := by
        ext y
        simp [L, ContinuousLinearMap.mulLeftRight_apply, pow_two, mul_comm, mul_left_comm]
      exact hcomp.congr_fderiv hL
    simpa [H, H'] using hinv.neg
  have hToLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin n → ℝ) → Eₙ)
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
        (H (x : Eₙ)) := by
    simpa using PiLp.hasFDerivAt_toLp (2 : ENNReal) (H (x : Eₙ))
  have hG :
      HasFDerivAt
        G
        ((
          PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)
        ).symm.toContinuousLinearMap.comp H')
        (x : Eₙ) := by
    simpa [G, H] using hToLp.comp (x : Eₙ) hH
  simpa [H'] using hG.congr_of_eventuallyEq hEq

private theorem standardLogarithmicBarrierAmbient_hessian_apply
    (x : Xₙ) (h : Eₙ) :
    hessian (standardLogarithmicBarrierAmbient n) (x : Eₙ) h =
      WithLp.toLp 2 fun i ↦ h i / ((x : Eₙ) i) ^ (2 : ℕ) := by
  have hderiv := standardLogarithmicBarrierAmbient_hasFDerivAt_gradient x
  change fderiv ℝ (∇ (standardLogarithmicBarrierAmbient n)) (x : Eₙ) h = _
  rw [hderiv.fderiv]
  ext i
  simp [div_eq_mul_inv, mul_comm]

private theorem standardLogarithmicBarrierAmbient_hessian_quadratic
    (x : Xₙ) (h : Eₙ) :
    inner ℝ h
        (hessian (standardLogarithmicBarrierAmbient n) (x : Eₙ) h) =
      ‖δ[x](h)‖ ^ (2 : ℕ) := by
  rw [standardLogarithmicBarrierAmbient_hessian_apply]
  calc
    inner ℝ h (WithLp.toLp 2 fun i ↦ h i / ((x : Eₙ) i) ^ (2 : ℕ))
      = ∑ i : Fin n, h i * (h i / ((x : Eₙ) i) ^ (2 : ℕ)) := by
          rw [PiLp.inner_apply]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          change inner ℝ (h i) (h i / ((x : Eₙ) i) ^ (2 : ℕ)) = _
          change (h i / ((x : Eₙ) i) ^ (2 : ℕ)) * h i = _
          ring
    _ = ∑ i : Fin n, (h i / (x : Eₙ) i) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          field_simp [pow_two, ne_of_gt (x.2 i)]
    _ = ‖δ[x](h)‖ ^ (2 : ℕ) := by
          exact (EuclideanSpace.real_norm_sq_eq (δ[x](h))).symm

-- Proof sketch: compute the Hessian local norm of `standardLogarithmicBarrierAmbient n` at the
-- positive point `x` from the diagonal Hessian with entries `(x i)⁻²`; the resulting quadratic
-- form is `∑ i, (h i / x i)^2`, which is exactly `‖δ[x](h)‖^2`.
/-- Theorem 5.4.7.8: for the positive-orthant logarithmic barrier, the local norm induced by the
Hessian at a strictly positive point `x` agrees with the Euclidean norm of the scaled direction
`δ_x(h)`, written in Lean as `δ[x](h)`. -/
theorem positiveOrthantLogarithmicBarrier_localNorm_eq_norm_relativeDirection
    (x : Xₙ) (h : Eₙ) :
    ‖h‖[standardLogarithmicBarrierAmbient n; x] = ‖δ[x](h)‖ := by
  rw [hessianLocalNorm_def]
  rw [standardLogarithmicBarrierAmbient_hessian_quadratic]
  exact (Real.sqrt_sq_eq_abs ‖δ[x](h)‖).trans (abs_of_nonneg (norm_nonneg _))

end

/-! ### Theorem_5_4_7_9 (from Chap05) -/
open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.9 lies in the Chapter 5 simplex-monomial / positive-orthant directional-
derivative domain.

Sampled owner declarations:
* `lineDerivWithin` from mathlib, the canonical owner for within-domain directional derivatives
  along affine lines;
* `ambientMonomialXi` from `Definition_5_4_7_17`, the ambient owner whose restriction to
  `positiveOrthant n` is the source-facing monomial `ξ_[a]`;
* `relativeDirection` together with the notation `δ[x](h)` from `Definition_5_4_7_14`, the
  source-facing scaled direction;
* `Finset.centerMass` and `centerMass_relativeDirection_eq_sum` from `Definition_5_4_7_18`, the
  canonical weighted-mean owner and its simplex-specialized bridge for `δ_x(h)`.

Source/core/bridge triage:
* source-facing: the logarithmic derivative identity `D log ξ_a(x)[h] = ⟪a, δ_x(h)⟫`;
* core/canonical: `lineDerivWithin ℝ`;
* bridge/view: the ambient representative `Real.log ∘ ambientMonomialXi a` of `log ξ_a` on the
  strict positive orthant, and the center-of-mass expression for the simplex-weighted mean.

The public theorem is therefore a bridge statement over the canonical owner `lineDerivWithin`;
it should not introduce a parallel owner for the logarithmic derivative or a duplicate wrapper
for the weighted mean. -/

-- Proof sketch: on the positive orthant, rewrite `log ξ_a(y)` as the logarithm of the product
-- defining `ξ_a`; then differentiate along the affine line `x + t • h` inside the orthant and
-- identify `δ[x](h)` with the vector whose `i`-th coordinate is `h i / x i`, so the resulting
-- weighted sum is the canonical simplex center of mass `Finset.univ.centerMass a (δ[x](h))`.
/-- Theorem 5.4.7.9: for `a ∈ Δₙ`, the directional derivative of `log ξ_a` at a strictly positive
point `x` along the ambient direction `h`, taken within the positive orthant, is the
simplex-weighted mean `Finset.univ.centerMass a (δ_x(h)) = ⟪a, δ_x(h)⟫`. -/
theorem lineDerivWithin_log_monomialXi_eq_centerMass_relativeDirection
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    lineDerivWithin ℝ (Real.log ∘ ambientMonomialXi a) Xₙ x h =
      Finset.univ.centerMass a (δ[x](h)) := by
  sorry

end

/-! ### Definition_5_4_8_1 (from Chap05) -/
noncomputable section

universe u

open scoped BigOperators

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/-
Definition 5.4.8.1 lies in the separable convex optimization domain.

Sampled owner-style declarations:
- `LagrangianProblem` and `LagrangianProblem.feasibleSet` in `Chap01/Definition_1_10_2`, the
  project owner for primitive objective-and-constraint data and the derived inequality feasible
  set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for the
  ambient feasible-set / objective interface used by optimal-value statements;
- mathlib `ConvexOn.comp_affineMap`, the canonical affine-precomposition theorem for convex
  functions;
- mathlib `ConvexOn.smul` and `ConvexOn.add`, the canonical positive-scaling and sum operations
  used to build the block functions `qᵢ`.

Best owner abstraction:
- source-facing: `SeparableOptimizationProblem E m`, the textbook block data over an ambient real
  vector space `E`;
- core/canonical: `LagrangianProblem E m`, together with the inherited
  `SetConstrainedMinimizationProblem E` bridge;
- bridge/view: the Euclidean specialization
  `toConvexInequalityConstrainedMinimizationProblem`.

Primitive data:
- the block sizes;
- the positive weights;
- the affine functionals `E →ᵃ[ℝ] ℝ`;
- the scalar convex functions;
- the right-hand sides `β₁, …, βₘ`.

Derived API:
- the block functions `qFunction`;
- the textbook constraint family `constraintFunction`;
- the convexity lemmas for these derived functions;
- the canonical Chapter 1 bridge `toLagrangianProblem`, together with the inherited owner bridge
  `(problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem`;
- the Euclidean Chapter 5 specialization
  `toConvexInequalityConstrainedMinimizationProblem`.

The refinement therefore keeps the source-facing separable data, but replaces the coordinate
`ℝⁿ` presentation `(aᵢⱼ, bᵢⱼ)` by the intrinsic affine owner `E →ᵃ[ℝ] ℝ` and makes the generic
Chapter 1 problem owners primary. The Chapter 5 whole-space owner remains only as a Euclidean
specialization.
-/

/-- Definition 5.4.8.1: a separable optimization problem on a real vector space `E` is specified
by finite families of positive weights `αᵢⱼ`, affine functionals `ℓᵢⱼ : E →ᵃ[ℝ] ℝ`, convex
scalar functions `fᵢⱼ : ℝ → ℝ`, and right-hand sides `β₁, …, βₘ`, producing the functions
`qᵢ(x) = ∑ⱼ αᵢⱼ fᵢⱼ (ℓᵢⱼ(x))` and the problem of minimizing `q₀(x)` subject to
`qᵢ(x) ≤ βᵢ` for `i = 1, …, m`. -/
structure SeparableOptimizationProblem (E : Type u) [AddCommGroup E] [Module ℝ E] (m : ℕ) where
  /-- The number `mᵢ` of separable summands in `qᵢ`. -/
  blockSize : Fin (m + 1) → ℕ
  /-- The positive coefficients `αᵢⱼ` multiplying the scalar convex terms. -/
  weight (i : Fin (m + 1)) (j : Fin (blockSize i)) : ℝ
  /-- Each coefficient `αᵢⱼ` is positive. -/
  weight_pos (i : Fin (m + 1)) (j : Fin (blockSize i)) : 0 < weight i j
  /-- The affine functionals `ℓᵢⱼ : E →ᵃ[ℝ] ℝ`. -/
  affineMap (i : Fin (m + 1)) (j : Fin (blockSize i)) : E →ᵃ[ℝ] ℝ
  /-- The scalar convex functions `fᵢⱼ : ℝ → ℝ`. -/
  scalarFunction (i : Fin (m + 1)) (j : Fin (blockSize i)) : ℝ → ℝ
  /-- Each scalar function `fᵢⱼ` is convex on all of `ℝ`. -/
  scalarFunction_convex (i : Fin (m + 1)) (j : Fin (blockSize i)) :
      ConvexOn ℝ Set.univ (scalarFunction i j)
  /-- The right-hand sides `β₁, …, βₘ` of the inequality constraints. -/
  constraintBound : Fin m → ℝ

namespace SeparableOptimizationProblem

/-- The separable convex function `qᵢ(x) = ∑ⱼ αᵢⱼ fᵢⱼ (ℓᵢⱼ(x))`. -/
def qFunction (problem : SeparableOptimizationProblem E m) (i : Fin (m + 1)) : E → ℝ :=
  fun x ↦
    ∑ j : Fin (problem.blockSize i),
      problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x)

/-- The `i`-th inequality constraint function `q_{i+1}`. -/
abbrev constraintFunction (problem : SeparableOptimizationProblem E m) (i : Fin m) : E → ℝ :=
  problem.qFunction i.succ

/-- Expanding `qFunction` recovers the defining finite sum of weighted scalar convex terms. -/
theorem qFunction_apply
    (problem : SeparableOptimizationProblem E m) (i : Fin (m + 1)) (x : E) :
    problem.qFunction i x =
      ∑ j : Fin (problem.blockSize i),
        problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x) :=
  rfl

/-- Each block function `qᵢ` is convex on the whole ambient space. -/
theorem qFunction_convex
    (problem : SeparableOptimizationProblem E m) (i : Fin (m + 1)) :
    ConvexOn ℝ Set.univ (problem.qFunction i) := by
  classical
  let term : Fin (problem.blockSize i) → E → ℝ := fun j x ↦
    problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x)
  have hterm : ∀ j : Fin (problem.blockSize i), ConvexOn ℝ Set.univ (term j) := by
    intro j
    have hcomp : ConvexOn ℝ Set.univ
        (fun x ↦ problem.scalarFunction i j (problem.affineMap i j x)) := by
      simpa using (problem.scalarFunction_convex i j).comp_affineMap (problem.affineMap i j)
    simpa [term] using ConvexOn.smul (le_of_lt (problem.weight_pos i j)) hcomp
  have hsum :
      ∀ s : Finset (Fin (problem.blockSize i)),
        ConvexOn ℝ Set.univ (fun x ↦ s.sum (fun j ↦ term j x)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
    · intro j s hj hs
      simpa [Finset.sum_insert hj] using (hterm j).add hs
  simpa [qFunction, term] using hsum Finset.univ

/-- Each textbook constraint function `q_{i+1}` is convex on the whole ambient space. -/
theorem constraintFunction_convex
    (problem : SeparableOptimizationProblem E m) (i : Fin m) :
    ConvexOn ℝ Set.univ (problem.constraintFunction i) := by
  simpa [constraintFunction] using problem.qFunction_convex i.succ

/-- The canonical Chapter 1 Lagrangian problem attached to a separable optimization problem. -/
def toLagrangianProblem (problem : SeparableOptimizationProblem E m) : LagrangianProblem E m where
  objective := problem.qFunction 0
  constraints := fun i x ↦ problem.constraintFunction i x - problem.constraintBound i

/-- A separable optimization problem coerces to its canonical Chapter 1 Lagrangian owner. -/
instance : Coe (SeparableOptimizationProblem E m) (LagrangianProblem E m) where
  coe := toLagrangianProblem

/-- A separable optimization problem can be used as its objective function `q₀ : E → ℝ`. -/
instance : CoeFun (SeparableOptimizationProblem E m) (fun _ ↦ E → ℝ) where
  coe problem := problem.qFunction 0

/-- The Chapter 1 Lagrangian owner evaluates to the source-facing objective `q₀`. -/
@[simp] theorem toLagrangianProblem_apply
    (problem : SeparableOptimizationProblem E m) (x : E) :
    problem.toLagrangianProblem x = problem.qFunction 0 x :=
  rfl

/-- Evaluating a separable optimization problem returns the source-facing objective `q₀`. -/
@[simp] theorem coe_apply (problem : SeparableOptimizationProblem E m) (x : E) :
    problem x = problem.qFunction 0 x :=
  rfl

@[simp] theorem toLagrangianProblem_constraints_apply
    (problem : SeparableOptimizationProblem E m) (i : Fin m) (x : E) :
    (problem : LagrangianProblem E m).constraints i x =
      problem.constraintFunction i x - problem.constraintBound i :=
  rfl

/-- The feasible set consists of those `x ∈ E` satisfying `qᵢ(x) ≤ βᵢ` for every
constraint index `i = 1, …, m`. -/
def feasibleSet (problem : SeparableOptimizationProblem E m) : Set E :=
  problem.toLagrangianProblem.feasibleSet

/-- Membership in the feasible set is equivalent to satisfying all separable inequality
constraints. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : SeparableOptimizationProblem E m) (x : E) :
    x ∈ problem.feasibleSet ↔
      ∀ i : Fin m, problem.qFunction i.succ x ≤ problem.constraintBound i := by
  rw [feasibleSet]
  constructor
  · intro hx i
    exact sub_nonpos.mp ((problem.toLagrangianProblem.mem_feasibleSet_iff).1 hx i)
  · intro hx
    exact (problem.toLagrangianProblem.mem_feasibleSet_iff).2
      (fun i ↦ sub_nonpos.mpr (hx i))

section Euclidean

variable {n : ℕ}

/-- The Euclidean Chapter 5 whole-space convex inequality owner attached to a separable
optimization problem. This is a specialization of the generic Chapter 1 bridge. -/
def toConvexInequalityConstrainedMinimizationProblem
    (problem : SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m) :
    ConvexInequalityConstrainedMinimizationProblem n m where
  objective := problem.qFunction 0
  constraints := fun i x ↦ problem.constraintFunction i x - problem.constraintBound i
  objective_convex := problem.qFunction_convex 0
  constraints_convex i := by
    simpa [sub_eq_add_neg] using
      (problem.constraintFunction_convex i).add_const (-problem.constraintBound i)

/-- A Euclidean separable optimization problem coerces to its Chapter 5 whole-space owner. -/
instance : Coe (SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m)
    (ConvexInequalityConstrainedMinimizationProblem n m) where
  coe := toConvexInequalityConstrainedMinimizationProblem

/-- The Chapter 5 owner evaluates to the source-facing objective `q₀`. -/
@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_apply
    (problem : SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m)
    (x : EuclideanSpace ℝ (Fin n)) :
    problem.toConvexInequalityConstrainedMinimizationProblem x = problem.qFunction 0 x :=
  rfl

@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_constraints_apply
    (problem : SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m)
    (i : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
    (problem : ConvexInequalityConstrainedMinimizationProblem n m).constraints i x =
      problem.constraintFunction i x - problem.constraintBound i :=
  rfl

end Euclidean

end SeparableOptimizationProblem

end

/-! ### Definition_5_4_8_10 (from Chap05) -/
noncomputable section

/- Definition 5.4.8.10 lies in the Chapter 5 entropy-epigraph / barrier-slice domain.

Sampled owner declarations:
* `entropyEpigraphConeBarrier` and `entropyEpigraphConeBarrier_apply` from `Theorem_5_4_7_6`, the
  upstream Chapter 5 owner/view for the entropy-epigraph cone barrier;
* `separableLogBarrierF6` from `Definition_5_4_8_16`, the nearby chapter pattern of realizing a
  planar source-facing barrier directly as an affine slice of an earlier owner;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the lower-level chapter owner used internally by
  `entropyEpigraphConeBarrier`.

Best owner abstraction:
* source-facing: the textbook barrier `F₃`;
* core/canonical: `entropyEpigraphConeBarrier`;
* bridge/view: the affine slice `(x, t) ↦ ((x, 1), t)` and the evaluation theorem below.

Primitive data:
* the upstream entropy-epigraph cone barrier owner;
* the affine slice fixing the second cone coordinate to `1`.

Derived API:
* the source-facing barrier `separableLogBarrierF3`;
* its coordinate formula `separableLogBarrierF3_apply`.

The previous version rebuilt `F₃` as a separate sum of logarithmic barrier factors. The chapter
already owns the same barrier geometry through `entropyEpigraphConeBarrier`, so this refinement
keeps only the source-facing planar specialization and its textbook evaluation formula. -/

/-- Definition 5.4.8.10: the function `F₃` on `ℝ²` given by
`F₃(x, t) = - log x - log (t - x log x)`. -/
def separableLogBarrierF3 : ℝ × ℝ → ℝ :=
  fun p ↦ entropyEpigraphConeBarrier ((p.1, 1), p.2)

-- Proof sketch: `separableLogBarrierF3` is the affine slice `x₂ = 1` of
-- `entropyEpigraphConeBarrier`. Evaluate the owner and simplify `log (x / 1)` and `log 1`.
/-- Evaluating `separableLogBarrierF3` at `(x, t)` recovers the textbook formula
`F₃(x, t) = - log x - log (t - x log x)`. -/
theorem separableLogBarrierF3_apply (x t : ℝ) :
    separableLogBarrierF3 (x, t) = -Real.log x - Real.log (t - x * Real.log x) := by
  rw [separableLogBarrierF3, entropyEpigraphConeBarrier_apply, Real.log_one]
  ring_nf

/-! ### Definition_5_4_8_11 (from Chap05) -/
/- Definition 5.4.8.11 lies in the chapter's real epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a feasible set;
- `mem_constrainedEpigraph_negLog_iff` from `Definition_5_4_8_5`, the nearby chapter pattern for
  specializing this owner to a one-variable epigraph;
- `Q₃` and `mem_Q₃_iff` from `Definition_5_4_8_9`, another nearby source-facing
  epigraph-owner/membership pair;
- `mem_Q₆_iff` from `Definition_5_4_8_15`, the matching source-facing `Real.rpow`
  specialization pattern later in the same subsection.

Best owner abstraction:
- core/canonical:
  `constrainedEpigraph (Set.univ : Set ℝ) (fun x : ℝ ↦ ((|x| ^ p : ℝ) : WithTop ℝ))`.

Primitive data:
- the feasible set `Set.univ`;
- the function `x ↦ |x| ^ p`.

Derived API:
- the canonical epigraph expression itself;
- its specialized membership expansion.

Source/core/bridge triage:
- source-facing: the textbook set `Q₄`;
- core/canonical: the chapter epigraph owner `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.

This item therefore deletes the parallel local abbreviation `Q₄` and reuses the chapter epigraph
owner directly. -/

/- Definition 5.4.8.11 recalls the chapter epigraph owner specialized to `x ↦ |x| ^ p` on `ℝ`. -/
#check
  (fun p : ℝ ↦ constrainedEpigraph (Set.univ : Set ℝ)
    (fun x : ℝ ↦ ((|x| ^ p : ℝ) : WithTop ℝ)) : ℝ → Set (ℝ × ℝ))

-- Proof sketch: specialize `mem_constrainedEpigraph_iff` to `Q = Set.univ`; the feasible-set
-- condition is automatic, leaving exactly the inequality `|x| ^ p ≤ t`.
/-- Membership in the canonical epigraph expression for Definition 5.4.8.11, i.e. the textbook
set `Q₄`, means exactly that `t` lies above `|x| ^ p`. -/
@[simp] theorem mem_constrainedEpigraph_abs_pow_iff {p x t : ℝ} :
    (x, t) ∈ constrainedEpigraph (Set.univ : Set ℝ)
      (fun y : ℝ ↦ ((|y| ^ p : ℝ) : WithTop ℝ)) ↔
      t ≥ |x| ^ p := by
  rw [mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨_, hxt⟩
    exact_mod_cast hxt
  · intro hxt
    refine ⟨by simp, ?_⟩
    exact_mod_cast hxt

/-! ### Definition_5_4_8_12 (from Chap05) -/
noncomputable section

/- Definition 5.4.8.12 lies in the Chapter 5 logarithmic-sublevel-barrier domain.

Sampled owner declarations:
* `sublevelLogBarrier` and `sublevelLogBarrier_apply` from `Theorem_5_1_4`, the chapter owner for
  barriers of the form `x ↦ -log (β - f x)`;
* `power_cone_barrier` from `Theorem_5_4_7_3`, the higher-level Chapter 5 owner for the same
  power-gap geometry, later reused through the nonnegative slice `((t, 1), x)`;
* `separableLogBarrierF3` from `Definition_5_4_8_10`, the nearby source-facing barrier already
  refined to canonical Chapter 5 owners rather than a raw logarithmic body;
* `hypographBarrierPsi` from `Definition_5_4_7_20`, the generic chapter pattern for keeping a
  source-facing barrier name while reusing the canonical logarithmic-sublevel owner.

Best owner abstraction:
* source-facing: the textbook barrier `F₄`;
* core/canonical: the sum of two `sublevelLogBarrier` factors attached to the gap maps
  `(x, t) ↦ -t` and `(x, t) ↦ x^2 - t^(2 / p)`;
* bridge/view: the coordinate evaluation theorem below, and under the stronger slice condition
  `0 ≤ t`, the later power-cone comparison in `Theorem_5_4_8_5`.

Primitive data:
* the positivity gap map `(x, t) ↦ -t`;
* the epigraph gap map `(x, t) ↦ x^2 - t^(2 / p)`.

Derived API:
* the source-facing barrier `separableLogBarrierF4`;
* its coordinate formula `separableLogBarrierF4_apply`.

This refinement keeps the textbook owner `F₄`, but removes the duplicate raw logarithmic body in
favor of the chapter owner `sublevelLogBarrier`. The upstream power-cone owner is kept as a
bridge only: promoting it to the main definition here would force an extra `0 ≤ t` hypothesis in
the coordinate comparison, so it would shift the source-facing semantics. -/

/-- Definition 5.4.8.12: the function `F₄` on `ℝ²` given by
`F₄(x, t) = - log t - log (t^(2 / p) - x^2)`. -/
def separableLogBarrierF4 (p : ℝ) : ℝ × ℝ → ℝ :=
  sublevelLogBarrier (fun q : ℝ × ℝ ↦ -q.2) 0 +
    sublevelLogBarrier (fun q : ℝ × ℝ ↦ q.1 ^ (2 : ℕ) - Real.rpow q.2 (2 / p)) 0

-- Proof sketch: evaluate the two canonical `sublevelLogBarrier` factors at `(x, t)`. The first
-- becomes `-log t`, and the second becomes `-log (t^(2 / p) - x^2)`.
/-- Evaluating `separableLogBarrierF4 p` at `(x, t)` reproduces the textbook formula
`F₄(x, t) = - log t - log (t^(2 / p) - x^2)`. -/
theorem separableLogBarrierF4_apply (p x t : ℝ) :
    separableLogBarrierF4 p (x, t) =
      -Real.log t - Real.log (Real.rpow t (2 / p) - x ^ (2 : ℕ)) := by
  simp [separableLogBarrierF4, sublevelLogBarrier, sub_eq_add_neg, add_comm]

/-! ### Definition_5_4_8_13 (from Chap05) -/
noncomputable section

/- Definition 5.4.8.13 lies in the chapter's real hypograph / sublevel-set domain.

Sampled owner declarations:
- `constrainedSublevelSet` and `mem_constrainedSublevelSet_iff` from `Chap03/Definition_3_3`, the
  chapter owner for closed constraint sets cut out by a feasible region and a scalar inequality;
- `hypographBarrierDomain` from `Definition_5_4_7_20`, the nearby strict hypograph owner built
  from the same gap-map idea;
- `Q₃`, `mem_Q₃_iff`, and `mem_Q₆_iff` from `Definition_5_4_8_9` and
  `Definition_5_4_8_15`, the neighboring Chapter 5 pattern of exposing a source-facing owner when
  it is reused downstream.

Best owner abstraction:
- source-facing: the textbook set `Q₅`;
- core/canonical:
  `constrainedSublevelSet ((Set.univ : Set ℝ) ×ˢ Set.Ici (0 : ℝ))
    (fun xt : ℝ × ℝ ↦ ((xt.1 - Real.rpow xt.2 p : ℝ) : WithTop ℝ)) 0`;
- bridge/view: `mem_Q₅_iff`.

Primitive data:
- the feasible strip `ℝ × [0, ∞)`;
- the gap map `(x, t) ↦ x - t^p`.

Derived API:
- the source-facing owner `Q₅`;
- its coordinate membership theorem.

Source/core/bridge triage:
- source-facing: the textbook set `Q₅`;
- core/canonical: the constrained sublevel-set owner from Chapter 3;
- bridge/view: the specialized membership expansion below.

This item follows the same reused-owner pattern as `Q₃` and `Q₆`: the mathematical content is a
closed constrained sublevel set on `(x, t)`, and later theorems refer to the textbook set by name.
The public owner is therefore `Q₅`, realized directly through the chapter constrained
sublevel-set owner. -/

/-- Definition 5.4.8.13: the set `Q₅`, namely the constrained hypograph-type region
`{(x, t) ∈ ℝ² | t ≥ 0, x ≤ t^p}`. -/
abbrev Q₅ (p : ℝ) : Set (ℝ × ℝ) :=
  constrainedSublevelSet (Set.univ ×ˢ Set.Ici (0 : ℝ))
    (fun xt : ℝ × ℝ ↦ ((xt.1 - xt.2.rpow p : ℝ) : WithTop ℝ))
    0

-- Proof sketch: unfold `Q₅` and then `mem_constrainedSublevelSet_iff`; membership in the
-- feasible strip gives `0 ≤ t`, and the scalar inequality `x - t^p ≤ 0` is equivalent to
-- `t^p ≥ x`.
/-- Membership in `Q₅ p` means exactly that `t ≥ 0` and `t^p ≥ x`. -/
@[simp] theorem mem_Q₅_iff {p x t : ℝ} :
    (x, t) ∈ Q₅ p ↔ 0 ≤ t ∧ t.rpow p ≥ x := by
  rw [Q₅, mem_constrainedSublevelSet_iff]
  constructor
  · rintro ⟨hxt, hsub⟩
    have ht : 0 ≤ t := by
      simpa [Set.mem_prod] using hxt.2
    have hsub' : x - t.rpow p ≤ 0 := by
      exact_mod_cast hsub
    constructor
    · exact ht
    · linarith
  · rintro ⟨ht, htx⟩
    refine ⟨?_, ?_⟩
    · simpa [Set.mem_prod] using And.intro (Set.mem_univ x) ht
    · have hsub : x - t.rpow p ≤ 0 := by
        linarith
      exact_mod_cast hsub

/-! ### Definition_5_4_8_14 (from Chap05) -/
noncomputable section

/- Definition 5.4.8.14 lies in the Chapter 5 power-cone / barrier-slice domain.

Sampled owner declarations:
* `power_cone_plus_barrier` and `power_cone_plus_barrier_apply` from `Theorem_5_4_7_4`, the
  chapter owner for the one-sided power-cone logarithmic barrier;
* `powerConeGeometricMean` from `Definition_5_4_7_1`, the weighted geometric mean whose unit
  slice gives the same power-gap term `t^p`;
* `separableLogBarrierF6` from `Definition_5_4_8_16`, the neighboring chapter pattern of keeping
  a planar source-facing barrier name while defining it as an affine slice of
  `power_cone_plus_barrier`;
* `separableLogBarrierF4` from `Definition_5_4_8_12`, the adjacent planar barrier still using
  lower-level `sublevelLogBarrier` factors because there is no equally exact upstream owner at
  the same slice level without changing the source semantics.

Best owner abstraction:
* source-facing: the textbook barrier `F₅`;
* core/canonical: `power_cone_plus_barrier p`;
* bridge/view: the affine slice `((t, 1), x)` and the coordinate evaluation theorem below.

Primitive data:
* the upstream owner `power_cone_plus_barrier p`;
* the affine slice fixing the second cone coordinate to `1`.

Derived API:
* the source-facing barrier `separableLogBarrierF5`;
* its coordinate formula `separableLogBarrierF5_apply`.

The previous version kept a lower-level sum of `sublevelLogBarrier` factors as primitive data.
That geometry is already owned upstream by `power_cone_plus_barrier`, and the neighboring `F₆`
file already uses the same slice-based pattern. This refinement keeps the textbook owner `F₅`,
but presents it directly as the affine slice of the existing power-cone barrier owner. -/

/-- Definition 5.4.8.14: the function `F₅` on `ℝ²` given by
`F₅(x, t) = - log t - log (t^p - x)`. -/
def separableLogBarrierF5 (p : ℝ) : ℝ × ℝ → ℝ :=
  fun q ↦ power_cone_plus_barrier p ((q.2, 1), q.1)

-- Proof sketch: `separableLogBarrierF5` is the affine slice `((t, 1), x)` of
-- `power_cone_plus_barrier p`. Evaluate the owner and simplify `log 1 = 0` and
-- `1 ^ (1 - p) = 1`.
/-- Evaluating `separableLogBarrierF5 p` at `(x, t)` reproduces the textbook formula
`F₅(x, t) = - log t - log (t^p - x)`. -/
theorem separableLogBarrierF5_apply (p x t : ℝ) :
    separableLogBarrierF5 p (x, t) = -Real.log t - Real.log (Real.rpow t p - x) := by
  rw [separableLogBarrierF5, power_cone_plus_barrier_apply]
  simp [sub_eq_add_neg, add_comm]

/-! ### Definition_5_4_8_15 (from Chap05) -/
/- Definition 5.4.8.15 lies in the chapter's scalar epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner and its atomic membership expansion for constrained epigraphs;
- `Q₃` and `mem_Q₃_iff` from `Definition_5_4_8_9`, the nearby source-facing pattern where the
  textbook epigraph remains the public owner because later items reuse that name directly;
- the direct `constrainedEpigraph` recall in `Definition_5_4_8_11`, the neighboring pattern for a
  non-reused textbook epigraph whose public surface needs only the canonical owner and a thin
  membership bridge.

Best owner abstraction:
- source-facing owner: `Q₆`;
- canonical realization:
  `constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ ((1 / Real.rpow x p : ℝ) : WithTop ℝ))`.

Primitive data:
- the positive half-line `(0, ∞)`;
- the scalar function `x ↦ x^{-p}`, written in Lean as `x ↦ 1 / Real.rpow x p`.

Derived API:
- the source-facing membership expansion `mem_Q₆_iff`.

Source/core/bridge triage:
- source-facing: the textbook set `Q₆`;
- core/canonical: `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.
-/

/-- Definition 5.4.8.15: the set `Q₆`, namely the epigraph of the function `x ↦ x^{-p}` on
`(0, ∞)`. -/
abbrev Q₆ (p : ℝ) : Set (ℝ × ℝ) :=
  constrainedEpigraph (Set.Ioi (0 : ℝ))
    (fun x : ℝ ↦ ((1 / Real.rpow x p : ℝ) : WithTop ℝ))

-- Proof sketch: unfold `Q₆` and then use the Chapter 3 characterization
-- `mem_constrainedEpigraph_iff`; the feasible-set condition gives `x > 0`, and the remaining
-- inequality is exactly the epigraph inequality `t ≥ x^{-p}`.
/-- Membership in `Q₆ p` means exactly that `x > 0` and `t ≥ x^{-p}`. -/
@[simp]
theorem mem_Q₆_iff {p x t : ℝ} :
    (x, t) ∈ Q₆ p ↔
      0 < x ∧ t ≥ 1 / Real.rpow x p := by
  rw [Q₆, mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt

/-! ### Definition_5_4_8_16 (from Chap05) -/
noncomputable section

/- Definition 5.4.8.16 lies in the Chapter 5 power-cone / epigraph-barrier domain.

Sampled owner declarations:
* `power_cone_plus_barrier` and `power_cone_plus_barrier_apply` from `Theorem_5_4_7_4`, the
  chapter owner for the one-sided power-cone logarithmic barrier;
* `powerConeGeometricMean` from `Definition_5_4_7_1`, the weighted geometric mean
  `x^α t^(1 - α)` appearing in the same barrier geometry;
* `separableLogBarrierF5` from `Definition_5_4_8_14`, the neighboring Chapter 5 pattern of
  keeping a source-facing planar barrier name while defining it through an existing owner.

Best owner abstraction:
* source-facing: the textbook planar barrier `F₆`;
* core/canonical: `power_cone_plus_barrier α`;
* bridge/view: the affine slice `((x, t), 1)` with `α = p / (p + 1)`.

Primitive data:
* the parameter-to-exponent map `p ↦ p / (p + 1)`;
* the affine slice fixing the power-cone coordinate `z = 1`.

Derived API:
* the source-facing barrier `separableLogBarrierF6`;
* its coordinate formula `separableLogBarrierF6_apply`.

The previous file stored the full logarithmic formula as primitive data and added a one-off alias
for the exponent. The chapter already owns the same barrier geometry through
`power_cone_plus_barrier`, so this refinement keeps only the source-facing planar specialization
and its evaluation theorem. -/

/-- Definition 5.4.8.16: the function `F₆` on `ℝ²` given by
`F₆(x, t) = - log x - log t - log (x^α t^(1 - α) - 1)`, where `α = p / (p + 1)`. -/
def separableLogBarrierF6 (p : ℝ) : ℝ × ℝ → ℝ :=
  fun q ↦ power_cone_plus_barrier (p / (p + 1)) (q, 1)

-- Proof sketch: `separableLogBarrierF6` is the affine slice `z = 1` of
-- `power_cone_plus_barrier (p / (p + 1))`. Evaluating the owner and reordering the three
-- logarithmic summands gives the textbook planar formula.
/-- Evaluating `separableLogBarrierF6 p` at `(x, t)` reproduces the textbook formula
`F₆(x, t) = - log x - log t - log (x^α t^(1 - α) - 1)` with `α = p / (p + 1)`. -/
theorem separableLogBarrierF6_apply (p x t : ℝ) :
    separableLogBarrierF6 p (x, t) =
      -Real.log x - Real.log t -
        Real.log
          (Real.rpow x (p / (p + 1)) * Real.rpow t (1 - p / (p + 1)) - 1) := by
  simpa [separableLogBarrierF6, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    power_cone_plus_barrier_apply (p / (p + 1)) x t 1
