import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_4_6_8 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u v w

/- Theorem 5.4.6.8 lies in the subsection's composed Hessian / local-norm domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical owner for `∇² Φ`;
* `hessianLocalNorm` / `‖h‖[Φ; p]` in `Definition_5_1_1`, the canonical owner for the square root
  of the Hessian quadratic form;
* `(hessian Φ p).IsPositive` from mathlib's `ContinuousLinearMap.IsPositive` API, together with
  the chapter's `IsSelfConcordantOnWith.hessian_isPositive`, the canonical pointwise
  Hessian-positivity owner and the upstream bridge from self-concordance to that owner;
* `compositionPotentialSigmaOne` and `compositionPotentialSigmaTwo` in `Theorem_5_4_6_5`, the
  source-facing `σ₁` and `σ₂` terms in the subsection;
* `compositionSecondLiftedDirectionDerivative` in `Definition_5_4_6_7`, the bridge realizing the
  lifted derivative direction `l' = (D²ξ(x)[d, d], 0)`;
* the specialized owner-level estimate `‖-l'‖[Φ; (ξ(x), z)] ≤ σ₂`, which is the only `(5.3.13)`
  input used in this cross-term bound.

Source/core/bridge triage:
* source-facing: the cross-term estimate `⟪∇² Φ(ξ(x), z) l, l'⟫ ≤ σ₁^(1/2) σ₂`;
* core/canonical: `(hessian Φ (ξ x, z)).IsPositive`, `hessian Φ (ξ x, z)`, and
  `‖·‖[Φ; (ξ x, z)]`;
* bridge/view: the canonical lifted pair `(fderiv ℝ ξ x d, 0)` and
  `compositionSecondLiftedDirectionDerivative ξ x d`.

Primitive data:
* the map `ξ`, point `x`, direction `d`, and auxiliary point `z`;
* pointwise positivity of the Hessian at `(ξ x, z)`;
* the specialized local-norm estimate for `-l'`.

Derived API:
* the lifted direction `l = (Dξ(x)[d], 0)`;
* the source-facing scalar terms `σ₁` and `σ₂`;
* the local self-concordance bridge hypothesis only when a larger subsection needs to derive the
  pointwise positivity owner above from a domain-level assumption.

The public statement should therefore use the pointwise Hessian-positivity owner together with the
owner-level Hessian and Hessian local norm, rather than carrying redundant self-concordance and
interior-membership assumptions whose only role was to derive this local positivity. -/

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

-- Proof sketch: the pointwise positivity hypothesis on `hessian Φ (ξ x, z)` makes the Hessian
-- local norm a genuine seminorm at `(ξ x, z)`, so Cauchy--Schwarz applies to the Hessian-induced
-- pairing. Bound the mixed Hessian term by
-- `‖(fderiv ℝ ξ x d, 0)‖[Φ; (ξ x, z)] *
-- ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)]`, rewrite the first factor as
-- `σ₁^(1/2)`, and use the specialized `(5.3.13)` estimate for
-- `-compositionSecondLiftedDirectionDerivative ξ x d` to identify the second factor with `σ₂`.
/-- Theorem 5.4.6.8: if the Hessian of `Φ` at `(ξ(x), z)` is positive and the negative lifted
derivative direction `-l'` satisfies the specialized owner-level estimate
`‖-l'‖[Φ; (ξ(x), z)] ≤ σ₂`, then the cross Hessian term
`⟪∇² Φ(ξ(x), z) (Dξ(x)[d], 0), Dl(x)[d]⟫` is bounded above by `σ₁^(1/2) σ₂`, where
`Dl(x)[d] = compositionSecondLiftedDirectionDerivative ξ x d`,
`σ₁ = ⟪∇² Φ(ξ(x), z) (Dξ(x)[d], 0), (Dξ(x)[d], 0)⟫`, and
`σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫`. -/
theorem compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hH : (hessian Φ (ξ x, z)).IsPositive)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z d) :
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x d) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
        compositionPotentialSigmaTwo Φ ξ x z d := sorry

end

/-! ### Theorem_5_4_6_9 (from Chap05) -/
open ProperCone
open scoped Gradient HessianLocalNorm

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Theorem 5.4.6.9 lies in the subsection's cone-ordered third-derivative / barrier-composition
pairing domain.

Sampled owner declarations:
* `IsBetaCompatibleWith.compatibility_bound_sign_reversal` from `Theorem_5_4_6_1`, the owner-level
  sign-reversed compatibility bound on `D³ξ`;
* `compositionPotentialSigmaTwo` from `Theorem_5_4_6_5`, the source-facing owner for the
  `∇ᵧ Φ` pairing with `D²ξ`;
* `sigmaThree` from `Definition_5_4_6_8`, the source-facing name for the squared Hessian local
  norm;
* mathlib `ProperCone.innerDual` and `ProperCone.mem_innerDual`, the canonical owner abstraction
  for dual-cone membership in this cone-pairing domain;
* `barrier_yGradient_pairing_nonpos` from `Definition_5_4_6_4`, the barrier-owner bridge that
  supplies the dual-cone membership bridge in the barrier specialization.

Source/core/bridge triage:
* source-facing: the textbook upper bound for
  `⟪∇ᵧ Φ(ξ(x), z), D³ξ(x)[h, h, h]⟫`;
* core/canonical: `IsBetaCompatibleWith`, `vectorThirdDirectionalDerivative`, and the Hessian
  local norm `‖h‖[F; x]`;
* bridge/view: the source-facing scalars `compositionPotentialSigmaTwo` and `sigmaThree`, plus the
  barrier specialization `barrier_yGradient_pairing_nonpos`.

Primitive data:
* the compatibility owner `hξ`, the point `x ∈ interior Q₁`, the direction `h`, and the fixed
  parameter `z`;
* the dual-cone membership hypothesis
  `-∇ᵧ Φ(ξ(x), z) ∈ innerDual (K : Set E₂)`.

Derived API:
* the sign-reversed compatibility cone element;
* `compositionPotentialSigmaTwo Φ ξ x z h`;
* `sigmaThree F x h = ‖h‖[F; x]^2`.

The theorem therefore stays a bridge theorem over the compatibility owner and the subsection
source-facing scalar names, and it should live on the same complete-Hilbert-space owner layer as
those reused declarations rather than on an unnecessary finite-dimensional specialization. -/

/-- Theorem 5.4.6.9: if `ξ` is `β`-compatible with the barrier `F` on `Q₁`, if `x` lies in
`interior Q₁`, and if `-∇ᵧ Φ(ξ(x), z)` belongs to the dual cone `innerDual (K : Set E₂)`, then
`⟪∇ᵧ Φ(ξ(x), z), D³ξ(x)[h, h, h]⟫ ≤ 3 β σ₂ σ₃^{1/2}`, where
`σ₂ = compositionPotentialSigmaTwo Φ ξ x z h` and `σ₃ = sigmaThree F x h`. -/
theorem yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ}
    {β : NNReal} {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorThirdDirectionalDerivative ξ x h) ≤
      3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
        Real.sqrt (sigmaThree F x h) := by
  let g : E₂ := ∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)
  let s : E₂ :=
    (3 * (β : ℝ) * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) +
      vectorThirdDirectionalDerivative ξ x h
  have hs : s ∈ K := by
    simpa [s] using hξ.compatibility_bound_sign_reversal hx h
  rw [mem_innerDual] at hneg_yGradient_mem_innerDual
  have hpair : inner ℝ g s ≤ 0 :=
    by simpa [g, real_inner_comm] using hneg_yGradient_mem_innerDual hs
  dsimp [g, s] at hpair ⊢
  rw [inner_add_right, inner_smul_right, inner_neg_right] at hpair
  rw [compositionPotentialSigmaTwo_def]
  rw [sqrt_sigmaThree]
  linarith

section Barrier

variable [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance : CompleteSpace (E₂ × E₃) := inferInstance

-- Proof sketch: use `barrier_yGradient_pairing_nonpos` from Definition 5.4.6.4 to prove the
-- canonical dual-cone membership `-∇ᵧ Φ(ξ(x), z) ∈ innerDual K` via `mem_innerDual`, then apply
-- Theorem 5.4.6.9 with that owner-level hypothesis.
/-- Under the barrier and recession hypotheses from Definition 5.4.6.4, the cone-pairing
assumption in Theorem 5.4.6.9 is automatic, equivalently
`-∇ᵧ Φ(ξ(x), z) ∈ innerDual (K : Set E₂)`. -/
theorem yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility_of_barrier
    {Q₁ : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {β : NNReal}
    {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hQ₂_convex : Convex ℝ Q₂)
    (hΦ : ∃ μ : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_ : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_ : p ∈ Q₂) (τ : ℝ) (_ : 0 ≤ τ), p + τ • (s, (0 : E₃)) ∈ Q₂)
    (hyz : (ξ x, z) ∈ interior Q₂) :
    inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorThirdDirectionalDerivative ξ x h) ≤
      3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
        Real.sqrt (sigmaThree F x h) := by
  have hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂) := by
    rw [mem_innerDual]
    intro s hs
    simpa [real_inner_comm] using
      barrier_yGradient_pairing_nonpos hQ₂_convex K hΦ hK_recession hyz hs
  exact
    yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility hξ hx
      hneg_yGradient_mem_innerDual

end Barrier

end

/-! ### Definition_5_4_7_1 (from Chap05) -/
noncomputable section

open scoped BigOperators EuclideanOrthant SecondOrderCone

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

noncomputable local instance : Fintype (Fin 2) := Fintype.ofFinite (Fin 2)

/- Definition 5.4.7.1 lies in the Chapter 5 power-cone / cone-composition domain.

Sampled owner declarations:
* `coneCompositionFeasibleSet` and `mem_coneCompositionFeasibleSet_iff` from
  `Definition_5_4_6_3`, the chapter owner for feasible sets cut out by a cone-order comparison;
* `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` from
  `Chap01/Definition_1_10_2`, the canonical owner/view for `ℝ_+^2`;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the chapter ambient bridge for
  the standard orthant logarithmic barrier;
* `secondOrderCone` and `mem_secondOrderCone_iff` from `Lemma_5_4_3_3`, the canonical owner/view
  for the planar cone `\{(z, y) \mid |z| ≤ y\}`;
* `Prod.swap`, the canonical bridge between the source `(y, z)` coordinates and the owner
  `(z, y)` coordinates.

Source/core/bridge triage:
* source-facing: `powerCone α`, the textbook power cone `K_α`;
* core/canonical: `coneCompositionFeasibleSet`, `ℝ₊^2`, and
  `standardLogarithmicBarrierAmbient 2`;
* bridge/view: the private coordinate bridge `powerConePairToEuclidean` together with
  `mem_powerConeQ1_iff`, `powerConeBarrier_apply`, and `mem_powerCone_iff`.

Primitive data:
* the weighted geometric mean `powerConeGeometricMean α`;
* the scalar positive cone `ConvexCone.positive ℝ ℝ`.

Derived API:
* the orthant `powerConeQ1 = ℝ_+²`, pulled back from the canonical owner `ℝ₊^2`;
* the planar comparison set `powerConeQ2`, viewed as the swapped-coordinate second-order cone;
* the orthant barrier `powerConeBarrier`, pulled back from
  `standardLogarithmicBarrierAmbient 2`;
* the barrier parameter `powerConeBarrierParameter`;
* the pointwise evaluation and membership lemmas below.

The scalar cone `K = ℝ_+` is already canonically owned by `ConvexCone.positive ℝ ℝ`, the orthant
`Q₁ = ℝ_+²` by `ℝ₊^2`, and its logarithmic barrier by `standardLogarithmicBarrierAmbient 2`,
while the comparison cone `Q₂ = {(y, z) | y ≥ |z|}` is the coordinate-swapped view of the
Chapter 5 second-order cone owner. This file therefore keeps the textbook owner `powerCone α`,
but makes its pair-level orthant and barrier data thin coordinate bridges to those earlier
owners instead of repeating the raw coordinate model as parallel primitive declarations. -/

private def powerConePairToEuclidean : ℝ × ℝ → E₂ :=
  fun x ↦ WithLp.toLp 2 ![x.1, x.2]

private theorem neg_sum_log_pair_eq (x₁ x₂ : ℝ) :
    -(∑ x : Fin 2, Real.log (![x₁, x₂] x)) = -Real.log x₁ - Real.log x₂ := by
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    ext i
    constructor
    · intro _
      have hi : i = 0 ∨ i = 1 := by
        omega
      simp [hi]
    · intro _
      simp
  have hsum : (∑ x : Fin 2, Real.log (![x₁, x₂] x)) = Real.log x₁ + Real.log x₂ := by
    simp [huniv]
  have hneg : -(∑ x : Fin 2, Real.log (![x₁, x₂] x)) = -(Real.log x₁ + Real.log x₂) :=
    congrArg (fun s : ℝ ↦ -s) hsum
  calc
    -(∑ x : Fin 2, Real.log (![x₁, x₂] x)) = -(Real.log x₁ + Real.log x₂) := hneg
    _ = -Real.log x₁ - Real.log x₂ := by
      ring

/-- The weighted geometric mean `x₁^α x₂^(1 - α)` that appears in the power-cone representation;
this is the scalar map `ξ`. -/
def powerConeGeometricMean (α : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.rpow x.1 α * Real.rpow x.2 (1 - α)

namespace PowerConeGeometricMean

/- Source-facing Lean notation for the textbook weighted geometric mean `ξ`. -/
scoped notation:max "ξ[" α:arg "]" => powerConeGeometricMean α

end PowerConeGeometricMean

open scoped PowerConeGeometricMean

-- Proof sketch: unfold `ξ[α]`.
/-- Evaluating `ξ[α]` at `(x₁, x₂)` gives the product
`x₁^α x₂^(1 - α)` written using `Real.rpow`. -/
theorem powerConeGeometricMean_apply (α x₁ x₂ : ℝ) :
    ξ[α] (x₁, x₂) =
      Real.rpow x₁ α * Real.rpow x₂ (1 - α) :=
  rfl

/-- The orthant `Q₁ = ℝ_+²` used in the power-cone representation, pulled back from the
canonical Euclidean orthant owner along the source coordinate bridge. -/
abbrev powerConeQ1 : Set (ℝ × ℝ) :=
  powerConePairToEuclidean ⁻¹' (ℝ₊^2 : Set E₂)

-- Proof sketch: rewrite through the canonical orthant owner `ℝ₊^2` and its coordinatewise
-- membership theorem.
/-- A point `(x₁, x₂)` belongs to `powerConeQ1` exactly when both coordinates are nonnegative. -/
theorem mem_powerConeQ1_iff (x₁ x₂ : ℝ) :
    (x₁, x₂) ∈ powerConeQ1 ↔ 0 ≤ x₁ ∧ 0 ≤ x₂ := by
  simp [powerConeQ1, powerConePairToEuclidean, EuclideanSpace.mem_nonnegativeOrthant_iff]

/-- The set `Q₂ = {(y, z) ∈ ℝ × ℝ : y ≥ |z|}` used in the power-cone representation. It is the
`(y, z)`-coordinate view of the canonical second-order cone on `ℝ × ℝ`. -/
abbrev powerConeQ2 : Set (ℝ × ℝ) :=
  Prod.swap ⁻¹' (K₂[ℝ] : Set (ℝ × ℝ))

-- Proof sketch: rewrite through the swapped-coordinate second-order cone owner and then apply
-- `mem_secondOrderCone_iff`.
/-- A pair `(y, z)` belongs to `powerConeQ2` exactly when `y ≥ |z|`. -/
theorem mem_powerConeQ2_iff (y z : ℝ) :
    (y, z) ∈ powerConeQ2 ↔ y ≥ |z| := by
  change (z, y) ∈ K₂[ℝ] ↔ y ≥ |z|
  rw [mem_secondOrderCone_iff]
  simp [Real.norm_eq_abs, ge_iff_le]

/-- Definition 5.4.7.1: for `α ∈ (0, 1)`, the power cone `K_α` consists of the triples
`((x₁, x₂), z)` with `(x₁, x₂) ∈ ℝ_+²` and `|z| ≤ x₁^α x₂^(1 - α)`. The companion declarations
below record the associated representation data `Q₁`, `F`, `ν`, `K`, `ξ`, and `Q₂`. -/
def powerCone (α : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  coneCompositionFeasibleSet
    powerConeQ1
    (ConvexCone.positive ℝ ℝ)
    ξ[α]
    powerConeQ2

namespace PowerCone

/- Source-facing Lean notation for the textbook power cone `K_α`. -/
scoped notation:max "K_[" α:arg "]" => powerCone α

end PowerCone

open scoped PowerCone

-- Proof sketch: expand the owner specialization `powerCone α` through
-- `mem_coneCompositionFeasibleSet_iff`. The comparison witness `y` satisfies
-- `|z| ≤ y ≤ x₁^α x₂^(1 - α)`, and conversely `y = |z|` realizes the owner constraints.
/-- A triple `((x₁, x₂), z)` belongs to `K_[α]` exactly when `x₁, x₂ ≥ 0` and
`|z| ≤ x₁^α x₂^(1 - α)`. -/
theorem mem_powerCone_iff (α x₁ x₂ z : ℝ) :
    ((x₁, x₂), z) ∈ K_[α] ↔
      0 ≤ x₁ ∧ 0 ≤ x₂ ∧ |z| ≤ ξ[α] (x₁, x₂) := by
  rw [powerCone, mem_coneCompositionFeasibleSet_iff]
  constructor
  · rintro ⟨y, hx, hy, hz⟩
    have hx' : 0 ≤ x₁ ∧ 0 ≤ x₂ := (mem_powerConeQ1_iff x₁ x₂).1 (by simpa using hx)
    have hy' : y ≤ ξ[α] (x₁, x₂) := by
      rw [ConvexCone.mem_positive] at hy
      exact sub_nonneg.mp (by simpa using hy)
    have hz' : |z| ≤ y := (mem_powerConeQ2_iff y z).1 (by simpa using hz)
    exact ⟨hx'.1, hx'.2, le_trans hz' hy'⟩
  · rintro ⟨hx₁, hx₂, hz⟩
    refine ⟨|z|, (mem_powerConeQ1_iff x₁ x₂).2 ⟨hx₁, hx₂⟩, ?_, ?_⟩
    · rw [ConvexCone.mem_positive]
      exact sub_nonneg.mpr hz
    · exact (mem_powerConeQ2_iff |z| z).2 le_rfl

/-- The logarithmic barrier `F(x) = -log x₁ - log x₂` on the interior of `Q₁ = ℝ_+²`, obtained
by pulling back the canonical positive-orthant ambient barrier along the source coordinate
bridge. -/
def powerConeBarrier : (ℝ × ℝ) → ℝ :=
  standardLogarithmicBarrierAmbient 2 ∘ powerConePairToEuclidean

-- Proof sketch: unfold `powerConeBarrier` through the canonical ambient orthant barrier and
-- simplify the `Fin 2` sum back to the two-coordinate formula.
/-- Evaluating `powerConeBarrier` at `(x₁, x₂)` gives the textbook formula
`-log x₁ - log x₂`. -/
theorem powerConeBarrier_apply (x₁ x₂ : ℝ) :
    powerConeBarrier (x₁, x₂) = -Real.log x₁ - Real.log x₂ :=
  by
    simpa [powerConeBarrier, powerConePairToEuclidean, standardLogarithmicBarrierAmbient,
      Function.comp_apply] using neg_sum_log_pair_eq x₁ x₂

/-- The barrier parameter `ν = 2` attached to the orthant barrier in the power-cone
representation. -/
def powerConeBarrierParameter : NNReal :=
  2

-- Proof sketch: unfold `powerConeBarrierParameter`.
/-- The power-cone representation uses barrier parameter `ν = 2`. -/
theorem powerConeBarrierParameter_eq :
    powerConeBarrierParameter = 2 :=
  rfl

/-! ### Definition_5_4_7_10 (from Chap05) -/
noncomputable section

/- Definition 5.4.7.10 lies in the Chapter 5 entropy-epigraph / exponential-cone domain.

Sampled owner declarations:
* `entropyEpigraphCone` from `Definition_5_4_7_8`, the upstream source-facing owner for the
  conic entropy epigraph;
* `mem_entropyEpigraphCone_iff` from `Definition_5_4_7_8`, the explicit coordinate membership
  theorem for that owner;
* `entropyEpigraphConeBarrier` from `Theorem_5_4_7_6`, the upstream logarithmic barrier owner on
  the entropy-epigraph cone;
* `entropyEpigraphConeBarrier_apply` from `Theorem_5_4_7_6`, the pointwise bridge for that
  barrier.

Best owner abstraction:
* keep Definition 5.4.7.10 source-facing as the exponential cone and its barrier;
* reuse `entropyEpigraphCone` and `entropyEpigraphConeBarrier` as the core owners;
* express the present file through the coordinate change `((x, y), τ) ↦ ((τ, y), -x)`.

Primitive data:
* no new cone/barrier data beyond the source-facing coordinate change.

Derived API:
* `exponentialCone` and `exponentialConeBarrier`;
* the textbook membership criterion `mem_exponentialCone_iff`;
* the textbook evaluation formula `exponentialConeBarrier_apply`.

Source/core/bridge triage:
* source-facing: `exponentialCone` and `exponentialConeBarrier`;
* core/canonical: `entropyEpigraphCone` and `entropyEpigraphConeBarrier`;
* bridge/view: the coordinate change `((x, y), τ) ↦ ((τ, y), -x)`.

This refinement removes the duplicate raw cone and barrier bodies. The exponential cone is kept as
the source-facing object from the text, but its implementation now reuses the chapter owner
`entropyEpigraphCone`, and the barrier is the corresponding pullback of
`entropyEpigraphConeBarrier`. -/

/-- Definition 5.4.7.10 (1): the exponential cone is the source-facing coordinate view of the
entropy-epigraph cone under `((x, y), τ) ↦ ((τ, y), -x)`. -/
def exponentialCone : Set ((ℝ × ℝ) × ℝ) :=
  {p | ((p.2, p.1.2), -p.1.1) ∈ entropyEpigraphCone}

/-- A triple `((x, y), τ)` belongs to `exponentialCone` exactly when
`y ≥ τ * exp (x / τ)` and `τ > 0`. -/
theorem mem_exponentialCone_iff (x y τ : ℝ) :
    ((x, y), τ) ∈ exponentialCone ↔
      y ≥ τ * Real.exp (x / τ) ∧ 0 < τ := by
  change ((τ, y), -x) ∈ entropyEpigraphCone ↔
      y ≥ τ * Real.exp (x / τ) ∧ 0 < τ
  rw [mem_entropyEpigraphCone_iff]
  constructor
  · rintro ⟨hτ, hy, hx⟩
    refine ⟨?_, hτ⟩
    have hlog : x / τ ≤ Real.log (y / τ) := by
      have hx' : x ≤ τ * Real.log (y / τ) := by
        have hlog_div : Real.log (y / τ) = Real.log y - Real.log τ :=
          Real.log_div hy.ne' hτ.ne'
        rw [hlog_div]
        linarith
      exact (div_le_iff₀ hτ).2 <| by simpa [mul_comm] using hx'
    have hexp : Real.exp (x / τ) ≤ y / τ :=
      (Real.le_log_iff_exp_le (div_pos hy hτ)).1 hlog
    calc
      τ * Real.exp (x / τ) ≤ τ * (y / τ) := by
        exact mul_le_mul_of_nonneg_left hexp hτ.le
      _ = y := by field_simp [hτ.ne']
  · rintro ⟨hy, hτ⟩
    have hy_pos : 0 < y := by
      exact lt_of_lt_of_le (mul_pos hτ (Real.exp_pos (x / τ))) hy
    refine ⟨hτ, hy_pos, ?_⟩
    have hdiv : Real.exp (x / τ) ≤ y / τ := by
      exact (le_div_iff₀ hτ).2 <| by simpa [mul_comm] using hy
    have hlog : x / τ ≤ Real.log (y / τ) :=
      (Real.le_log_iff_exp_le (div_pos hy_pos hτ)).2 hdiv
    have hx' : x ≤ τ * Real.log (y / τ) :=
      by simpa [mul_comm] using (div_le_iff₀ hτ).1 hlog
    rw [Real.log_div hy_pos.ne' hτ.ne'] at hx'
    linarith

/-- Definition 5.4.7.10 (2): the exponential-cone barrier is the pullback of the entropy-epigraph
cone barrier under the same coordinate change. -/
def exponentialConeBarrier : ((ℝ × ℝ) × ℝ) → ℝ :=
  fun p ↦ entropyEpigraphConeBarrier ((p.2, p.1.2), -p.1.1)

/-- Evaluating `exponentialConeBarrier` at `((x, y), τ)` gives the textbook formula
`-log (τ log (y / τ) - x) - log y - log τ`. -/
theorem exponentialConeBarrier_apply (x y τ : ℝ) :
    exponentialConeBarrier ((x, y), τ) =
      -Real.log (τ * Real.log (y / τ) - x) - Real.log y - Real.log τ := by
  rw [exponentialConeBarrier, entropyEpigraphConeBarrier_apply]
  by_cases hτ : τ = 0
  · simp [hτ]
  · by_cases hy : y = 0
    · simp [hy]
    · rw [Real.log_div hτ hy, Real.log_div hy hτ]
      ring_nf

end

/-! ### Definition_5_4_7_11 (from Chap05) -/
noncomputable section

open scoped BigOperators

/- Definition 5.4.7.11 lies in the Chapter 5 log-sum-exp / perspective-epigraph domain.

Sampled owner declarations:
* `convexOn_log_sum_exp_of_convexOn` from `Chap03/Proposition_3_21`, the project owner theorem
  for finite-family log-sum-exp on a common domain;
* `perspectiveTransform` from `Chap03/Remark_3_1_2_3`, the chapter owner for the scaled-input
  construction `(τ, x) ↦ τ f (τ⁻¹ • x)`;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraphs over a
  specified feasible domain;
* `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the atomic membership bridge for
  that owner.

Best owner abstraction:
* source-facing: `logSumExp` and the textbook cone `logSumExpEpigraphCone`;
* core/canonical: `perspectiveTransform` together with `constrainedEpigraph`;
* bridge/view: the `Fin n` specialization `EuclideanSpace ℝ (Fin n)` of the intrinsic finite-family
  owner below, together with the coordinate permutation `(x, t, τ) ↦ (((τ, x), t))`.

Primitive data:
* a finite index type `ι`;
* the source-facing log-sum-exp function on `EuclideanSpace ℝ ι`.

Derived API:
* the evaluation lemma `logSumExp_apply`;
* the perspective-epigraph owner `logSumExpEpigraphCone`;
* the membership bridge `mem_logSumExpEpigraphCone_iff`.

The previous version stored the conic epigraph as a raw inequality set and pinned the owner to the
coordinate model `EuclideanSpace ℝ (Fin n)`. The mathematics is still the same source-facing cone,
but its implementation should reuse the chapter owners for perspectives and constrained epigraphs
at the canonical finite-family level, with the textbook `ℝⁿ` presentation obtained by
specialization to `ι = Fin n`. -/

universe v

variable {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "P" => ℝ × E

/-- The finite-family log-sum-exp function `x ↦ log (∑ i, exp (x i))` on
`EuclideanSpace ℝ ι`. Specializing to `ι = Fin n` recovers the textbook `n`-variable formula. -/
def logSumExp : E → ℝ :=
  fun x ↦ Real.log (∑ i : ι, Real.exp (x i))

/-- Evaluating `logSumExp` at `x` gives `log (∑ i, exp (x i))`. -/
@[simp] theorem logSumExp_apply (x : E) :
    logSumExp x = Real.log (∑ i : ι, Real.exp (x i)) :=
  rfl

/-- Definition 5.4.7.11: the conic-hull epigraph of the finite-family log-sum-exp function is the
set of triples `(x, t, τ)` with `τ > 0` and `t ≥ τ * logSumExp (τ⁻¹ • x)`, i.e. the scaled-input
form of `t ≥ τ f(x / τ)`. This is the constrained epigraph of the perspective transform of
`logSumExp`, written in the source-facing coordinates `(x, t, τ)`. Specializing to `ι = Fin n`
recovers the textbook `n`-variable cone. -/
def logSumExpEpigraphCone : Set (E × ℝ × ℝ) :=
  (fun p : E × ℝ × ℝ ↦ (((p.2.2, p.1), p.2.1) : P × ℝ)) ⁻¹'
    constrainedEpigraph
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E))
      (fun z : P ↦ (perspectiveTransform logSumExp z : WithTop ℝ))

/-- A triple `(x, t, τ)` lies in `logSumExpEpigraphCone` exactly when `τ > 0` and
`t ≥ τ * logSumExp (τ⁻¹ • x)`. -/
theorem mem_logSumExpEpigraphCone_iff
    (x : E) (t τ : ℝ) :
    (x, t, τ) ∈ logSumExpEpigraphCone ↔
      0 < τ ∧ t ≥ τ * logSumExp (τ⁻¹ • x) := by
  rw [logSumExpEpigraphCone, Set.mem_preimage, mem_constrainedEpigraph_iff]
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
  constructor
  · rintro ⟨hτ, ht⟩
    refine ⟨hτ, ?_⟩
    rw [perspectiveTransform_apply_of_pos logSumExp hτ] at ht
    exact_mod_cast ht
  · rintro ⟨hτ, ht⟩
    refine ⟨hτ, ?_⟩
    rw [perspectiveTransform_apply_of_pos logSumExp hτ]
    exact_mod_cast ht

end

/-! ### Definition_5_4_7_12 (from Chap05) -/
noncomputable section

open scoped BigOperators

universe v

variable {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "LPoint" => E × E × ℝ × ℝ

/- Definition 5.4.7.12 lies in the Chapter 5 log-sum-exp epigraph / lifted exponential-cone
domain.

Sampled owner declarations:
* `exponentialCone` from `Definition_5_4_7_10`, the Chapter 5 source-facing scalar cone owner;
* `mem_exponentialCone_iff` from `Definition_5_4_7_10`, the scalar membership bridge for that
  owner;
* `logSumExpEpigraphCone` from `Definition_5_4_7_11`, the unlifted conic log-sum-exp epigraph
  owner on the same finite index family, obtained after forgetting the slack coordinates
  `y`.
* `mem_logSumExpEpigraphCone_iff` from `Definition_5_4_7_11`, the canonical owner-level
  membership bridge on that same finite-family ambient space.

Source/core/bridge triage:
* source-facing: `liftedConeLogSumExp`, the lifted cone `hat Q`;
* core/canonical: the earlier scalar owner `exponentialCone`;
* bridge/view: the coordinate map `i ↦ ((x i - t, y i), τ)` together with the normalization
  equation `∑ i, y i = τ`.

Primitive data:
* coordinatewise membership in the scalar exponential cone;
* the normalization equation `∑ i, y i = τ`.

Derived API:
* the membership bridge `mem_liftedConeLogSumExp_iff`, which keeps the lifted cone expressed
  through the scalar cone owner rather than re-expanding to raw inequalities;
* the owner-to-owner bridge `mem_logSumExpEpigraphCone_of_mem_liftedConeLogSumExp`, sending a
  lifted feasible point to the corresponding point of the canonical conic epigraph owner
  `logSumExpEpigraphCone`.

This refinement removes the recall-only surface and restores Definition 5.4.7.12 as the owner
file for the lifted log-sum-exp cone. The public definition now grows from the earlier
source-facing owner `exponentialCone`, exactly as the analogous lifted `ℓ_p` file grows from
`powerCone`, instead of bypassing the chapter owner with a raw coordinate inequality set. The
ambient family is now parameterized by an arbitrary finite index type `ι`, matching the upstream
owner `logSumExpEpigraphCone`; the textbook coordinate model `Fin n` is recovered by
specialization, and the nonempty-family hypothesis is only used where the projection theorem needs
one coordinate to read off the positivity of `τ`.
-/

/-- Definition 5.4.7.12: the lifted cone `hat Q` for the log-sum-exp epigraph consists of the
quadruples `(x, y, t, τ)` such that each coordinate triple `((x^(i) - t, y^(i)), τ)` lies in the
scalar exponential cone and the slack variables satisfy the normalization equation
`∑ i, y^(i) = τ`. -/
def liftedConeLogSumExp : Set LPoint
  | (x, y, t, τ) =>
      (∀ i : ι, ((x i - t, y i), τ) ∈ exponentialCone) ∧
        ∑ i : ι, y i = τ

/-- A quadruple `(x, y, t, τ)` belongs to `liftedConeLogSumExp` exactly when each coordinate
triple `((x^(i) - t, y^(i)), τ)` belongs to `exponentialCone` and `∑ i, y^(i) = τ`. -/
theorem mem_liftedConeLogSumExp_iff
    {x y : E} {t τ : ℝ} :
    (x, y, t, τ) ∈ liftedConeLogSumExp ↔
      (∀ i : ι, ((x i - t, y i), τ) ∈ exponentialCone) ∧
        ∑ i : ι, y i = τ :=
  Iff.rfl

/-- A lifted feasible point `(x, y, t, τ)` projects to a feasible point `(x, t, τ)` of the
canonical log-sum-exp epigraph cone. This is the owner-level bridge from the lifted source-facing
cone `hat Q` to the earlier conic epigraph owner `logSumExpEpigraphCone`. -/
theorem mem_logSumExpEpigraphCone_of_mem_liftedConeLogSumExp
    [Nonempty ι] {x y : E} {t τ : ℝ}
    (h : (x, y, t, τ) ∈ liftedConeLogSumExp) :
    (x, t, τ) ∈ logSumExpEpigraphCone := by
  classical
  rw [mem_liftedConeLogSumExp_iff] at h
  rcases h with ⟨hcone, hsum⟩
  let i0 : ι := Classical.choice inferInstance
  have hτ : 0 < τ := (mem_exponentialCone_iff (x i0 - t) (y i0) τ).1 (hcone i0) |>.2
  let s : ℝ := ∑ i : ι, Real.exp (x i / τ)
  have hy_div (i : ι) : Real.exp ((x i - t) / τ) ≤ y i / τ := by
    have hi : τ * Real.exp ((x i - t) / τ) ≤ y i :=
      (mem_exponentialCone_iff (x i - t) (y i) τ).1 (hcone i) |>.1
    exact (le_div_iff₀ hτ).2 <| by simpa [mul_comm] using hi
  have hsum_div :
      ∑ i : ι, Real.exp ((x i - t) / τ) ≤ ∑ i : ι, y i / τ :=
    Finset.sum_le_sum fun i _ ↦ hy_div i
  have hy_norm : ∑ i : ι, y i / τ = 1 := by
    rw [← Finset.sum_div, hsum, div_self hτ.ne']
  have hshift :
      ∑ i : ι, Real.exp ((x i - t) / τ) = Real.exp (-t / τ) * s := by
    calc
      ∑ i : ι, Real.exp ((x i - t) / τ)
          = ∑ i : ι, Real.exp (x i / τ) * Real.exp (-t / τ) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [sub_eq_add_neg, add_div, neg_div, Real.exp_add]
      _ = (∑ i : ι, Real.exp (x i / τ)) * Real.exp (-t / τ) := by
            rw [Finset.sum_mul]
      _ = Real.exp (-t / τ) * s := by
            dsimp [s]
            rw [mul_comm]
  have hs_le : Real.exp (-t / τ) * s ≤ 1 := by
    simpa [hshift, hy_norm] using hsum_div
  have hs_pos : 0 < s := by
    have hs_ge : Real.exp (x i0 / τ) ≤ s := by
      dsimp [s]
      change Real.exp (x i0 / τ) ≤ ∑ i : ι, Real.exp (x i / τ)
      exact
        Finset.single_le_sum
          (fun i _ ↦ (Real.exp_pos (x i / τ)).le)
          (show i0 ∈ (Finset.univ : Finset ι) from by simp)
    exact lt_of_lt_of_le (Real.exp_pos (x i0 / τ)) hs_ge
  have hs_le_exp : s ≤ Real.exp (t / τ) := by
    have hs_le_div : s ≤ 1 / Real.exp (-t / τ) := by
      exact (le_div_iff₀ (Real.exp_pos (-t / τ))).2 <| by simpa [mul_comm] using hs_le
    simpa [one_div, neg_div, Real.exp_neg] using hs_le_div
  have hlog : Real.log s ≤ t / τ :=
    (Real.log_le_iff_le_exp hs_pos).2 hs_le_exp
  have hmem : τ * Real.log s ≤ t := by
    simpa [mul_comm] using (le_div_iff₀ hτ).1 hlog
  rw [mem_logSumExpEpigraphCone_iff x t τ]
  refine ⟨hτ, ?_⟩
  simpa [logSumExp, s, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmem

end

/-! ### Definition_5_4_7_13 (from Chap05) -/
noncomputable section

open scoped BigOperators

universe v

variable {ι : Type v} [Fintype ι]

/- Definition 5.4.7.13 lies in the lifted finite-family log-sum-exp barrier domain.

Sampled owner declarations:
* `exponentialConeBarrier` from `Definition_5_4_7_10`, the scalar barrier summed coordinatewise
  upstream;
* `liftedConeLogSumExp` from `Definition_5_4_7_12`, the lifted finite-family cone owner;
* `liftedConeLogSumExpBarrier` from `Theorem_5_4_7_7`, the Chapter 5 owner for the ambient lifted
  barrier;
* `liftedConeLogSumExpBarrier_apply` from `Theorem_5_4_7_7`, the canonical coordinate-sum bridge.

Best owner abstraction:
* source-facing: the lifted finite-family barrier `Ψ_L`;
* core/canonical: the upstream owner `liftedConeLogSumExpBarrier`;
* bridge/view: specialization to `ι = Fin n` for the textbook `n`-coordinate presentation.

Primitive data:
* none in this file; the owner and its bridges are already defined upstream.

Derived API:
* the recalled owner `liftedConeLogSumExpBarrier`;
* the recalled coordinate-sum bridge `liftedConeLogSumExpBarrier_apply`;
* the recalled positive-branch formula `liftedConeLogSumExpBarrier_apply_formula`.

This item is recall-only. The public surface stays at the same arbitrary finite index type as
Definitions 5.4.7.11 and 5.4.7.12; `Fin n` is only the standard specialization bridge. -/

/- The textbook `n`-coordinate barrier is the `ι = Fin n` specialization of the finite-family
owner. -/
example (n : ℕ+) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ × ℝ → ℝ :=
  liftedConeLogSumExpBarrier

/- Definition 5.4.7.13 recalls the Chapter 5 owner for the lifted finite-family log-sum-exp
barrier. -/
recall liftedConeLogSumExpBarrier {ι : Type v} [Fintype ι] :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι × ℝ × ℝ → ℝ

/- The ambient owner is recalled through its canonical coordinate-sum bridge. -/
recall liftedConeLogSumExpBarrier_apply
    {ι : Type v} [Fintype ι] (x y : EuclideanSpace ℝ ι) (t τ : ℝ) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      ∑ i : ι, exponentialConeBarrier ((x i - t, y i), τ)

/- On the positive branch, the coordinate-sum owner reduces to the textbook logarithmic formula.
-/
recall liftedConeLogSumExpBarrier_apply_formula
    {ι : Type v} [Fintype ι] (x y : EuclideanSpace ℝ ι) (t τ : ℝ)
    (hτ : 0 < τ) (hy : ∀ i : ι, 0 < y i) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      -∑ i : ι,
        (Real.log (t + τ * Real.log (y i) - x i - τ * Real.log τ) +
          Real.log (y i) + Real.log τ)

end

/-! ### Definition_5_4_7_14 (from Chap05) -/
noncomputable section

open EuclideanSpace (positiveOrthant)

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.14 lies in the Chapter 5 positive-orthant / coordinatewise-scaling domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the chapter owner for the
  strict positive orthant;
* `EuclideanSpace.mem_positiveOrthant_iff` from `Chap01/Definition_1_10_2`, the coordinatewise
  membership bridge for that owner;
* `WithLp.toLp` from mathlib, the canonical constructor from coordinate families into
  `EuclideanSpace`;
* `EuclideanSpace` as the ambient `PiLp 2` owner, whose coordinates are already accessed
  pointwise.

Best owner abstraction:
* source-facing: `relativeDirection x h`, the textbook relative direction `δ_x(h)`;
* core/canonical: the strict-orthant owner `positiveOrthant n` together with the canonical
  ambient `EuclideanSpace` constructor `WithLp.toLp`;
* bridge/view: the coordinate formula `δ[x](h) i = h i / x i`.

Primitive data:
* a base point `x : positiveOrthant n`;
* a direction `h : ℝⁿ`.

Derived API:
* the owner definition `relativeDirection`;
* the scoped notation `δ[x](h)` for the textbook relative direction `δ_x(h)`;
* the coordinate projection lemma `relativeDirection_apply`.

The previous version routed the source-facing owner through ad hoc local `Div` and `CoeFun`
instances. This refinement keeps the same mathematical object, but defines it directly by its
canonical coordinate formula in `EuclideanSpace`; the public bridge API is therefore the textbook
coordinate identity itself, with no hidden instance scaffolding. -/

/-- Definition 5.4.7.14: for a strictly positive point `x ∈ ℝ^n_{++}` and a direction `h ∈ ℝⁿ`,
the relative direction `δ_x(h)` is the vector whose `i`-th coordinate is `h^(i) / x^(i)`. -/
def relativeDirection (x : Xₙ) (h : Eₙ) : Eₙ :=
  WithLp.toLp 2 fun i ↦ h i / (x : Eₙ) i

namespace RelativeDirection

/- Source-facing Lean notation for the textbook relative direction `δ_x(h)`. -/
scoped notation:max "δ[" x "](" h ")" => relativeDirection x h

end RelativeDirection

open scoped RelativeDirection

-- Proof sketch: `relativeDirection` is defined by the coordinate formula
-- `WithLp.toLp 2 (fun i ↦ h i / x i)`, so evaluation at `i` is definitional.
/-- Evaluating `δ[x](h)` at `i` recovers the coordinate quotient `h^(i) / x^(i)`. -/
@[simp] theorem relativeDirection_apply (x : Xₙ) (h : Eₙ) (i : Fin n) :
    δ[x](h) i = h i / (x : Eₙ) i :=
  rfl

-- Proof sketch: extensionality reduces the vector equality to coordinates, where
-- `relativeDirection_apply` gives `0 / x i = 0`.
/-- The relative direction of the zero vector is zero. -/
@[simp] theorem relativeDirection_zero (x : Xₙ) :
    δ[x]((0 : Eₙ)) = 0 :=
  by
    ext i
    change 0 / (x : Eₙ) i = 0
    simp

-- Proof sketch: extensionality reduces to coordinates, where `relativeDirection_apply` turns the
-- statement into `(h₁ i + h₂ i) / x i = h₁ i / x i + h₂ i / x i`.
/-- The relative direction is additive in the ambient direction argument. -/
theorem relativeDirection_add (x : Xₙ) (h₁ h₂ : Eₙ) :
    δ[x]((h₁ + h₂)) = δ[x](h₁) + δ[x](h₂) :=
  by
    ext i
    change (h₁ i + h₂ i) / (x : Eₙ) i = h₁ i / (x : Eₙ) i + h₂ i / (x : Eₙ) i
    rw [add_div]

-- Proof sketch: extensionality reduces to coordinates, where `relativeDirection_apply` turns the
-- statement into `(t * h i) / x i = t * (h i / x i)`.
/-- The relative direction commutes with scalar multiplication in the ambient direction. -/
theorem relativeDirection_smul (x : Xₙ) (t : ℝ) (h : Eₙ) :
    δ[x]((t • h)) = t • δ[x](h) :=
  by
    ext i
    change (t * h i) / (x : Eₙ) i = t * (h i / (x : Eₙ) i)
    rw [mul_div_assoc]

end

/-! ### Definition_5_4_7_15 (from Chap05) -/
noncomputable section

open scoped EuclideanOrthant

/- Definition 5.4.7.15 lies in the Chapter 5 positive-orthant / logarithmic-barrier domain.

Primary domain:
* the strict positive orthant and its standard logarithmic barrier.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the canonical owner and membership view for the strict positive
  orthant;
* `logarithmicBarrier` from `Chap01/Proposition_1_10_17`, the chapter owner for logarithmic
  barriers on strict inequality loci;
* `standardLogarithmicBarrier` from `Definition_5_4_3_2`, the intrinsic Chapter 5 specialization
  of that owner to `positiveOrthant n`;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the thin ambient bridge used by
  downstream self-concordance files.

Best owner abstraction:
* source-facing: `positiveOrthant n` together with its standard logarithmic barrier;
* core/canonical: the upstream owners `EuclideanSpace.positiveOrthant` and
  `standardLogarithmicBarrier`;
* bridge/view: `standardLogarithmicBarrierAmbient`.

Primitive data:
* the positive orthant owner `EuclideanSpace.positiveOrthant n`.

Derived API:
* the intrinsic barrier owner
  `standardLogarithmicBarrier n : C(↑(EuclideanSpace.positiveOrthant n), ℝ)`;
* the ambient bridge
  `standardLogarithmicBarrierAmbient n : EuclideanSpace ℝ (Fin n) → ℝ`.

This item is therefore recall-only. The file keeps no parallel local copy of the positive-orthant
barrier data and points directly to the existing owner declarations from Chapter 1 / Definition
5.4.3.2. -/

/- Definition 5.4.7.15 recalls the Chapter 1 positive orthant owner. -/
recall EuclideanSpace.positiveOrthant
    (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n))

/- The intrinsic positive-orthant logarithmic barrier is recalled from Definition 5.4.3.2. -/
recall standardLogarithmicBarrier
    (n : ℕ) :
    C(↑(ℝ₊₊^n), ℝ)

/- The ambient bridge for the same barrier is recalled through its canonical owner declaration. -/
recall standardLogarithmicBarrierAmbient
    (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ

end

/-! ### Definition_5_4_7_16 (from Chap05) -/
open scoped BigOperators

namespace StandardSimplex

/- Source-facing Lean notation for the textbook standard simplex `Δ_n` in `ℝⁿ`. -/
scoped[StandardSimplex] notation:max "Δ[" n:arg "]" => stdSimplex ℝ (Fin n)

end StandardSimplex

open scoped StandardSimplex

section

variable (n : ℕ)

/- Definition 5.4.7.16 lies in the finite-dimensional simplex / coordinate-vector domain.

Sampled owner declarations:
* mathlib `stdSimplex`, the canonical owner of the standard simplex;
* mathlib `stdSimplex_eq_inter`, the companion decomposition of the same owner into
  nonnegativity and normalization constraints;
* mathlib `Pi.one_apply`, the canonical coordinate formula for the constant-one function;
* `Definition_6_11`, a later project recall of the same simplex owner, reusing the same shared
  notation surface.

Best owner abstraction:
* source-facing: the textbook simplex `Δ_n`, exposed in Lean by the reusable notation `Δ[n]`, and
  the all-ones vector `\bar e_n` in `ℝⁿ`;
* core/canonical: `stdSimplex ℝ (Fin n)` and `(1 : Fin n → ℝ)`;
* bridge/view: the set-builder expansion of `stdSimplex` and the coordinate formula
  `(1 : Fin n → ℝ) i = 1`.

Primitive data:
* the dimension `n`.

Derived API:
* the defining set-builder equation for `Δ[n]`;
* the coordinatewise evaluation fact for the constant-one vector, already owned by
  `Pi.one_apply`.

This item is therefore recall-first. The file keeps no parallel local wrapper such as `barE`:
the all-ones vector is canonically the function `1`, and the simplex is canonically `stdSimplex`,
with the reusable source-facing notation `Δ[n]`.
-/

/- The exported notation `Δ[n]` is the canonical real `Fin n` specialization of the simplex
owner. -/
example : Set (Fin n → ℝ) := Δ[n]

/- Definition 5.4.7.16 recalls the canonical standard simplex owner. -/
recall stdSimplex
    (𝕜 : Type*) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι] :
    Set (ι → 𝕜)

/- Definition 5.4.7.16: in `ℝⁿ`, the standard simplex `Δ_n`, written in Lean as `Δ[n]`, is
definitionally the set of vectors with nonnegative coordinates and coordinate sum equal to `1`. -/
#check
  (show Δ[n] = {x : Fin n → ℝ | (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, x i = 1} from rfl)

variable (i : Fin n)

/- The textbook vector `\bar e_n = (1, \dots, 1)^{\mathsf T}` is the canonical constant-one
function in `ℝⁿ`. -/
#check (1 : Fin n → ℝ)

/- Every coordinate of the same vector is `1`, by the canonical owner theorem `Pi.one_apply`. -/
#check (show (1 : Fin n → ℝ) i = 1 from Pi.one_apply i)

end

/-! ### Definition_5_4_7_17 (from Chap05) -/
open scoped BigOperators StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.17 lies in the Chapter 5 simplex-monomial / positive-orthant domain.

Sampled owner declarations:
* `stdSimplex`, the canonical owner of the exponent simplex `Δₙ`;
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the chapter owner and membership bridge for the strict positive
  orthant `ℝⁿ₊₊`;
* `relativeDirection` together with the notation `δ[x](h)` from `Definition_5_4_7_14`, the
  nearby owner-level pattern for source-facing orthant objects in this subsection.

Best owner abstraction:
* source-facing: the simplex monomial `ξ_a`, written in Lean as `ξ_[a]`;
* core/canonical: `stdSimplex ℝ (Fin n)` for the exponent vector and `positiveOrthant n` for the
  domain;
* bridge/view: the ambient monomial `ambientMonomialXi a : Eₙ → ℝ`, whose restriction to
  `positiveOrthant n` is the source-facing owner `ξ_[a]`.

Primitive data:
* the simplex exponent `a : Δ[n]`.

Derived API:
* the ambient monomial on `ℝⁿ`;
* the source-facing monomial owner `ξ_[a]` on the canonical positive orthant;
* the evaluation lemmas relating the ambient and restricted views.

The previous file used a raw subtype presentation of the strict orthant. This refinement keeps the
same mathematical object but reuses the chapter owner `positiveOrthant n` for the domain, adds the
textbook notation `ξ_[a]`, and exposes the ambient `ℝⁿ` bridge needed by the nearby derivative
API. -/

/-- The ambient monomial `x ↦ x^a = ∏ i, (x^(i))^(a^(i))` on `ℝⁿ`. Its restriction to the
strict positive orthant is the source-facing owner `ξ_[a]`. -/
def ambientMonomialXi (a : Δ[n]) : Eₙ → ℝ :=
  fun x ↦ ∏ i : Fin n, Real.rpow (x i) (a i)

/-- Definition 5.4.7.17: for a simplex vector `a ∈ Δₙ`, `monomialXi a` is the monomial
`ξ_a(x) = x^a = ∏_{i=1}^n (x^(i))^(a^(i))` on the strict positive orthant `\mathbb{R}^n_{++}`. -/
def monomialXi (a : Δ[n]) : Xₙ → ℝ :=
  fun x ↦ ambientMonomialXi a x

namespace MonomialXi

/- Source-facing Lean notation for the textbook simplex monomial `ξ_a`. -/
scoped notation:max "ξ_[" a:arg "]" => monomialXi a

end MonomialXi

open scoped MonomialXi

/-- Evaluating the ambient monomial at `x : ℝⁿ` gives the coordinate product formula
`∏ i, (x^(i))^(a^(i))`. -/
@[simp] theorem ambientMonomialXi_apply
    (a : Δ[n])
    (x : Eₙ) :
    ambientMonomialXi a x = ∏ i : Fin n, Real.rpow (x i) (a i) :=
  rfl

-- Proof sketch: unfold `monomialXi`; its value is definitionally the finite product of the
-- coordinatewise real powers prescribed by the exponent vector `a`.
/-- Evaluating `ξ_[a]` at a positive vector `x` gives the textbook formula
`∏_{i=1}^n (x^(i))^(a^(i))`. -/
@[simp] theorem monomialXi_apply
    (a : Δ[n])
    (x : Xₙ) :
    ξ_[a] x = ∏ i : Fin n, Real.rpow ((x : Eₙ) i) (a i) :=
  rfl

/-- Restricting the ambient monomial to the strict positive orthant recovers the source-facing
owner `ξ_[a]`. -/
@[simp] theorem ambientMonomialXi_eq_monomialXi
    (a : Δ[n])
    (x : Xₙ) :
    ambientMonomialXi a x = ξ_[a] x :=
  rfl

end

/-! ### Definition_5_4_7_18 (from Chap05) -/
open scoped BigOperators RelativeDirection StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.18 lies in the Chapter 5 positive-orthant / simplex-weighted moment domain.

Sampled owner declarations:
* `relativeDirection` in `Definition_5_4_7_14`, the source-facing scaled direction `δ_x(h)`;
* `Finset.centerMass` and `Finset.centerMass_eq_of_sum_1`, the canonical finite weighted-average
  owner and its sum-`1` bridge;
* `stdSimplex.sum_eq_one` and `stdSimplex.zero_le`, the canonical simplex facts needed for
  weighted means and nonnegativity.

Source/core/bridge triage:
* source-facing: `quantityS2`, the textbook weighted centered second moment of `δ_x(h)`;
* core/canonical: `Finset.univ.centerMass a (δ[x](h))` for the simplex-weighted mean;
* bridge/view: the explicit coordinate-sum formulas for the mean and for `quantityS2`.

Primitive data:
* simplex weights `a : Δ[n]`;
* a base point `x : Xₙ`;
* a direction `h : Eₙ`.

Derived API:
* the center-of-mass specialization `Finset.univ.centerMass a (δ[x](h))`;
* the coordinate bridge `centerMass_relativeDirection_eq_sum`;
* the source-facing quantity `quantityS2` and its sum/nonnegativity lemmas.

The previous version introduced a separate owner `weightedRelativeDirectionMean` for a notion
already owned by `Finset.centerMass`, and it used the raw subtype presentation of the strict
orthant. This refinement keeps the same `S₂` quantity, but reuses the chapter owner
`positiveOrthant n` and the canonical finite weighted-average owner for the auxiliary mean. -/

-- Proof sketch: `a` lies in the standard simplex, so its coordinates sum to `1`. Therefore the
-- center of mass with weights `a` is exactly the weighted coordinate sum.
/-- The simplex-weighted mean of the relative direction is the coordinate sum
`∑ i, a^(i) δ^(i)`. -/
theorem centerMass_relativeDirection_eq_sum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    Finset.univ.centerMass a (δ[x](h)) =
      ∑ i : Fin n, a i * δ[x](h) i := by
  simpa [smul_eq_mul] using
    (show Finset.univ.centerMass a (δ[x](h)) = ∑ i : Fin n, a i • δ[x](h) i from
      Finset.univ.centerMass_eq_of_sum_1 (δ[x](h)) (stdSimplex.sum_eq_one a))

/-- Definition 5.4.7.18: the quantity `S₂` is the simplex-weighted second centered moment of the
relative direction `δ_x(h)`, centered by its simplex-weighted mean
`Finset.univ.centerMass a (δ[x](h))`. -/
def quantityS2 (a : Δ[n]) (x : Xₙ) (h : Eₙ) : ℝ :=
  a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (2 : ℕ)

-- Proof sketch: unfold `quantityS2`; the canonical dot-product notation `⬝ᵥ` is definitionally the
-- finite sum of the weighted squared centered coordinates.
/-- Evaluating `quantityS2` gives the textbook sum formula
`S₂ = ∑ i, a^(i) (δ^(i) - m)^2`, with `m = ⟪a, δ_x(h)⟫`. -/
theorem quantityS2_eq_sum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS2 a x h =
      ∑ i : Fin n,
        a i * (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (2 : ℕ) := by
  rfl

-- Proof sketch: each simplex weight `a i` is nonnegative and each square
-- `(δ[x](h) i - Finset.univ.centerMass a (δ[x](h)))^2` is nonnegative, so every
-- summand in `quantityS2_eq_sum` is nonnegative and the finite sum is nonnegative.
/-- The quantity `S₂` is nonnegative. -/
theorem quantityS2_nonneg
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    0 ≤ quantityS2 a x h := by
  rw [quantityS2_eq_sum]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  exact mul_nonneg (stdSimplex.zero_le a i) (by positivity)

end

/-! ### Definition_5_4_7_19 (from Chap05) -/
open scoped BigOperators RelativeDirection StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.19 is a source-facing centered-moment item in the chapter's positive-orthant /
simplex-weighted moment domain.

Sampled owner declarations:
* `relativeDirection` in `Definition_5_4_7_14`, the source-facing scaled direction `δ_x(h)`;
* `Finset.centerMass` and `Finset.centerMass_eq_of_sum_1`, the canonical finite weighted-average
  owner and its sum-`1` bridge;
* mathlib `dotProduct` / `⬝ᵥ`, the canonical owner for finite weighted sums of coordinatewise
  products;
* `quantityS2` in `Definition_5_4_7_18`, the immediately preceding source-facing weighted centered
  second moment built from the same owner data.

Best owner abstraction:
* source-facing: `quantityS3`, the weighted third centered moment of the relative direction
  `δ_x(h)`;
* core/canonical: `Finset.univ.centerMass a (δ[x](h))` for the simplex-weighted mean together
  with the `dotProduct` specialization
  `a ⬝ᵥ fun i ↦ (δ[x](h) i - Finset.univ.centerMass a (δ[x](h)))^3`;
* bridge/view: the explicit finite-sum expansion.

Primitive data:
* simplex weights `a : Δ[n]`;
* a base point `x : Xₙ`;
* a direction `h : Eₙ`.

Derived API:
* the center-of-mass specialization `Finset.univ.centerMass a (δ[x](h))`;
* the coordinate formula
  `S₃ = ∑ i, a i * (δ[x](h) i - Finset.univ.centerMass a (δ[x](h)))^3`.

The previous version exposed an auxiliary vector `delta` and center `m` as primitive data even
though the surrounding subsection canonically obtains both from `x`, `h`, and `a`. This
refinement keeps the same mathematical quantity `S₃`, but places it on the same source-facing
owner layer as `quantityS2`, with the mean derived canonically by `Finset.centerMass`.
-/

/-- Definition 5.4.7.19: the quantity `S₃` is the simplex-weighted third centered moment of the
relative direction `δ_x(h)`, centered by its simplex-weighted mean
`Finset.univ.centerMass a (δ[x](h))`. -/
def quantityS3 (a : Δ[n]) (x : Xₙ) (h : Eₙ) : ℝ :=
  a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (3 : ℕ)

-- Proof sketch: unfold `quantityS3`; the canonical dot-product notation `⬝ᵥ` is definitionally the
-- finite sum of the weighted cubed centered coordinates.
/-- Expanding `quantityS3` gives the coordinate formula
`S₃ = ∑ i, a^(i) (δ^(i) - m)^3`, with `m = Finset.univ.centerMass a (δ[x](h))`. -/
theorem quantityS3_eq_sum (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS3 a x h =
      ∑ i : Fin n,
        a i * (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (3 : ℕ) :=
  rfl

end

/-! ### Definition_5_4_7_2 (from Chap05) -/
noncomputable section

/- Definition 5.4.7.2 stays in the same planar power-cone barrier domain as
`Definition_5_4_7_1`.

Sampled owner declarations:
* `powerConeQ2` from `Definition_5_4_7_1`, the earlier source-facing owner for the planar cone
  `Q₂`;
* `secondOrderCone` and `secondOrderConeBarrier` from `Lemma_5_4_3_3`, the chapter owner/view for
  the same geometry in canonical `(x, t)` coordinates;
* `Prod.swap`, the canonical bridge between the source `(y, z)` coordinates and the owner
  `(z, y)` coordinates.

Source/core/bridge triage:
* source-facing: the textbook barrier on `Q₂`;
* core/canonical: `secondOrderConeBarrier`;
* bridge/view: the coordinate swap `Prod.swap`.

This file therefore keeps no second public barrier owner: Definition 5.4.7.2 is a recall of the
canonical barrier `secondOrderConeBarrier` seen in `(y, z)` coordinates through `Prod.swap`. -/

set_option linter.hashCommand false in
/- Definition 5.4.7.2 recalls the `(y, z)`-coordinate specialization of the canonical
second-order-cone barrier. -/
#check (secondOrderConeBarrier ∘ Prod.swap : (ℝ × ℝ) → ℝ)

-- Proof sketch: evaluate `secondOrderConeBarrier` at `(z, y)`.
/-- Evaluating the recalled swapped-coordinate second-order-cone barrier at `(y, z)` reproduces
the textbook formula `Φ(y, z) = -log (y^2 - z^2)`. -/
theorem secondOrderConeBarrier_swap_apply (y z : ℝ) :
    (secondOrderConeBarrier ∘ Prod.swap) (y, z) = -Real.log (y ^ (2 : ℕ) - z ^ (2 : ℕ)) := by
  simp [secondOrderConeBarrier_apply]

/-! ### Definition_5_4_7_20 (from Chap05) -/
noncomputable section
open EuclideanSpace (positiveOrthant)

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

private def hypographGap (ξ : Xₙ → ℝ) : Xₙ × ℝ → ℝ :=
  fun xt ↦ xt.2 - ξ xt.1

/- Definition 5.4.7.20 lies in the Chapter 5 positive-orthant / logarithmic-sublevel-barrier
domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the intrinsic owner for the
  strict positive orthant `ℝⁿ_{++}`;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the earlier Chapter 5 barrier
  owner on the same orthant domain;
* `sublevelLogBarrier` and `sublevelLogBarrier_apply` from `Theorem_5_1_4`, the canonical Chapter
  5 owner for logarithmic barriers of strict sublevel sets;
* ordinary product-space function evaluation on `Xₙ × ℝ`, the ambient owner layer for the scalar
  gap map `(x, t) ↦ t - ξ(x)`.

Best owner abstraction:
* source-facing: the hypograph domain `𝒟 = {(x, t) ∈ ℝⁿ_{++} × ℝ | t < ξ(x)}` and the barrier
  `Ψ(x, t) = -log (ξ(x) - t) + F(x)`;
* core/canonical: `sublevelLogBarrier (fun xt : Xₙ × ℝ ↦ xt.2 - ξ xt.1) 0`;
* bridge/view: the textbook membership and evaluation lemmas below.

Primitive data:
* the positive-orthant function `ξ : Xₙ → ℝ`;
* the base barrier term `F : Xₙ → ℝ`.

Derived API:
* the source-facing hypograph domain, expressed as the strict sublevel set of the gap map
  `(x, t) ↦ t - ξ(x)`;
* the source-facing barrier `hypographBarrierPsi F ξ`, obtained by adding `F(x)` to the canonical
  strict-sublevel logarithmic barrier.

This refinement keeps the textbook domain and barrier names, but deletes the duplicate raw
logarithmic-barrier body in favor of the Chapter 5 owner `sublevelLogBarrier`. -/

/-- The domain `𝒟 = {(x, t) ∈ ℝ^n_{++} × ℝ : t < ξ(x)}` attached to a function
`ξ : ℝ^n_{++} → ℝ`. -/
def hypographBarrierDomain (ξ : Xₙ → ℝ) : Set (Xₙ × ℝ) :=
  {xt | hypographGap ξ xt < 0}

-- Proof sketch: unfold `hypographBarrierDomain`; membership is exactly the strict inequality
-- `t < ξ(x)` defining the hypograph of `ξ` over the positive orthant.
/-- Membership in `hypographBarrierDomain ξ` means exactly that the scalar coordinate lies below
the value of `ξ` at the positive-orthant point. -/
@[simp]
theorem mem_hypographBarrierDomain_iff
    (ξ : Xₙ → ℝ) (x : Xₙ) (t : ℝ) :
    (x, t) ∈ hypographBarrierDomain ξ ↔ t < ξ x := by
  simp [hypographBarrierDomain, hypographGap]

/-- Definition 5.4.7.20: for functions `F, ξ : ℝ^n_{++} → ℝ`, the associated barrier on
`𝒟 = {(x, t) : t < ξ(x)}` is `Ψ(x, t) = -log (ξ(x) - t) + F(x)`. -/
def hypographBarrierPsi (F ξ : Xₙ → ℝ) : hypographBarrierDomain ξ → ℝ :=
  fun xt ↦ sublevelLogBarrier (hypographGap ξ) 0 xt.1 + F xt.1.1

-- Proof sketch: unfold `hypographBarrierPsi`; the subtype argument carries a pair `(x, t)` in the
-- domain, and evaluation substitutes that pair into the defining formula.
/-- Evaluating `hypographBarrierPsi F ξ` recovers the formula
`Ψ(x, t) = -log (ξ(x) - t) + F(x)` for a domain point `(x, t)`. -/
@[simp]
theorem hypographBarrierPsi_apply
    (F ξ : Xₙ → ℝ) (xt : hypographBarrierDomain ξ) :
    hypographBarrierPsi F ξ xt =
      -Real.log (ξ xt.1.1 - xt.1.2) + F xt.1.1 := by
  simp [hypographBarrierPsi, hypographGap, sublevelLogBarrier]

end

/-! ### Definition_5_4_7_21 (from Chap05) -/
open scoped BigOperators MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

/- Definition 5.4.7.21 lies in the Chapter 5 posynomial / positive-orthant domain.

Primary domain:
- finite positive linear combinations of simplex monomials on the strict positive orthant.

Relevant owner declarations sampled before refinement:
- `monomialXi` and `monomialXi_apply` in `Definition_5_4_7_17`, the chapter owner and evaluation
  bridge for the simplex monomials `ξ_[a]`;
- `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the ambient owner for the
  strict positive orthant `ℝⁿ₊₊`;
- `posynomialXi` in `Theorem_5_4_7_14`, the existing Chapter 5 owner for the same posynomial
  construction;
- `posynomialXi_apply` in `Theorem_5_4_7_14`, the canonical evaluation lemma on that owner.

Best owner abstraction:
- `posynomialXi`.

Primitive data:
- the positive coefficients `α : Fin m → Set.Ioi (0 : ℝ)`;
- the simplex exponents `a : Fin m → Δ[n]`.

Derived API:
- the owner declaration `posynomialXi`;
- the evaluation lemma `posynomialXi_apply`.

Source/core/bridge triage:
- source-facing: the posynomial `ξ(x) = ∑ₖ αₖ x^{aₖ}` on `ℝⁿ₊₊`;
- core/canonical: the Chapter 5 owner `posynomialXi`;
- bridge/view: the monomial notation `ξ_[(a k)]` used in the canonical evaluation formula.

The previous version rebuilt the same owner and its apply lemma locally. This file now reuses the
existing Chapter 5 declaration directly instead of keeping a parallel duplicate API.
-/

recall posynomialXi
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n]) :
    positiveOrthant n → ℝ

/- Evaluating the recalled owner keeps the Chapter 5 monomial surface `ξ_[(a k)]`, which is the
canonical source-facing notation for the monomials `x ↦ x^{aₖ}` introduced earlier in the same
subsection. -/
recall posynomialXi_apply
    (n m : ℕ)
    (α : Fin m → Set.Ioi (0 : ℝ))
    (a : Fin m → Δ[n])
    (x : positiveOrthant n) :
    posynomialXi n m α a x =
      ∑ k : Fin m, (α k : ℝ) * ξ_[(a k)] x

end

/-! ### Definition_5_4_7_22 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u}

/- Definition 5.4.7.22 lies in the Chapter 5 self-concordant-barrier / exponential-transform
domain.

Sampled owner-style declarations before refinement:
* `Set.restrict` from mathlib `Data/Set/Restrict`, the canonical owner for restricting an ambient
  map to a subtype domain;
* `barrierExponentialTransform` in `Lemma_5_3_1`, the ambient owner
  `x ↦ exp (-(F x / p))` for positive barrier parameters `p : NNRealˣ`;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` in `Lemma_5_3_1`, which already uses that
  ambient owner on `dom`;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` in `Lemma_5_3_1`, the source-facing
  Chapter 5 equivalence stated through the same ambient transform;
* `isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound` in `Theorem_5_3_7`, the
  downstream theorem that continues to use that ambient owner surface.

Best owner abstraction:
* core/canonical: `barrierExponentialTransform p F`;
* bridge/view: its canonical restriction `dom.restrict ...` to the source domain subtype.

Primitive data:
* the domain `dom`;
* the positive exponent parameter `p`;
* the barrier `F`.

Derived API:
* the direct source-domain view `dom.restrict (barrierExponentialTransform p F)`.

Source/core/bridge triage:
* source-facing: the function `ξₚ` on `dom`, viewed directly as the restricted ambient transform;
* core/canonical: the ambient exponential transform on `E`;
* bridge/view: this numbered file, which is recall-only because the exact restricted composite is
  already available from the upstream owners.

The previous version introduced the duplicate public wrapper `barrierExponent` for this restricted
composite. Under the chapter's exact-interface reuse rule, Definition 5.4.7.22 should instead stay
at direct recall/check surface for the canonical restriction of the ambient owner. -/

section

variable (dom : Set E) (p : NNRealˣ) (F : E → ℝ)

set_option linter.hashCommand false in
/- Definition 5.4.7.22 recalls the source-domain restriction of the Chapter 5 ambient exponential
transform. -/
#check (dom.restrict (barrierExponentialTransform p F) : dom → ℝ)

end

end
