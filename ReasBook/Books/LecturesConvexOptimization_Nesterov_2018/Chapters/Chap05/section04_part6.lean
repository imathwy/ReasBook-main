import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_4_6_6 (from Chap05) -/
noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Definition 5.4.6.6 lies in the subsection's basic product-composition domain.

Sampled owner declarations:
* `fderiv`, the canonical mathlib owner for the auxiliary derivative term `Dξ(x)[h]`;
* `Prod.map`, the canonical product-map owner packaging `(x, z) ↦ (ξ x, z)`;
* `coneCompositionBarrier` in `Definition_5_4_6_5`, an adjacent source-facing owner file whose
  public API is a named function together with atomic evaluation lemmas.

Source/core/bridge triage:
* source-facing: the textbook potential `ψ(x, z) = Φ (ξ x, z)`;
* core/canonical: `Φ ∘ Prod.map ξ id`, while the auxiliary direction
  `l = (Dξ(x)[h], v)` is already the canonical pair `(fderiv ℝ ξ x h, v)`;
* bridge/view: the atomic evaluation lemma below.

Primitive data:
* the outer scalar map `Φ`;
* the map `ξ`.

Derived API:
* the canonical product-map composite for the source-facing potential.

The auxiliary lifted direction from the source,
`l = (Dξ(x)[h], v)`, is already the canonical pair `(fderiv ℝ ξ x h, v)`, so this file keeps no
separate public wrapper for it. -/

section CompositionPotential

variable (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃)

/-- Definition 5.4.6.6 (2): the textbook scalar potential `ψ(x, z) = Φ (ξ x, z)`. -/
abbrev compositionPotential : E₁ × E₃ → ℝ :=
  Φ ∘ Prod.map ξ id

/-- Evaluating `compositionPotential Φ ξ` at `(x, z)` recovers `Φ (ξ x, z)`. -/
@[simp] theorem compositionPotential_apply :
    compositionPotential Φ ξ (x, z) = Φ (ξ x, z) :=
  rfl

end CompositionPotential

/-! ### Definition_5_4_6_7 (from Chap05) -/
noncomputable section

universe u v w

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Definition 5.4.6.7 lies in the Fréchet-derivative/product-map domain.

Sampled owner-style declarations:
* `fderiv`
* `HasFDerivAt.prodMk`
* `DifferentiableAt.fderiv_prodMk`
* `fderiv_const_apply`

Best owner abstraction:
* source-facing: the directional derivative of the lifted map `y ↦ (ξ' y, v)` at `x` applied to
  `d`;
* core/canonical: `fderiv 𝕜 (fun y ↦ (ξ' y, v)) x d`;
* bridge/view: the component formula identifying this derivative with `(fderiv 𝕜 ξ' x d, 0)`.

Primitive data:
* `ξ'`, `v`, `x`, `d`;
* for the subsection-specialized bridge, the map `ξ` together with the repeated direction `d`.

Derived API:
* the componentwise derivative formula below;
* the subsection-specialized bridge `compositionSecondLiftedDirectionDerivative 𝕜 ξ x d =
  (D²ξ(x)[d, d], 0)`. -/

section

variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
variable [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
variable [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]

variable (ξ' : E₁ → E₂) (v : E₃) (x d : E₁)

/- Definition 5.4.6.7: for the lifted map `l(y) = (ξ' y, v)`, the textbook directional
derivative `Dl(x)[d]` is the canonical Fréchet derivative application below. -/
#check fderiv 𝕜 (fun y : E₁ ↦ (ξ' y, v)) x d

end

section LiftedSecondDerivative

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable [Zero E₃]

/-- The lifted derivative direction `l' = (D²ξ(x)[d, d], 0)` used in the subsection's
composition formulas. -/
abbrev compositionSecondLiftedDirectionDerivative
    (ξ : E₁ → E₂) (x d : E₁) : E₂ × E₃ :=
  (iteratedFDeriv ℝ 2 ξ x (fun _ ↦ d), 0)

end LiftedSecondDerivative

section LiftedSecondDerivativeEq

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable [Zero E₃]

/- If `ξ` is `C²` at `x`, then the product-space lift of `D²ξ(x)[d, d]` is the canonical pair
whose first component is the nested Fréchet derivative `D(Dξ(·)[d])(x)[d]`. -/
theorem compositionSecondLiftedDirectionDerivative_eq
    {ξ : E₁ → E₂} {x d : E₁}
    (hξ : ContDiffAt ℝ 2 ξ x) :
    compositionSecondLiftedDirectionDerivative ξ x d =
      (fderiv ℝ (fun y ↦ fderiv ℝ ξ y d) x d, (0 : E₃)) := by
  rw [compositionSecondLiftedDirectionDerivative]
  have hξ' : ContDiffAt ℝ 1 (fderiv ℝ ξ) x := by
    simpa using (show ContDiffAt ℝ (1 + 1) ξ x from hξ).fderiv_right_succ
  have hξfderiv :
      HasFDerivAt (fderiv ℝ ξ) (fderiv ℝ (fderiv ℝ ξ) x) x :=
    hξ'.differentiableAt_one.hasFDerivAt
  have hfd :
      HasFDerivAt (fun y ↦ fderiv ℝ ξ y d) ((fderiv ℝ (fderiv ℝ ξ) x).flip d) x := by
    simpa using hξfderiv.clm_apply (hasFDerivAt_const d x)
  rw [show fderiv ℝ (fun y ↦ fderiv ℝ ξ y d) x = (fderiv ℝ (fderiv ℝ ξ) x).flip d from
    hfd.fderiv]
  ext
  · simpa using iteratedFDeriv_two_apply ξ x (fun _ ↦ d)
  · rfl

end LiftedSecondDerivativeEq

/-! ### Definition_5_4_6_8 (from Chap05) -/
noncomputable section

open scoped HessianLocalNorm

universe u

variable {E₁ : Type u}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

/-
Definition 5.4.6.8 lies in the chapter's Hessian local-norm domain.

Source/core/bridge triage:
* source-facing: `sigmaThree F x h`, the local squared norm `σ₃`
* core/canonical: `hessianLocalNorm` / `‖h‖[F; x]`
* bridge/view: the comparison of `sigmaThree` with the raw Hessian quadratic form via
  `hessianLocalNorm_def` together with `Real.sq_sqrt`

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the chapter owner for the local norm
* `hessianLocalNorm_def` in `Chap05/Definition_5_1_1`, the canonical owner expansion

Best owner abstraction:
* `hessianLocalNorm`

Primitive data:
* a function `F`
* a base point `x`
* a direction `h`

Derived API:
* the local squared norm `sigmaThree F x h = ‖h‖[F; x]^2`
* the bridge back to `inner ℝ h (hessian F x h)` under the standard nonnegativity hypothesis,
  obtained by squaring `hessianLocalNorm_def`

The source-facing name `sigmaThree` therefore remains, but only as a thin view of the chapter
owner `hessianLocalNorm`, not as a second raw Hessian-level owner. -/

/-- Definition 5.4.6.8: the local squared norm in `\mathbb E_1` is the square of the chapter's
canonical Hessian local norm. -/
abbrev sigmaThree (F : E₁ → ℝ) (x h : E₁) : ℝ :=
  ‖h‖[F; x] ^ (2 : ℕ)

/- Expanding `sigmaThree F x h` gives the square of the canonical Hessian local norm. -/
theorem sigmaThree_def (F : E₁ → ℝ) (x h : E₁) :
    sigmaThree F x h = ‖h‖[F; x] ^ (2 : ℕ) :=
  rfl

/-- The local squared norm `sigmaThree F x h` is always nonnegative. -/
theorem sigmaThree_nonneg (F : E₁ → ℝ) (x h : E₁) :
    0 ≤ sigmaThree F x h :=
  sq_nonneg ‖h‖[F; x]

/-- Taking the square root of the local squared norm recovers the canonical Hessian local norm. -/
@[simp] theorem sqrt_sigmaThree (F : E₁ → ℝ) (x h : E₁) :
    Real.sqrt (sigmaThree F x h) = ‖h‖[F; x] := by
  rw [sigmaThree_def, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact hessianLocalNorm_nonneg F x h

/-- Under the standard pointwise nonnegativity hypothesis on the Hessian quadratic form,
`sigmaThree F x h` agrees with that quadratic form. -/
theorem sigmaThree_eq_inner_hessian
    (F : E₁ → ℝ) (x h : E₁) (hh : 0 ≤ inner ℝ h (hessian F x h)) :
    sigmaThree F x h = inner ℝ h (hessian F x h) := by
  simpa [sigmaThree, hessianLocalNorm_def] using Real.sq_sqrt hh

end

/-! ### Definition_5_4_6_9 (from Chap05) -/
noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

/- Definition 5.4.6.9 is a recall-only item in the subsection's directional differential-calculus
domain for the composed barrier `Ψ = coneCompositionBarrier F Φ ξ β`.

Sampled owner declarations:
* mathlib `lineDeriv`, the canonical first directional-derivative owner;
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for repeated second
  directional derivatives of real-valued functions;
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the corresponding third-order owner;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier whose
  directional derivatives are being recalled here.

Best owner abstraction:
* source-facing: the textbook quantities `D₁`, `D₂`, and `D₃` attached to `Ψ`;
* core/canonical: `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`
  applied to `coneCompositionBarrier F Φ ξ β`;
* bridge/view: none beyond this direct specialization.

Primitive data:
* the barrier `F`, outer term `Φ`, map `ξ`, and parameter `β`;
* the base point `(x, z)` and direction `(h, v)`.

Derived API:
* the three canonical owner expressions for the first, second, and third directional derivatives
  of `coneCompositionBarrier F Φ ξ β`.

Definition 5.4.6.9 introduces no new owner beyond those established derivative operators, so the
file recalls the canonical applications directly instead of keeping exact-interface wrapper aliases
with `rfl` companion lemmas. -/

section

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁) (v : E₃)

local notation "Ψ" => coneCompositionBarrier F Φ ξ β

/- Definition 5.4.6.9: for `Ψ(x, z) = Φ (ξ x, z) + β^3 F x`, the textbook quantities `D₁`, `D₂`,
and `D₃` are the following direct canonical directional-derivative owners applied to `Ψ`. -/
#check lineDeriv ℝ Ψ (x, z) (h, v)
#check secondDirectionalDerivative Ψ (x, z) (h, v)
#check thirdDirectionalDerivative Ψ (x, z) (h, v)

end

end

/-! ### Theorem_5_4_6_1 (from Chap05) -/
open scoped HessianLocalNorm

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Proof sketch: for a fixed interior point `x`, replace `h` by `-h`. The second directional
-- derivative and the Hessian local norm are even in `h`, while the third directional derivative
-- is odd, so the two displayed cone-membership conditions transform into one another.
/-- Theorem 5.4.6.1: for a map `ξ`, the cone-order bound
`D³ξ(x)[h,h,h] \preceq_K -3β D²ξ(x)[h,h] ‖h‖[F; x]` on `interior Q₁` is equivalent to the same
bound with `D³ξ(x)[h,h,h]` replaced by `-D³ξ(x)[h,h,h]`. The theorem is stated on the chapter's
owner surface for the vector-valued directional derivatives and the barrier Hessian local norm. -/
theorem betaCompatibility_sign_reversal_iff
    (Q₁ : Set E₁) (K : ConvexCone ℝ E₂) (F : E₁ → ℝ) (β : ℝ) (ξ : E₁ → E₂) :
    (∀ ⦃x : E₁⦄ (_ : x ∈ interior Q₁) (h : E₁),
      (3 * β * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) -
          vectorThirdDirectionalDerivative ξ x h ∈
        K) ↔
      ∀ ⦃x : E₁⦄ (_ : x ∈ interior Q₁) (h : E₁),
        (3 * β * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) +
            vectorThirdDirectionalDerivative ξ x h ∈
          K := by
  have h2 (x h : E₁) :
      vectorSecondDirectionalDerivative ξ x (-h) = vectorSecondDirectionalDerivative ξ x h := by
    calc
      vectorSecondDirectionalDerivative ξ x (-h)
          = (iteratedFDeriv ℝ 2 ξ x) (fun _ : Fin 2 ↦ (-1 : ℝ) • h) := by
              simp [vectorSecondDirectionalDerivative]
      _ = (∏ _ : Fin 2, (-1 : ℝ)) • (iteratedFDeriv ℝ 2 ξ x) (fun _ : Fin 2 ↦ h) := by
            rw [(iteratedFDeriv ℝ 2 ξ x).map_smul_univ (fun _ : Fin 2 ↦ (-1 : ℝ))
              (fun _ : Fin 2 ↦ h)]
      _ = vectorSecondDirectionalDerivative ξ x h := by
            norm_num [vectorSecondDirectionalDerivative]
  have h3 (x h : E₁) :
      vectorThirdDirectionalDerivative ξ x (-h) = -vectorThirdDirectionalDerivative ξ x h := by
    calc
      vectorThirdDirectionalDerivative ξ x (-h)
          = (iteratedFDeriv ℝ 3 ξ x) (fun _ : Fin 3 ↦ (-1 : ℝ) • h) := by
              simp [vectorThirdDirectionalDerivative]
      _ = (∏ _ : Fin 3, (-1 : ℝ)) • (iteratedFDeriv ℝ 3 ξ x) (fun _ : Fin 3 ↦ h) := by
            rw [(iteratedFDeriv ℝ 3 ξ x).map_smul_univ (fun _ : Fin 3 ↦ (-1 : ℝ))
              (fun _ : Fin 3 ↦ h)]
      _ = -vectorThirdDirectionalDerivative ξ x h := by
            norm_num [vectorThirdDirectionalDerivative]
  constructor <;> intro hbound x hx h
  · simpa [sub_eq_add_neg, h2, h3, hessianLocalNorm_neg] using hbound hx (-h)
  · simpa [sub_eq_add_neg, h2, h3, hessianLocalNorm_neg] using hbound hx (-h)

namespace IsBetaCompatibleWith

/-- A `β`-compatible map satisfies the sign-reversed pointwise cone-order bound from Theorem
5.4.6.1. -/
theorem compatibility_bound_sign_reversal
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal} {ξ : E₁ → E₂}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ) {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
    (3 * (β : ℝ) * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) +
        vectorThirdDirectionalDerivative ξ x h ∈ K := by
  exact
    (betaCompatibility_sign_reversal_iff Q₁ K F (β : ℝ) ξ).mp
      (fun {_} hx' h' ↦ hξ.compatibility_bound hx' h') hx h

end IsBetaCompatibleWith

/-! ### Theorem_5_4_6_10 (from Chap05) -/
open ProperCone
open scoped Gradient HessianLocalNorm

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.10 lies in the subsection's third-directional-derivative / sigma-bound domain.

Sampled owner declarations:
* `compositionPotential_thirdDirectionalDerivative_eq` from `Theorem_5_4_6_7`, the source-facing
  decomposition `(5.4.25)`;
* `compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo` from `Theorem_5_4_6_8`, the
  owner-level cross-term estimate;
* `yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility` from
  `Theorem_5_4_6_9`, the owner-level `β`-compatibility bound;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for the standard
  self-concordance hypothesis appearing in this item;
* `IsSelfConcordantOnWith.third_deriv_bound` and
  `IsSelfConcordantOnWith.hessian_isPositive` from `Definition_5_1_1`, the canonical
  quantitative self-concordance API recovered internally from that standard owner.

Source/core/bridge triage:
* source-facing: the textbook upper bound for the third directional derivative of the composition
  potential;
* core/canonical: the upstream theorems `Theorem_5_4_6_7`, `Theorem_5_4_6_8`, `Theorem_5_4_6_9`,
  and the standard self-concordance owner `IsStandardSelfConcordantOn`;
* bridge/view: the internal quantitative view `IsSelfConcordantOnWith dom 1 Φ` together with the
  source-facing scalars `compositionPotentialSigmaOne`, `compositionPotentialSigmaTwo`, and
  `sigmaThree`.

Primitive data:
* `F`, `Φ`, `ξ`, `β`, `x`, `z`, `d`;
* `ContDiffAt ℝ 3 ξ x`;
* the standard self-concordance owner `IsStandardSelfConcordantOn dom Φ`;
* the specialized local-norm estimate for the lifted derivative direction;
* the `β`-compatibility owner and the dual-cone hypothesis on `-∇ᵧ Φ(ξ(x), z)`.

Derived API:
* the final sigma-bound for the third directional derivative of the composition potential.

The public theorem should therefore be stated directly in terms of those owner-level inputs,
rather than exposing the intermediate outputs `hΔ₃`, `hCross`, `hBeta`, and the isolated
third-derivative estimate as primitive hypotheses. -/

-- Proof sketch: rewrite the third directional derivative using the decomposition into the third
-- derivative term of `Φ`, the mixed Hessian term, and the `y`-gradient pairing with
-- `D³ξ(x)[d, d, d]` using `Theorem_5_4_6_7`. Bound these three summands respectively by the
-- self-concordance owner API for `Φ`, `Theorem_5_4_6_8`, and `Theorem_5_4_6_9`, then add the
-- resulting inequalities.
/-- Theorem 5.4.6.10: if `ξ` is `C³` at `x`, if `Φ` is standard self-concordant on a domain
containing `(ξ(x), z)`, if the negative lifted derivative direction satisfies the specialized
local-norm estimate used in Theorem 5.4.6.8, and if `ξ` is `β`-compatible with the dual-cone
sign condition from Theorem 5.4.6.9, then the third directional derivative of
`x' ↦ Φ(ξ(x'), z)` is bounded above by
`2 σ₁^(3/2) + 3 σ₁^(1/2) σ₂ + 3 β σ₂ σ₃^(1/2)`, where
`σ₁ = compositionPotentialSigmaOne Φ ξ x z d`,
`σ₂ = compositionPotentialSigmaTwo Φ ξ x z d`, and
`σ₃ = sigmaThree F x d`. -/
theorem compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound
    {dom : Set (E₂ × E₃)} {Q₁ : Set E₁} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {β : NNReal} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x)
    (hΦ_self : IsStandardSelfConcordantOn dom Φ)
    (hyz : (ξ x, z) ∈ dom)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z d)
    (hξ_compat : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d ≤
      2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d)) ^ (3 : ℕ) +
        3 * Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
          compositionPotentialSigmaTwo Φ ξ x z d +
        3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z d *
          Real.sqrt (sigmaThree F x d) := by
  let _ : NormedSpace ℝ (E₂ × E₃) := InnerProductSpace.toNormedSpace
  let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0)
  have hΦ : ContDiffAt ℝ 3 Φ (ξ x, z) :=
    hΦ_self.contDiffOn.contDiffAt (hΦ_self.isOpen_domain.mem_nhds hyz)
  have hThirdDecomp :
      thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
        thirdDirectionalDerivative Φ (ξ x, z) l +
          (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
            (compositionSecondLiftedDirectionDerivative ξ x d) +
          inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
            (vectorThirdDirectionalDerivative ξ x d) := by
    simpa [l] using compositionPotential_thirdDirectionalDerivative_eq hξ hΦ
  have hThirdAbs :
      |thirdDirectionalDerivative Φ (ξ x, z) l| ≤
        2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d)) ^ (3 : ℕ) := by
    simpa [compositionPotentialSigmaOne_def, hessianLocalNorm_def] using
      hΦ_self.third_deriv_bound hyz l
  have hThird :
      thirdDirectionalDerivative Φ (ξ x, z) l ≤
        2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d)) ^ (3 : ℕ) :=
    le_trans (le_abs_self _) hThirdAbs
  have hH : (hessian Φ (ξ x, z)).IsPositive :=
    hΦ_self.hessian_isPositive hyz
  have hCrossBound :
      inner ℝ (hessian Φ (ξ x, z) l) (compositionSecondLiftedDirectionDerivative ξ x d) ≤
        Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
          compositionPotentialSigmaTwo Φ ξ x z d := by
    simpa using
      compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo hH
        hneg_liftedDirectionDerivative_le_sigmaTwo
  have hBetaBound :
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
          (vectorThirdDirectionalDerivative ξ x d) ≤
        3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z d *
          Real.sqrt (sigmaThree F x d) :=
    yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility hξ_compat hx
      hneg_yGradient_mem_innerDual
  rw [hThirdDecomp]
  linarith [hThird, hCrossBound, hBetaBound]

end

/-! ### Theorem_5_4_6_11 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

/- Theorem 5.4.6.11 lies in the subsection's slice-level second-directional-derivative domain.

Sampled owner declarations:
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing composed barrier owner;
* `compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo` from
  `Theorem_5_4_6_5`, the upstream owner for the fixed-`z` composition slice;
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for `D₂`;
* `sigmaThree` from `Definition_5_4_6_8`, the source-facing name for the barrier local squared
  norm.

Source/core/bridge triage:
* source-facing: the second-derivative formula and lower bound for the fixed-`z` slice
  `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`;
* core/canonical: `secondDirectionalDerivative`;
* bridge/view: the additive slice decomposition of `coneCompositionBarrier` together with the
  upstream identity `Δ₂ = σ₁ + σ₂`.

Primitive data:
* the standard self-concordance owner for `F` at `x`, used to identify the barrier part of the
  second derivative with `sigmaThree F x h`;
* the `C²` hypotheses on `ξ` and `Φ`, used by the upstream composition-potential owner;
* the parameter bound `1 ≤ β` for the lower bound.

Derived API:
* the slice decomposition
  `secondDirectionalDerivative (fun x' ↦ coneCompositionBarrier F Φ ξ β (x', z)) x h =
    secondDirectionalDerivative (fun x' ↦ compositionPotential Φ ξ (x', z)) x h + β^3 σ₃`;
* the rewritten equality
  `D₂ = compositionPotentialSigmaOne Φ ξ x z h + compositionPotentialSigmaTwo Φ ξ x z h + β^3 σ₃`;
* the lower bound
  `compositionPotentialSigmaOne Φ ξ x z h + compositionPotentialSigmaTwo Φ ξ x z h + β^2 σ₃ ≤ D₂`.

The public theorem surface therefore belongs on the fixed-`z` slice owner
`x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`, not on an arbitrary product direction
`(h, v)`. The upstream theorem `Theorem_5_4_6_5` remains the owner for
`Δ₂ = σ₁ + σ₂`, while this file supplies the source-facing bridge for the barrier term and
combines the two owner-level formulas into the textbook `D₂` identity and lower bound. -/

section SliceDecomposition

variable [NormedSpace ℝ E₂]

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁)

local notation "ψ" => fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)
local notation "Ψ" => fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)

-- Proof sketch: rewrite the directional slice of `Ψ` as the sum of the directional slice of
-- `ψ` and the scaled barrier slice `β^3 • directionalSlice F x h`. Additivity of
-- `secondDirectionalDerivative` on `C²` slices gives the decomposition
-- `D₂(Ψ) = D₂(ψ) + β^3 D₂(F)`. The standard self-concordance owner for `F` makes the Hessian
-- quadratic form nonnegative, so `D₂(F)` identifies with `sigmaThree F x h`.
/-- The second directional derivative of the fixed-`z` slice
`Ψ(x') = coneCompositionBarrier F Φ ξ β (x', z)` splits as the second directional derivative of
`ψ(x') = compositionPotential Φ ξ (x', z)` plus the barrier term `β^3 σ₃`, where
`σ₃ = sigmaThree F x h`. -/
theorem
    coneCompositionBarrier_slice_secondDirectionalDerivative_eq_compositionPotential_add_betaCube_sigmaThree
    {dom : Set E₁}
    (hF_self : IsStandardSelfConcordantOn dom F) (hx : x ∈ dom)
    (hξ : ContDiffAt ℝ 2 ξ x) (hΦ : ContDiffAt ℝ 2 Φ (ξ x, z)) :
    secondDirectionalDerivative Ψ x h =
      secondDirectionalDerivative ψ x h + ((β : ℝ) ^ 3) * sigmaThree F x h := by
  have hF_sigma : secondDirectionalDerivative F x h = sigmaThree F x h := by
    have hF3 : ContDiffAt ℝ 3 F x :=
      hF_self.contDiffOn.contDiffAt (hF_self.isOpen_domain.mem_nhds hx)
    have hF2 : ContDiffAt ℝ 2 F x := hF3.of_le (by norm_num)
    have hF_diff : DifferentiableAt ℝ F x := hF3.differentiableAt (by norm_num)
    have hF_fderiv : ContDiffAt ℝ 1 (fderiv ℝ F) x := by
      simpa using hF2.fderiv_right_succ
    have hgrad : DifferentiableAt ℝ (∇ F) x := by
      simpa [gradient] using
        (InnerProductSpace.toDual ℝ E₁).symm.differentiableAt.comp x
          (hF_fderiv.differentiableAt (by norm_num))
    rw [secondDirectionalDerivative_eq_hessian_quadratic_form hF_diff hgrad]
    symm
    exact sigmaThree_eq_inner_hessian F x h (hF_self.hessian_posSemidef hx h)
  have hψ : ContDiffAt ℝ 2 ψ x := by
    simpa [compositionPotential] using hΦ.comp x (hξ.prodMk contDiffAt_const)
  have hψ_slice : ContDiffAt ℝ 2 (directionalSlice ψ x h) 0 := by
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • h) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hψ' : ContDiffAt ℝ 2 ψ ((fun t : ℝ ↦ x + t • h) 0) := by
      simpa using hψ
    simpa [directionalSlice] using hψ'.comp 0 hline
  have hF2 : ContDiffAt ℝ 2 F x := by
    have hF3 : ContDiffAt ℝ 3 F x :=
      hF_self.contDiffOn.contDiffAt (hF_self.isOpen_domain.mem_nhds hx)
    exact hF3.of_le (by norm_num)
  have hF_slice : ContDiffAt ℝ 2 (directionalSlice F x h) 0 := by
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • h) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hF' : ContDiffAt ℝ 2 F ((fun t : ℝ ↦ x + t • h) 0) := by
      simpa using hF2
    simpa [directionalSlice] using hF'.comp 0 hline
  let g : ℝ → ℝ := ((β : ℝ) ^ 3) • directionalSlice F x h
  have hg : ContDiffAt ℝ 2 g 0 := by
    simpa [g] using ContDiffAt.const_smul ((β : ℝ) ^ 3) hF_slice
  have hslice : directionalSlice Ψ x h = directionalSlice ψ x h + g := by
    funext t
    simp [g, directionalSlice, coneCompositionBarrier, compositionPotential, smul_eq_mul]
  rw [secondDirectionalDerivative, hslice, iteratedDeriv_add hψ_slice hg]
  simp only [g, iteratedDeriv_const_smul_field]
  rw [show iteratedDeriv 2 (directionalSlice F x h) 0 = secondDirectionalDerivative F x h by
    rfl]
  rw [hF_sigma]
  rfl

end SliceDecomposition

section SigmaTheorems

variable [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁)

local notation "ψ" => fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)
local notation "Ψ" => fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)

-- Proof sketch: rewrite the directional slice of `Ψ` as the sum of the directional slice of
-- `ψ` and the scaled barrier slice `β^3 • directionalSlice F x h`. Additivity of
-- `secondDirectionalDerivative` on `C²` slices gives the decomposition
-- `D₂(Ψ) = D₂(ψ) + β^3 D₂(F)`. The standard self-concordance owner for `F` makes the Hessian
-- quadratic form nonnegative, so `D₂(F)` identifies with `sigmaThree F x h`.
-- Proof sketch: combine the slice decomposition above with the canonical upstream decomposition
-- `Δ₂ = σ₁ + σ₂` from `Theorem_5_4_6_5`.
/-- Theorem 5.4.6.11: if `F` is standard self-concordant at `x` and `ξ`, `Φ` are `C²` at the
relevant points, then the fixed-`z` slice
`Ψ(x') = coneCompositionBarrier F Φ ξ β (x', z)` satisfies
`D₂ = σ₁ + σ₂ + β^3 σ₃`, where `σ₁`, `σ₂`, and `σ₃` are the canonical subsection owners. -/
theorem
    coneCompositionBarrier_slice_secondDirectionalDerivative_eq_sigmaSum_add_betaCube_sigmaThree
    {dom : Set E₁}
    (hF_self : IsStandardSelfConcordantOn dom F) (hx : x ∈ dom)
    (hξ : ContDiffAt ℝ 2 ξ x) (hΦ : ContDiffAt ℝ 2 Φ (ξ x, z)) :
    secondDirectionalDerivative Ψ x h =
      compositionPotentialSigmaOne Φ ξ x z h +
        compositionPotentialSigmaTwo Φ ξ x z h +
          ((β : ℝ) ^ 3) * sigmaThree F x h := by
  have hψ : ContDiffAt ℝ 2 ψ x := by
    simpa [compositionPotential] using hΦ.comp x (hξ.prodMk contDiffAt_const)
  have hslice :=
    coneCompositionBarrier_slice_secondDirectionalDerivative_eq_compositionPotential_add_betaCube_sigmaThree
      F Φ ξ β x z h hF_self hx hξ hΦ
  rw [hslice]
  rw [compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo hξ hψ]

-- Proof sketch: rewrite `D₂` using the previous theorem, then use `β ≥ 1` and the automatic
-- nonnegativity of `sigmaThree F x h` to compare the coefficients `β^2` and `β^3`.
/-- If `β ≥ 1`, then the fixed-`z` slice decomposition yields the lower bound
`σ₁ + σ₂ + β^2 σ₃ ≤ D₂`, where
`D₂ = secondDirectionalDerivative (fun x' ↦ coneCompositionBarrier F Φ ξ β (x', z)) x h`
and `σ₃ = sigmaThree F x h`. -/
theorem
    coneCompositionBarrier_slice_secondDirectionalDerivative_ge_sigmaSum_add_betaSq_sigmaThree
    {dom : Set E₁}
    (hF_self : IsStandardSelfConcordantOn dom F) (hx : x ∈ dom)
    (hξ : ContDiffAt ℝ 2 ξ x) (hΦ : ContDiffAt ℝ 2 Φ (ξ x, z))
    (hβ : 1 ≤ β) :
    compositionPotentialSigmaOne Φ ξ x z h +
        compositionPotentialSigmaTwo Φ ξ x z h +
          ((β : ℝ) ^ 2) * sigmaThree F x h ≤
      secondDirectionalDerivative Ψ x h := by
  rw
    [coneCompositionBarrier_slice_secondDirectionalDerivative_eq_sigmaSum_add_betaCube_sigmaThree
      F Φ ξ β x z h hF_self hx hξ hΦ]
  have hβ_real : (1 : ℝ) ≤ (β : ℝ) := by
    exact_mod_cast hβ
  have hβ_nonneg : 0 ≤ (β : ℝ) := by
    exact_mod_cast β.2
  have hβsq : ((β : ℝ) ^ 2) ≤ (β : ℝ) ^ 3 := by
    nlinarith
  have hmul :
      ((β : ℝ) ^ 2) * sigmaThree F x h ≤ ((β : ℝ) ^ 3) * sigmaThree F x h :=
    mul_le_mul_of_nonneg_right hβsq (sigmaThree_nonneg F x h)
  linarith

end SigmaTheorems

end

/-! ### Theorem_5_4_6_12 (from Chap05) -/
noncomputable section

open ProperCone
open scoped Gradient HessianLocalNorm

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.12 lies in the subsection's fixed-`z` slice self-concordance domain.

Sampled owner declarations:
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier owner on
  `E₁ × E₃`;
* `compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound` from
  `Theorem_5_4_6_10`, the subsection owner upper bound for the composition-potential slice;
* `coneCompositionBarrier_slice_secondDirectionalDerivative_ge_sigmaSum_add_betaSq_sigmaThree`
  from `Theorem_5_4_6_11`, the slice-level second-derivative owner for the same barrier slice;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the compatibility owner supplying the hidden
  `β ≥ 1`, `C³`, and barrier inputs used by the slice estimates;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for the standard
  self-concordance hypothesis on `Φ`.

Source/core/bridge triage:
* source-facing: the fixed-`z` slice
  `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`;
* core/canonical: `thirdDirectionalDerivative` and `secondDirectionalDerivative`;
* bridge/view: the `D₃` upper bound from `Theorem_5_4_6_10`, the `D₂` lower bound from
  `Theorem_5_4_6_11`, and the compatibility-owner projections used to recover their hidden local
  hypotheses.

Primitive data:
* `F`, `Φ`, `ξ`, `β`, `x`, `z`, `h`;
* standard self-concordance of `Φ` on `interior Q₂` at `(ξ x, z)`;
* the lifted-direction local-norm bound and the dual-cone gradient hypothesis;
* the compatibility owner `IsBetaCompatibleWith Q₁ K F β ξ`.

Derived API:
* the slice self-concordance inequality
  `D₃ ≤ 2 D₂^(3/2)` for `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`.

This theorem should therefore sit directly on the existing `coneCompositionBarrier` slice owner
and depend on the slice-level `D₂` theorem from `5.4.6.11`, rather than reaching back to the
earlier sigma decomposition theorem and reassembling the barrier slice data locally. -/

section

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁)

local notation "Ψ" => fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)

-- Proof sketch: combine the third-derivative sigma bound from
-- `compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound` with the
-- second-derivative lower bound coming from
-- `coneCompositionBarrier_slice_secondDirectionalDerivative_ge_sigmaSum_add_betaSq_sigmaThree`
-- together with the barrier and regularity data packaged by `hξ_compat`, then apply the scalar
-- inequality
-- `t * (3 * s - t^2) ≤ 2 * s^(3/2)` to the resulting `σ₁`, `σ₂`, `σ₃` expression.
/-- Theorem 5.4.6.12: assume `Φ` is standard self-concordant at `(ξ x, z)`, `ξ` is
`β`-compatible with the barrier `F` on `Q₁`, and the local hypotheses used in
Theorem 5.4.6.10 hold for the slice `x' ↦ compositionPotential Φ ξ (x', z)`. The hidden
`β ≥ 1`, `C³`, and barrier inputs needed for the slice second-derivative estimate come from the
compatibility owner `hξ_compat`. Then the slice
`Ψ(x') = coneCompositionBarrier F Φ ξ β (x', z)` satisfies the third-derivative inequality
`D₃ ≤ 2 D₂^(3/2)` at `x` in direction `h`. -/
theorem coneCompositionBarrier_slice_selfConcordant_bound
    {Q₁ : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    (hΦ : IsStandardSelfConcordantOn (interior Q₂) Φ)
    (hyz : (ξ x, z) ∈ interior Q₂)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z h)
    (hξ_compat : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    thirdDirectionalDerivative Ψ x h ≤
      2 * (Real.sqrt (secondDirectionalDerivative Ψ x h)) ^ (3 : ℕ) := sorry

end

/-! ### Theorem_5_4_6_13 (from Chap05) -/
noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₁ × E₃)]
  [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)]
  [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.13 lies in the subsection's cone-composition self-concordant-barrier domain.

Sampled owner declarations:
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the source-facing feasible-set owner
  for the composed cone constraint;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier owner on
  `E₁ × E₃`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for barrier
  self-concordance on an open domain;
* `coneCompositionBarrier_slice_selfConcordant_bound` from `Theorem_5_4_6_12`, the slice-level
  self-concordance estimate feeding this global barrier statement.

Best owner abstraction:
* source-facing: the composed barrier `coneCompositionBarrier F Φ ξ β` on the composed feasible
  set `coneCompositionFeasibleSet Q K ξ Q₂`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: the pointwise formula `coneCompositionBarrier_apply` and the one-variable slice
  owner used in `Theorem_5_4_6_12`.

Primitive data:
* the cone-concavity owner `IsThreeTimesContDiffConcaveOnWith Q K ξ`;
* the compatibility owner `IsBetaCompatibleWith Q K F β ξ`;
* the barrier owners on `interior Q` and `interior Q₂`;
* convexity of `Q₂` and the recession-direction hypothesis for `K × {0}`.

Derived API:
* the final barrier owner on `interior (coneCompositionFeasibleSet Q K ξ Q₂)` with parameter
  `μ + β^3 ν`.

This theorem is therefore already at the right owner level: it should state the barrier result
directly for the existing feasible-set and composed-barrier owners, not through any extra local
wrapper or duplicated set/function definition. -/

section

variable {Q : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
  {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂}
  {β μ ν : NNReal}

-- Proof sketch: combine the cone-concavity of `ξ` and its `β`-compatibility with the
-- self-concordant barriers on `Q` and `Q₂` to verify the standard self-concordance and barrier
-- parameter inequalities for `coneCompositionBarrier F Φ ξ β`, whose pointwise formula is
-- `Φ (ξ x, z) + β^3 F x`, on the interior of `coneCompositionFeasibleSet Q K ξ Q₂`. The
-- recession-direction hypothesis for `K × {0}` is used to control the barrier part inherited
-- from `Φ`, and the resulting parameter is `μ + β^3 ν`.
/-- Theorem 5.4.6.13: if `ξ` is three-times continuously differentiable and concave with respect
to the cone `K`, if `ξ` is `β`-compatible with the barrier `F` on `Q`, if `Φ` is a
`μ`-self-concordant barrier on `interior Q₂`, if `Q₂` is convex, and if every direction
`(s, 0)` with `s ∈ K` is a recession direction of `Q₂`, then the composed function
`coneCompositionBarrier F Φ ξ β (x, z) = Φ (ξ x, z) + β^3 F x` is a `(\mu + β^3 ν)`-
self-concordant barrier on
`interior (coneCompositionFeasibleSet Q K ξ Q₂)`. -/
theorem coneCompositionBarrier_isSelfConcordantBarrierOnWith
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (hp : p ∈ Q₂) (τ : ℝ) (hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) :
    IsSelfConcordantBarrierOnWith
      (interior (coneCompositionFeasibleSet Q K ξ Q₂))
      (μ + β ^ 3 * ν)
      (coneCompositionBarrier F Φ ξ β) := sorry

end

end

/-! ### Theorem_5_4_6_2 (from Chap05) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 5.4.6.2 stays on the compatibility owner `IsBetaCompatibleWith`.

Sampled declarations in the same domain:
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the source-facing compatibility owner;
* mathlib `ConvexCone.smul_mem` and `ConvexCone.add_mem`, the ambient cone-owner closure API;
* `IsPositivelyHomogeneousOn.smul_mem` from `Chap03/Definition_3_1_7`, the chapter's bundled
  nonnegative-scalar owner surface;
* `IsThreeTimesContDiffConcaveOnWith` from `Definition_5_4_6_1`, the neighboring subsection owner
  on the same cone-ordered map space.

Source/core/bridge triage:
* source-facing: Theorem 5.4.6.2 on positive linear combinations of `β`-compatible maps;
* core/canonical: closure of `IsBetaCompatibleWith Q₁ K F β` under nonnegative scaling and
  addition, matching the cone-owner surface already used elsewhere in the chapter;
* bridge/view: the source-faithful positive-combination theorem built directly from that
  nonnegative closure API.

Primitive data:
* `Q₁`, `K`, `F`, `β`, and the map `ξ`.

Derived API:
* the owner-level closure theorems `IsBetaCompatibleWith.smul` and `IsBetaCompatibleWith.add`;
* the source-facing specialization `IsBetaCompatibleWith.pos_combination`.

The previous carrier-level cone wrapper duplicated the owner predicate with no extra mathematics, so
this refinement keeps only the closure statements on `IsBetaCompatibleWith` itself and aligns the
scalar-closure surface with the chapter's canonical nonnegative-scalar cone API. -/

namespace IsBetaCompatibleWith

variable {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal}

-- Proof sketch: scaling a `β`-compatible map by a bundled nonnegative scalar preserves convexity
-- and differentiability data, and multiplies both derivative terms in the compatibility
-- inequality by the same nonnegative factor. For `α > 0` this is the cone-owner closure
-- `K.smul_mem`; for `α = 0` the rescaled map is the zero map, whose compatibility expression is
-- the zero vector.
/-- `NNReal`-scalar multiples of a `β`-compatible map are again `β`-compatible with the same
barrier. -/
theorem smul
    {ξ : E₁ → E₂} (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (α : NNReal) :
    IsBetaCompatibleWith Q₁ K F β (α • ξ) := sorry

-- Proof sketch: the sum of two `β`-compatible maps preserves the shared convexity, interior,
-- parameter, and barrier data, while linearity of iterated derivatives turns the compatibility
-- expression for `ξ₁ + ξ₂` into the sum of the two corresponding expressions. Closure of `K`
-- under addition then gives the result.
/-- The sum of two `β`-compatible maps is again `β`-compatible with the same barrier. -/
theorem add
    {ξ₁ ξ₂ : E₁ → E₂}
    (hξ₁ : IsBetaCompatibleWith Q₁ K F β ξ₁)
    (hξ₂ : IsBetaCompatibleWith Q₁ K F β ξ₂) :
    IsBetaCompatibleWith Q₁ K F β (ξ₁ + ξ₂) := sorry

-- Proof sketch: apply the owner-level closure lemmas `IsBetaCompatibleWith.smul` to the two
-- positive coefficients viewed as `NNReal`, then combine the two resulting hypotheses with
-- `IsBetaCompatibleWith.add`.
/-- Theorem 5.4.6.2: positive linear combinations of `β`-compatible functions are again
`β`-compatible with the same self-concordant barrier. -/
theorem pos_combination
    {ξ₁ ξ₂ : E₁ → E₂} {α₁ α₂ : ℝ}
    (hξ₁ : IsBetaCompatibleWith Q₁ K F β ξ₁)
    (hξ₂ : IsBetaCompatibleWith Q₁ K F β ξ₂)
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    IsBetaCompatibleWith Q₁ K F β (α₁ • ξ₁ + α₂ • ξ₂) :=
  by
    simpa using
      IsBetaCompatibleWith.add
        (IsBetaCompatibleWith.smul hξ₁ ⟨α₁, hα₁.le⟩)
        (IsBetaCompatibleWith.smul hξ₂ ⟨α₂, hα₂.le⟩)

end IsBetaCompatibleWith

end

/-! ### Theorem_5_4_6_3 (from Chap05) -/
noncomputable section

open scoped PowerCone

/- Theorem 5.4.6.3 is a bridge/view statement in the chapter's power-cone domain.

Sampled declarations:
* `ConvexCone.positive` and `ConvexCone.mem_positive` for the scalar cone `ℝ₊`;
* `coneCompositionFeasibleSet` and `mem_coneCompositionFeasibleSet_iff` as the generic cone-
  composition owner;
* `powerConeGeometricMean`, `powerConeQ1`, `powerConeQ2`, and `powerCone` as the chapter's
  existing source-facing `K_α` owner data.

Owner choice:
* source-facing: `powerCone α`;
* core/canonical: `coneCompositionFeasibleSet`;
* bridge/view: the equality below.

This file therefore reuses the chapter owner `powerCone α` directly and does not introduce a
parallel local power-cone definition. After `Definition_5_4_7_1` is expressed through the owner
`coneCompositionFeasibleSet`, the bridge below is definitional rather than a second proof-level
reconstruction. -/

/-- Theorem 5.4.6.3: specializing `coneCompositionFeasibleSet` to the power-cone data
`Q₁ = powerConeQ1`, `K = ℝ₊`, `ξ = powerConeGeometricMean α`, and `Q₂ = powerConeQ2` recovers
the chapter's source-facing power cone `K_α = powerCone α`. The textbook assumptions
`0 < α < 1` are redundant for this set identity. -/
theorem coneCompositionFeasibleSet_eq_powerCone (α : ℝ) :
    coneCompositionFeasibleSet
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      (powerConeGeometricMean α)
      powerConeQ2 =
    K_[α] := by
  simp [powerCone]

/-! ### Theorem_5_4_6_4 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

local notation "Z" => WithLp 2 (E₂ × E₃)

private theorem fderiv_prod_eq_sum_partialGradient_pairings
    {Φ : E₂ × E₃ → ℝ} {y u : E₂} {z v : E₃}
    (hΦ : DifferentiableAt ℝ Φ (y, z)) :
    fderiv ℝ Φ (y, z) (u, v) =
      inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v := by
  have hleft :
      HasFDerivAt (fun y' : E₂ ↦ Φ (y', z))
        ((fderiv ℝ Φ (y, z)).comp (ContinuousLinearMap.inl ℝ E₂ E₃)) y := by
    simpa [Function.comp] using
      hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_left y z)
  have hright :
      HasFDerivAt (fun z' : E₃ ↦ Φ (y, z'))
        ((fderiv ℝ Φ (y, z)).comp (ContinuousLinearMap.inr ℝ E₂ E₃)) z := by
    simpa [Function.comp] using
      hΦ.hasFDerivAt.comp z (hasFDerivAt_prodMk_right y z)
  have hsplit : ((u, v) : E₂ × E₃) = (u, (0 : E₃)) + ((0 : E₂), v) := by
    ext <;> simp
  have hleft_apply :
      fderiv ℝ (fun y' : E₂ ↦ Φ (y', z)) y u =
        fderiv ℝ Φ (y, z) (u, (0 : E₃)) := by
    rw [hleft.fderiv]
    simp
  have hright_apply :
      fderiv ℝ (fun z' : E₃ ↦ Φ (y, z')) z v =
        fderiv ℝ Φ (y, z) ((0 : E₂), v) := by
    rw [hright.fderiv]
    simp
  calc
    fderiv ℝ Φ (y, z) (u, v)
        = fderiv ℝ Φ (y, z) (u, (0 : E₃)) + fderiv ℝ Φ (y, z) ((0 : E₂), v) := by
            rw [hsplit, map_add]
    _ = fderiv ℝ (fun y' : E₂ ↦ Φ (y', z)) y u +
          fderiv ℝ (fun z' : E₃ ↦ Φ (y, z')) z v := by
            rw [← hleft_apply, ← hright_apply]
    _ = inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
          inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v := by
            rw [← inner_gradient_left hleft.differentiableAt,
              ← inner_gradient_left hright.differentiableAt]

omit [CompleteSpace E₂] [CompleteSpace E₃] in
private theorem compositionPotential_hasFDerivAt
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x : E₁} {z : E₃}
    (hξ : DifferentiableAt ℝ ξ x) (hΦ : DifferentiableAt ℝ Φ (ξ x, z)) :
    HasFDerivAt (compositionPotential Φ ξ)
      ((fderiv ℝ Φ (ξ x, z)).comp
        ((fderiv ℝ ξ x).prodMap (ContinuousLinearMap.id ℝ E₃))) (x, z) := by
  have hmap_has :
      HasFDerivAt (Prod.map ξ (id : E₃ → E₃))
        ((fderiv ℝ ξ x).prodMap (ContinuousLinearMap.id ℝ E₃)) (x, z) := by
    simpa using HasFDerivAt.prodMap (x, z) hξ.hasFDerivAt (hasFDerivAt_id z)
  simpa [compositionPotential, Function.comp] using hΦ.hasFDerivAt.comp (x, z) hmap_has

private theorem compositionPotential_fderiv_eq_sum_partialGradient_pairings
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z v : E₃}
    (hξ : DifferentiableAt ℝ ξ x) (hΦ : DifferentiableAt ℝ Φ (ξ x, z)) :
    fderiv ℝ (compositionPotential Φ ξ) (x, z) (h, v) =
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)) (fderiv ℝ ξ x h) +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) v := by
  have hcomp :
      fderiv ℝ (compositionPotential Φ ξ) (x, z) (h, v) =
        fderiv ℝ Φ (ξ x, z) (fderiv ℝ ξ x h, v) := by
    rw [(compositionPotential_hasFDerivAt hξ hΦ).fderiv]
    simp
  calc
    fderiv ℝ (compositionPotential Φ ξ) (x, z) (h, v)
        = fderiv ℝ Φ (ξ x, z) (fderiv ℝ ξ x h, v) := hcomp
    _ = inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)) (fderiv ℝ ξ x h) +
          inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) v :=
      fderiv_prod_eq_sum_partialGradient_pairings hΦ

-- Proof sketch: differentiate the map `(x, z) ↦ (ξ x, z)` at `(x, z)`, obtaining the lifted
-- direction `(Dξ(x)[h], v)`, and then apply the chain rule together with the gradient pairing
-- formula for the directional derivative of `Φ` at `(ξ x, z)`.
/-- Theorem 5.4.6.4: under the auxiliary data from Definition 5.4.6.6, if `ξ` is
differentiable at `x` and `Φ` is differentiable at `(ξ x, z)`, then the first directional
derivative of `ψ(x, z) = Φ (ξ x, z)` in direction `(h, v)` splits into the `y`-gradient term
paired with `Dξ(x)[h]` and the `z`-gradient term paired with `v`. -/
theorem compositionPotential_lineDeriv_eq_sum_partialGradient_pairings
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z v : E₃}
    (hξ : DifferentiableAt ℝ ξ x) (hΦ : DifferentiableAt ℝ Φ (ξ x, z)) :
    lineDeriv ℝ (compositionPotential Φ ξ) (x, z) (h, v) =
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)) (fderiv ℝ ξ x h) +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) v := by
  rw [(compositionPotential_hasFDerivAt hξ hΦ).differentiableAt.lineDeriv_eq_fderiv]
  exact compositionPotential_fderiv_eq_sum_partialGradient_pairings hξ hΦ

-- Proof sketch: identify the gradient of the ambient bridge
-- `w ↦ Φ w.ofLp` on the canonical `L²` product owner `Z = WithLp 2 (E₂ × E₃)` with the pair of
-- partial gradients, then expand the `L²` inner product against
-- `WithLp.toLp 2 (Dξ(x)[h], v)`.
/-- With the canonical `L²` product inner-product structure on `Z = WithLp 2 (E₂ × E₃)`, the
sum of the partial-gradient pairings is the ambient gradient pairing of `w ↦ Φ w.ofLp` against
the lifted direction `WithLp.toLp 2 (u, v)`. -/
theorem sum_partialGradient_pairings_eq_inner_gradient_pair
    {Φ : E₂ × E₃ → ℝ} {y u : E₂} {z v : E₃}
    (hΦ : DifferentiableAt ℝ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z))) :
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v =
      inner ℝ
        (∇ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z)))
        (WithLp.toLp 2 (u, v)) := by
  have hΦraw : DifferentiableAt ℝ Φ (y, z) := by
    simpa using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).comp_right_differentiableAt_iff).1 hΦ
  have hchain :
      fderiv ℝ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z))
          (WithLp.toLp 2 (u, v)) =
        fderiv ℝ Φ (y, z) (u, v) := by
    have hchain_has :
        HasFDerivAt (fun w : Z ↦ Φ w.ofLp)
          ((fderiv ℝ Φ (y, z)).comp
            (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap)
          (WithLp.toLp 2 (y, z)) := by
      simpa [Function.comp] using
        hΦraw.hasFDerivAt.comp (WithLp.toLp 2 (y, z))
          (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).hasFDerivAt
    rw [hchain_has.fderiv]
    rfl
  calc
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u +
        inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) v
      = fderiv ℝ Φ (y, z) (u, v) := by
          symm
          exact fderiv_prod_eq_sum_partialGradient_pairings hΦraw
    _ = fderiv ℝ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z))
          (WithLp.toLp 2 (u, v)) := hchain.symm
    _ = inner ℝ
          (∇ (fun w : Z ↦ Φ w.ofLp) (WithLp.toLp 2 (y, z)))
          (WithLp.toLp 2 (u, v)) := by
          rw [← inner_gradient_left hΦ]

/-! ### Theorem_5_4_6_5 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Theorem 5.4.6.5 lies in the chapter's composed directional-differentiation domain.

Sampled owner declarations:
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for scalar second
  directional derivatives;
* `vectorSecondDirectionalDerivative` from `Definition_5_4_6_2`, the chapter owner for
  `D²ξ(x)[d, d]`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical Hessian owner;
* `compositionPotential` from `Definition_5_4_6_6`, the source-facing owner for
  `ψ(x, z) = Φ(ξ(x), z)`.

Source/core/bridge triage:
* source-facing: the decomposition `Δ₂ = σ₁ + σ₂` for `ψ(x, z) = Φ(ξ(x), z)`;
* core/canonical: `secondDirectionalDerivative`, `vectorSecondDirectionalDerivative`, and
  `hessian`;
* bridge/view: the fixed-`z` slice `fun x' ↦ compositionPotential Φ ξ (x', z)` together with the
  canonical lifted pair `(fderiv ℝ ξ x d, 0)`.

Primitive data:
* `Φ`, `ξ`, `x`, `z`, `d`.

Derived API:
* the Hessian term `compositionPotentialSigmaOne`;
* the mixed term `compositionPotentialSigmaTwo`.

The previous raw `iteratedFDeriv` duplicate for `Δ₂` is deleted in favor of the chapter owner
`secondDirectionalDerivative`, and the mixed term now reuses
`vectorSecondDirectionalDerivative` instead of repeating its defining formula. -/

section SigmaOne

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable [NormedAddCommGroup E₃]
variable [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/-- The Hessian quadratic term `σ₁ = ⟪∇² Φ(ξ(x), z) l, l⟫` in the decomposition of `Δ₂`. -/
abbrev compositionPotentialSigmaOne
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) : ℝ :=
  let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0)
  inner ℝ l (hessian Φ (ξ x, z) l)

-- Proof sketch: unfold `compositionPotentialSigmaOne`.
/-- Expanding `compositionPotentialSigmaOne Φ ξ x z d` gives the Hessian quadratic form of `Φ`
at `(ξ(x), z)` in the lifted direction `l = (Dξ(x)[d], 0)`. -/
theorem compositionPotentialSigmaOne_def
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) :
    compositionPotentialSigmaOne Φ ξ x z d =
      inner ℝ (fderiv ℝ ξ x d, (0 : E₃))
        (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃))) :=
  rfl

end SigmaOne

section SigmaTwo

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- The mixed term `σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫` in the decomposition of `Δ₂`. -/
abbrev compositionPotentialSigmaTwo
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) : ℝ :=
  inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
    (vectorSecondDirectionalDerivative ξ x d)

-- Proof sketch: unfold `compositionPotentialSigmaTwo`.
/-- Expanding `compositionPotentialSigmaTwo Φ ξ x z d` gives the pairing of the `y`-gradient of
`Φ` with the second directional derivative `D²ξ(x)[d, d]`. -/
theorem compositionPotentialSigmaTwo_def
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) :
    compositionPotentialSigmaTwo Φ ξ x z d =
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorSecondDirectionalDerivative ξ x d) :=
  rfl

end SigmaTwo

section MainTheorem

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
variable [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

-- Proof sketch: differentiate the fixed-`z` slice `x' ↦ compositionPotential Φ ξ (x', z)` along
-- the repeated direction `d`. The chain rule produces the Hessian quadratic term in the lifted
-- direction `l = (Dξ(x)[d], 0)`, and differentiating `l` contributes the pairing of the
-- `y`-gradient of `Φ` with `D²ξ(x)[d, d]`; the `z`-component contributes nothing because it is
-- constantly zero.
/-- Theorem 5.4.6.5: for `ψ(x, z) = Φ(ξ(x), z)`, if
`Δ₂ = D² (fun x' ↦ compositionPotential Φ ξ (x', z))(x)[d, d]`,
`σ₁ = ⟪∇² Φ(ξ(x), z) l, l⟫` with `l = (Dξ(x)[d], 0)`,
and `σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫`,
then the decomposition `(5.4.24)` reads `Δ₂ = σ₁ + σ₂`. -/
theorem compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 2 ξ x)
    (hψ : ContDiffAt ℝ 2 (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x) :
    secondDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
      compositionPotentialSigmaOne Φ ξ x z d +
        compositionPotentialSigmaTwo Φ ξ x z d := sorry

end MainTheorem

end

/-! ### Theorem_5_4_6_6 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u v w

open Set Topology

/- Theorem 5.4.6.6 lies in the subsection's self-concordant-barrier / recession-direction /
composition domain.

Sampled owner declarations:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for a
  `μ`-self-concordant barrier on an open convex domain;
* `IsSelfConcordantOn` from `Definition_5_1_1`, the chapter pattern for passing from a
  quantitative owner with an auxiliary constant to the source-facing existential owner when that
  constant is not part of the public statement;
* `compositionPotentialSigmaTwo` from `Theorem_5_4_6_5`, the source-facing owner for `σ₂`;
* `compositionSecondLiftedDirectionDerivative` from `Definition_5_4_6_7`, the source-facing owner
  for the lifted derivative direction `l' = (D²ξ(x)[d, d], 0)`;
* `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction` from
  `Corollary_5_3_2`, the canonical barrier-owner recession-direction inequality;
* mathlib `Convex.add_smul_mem_interior`, the convex-interior bridge that transfers a recession
  direction of `Q₂` to one of `interior Q₂`.

Best owner abstraction:
* `∃ μ : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ`.

Source/core/bridge triage:
* source-facing: the nonnegativity conclusion for `σ₂` under the recession-direction hypothesis on
  `-l'`;
* core/canonical: the quantitative barrier owner `IsSelfConcordantBarrierOnWith` on `Φ` over
  `interior Q₂`;
* bridge/view: the lifted product direction `compositionSecondLiftedDirectionDerivative ξ x d`
  together with the internal `WithLp 2 (E₂ × E₃)` pullback used to apply the ambient pairing
  theorem.

Primitive data:
* `Φ`, `ξ`, `x`, `d`, `z`, the set `Q₂`, and the recession-direction hypothesis on `-l'`;
* the convexity of `Q₂`;
* the source-facing existence of some barrier parameter for `Φ` on `interior Q₂`.

Derived API:
* the lifted second derivative `l' = (D²ξ(x)[d, d], 0)` from `Definition_5_4_6_7`;
* the internal pullback barrier `w ↦ Φ w.ofLp` on the canonical `L²` product owner;
* the recession transfer from `Q₂` to `interior Q₂`;
* the nonpositivity of the ambient gradient pairing with the recession direction `-l'`.

The local public API should therefore stay on the source-facing existence of a barrier owner for
`Φ` on `interior Q₂`; the numerical barrier parameter is auxiliary proof data, the canonical `L²`
pullback is only an internal bridge, and the public statement must make the convexity of `Q₂`
explicit because that hypothesis is exactly what moves the recession-direction assumption from
`Q₂` to the barrier domain `interior Q₂`. -/

section SigmaTwoNonneg

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

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

local notation "Z" => WithLp 2 (E₂ × E₃)
local notation "ofZ" => (WithLp.ofLp : Z → E₂ × E₃)

-- Proof sketch: pull the barrier back along `WithLp.ofLp` to the canonical `L²` product owner,
-- rewrite `σ₂` as the ambient gradient pairing of that pullback barrier with the lifted direction
-- `WithLp.toLp 2 l'`, transfer the recession-direction hypothesis on `-l'` from the convex set
-- `Q₂` to the barrier domain `interior Q₂`, and then apply
-- `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction`.
/-- Theorem 5.4.6.6: if the negative lifted derivative direction `-l'` is a recession direction
of `Q₂`, and if `Φ` is some self-concordant barrier on `interior Q₂`, then the term `σ₂` is
nonnegative. -/
theorem compositionPotentialSigmaTwo_nonneg_of_neg_liftedDirectionDerivative_recession
    {Q₂ : Set (E₂ × E₃)} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hQ₂_convex : Convex ℝ Q₂)
    (hΦ : ∃ μ : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hyz : (ξ x, z) ∈ interior Q₂)
    (hrecession :
      ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ →
        p + τ • (-compositionSecondLiftedDirectionDerivative ξ x d) ∈ Q₂) :
    0 ≤ compositionPotentialSigmaTwo Φ ξ x z d := by
  rcases hΦ with ⟨μ, hΦμ⟩
  let l' : E₂ × E₃ := compositionSecondLiftedDirectionDerivative ξ x d
  let g : Z →ᴬ[ℝ] E₂ × E₃ :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap).toContinuousAffineMap
  let hΦZ : IsSelfConcordantBarrierOnWith (ofZ ⁻¹' interior Q₂) μ (Φ ∘ ofZ) := by
    simpa [g, Function.comp] using
      IsSelfConcordantBarrierOnWith.comp_continuousAffineMap hΦμ g
  have hyzZ : WithLp.toLp 2 (ξ x, z) ∈ ofZ ⁻¹' interior Q₂ := by
    simpa using hyz
  have hrecessionZ :
      ∀ ⦃w : Z⦄, w ∈ ofZ ⁻¹' interior Q₂ →
        ∀ τ : ℝ, 0 ≤ τ → w + τ • WithLp.toLp 2 (-l') ∈ ofZ ⁻¹' interior Q₂ := by
    intro w hw τ hτ
    let p : E₂ × E₃ := w.ofLp
    let d' : E₂ × E₃ := -l'
    let q : E₂ × E₃ := p + (2 * τ) • d'
    have hp : p ∈ interior Q₂ := by
      simpa [p] using hw
    have hq : q ∈ Q₂ := by
      simpa [p, d', q, l'] using hrecession (interior_subset hp) (2 * τ) (by positivity)
    have hp' : q + (-(2 * τ)) • d' ∈ interior Q₂ := by
      convert hp using 1
      simp [p, d', q, add_assoc]
    have hmid :=
      hQ₂_convex.add_smul_mem_interior hq hp' (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc 0 1)
    have hsum : (2 * τ) • d' + -τ • d' = τ • d' := by
      rw [← add_smul]
      have hcoeff : (2 * τ : ℝ) + -τ = τ := by ring
      rw [hcoeff]
    have hinterior : p + τ • d' ∈ interior Q₂ := by
      convert hmid using 1
      rw [show q = p + (2 * τ) • d' by rfl, smul_smul]
      have hcoeff : (1 / 2 : ℝ) * (-(2 * τ)) = -τ := by ring
      rw [hcoeff]
      simpa [p, d', q, add_assoc] using congrArg (fun v : E₂ × E₃ ↦ p + v) hsum.symm
    simpa [p, d'] using hinterior
  let hstdZ : IsStandardSelfConcordantOn (ofZ ⁻¹' interior Q₂) (Φ ∘ ofZ) :=
    hΦZ.toIsStandardSelfConcordantOn
  have hdiffZ : DifferentiableAt ℝ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z)) := by
    simpa using
      (hstdZ.contDiffOn.contDiffAt (hstdZ.isOpen_domain.mem_nhds hyzZ)).differentiableAt
        (by norm_num)
  have hsigma :
      compositionPotentialSigmaTwo Φ ξ x z d =
        inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l') := by
    have hpair :
        inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) (ξ x))
            (vectorSecondDirectionalDerivative ξ x d) +
          inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) (0 : E₃) =
            inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l') :=
      by
        simpa [l', compositionSecondLiftedDirectionDerivative] using
          (@sum_partialGradient_pairings_eq_inner_gradient_pair
            E₂ E₃ _ _ _ _ _ _
            Φ (ξ x) (vectorSecondDirectionalDerivative ξ x d) z (0 : E₃) hdiffZ)
    simpa [compositionPotentialSigmaTwo_def] using hpair
  have hnonpos :
      inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 (-l')) ≤ 0 :=
    hΦZ.inner_gradient_nonpos_of_recession_direction hrecessionZ hyzZ
  have hnonneg :
      0 ≤ inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l') := by
    have hneg :
        -(inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l')) ≤ 0 := by
      simpa using hnonpos
    linarith
  simpa [hsigma] using hnonneg

end SigmaTwoNonneg

end

/-! ### Theorem_5_4_6_7 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.7 lies in the chapter's composed third-order directional-differentiation domain.

Sampled owner declarations:
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for scalar repeated
  third directional derivatives;
* `vectorThirdDirectionalDerivative` from `Definition_5_4_6_2`, the chapter owner for
  `D³ξ(x)[d, d, d]`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical owner for the mixed second-order term;
* `compositionPotential` from `Definition_5_4_6_6` together with
  `compositionSecondLiftedDirectionDerivative` from `Definition_5_4_6_7`, the subsection's
  source-facing composition owners.

Source/core/bridge triage:
* source-facing: the decomposition `(5.4.25)` for the third directional derivative of
  `ψ(x, z) = Φ(ξ(x), z)`;
* core/canonical: `thirdDirectionalDerivative`, `hessian`, and
  `vectorThirdDirectionalDerivative`;
* bridge/view: the canonical lifted pair `(fderiv ℝ ξ x d, 0)` and
  `compositionSecondLiftedDirectionDerivative`.

Primitive data:
* `Φ`, `ξ`, `x`, `z`, `d`.

Derived API:
* the third directional derivative of the fixed-`z` composition;
* the lifted direction `l = (Dξ(x)[d], 0)`;
* the derivative `l' = Dl(x)[d]`;
* the gradient pairing with `D³ξ(x)[d, d, d]`.

The theorem surface should therefore use the existing owner vocabulary for all three summands:
`thirdDirectionalDerivative Φ (ξ x, z) l`, the mixed Hessian pairing with the lifted derivative
`compositionSecondLiftedDirectionDerivative ξ x d`, and the final pairing with
`vectorThirdDirectionalDerivative ξ x d`, instead of exposing parallel raw `iteratedFDeriv` and
raw `fderiv` spellings. -/

-- Proof sketch: differentiate the second-derivative decomposition from
-- `compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo` once more along the
-- repeated direction `d`. The chain rule gives the third derivative of `Φ` in the lifted
-- direction `l = (Dξ(x)[d], 0)`, differentiating the Hessian quadratic form contributes the
-- coefficient `3` in front of the mixed Hessian pairing with `l' = (D²ξ(x)[d, d], 0)`, and the
-- remaining term is the pairing of the `y`-gradient of `Φ` with `D³ξ(x)[d, d, d]`.
/-- Theorem 5.4.6.7: the third directional derivative `Δ₃ = D³ψ(x, z)[d, d, d]` of
`ψ(x, z) = Φ(ξ(x), z)` is the sum of the third derivative of `Φ` in the lifted direction
`l = (Dξ(x)[d], 0)`, three times the mixed Hessian pairing with
`l' = (D²ξ(x)[d, d], 0)`, and the pairing of `∇ᵧ Φ(ξ(x), z)` with `D³ξ(x)[d, d, d]`. -/
theorem compositionPotential_thirdDirectionalDerivative_eq
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x)
    (hΦ : ContDiffAt ℝ 3 Φ (ξ x, z)) :
    let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0);
    thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
      thirdDirectionalDerivative Φ (ξ x, z) l +
        (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
          (compositionSecondLiftedDirectionDerivative ξ x d) +
        inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
          (vectorThirdDirectionalDerivative ξ x d) := sorry

end
