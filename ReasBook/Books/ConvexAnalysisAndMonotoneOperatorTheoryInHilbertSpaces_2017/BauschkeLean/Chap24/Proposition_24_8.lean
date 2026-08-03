import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap15.Proposition_15_7
import BauschkeLean.Chap15.Theorem_15_23

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

open InfimalConvolutionRegularity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: Proposition 24.8 studies explicit transformed functions built from `f`.
-- - `core/canonical`: the reusable proximal owners remain `Prox[γ, f, hf]`, `fᵛ`, `μ • f`,
--   and `f∗[hf]`.
-- - `bridge/view`: this file uses the existing repository translation and reflection lemmas
--   directly, and uses the Chapter 9 bridge `properIoi` only to package the raw `EReal`-valued
--   source function from part (8).

/-- The affine-quadratic perturbation
`f + (α / 2) ‖· - z‖² + ⟪·, u⟫ + β`
from Proposition 24.8 (1). -/
noncomputable def affineQuadraticTilt
    (f : H → Set.Ioi (⊥ : EReal)) (z u : H) (α : NNReal) (β : ℝ) :
    H → Set.Ioi (⊥ : EReal) :=
  f
    + (fun y : H ↦ ((α : ℝ) / 2) * ‖y - z‖ ^ 2).toEReal
    + (fun y : H ↦ ⟪y, u⟫_ℝ).toEReal
    + (fun _ : H ↦ β).toEReal

/-- The translate `τ_z f` from Proposition 24.8 (2), written pointwise as `y ↦ f (y - z)`,
again belongs to `Γ₀(H)`. -/
theorem translateSub_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (z : H) :
    (fun y : H ↦ f (y - z)) ∈ Γ₀(H) := by
  simpa [sub_eq_add_neg] using
    ERealFunction.translate_mem_gammaZero f hf (-z)

/-- The translated-linear perturbation `τ_z f - ⟪·, z⟫` from Proposition 24.8 (3). -/
noncomputable def translateSubInner (f : H → Set.Ioi (⊥ : EReal)) (z : H) :
    H → Set.Ioi (⊥ : EReal) :=
  (fun y : H ↦ f (y - z)) + (fun y : H ↦ -⟪y, z⟫_ℝ).toEReal

/-- The affine homothetic precomposition `y ↦ f (μ • y - z)` from Proposition 24.8 (5). -/
def affineHomothetyPrecomp (f : H → Set.Ioi (⊥ : EReal)) (μ : ℝ) (z : H) :
    H → Set.Ioi (⊥ : EReal) :=
  fun y : H ↦ f (μ • y - z)

/-- The affine-quadratic perturbation used in Proposition 24.8 (1) again belongs to `Γ₀(H)`. -/
theorem affineQuadraticTilt_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (z u : H) (α : NNReal) (β : ℝ) :
    affineQuadraticTilt f z u α β ∈ Γ₀(H) := sorry

/-- The translated-linear perturbation from Proposition 24.8 (3) again belongs to `Γ₀(H)`. -/
theorem translateSubInner_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (z : H) :
    translateSubInner f z ∈ Γ₀(H) := sorry

/-- Precomposing by an invertible operator whose inverse is its adjoint preserves `Γ₀(H)`. -/
theorem comp_invertible_adjoint_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] H) (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint) :
    f ∘ L ∈ Γ₀(H) := sorry

/-- The affine homothetic precomposition from Proposition 24.8 (5) again belongs to `Γ₀(H)`. -/
theorem affineHomothetyPrecomp_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {μ : ℝ} (hμ : μ ≠ 0) (z : H) :
    affineHomothetyPrecomp f μ z ∈ Γ₀(H) := sorry

/-- The shifted quadratic-minus-scaled perturbation
`(2 μ)⁻¹ ‖·‖² - μ f`
from Proposition 24.8 (8), viewed as an `EReal`-valued function before the canonical
Chapter 9 `properIoi` bridge. -/
noncomputable def shiftedQuadraticSubPosSmul
    (f : H → Set.Ioi (⊥ : EReal)) (μ : PosReal) :
    H → EReal :=
  fun y : H ↦
    ((((1 / (2 * (μ : ℝ))) * ‖y‖ ^ 2 : ℝ) : EReal) -
      ((μ : ℝ) : EReal) * (f y : EReal))

/-- The canonical `]-∞,+∞]`-valued owner attached to the shifted quadratic-minus-scaled
perturbation from Proposition 24.8 (8). -/
noncomputable def shiftedQuadraticSubPosSmulIoi
    (f : H → Set.Ioi (⊥ : EReal)) (μ : PosReal)
    (hproper : IsProper (shiftedQuadraticSubPosSmul f μ)) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (shiftedQuadraticSubPosSmul f μ) hproper

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Coercing the canonical `]-∞,+∞]`-valued owner for Proposition 24.8 (8) back to `EReal`
recovers the raw source formula. -/
@[simp] theorem shiftedQuadraticSubPosSmulIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (μ : PosReal)
    (hproper : IsProper (shiftedQuadraticSubPosSmul f μ)) (x : H) :
    (shiftedQuadraticSubPosSmulIoi f μ hproper x : EReal) =
      shiftedQuadraticSubPosSmul f μ x :=
  rfl

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The canonical `EReal` coercion of the `]-∞,+∞]`-valued owner for Proposition 24.8 (8) is
exactly the raw source formula. -/
@[simp] theorem asEReal_shiftedQuadraticSubPosSmulIoi
    (f : H → Set.Ioi (⊥ : EReal)) (μ : PosReal)
    (hproper : IsProper (shiftedQuadraticSubPosSmul f μ)) :
    (shiftedQuadraticSubPosSmulIoi f μ hproper).asEReal = shiftedQuadraticSubPosSmul f μ :=
  rfl

/-- The shifted quadratic-minus-scaled function from Proposition 24.8 (8) is proper. -/
theorem shiftedQuadraticSubPosSmul_isProper
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (μ : PosReal) :
    IsProper (shiftedQuadraticSubPosSmul f μ) := sorry

/-- The canonical `]-∞,+∞]`-valued owner from Proposition 24.8 (8) belongs to `Γ₀(H)`. -/
theorem shiftedQuadraticSubPosSmul_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (μ : PosReal) :
    shiftedQuadraticSubPosSmulIoi f μ (shiftedQuadraticSubPosSmul_isProper hf μ) ∈ Γ₀(H) := sorry

/-- Proposition 24.8 (1): for
`g = f + (α / 2) ‖· - z‖² + ⟪·, u⟫ + β`,
the proximal point of `g` at `x` is the proximal point of `f` with the scaled parameter and
shifted input shown in the source formula. -/
theorem prox_affineQuadraticTilt_eq_prox_scaled_shift
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (x z u : H) (γ : PosReal) (α : NNReal) (β : ℝ) :
    let η : PosReal :=
      ⟨(γ : ℝ) * (α : ℝ) + 1,
        add_pos_of_nonneg_of_pos (mul_nonneg γ.2.le α.2) zero_lt_one⟩
    Prox[γ, affineQuadraticTilt f z u α β, affineQuadraticTilt_mem_gammaZero hf z u α β] x =
      Prox[γ * η⁻¹, f, hf]
        ((η : ℝ)⁻¹ • (x + (γ : ℝ) • (((α : ℝ) • z) - u))) := sorry

/-- Proposition 24.8 (2): for the translate `g = τ_z f`, the proximal point satisfies
`Prox_(γ g) x = z + Prox_(γ f) (x - z)`. -/
theorem prox_translate_eq_add_prox_sub
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ : PosReal) (z x : H) :
    Prox[γ, (fun y : H ↦ f (y - z)), translateSub_mem_gammaZero hf z] x =
      z + Prox[γ, f, hf] (x - z) := sorry

/-- Proposition 24.8 (3): for `g = τ_z f - ⟪·, z⟫`, the proximal point satisfies
`Prox_(γ g) x = z + Prox_(γ f) x`. -/
theorem prox_translate_sub_inner_eq_add_prox
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ : PosReal) (z x : H) :
    Prox[γ, translateSubInner f z, translateSubInner_mem_gammaZero hf z] x =
      z + Prox[γ, f, hf] x := sorry

/-- Proposition 24.8 (4): if `L` is invertible and `L⁻¹ = L*`, then for `g = f ∘ L` one has
`Prox_(γ g) x = L* (Prox_(γ f) (L x))`. -/
theorem prox_comp_invertible_adjoint_eq_adjoint_prox
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ : PosReal) (L : H →L[ℝ] H) (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint)
    (x : H) :
    Prox[γ, f ∘ L, comp_invertible_adjoint_mem_gammaZero hf L hL hLadj] x =
      L.adjoint (Prox[γ, f, hf] (L x)) := sorry

/-- Proposition 24.8 (5): for `g = f (μ · - z)` with `μ ≠ 0`, the proximal point satisfies
`Prox_(γ g) x = μ⁻¹ (z + Prox_(γ μ² f) (μ x - z))`. -/
theorem prox_affineHomothetyPrecomp_eq_inv_smul_add_prox
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ : PosReal) {μ : ℝ} (hμ : μ ≠ 0) (z x : H) :
    let δ : PosReal := ⟨(γ : ℝ) * μ ^ (2 : ℕ), mul_pos γ.2 (sq_pos_of_ne_zero hμ)⟩
    Prox[γ, affineHomothetyPrecomp f μ z, affineHomothetyPrecomp_mem_gammaZero hf hμ z] x =
      (μ⁻¹ : ℝ) • (z + Prox[δ, f, hf] ((μ : ℝ) • x - z)) := sorry

/-- Proposition 24.8 (6): for the reflection `g = fᵛ`, the proximal point satisfies
`Prox_(γ g) x = - Prox_(γ f) (-x)`. -/
theorem prox_reverse_eq_neg_prox_neg
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ : PosReal) (x : H) :
    Prox[
      γ,
      Function.reverse f,
      reverse_mem_gammaZero_of_mem_gammaZero hf
    ] x =
      -Prox[γ, f, hf] (-x) := sorry

/-- Proposition 24.8 (7): for `g = μ f` with `μ ∈ ℝ_{++}`, the proximal point satisfies the
affine residual formula from the source. -/
theorem prox_posReal_smul_eq_add_scaled_residual
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ μ : PosReal) (x : H) :
    Prox[γ, μ • f, smul_mem_gammaZero f hf μ] x =
      x +
        ((γ : ℝ) * (((γ + μ : PosReal) : ℝ)⁻¹)) •
          (Prox[γ + μ, f, hf] x - x) := sorry

/-- Proposition 24.8 (8): for
`g = (2 μ)⁻¹ ‖·‖² - μ f`,
the proximal point satisfies
`Prox_(γ g) x = x - (γ / μ) Prox_((μ² / (μ + γ)) f) ((μ / (μ + γ)) x)`. -/
theorem prox_shiftedQuadraticSub_posReal_smul_eq_sub_scaled_prox
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ μ : PosReal) (x : H) :
    let δ : PosReal := μ * μ * (μ + γ)⁻¹
    Prox[
      γ,
      shiftedQuadraticSubPosSmulIoi f μ (shiftedQuadraticSubPosSmul_isProper hf μ),
      shiftedQuadraticSubPosSmul_mem_gammaZero hf μ
    ] x =
      x -
        ((γ : ℝ) / (μ : ℝ)) •
          (Prox[δ, f, hf] (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x)) := sorry

/-- Proposition 24.8 (9): for `g = f*`, the proximal point satisfies
`Prox_(γ g) x = x - γ Prox_(γ⁻¹ f) (γ⁻¹ x)`. -/
theorem prox_conjugate_eq_sub_scaled_primal_prox
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ : PosReal) (x : H) :
    Prox[γ, f∗[hf], gammaZeroConjugate_mem_gammaZero hf] x =
      x - (γ : ℝ) • (Prox[(γ⁻¹ : PosReal), f, hf] ((γ : ℝ)⁻¹ • x)) := sorry

end ERealFunction
