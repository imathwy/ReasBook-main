import Mathlib.Tactic.Recall
import BauschkeLean.Chap09.Proposition_9_42
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap24.Proposition_24_1

open InnerProductSpace
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section PerspectiveProximalFormula

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] scalar_prod_pseudoMetricSpace_l2
attribute [local instance] scalar_prod_normedAddCommGroup_l2
attribute [local instance] scalar_prod_normedSpace_l2
attribute [local instance] scalar_prod_completeSpace_l2
attribute [local instance] scalar_prod_innerProductSpace_l2

-- Semantic recall: `lean_leansearch` only surfaced generic inner-product recursion entries here,
-- so the owner/API choice was verified directly against the local Chapter 9 closed perspective
-- `closedPerspective`, the Chapter 13 conjugate packaging `φ∗[hφ]`, and the Chapter 12/24
-- `Prox` and `∂` surfaces already used throughout the repository.

/- Source/core/bridge triage:
- `source-facing`: Proposition 24.56 studies the proximal map of the perspective formula `(24.103)`
  attached to `φ`.
- `core/canonical`: the owner abstractions are the Chapter 9 closed perspective
  `closedPerspective`, the Chapter 13 conjugate owner `φ∗[hφ]`, and the Chapter 24 proximal
  residual/subdifferential bridge.
- `bridge/view`: the translated-set inclusion from the source is rewritten below in the equivalent
  residual form `x - γ • p ∈ α • ∂φ*(p)`, which is the canonical subdifferential surface already
  used elsewhere in the chapter. -/

/- Proposition 24.56 (1): under the stronger source hypothesis `dom φ* = H`, the `Γ₀(ℝ × H)`
statement for `(24.103)` is exactly the Chapter 9 owner theorem `closedPerspective_mem_gammaZero`.
-/
recall closedPerspective_mem_gammaZero

variable (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
variable (hdom_conj : effectiveDomain (φ∗[hφ]) = Set.univ)

/-- Proposition 24.56 (2): if `φ ∈ Γ₀(H)`, if `dom φ* = H`, if `γ ∈ ℝ_{++}`, and if
`ξ + γ φ*(γ⁻¹ • x) ≤ 0`, then the proximal point of the closed perspective `(24.103)` at
`(ξ, x)` is `(0, 0)`. -/
theorem scaledProx_closedPerspective_eq_zero_of_conjugate_test_nonpos
    (γ : PosReal) (ξ : ℝ) (x : H)
    (htest :
      (ξ : EReal) +
          ((γ : ℝ) : EReal) * (φ∗[hφ] ((γ : ℝ)⁻¹ • x) : EReal) ≤
        0) :
    Prox[γ, closedPerspective φ hφ.2.nonempty, closedPerspective_mem_gammaZero φ hφ] (ξ, x) =
      (0, 0) := sorry

/-- Proposition 24.56 (3): if `φ ∈ Γ₀(H)`, if `dom φ* = H`, if `γ ∈ ℝ_{++}`, and if
`0 < ξ + γ φ*(γ⁻¹ • x)`, then there is a unique `p` solving
`x - γ • p ∈ (ξ + γ φ*(p)) ∂ φ*(p)`. -/
theorem existsUnique_closedPerspective_subdifferential_inclusion_of_conjugate_test_pos
    (γ : PosReal) (ξ : ℝ) (x : H)
    (htest :
      0 <
        (ξ : EReal) +
          ((γ : ℝ) : EReal) * (φ∗[hφ] ((γ : ℝ)⁻¹ • x) : EReal)) :
    ∃! p : H,
      x - (γ : ℝ) • p ∈
        ((((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] p : EReal)).toReal) •
          (∂ (φ∗[hφ])) p) := sorry

/-- Proposition 24.56 (4): in the positive case of Proposition 24.56 (3), if `p` solves the
inclusion `x - γ • p ∈ (ξ + γ φ*(p)) ∂ φ*(p)`, then the proximal point of `(24.103)` is
`(ξ + γ φ*(p), x - γ • p)`. -/
theorem scaledProx_closedPerspective_eq_pair_of_conjugate_test_pos
    (γ : PosReal) (ξ : ℝ) (x : H)
    (htest :
      0 <
        (ξ : EReal) +
          ((γ : ℝ) : EReal) * (φ∗[hφ] ((γ : ℝ)⁻¹ • x) : EReal))
    {p : H}
    (hp :
      x - (γ : ℝ) • p ∈
        ((((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] p : EReal)).toReal) •
          (∂ (φ∗[hφ])) p)) :
    Prox[γ, closedPerspective φ hφ.2.nonempty, closedPerspective_mem_gammaZero φ hφ] (ξ, x) =
      ((((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] p : EReal)).toReal),
        x - (γ : ℝ) • p) := sorry

/-- Proposition 24.56 (5): if `p` solves the inclusion
`x - γ • p ∈ (ξ + γ φ*(p)) ∂ φ*(p)` and `φ*` is Gâteaux differentiable at `p` with gradient
`gradp`, then `p` satisfies `x = γ • p + (ξ + γ φ*(p)) • gradp`. -/
theorem differentiableSolution_eq_of_closedPerspective_subdifferential_inclusion
    (γ : PosReal) (ξ : ℝ) (x : H) {p gradp : H}
    (hp :
      x - (γ : ℝ) • p ∈
        ((((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] p : EReal)).toReal) •
          (∂ (φ∗[hφ])) p))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y ↦ ((φ∗[hφ] y : EReal).toReal))
        (toDualMap ℝ H gradp) p) :
    x =
        (γ : ℝ) • p +
          (((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] p : EReal)).toReal) • gradp := sorry

/-- Proposition 24.56 (6): if `p` is the unique solution of the inclusion
`x - γ • p ∈ (ξ + γ φ*(p)) ∂ φ*(p)` and `φ*` is Gâteaux differentiable at `p` with gradient
`gradp`, then `p` is the unique differentiable solution of
`x = γ • p + (ξ + γ φ*(p)) • ∇ φ*(p)`. -/
theorem unique_differentiableSolution_of_closedPerspective_subdifferential_inclusion
    (γ : PosReal) (ξ : ℝ) (x : H) {p gradp : H}
    (hp :
      x - (γ : ℝ) • p ∈
        ((((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] p : EReal)).toReal) •
          (∂ (φ∗[hφ])) p))
    (hp_unique :
      ∀ q : H,
        x - (γ : ℝ) • q ∈
            ((((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] q : EReal)).toReal) •
              (∂ (φ∗[hφ])) q) →
          q = p)
    (hgrad :
      HasGateauxDerivativeAt
        (fun y ↦ ((φ∗[hφ] y : EReal).toReal))
        (toDualMap ℝ H gradp) p) :
      x =
          (γ : ℝ) • p +
            (((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] p : EReal)).toReal) • gradp ∧
        ∀ q gradq : H,
          HasGateauxDerivativeAt
              (fun y ↦ ((φ∗[hφ] y : EReal).toReal))
              (toDualMap ℝ H gradq) q →
            x =
                (γ : ℝ) • q +
                  (((ξ : EReal) + ((γ : ℝ) : EReal) * (φ∗[hφ] q : EReal)).toReal) • gradq →
              q = p := sorry

end PerspectiveProximalFormula

end

end ERealFunction
