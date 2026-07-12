import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-transition limit API
-- `isAffineHom_π_app` and `isLimitOpensCone` in `Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
-- together with `Scheme.isAffine_of_isLimit`; the source-facing statements below specialize that
-- canonical limit-cone API to directed inverse systems indexed by `OrderDual I`.

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- Lemma 32.2.2 (1): a directed inverse system of schemes with affine transition morphisms has a
limit in `Scheme`. -/
@[stacks 01YX]
theorem existsLimitConeOfDirectedAffineTransition :
    Nonempty (LimitCone D) := sorry

/-- Lemma 32.2.2 (2): each projection from the canonical limit scheme of a directed inverse system
of schemes with affine transition morphisms is affine. -/
@[stacks 01YX]
theorem isAffineHom_pi_app_of_directedAffineTransition
    (c : Cone D) (hc : IsLimit c) (i : OrderDual I) :
    IsAffineHom (c.π.app i) := sorry

/-- Lemma 32.2.2 (3): for a chosen stage `i₀` and open subscheme `U₀ ⊆ Sᵢ₀`, the pullback
open subscheme of a chosen limit scheme is the limit of the inverse-image diagram over the stages
above `i₀`, encoded by the canonical cone `opensCone D c i₀ U₀`. -/
@[stacks 01YX]
noncomputable def isLimitOpensCone_of_directedAffineTransition
    (c : Cone D) (hc : IsLimit c) (i₀ : OrderDual I) (U₀ : (D.obj i₀).Opens) :
    IsLimit (opensCone D c i₀ U₀) := sorry

/-- Companion normal-form theorem for the source-facing limit-on-opens construction. -/
theorem isLimitOpensCone_of_directedAffineTransition_def
    (c : Cone D) (hc : IsLimit c) (i₀ : OrderDual I) (U₀ : (D.obj i₀).Opens) :
    isLimitOpensCone_of_directedAffineTransition D c hc i₀ U₀ =
      AlgebraicGeometry.isLimitOpensCone D c hc i₀ U₀ := sorry

end

end AlgebraicGeometry
