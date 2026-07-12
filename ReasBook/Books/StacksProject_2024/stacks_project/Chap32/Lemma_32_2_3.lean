import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the ambient scheme-limit API
-- `Scheme.isAffine_of_isLimit`; local mathlib inspection of
-- `AlgebraicGeometry/AffineTransitionLimit.lean` then fixes the source-faithful base-change owner
-- for stages over `i₀` as `Over.post D ⋙ Over.pullback t ⋙ Over.forget _`, with the induced cone
-- coming from `((Over.conePost D i₀).obj c)`.

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- The inverse system `i ↦ T ×_{Sᵢ₀} Sᵢ` over the stages above `i₀`. -/
noncomputable def baseChangeDiagramOfDirectedAffineTransition
    (i₀ : OrderDual I) {T : Scheme.{u}} (t : T ⟶ D.obj i₀) :
    Over i₀ ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback t ⋙ Over.forget _

/-- The canonical cone on the stagewise base changes induced from a limit cone of `D`. -/
noncomputable def baseChangeConeOfDirectedAffineTransition
    (c : Cone D) (i₀ : OrderDual I) {T : Scheme.{u}} (t : T ⟶ D.obj i₀) :
    Cone (baseChangeDiagramOfDirectedAffineTransition D i₀ t) :=
  (Over.pullback t ⋙ Over.forget _).mapCone ((Over.conePost D i₀).obj c)

/-- Lemma 32.2.3: if `c` is a limit cone on a directed inverse system of schemes with affine
transition morphisms and `t : T ⟶ Sᵢ₀` is a scheme over a chosen stage `Sᵢ₀`, then the pullback
`T ×_{Sᵢ₀} lim_i Sᵢ` is the limit of the base-changed inverse system
`i ↦ T ×_{Sᵢ₀} Sᵢ` over the stages above `i₀`. -/
@[stacks 01YZ]
theorem exists_isLimit_baseChangeCone_of_directedAffineTransition
    (c : Cone D) (hc : IsLimit c) (i₀ : OrderDual I) {T : Scheme.{u}} (t : T ⟶ D.obj i₀) :
    Nonempty (IsLimit (baseChangeConeOfDirectedAffineTransition D c i₀ t)) := sorry

end

end AlgebraicGeometry
