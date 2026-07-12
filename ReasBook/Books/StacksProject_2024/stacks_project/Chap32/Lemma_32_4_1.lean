import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

-- Semantic recall: `lean_leansearch` pointed to `Types.limitEquivSections` for limits in
-- `Type` and to `Mathlib.AlgebraicGeometry.AffineTransitionLimit` for affine-transition limits of
-- schemes; the source-facing statement below packages the points-of-the-limit claim as
-- bijectivity of the canonical map into the compatible families of the underlying-set diagram.

/-- The projection family of a point of a limit cone is compatible with the transition maps of the
underlying-set diagram. -/
theorem limitPointProjectionCompatible_of_directedAffineTransition
    (c : Cone D) {i j : OrderDual I} (f : i ⟶ j) (x : c.pt) :
    (D.map f) ((c.π.app i) x) = (c.π.app j) x := sorry

/-- Lemma 32.4.1: if `c : Cone D` is a limit cone for a directed inverse system of schemes with
affine transition morphisms, then the underlying set of the limit scheme `c.pt` is the inverse
limit of the underlying-set diagram `D ⋙ Scheme.forget`, expressed as bijectivity of the canonical
map from a point to its compatible family of projections. -/
@[stacks 0CUE]
theorem bijectiveToUnderlyingSetSections_of_directedAffineTransition
    (c : Cone D) (hc : IsLimit c) :
    Function.Bijective
      (fun x : c.pt ↦
        (⟨fun i ↦ (c.π.app i) x,
          fun {i j} f ↦ limitPointProjectionCompatible_of_directedAffineTransition D c f x⟩ :
          (D ⋙ Scheme.forget).sections)) := sorry

end

end AlgebraicGeometry
