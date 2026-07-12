import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` identified the canonical mathlib theorem
-- `Scheme.nonempty_of_isLimit` in `AlgebraicGeometry.AffineTransitionLimit`; the
-- source-facing statement below is its directed inverse system specialization.

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable [∀ i : OrderDual I, Nonempty ↥(D.obj i)]
variable [∀ i : OrderDual I, CompactSpace ↥(D.obj i)]

/-- Lemma 32.4.3: if `S = lim_i S_i` is the limit of a directed inverse system of schemes with
affine transition morphisms and every `S_i` is nonempty and quasi-compact, then `S` is
nonempty. -/
@[stacks 01Z2]
theorem nonempty_of_directedAffineTransition
    : Nonempty ↥c.pt := sorry

end

end AlgebraicGeometry
