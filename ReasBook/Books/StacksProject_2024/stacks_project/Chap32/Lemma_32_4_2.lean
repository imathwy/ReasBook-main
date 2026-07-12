import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

-- Semantic recall: `lean_leansearch` surfaced the affine-transition limit API
-- `AlgebraicGeometry.isBasis_preimage_isAffineOpen`; the source-facing statement below packages
-- the resulting topology assertion as preservation of this limit cone by `Scheme.forgetToTop`.

/-- Lemma 32.4.2: if `S = lim_i S_i` is the limit of a directed inverse system of schemes with
affine transition morphisms, then the underlying topological space `S_top` is the inverse limit
of the underlying topological spaces `S_{i,top}`. -/
@[stacks 0CUF]
noncomputable def isLimit_forgetToTop_mapCone_of_directedAffineTransition
    (hc : IsLimit c) :
    IsLimit (Scheme.forgetToTop.mapCone c) := sorry

/-- The limiting cone on underlying topological spaces supplied by Lemma 32.4.2 has the expected
projection factorization property. -/
theorem isLimit_forgetToTop_mapCone_of_directedAffineTransition_fac
    (hc : IsLimit c) (s : Cone (D ⋙ Scheme.forgetToTop)) (i : OrderDual I) :
    (isLimit_forgetToTop_mapCone_of_directedAffineTransition D c hc).lift s ≫
      (Scheme.forgetToTop.mapCone c).π.app i = s.π.app i := sorry

end

end AlgebraicGeometry
