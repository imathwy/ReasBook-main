import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine-transition limit API; local
-- Chapter 32 precedent represents absolute finite-type approximations as diagrams in
-- `Over (Spec (CommRingCat.of ℤ))` with affine transition maps and stage morphisms that are
-- quasi-compact and locally of finite type over `Spec(ℤ)`.

/-- Proposition 32.5.4: every quasi-compact and quasi-separated scheme is an inverse limit of
schemes of finite type over `ℤ` with affine transition morphisms. -/
@[stacks 01ZA]
theorem exists_absoluteNoetherianApproximation
    (S : Scheme) [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : OrderDual I ⥤ Over (Spec (CommRingCat.of ℤ)))
      (cS : Cone (D ⋙ Over.forget (Spec (CommRingCat.of ℤ))))
      (hcS : IsLimit cS) (eS : S ≅ cS.pt)
      (h_affine : ∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left)
      (h_qc : ∀ i : I, QuasiCompact (D.obj i).hom),
        ∀ i : I, LocallyOfFiniteType (D.obj i).hom := sorry

end AlgebraicGeometry
