import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the scheme-morphism owner
-- `AlgebraicGeometry.LocallyOfFinitePresentation`; local Chapter 32 precedent in
-- Proposition 32.6.1 represents the displayed `Mor_S` comparison map by the canonical
-- `colimit.desc` map from the Yoneda image of a limit cone in `Over S`. The Stacks tag evidence
-- for this item is consistent with tag `0CM0`.

/-- Lemma 32.6.3: for a morphism `f : X ⟶ S`, if for every directed inverse system of
`S`-schemes with affine stages the canonical map
`colim_i Mor_S(T_i, X) ⟶ Mor_S(lim_i T_i, X)` is surjective, then `f` is locally of finite
presentation. -/
@[stacks 0CM0]
theorem locallyOfFinitePresentation_of_surjective_yoneda_mapCocone_of_affineStages
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsurj :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          Function.Surjective
            (colimit.desc _ ((yoneda.obj (Over.mk f)).mapCocone c.op))) :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry
