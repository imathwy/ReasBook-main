import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `AlgebraicGeometry.LocallyOfFinitePresentation`. Local Chapter 32 precedent represents
-- directed inverse systems by diagrams `D : OrderDual I ⥤ Scheme`; for systems over a base `S`,
-- the canonical source-facing owner is the slice diagram `D : OrderDual I ⥤ Over S`. The Stacks
-- source tag evidence for this item is consistent with tag `01ZC`.

/-- Proposition 32.6.1 (1): for a morphism `f : X ⟶ S`, being locally of finite presentation is
equivalent to saying that for every directed inverse system of `S`-schemes with affine stages,
the canonical cocone on the sets of `S`-morphisms into `X` is a colimit. This is the Lean form of
`Mor_S(lim_i T_i, X) = colim_i Mor_S(T_i, X)`. -/
@[stacks 01ZC]
theorem locallyOfFinitePresentation_iff_isColimit_yoneda_mapCocone_of_affineStages
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          Nonempty (IsColimit ((yoneda.obj (Over.mk f)).mapCocone c.op)) := sorry

/-- Proposition 32.6.1 (2): the same local finite-presentation condition is equivalent to the
corresponding Hom-colimit assertion for every directed inverse system of `S`-schemes with affine
transition maps and quasi-compact, quasi-separated stages. -/
@[stacks 01ZC]
theorem locallyOfFinitePresentation_iff_isColimit_yoneda_mapCocone_of_qcqsAffineTransition
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
          IsLimit c →
          (∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left) →
          (∀ i : I, CompactSpace ↥((D.obj i).left)) →
          (∀ i : I, QuasiSeparatedSpace ↥((D.obj i).left)) →
          Nonempty (IsColimit ((yoneda.obj (Over.mk f)).mapCocone c.op)) := sorry

end AlgebraicGeometry
