import StacksProject_2024.Chap32.Lemma_32_22_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open OrderDual (toDual)

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed `IsProper` as the canonical scheme-morphism
-- owner for properness. Local Lemma 32.22.4 supplies the tail-system owner
-- `InverseSystemMorphismOverBase` and its `IsLimitMorphism` predicate for the descended maps.

/-- Lemma 32.22.8: with notation and assumptions as in Lemma 32.22.4, if the limit
morphism `f` is proper, then for some later stage `i3 >= i0` every descended stage morphism
`f_i` for `i >= i3` is proper. -/
@[stacks 0CNV]
theorem exists_eventually_isProper_descendedStageMorphism_of_isProper
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i1 i2 : I}
    {Xsys : Over (toDual i1) ⥤ Scheme.{u}}
    {Ysys : Over (toDual i2) ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i1)
    (yToBase : Ysys ⟶ tailBaseDiagram D i2)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (toDual i1),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (toDual i2),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [QuasiCompact xToS] [LocallyOfFiniteType xToS]
    [QuasiSeparated yToS] [QuasiCompact yToS] [LocallyOfFiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i1 Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i2 Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS) [IsProper f]
    (i0 : I) (hi1 : i1 ≤ i0) (hi2 : i2 ≤ i0)
    (φ : InverseSystemMorphismOverBase D i0
      (restrictTail hi1 Xsys) (restrictTail hi2 Ysys)
      (restrictTailToBase D hi1 xToBase) (restrictTailToBase D hi2 yToBase))
    (hφ : φ.IsLimitMorphism (Cone.whisker
      (Over.map (homOfLE hi1 : toDual i0 ⟶ toDual i1))
      xCone)
      (Cone.whisker
        (Over.map (homOfLE hi2 : toDual i0 ⟶ toDual i2))
        yCone) f) :
    ∃ (i3 : I) (hi0i3 : i0 ≤ i3), ∀ ⦃i : I⦄ (hi3i : i3 ≤ i),
      IsProper (φ.hom.app (tailObject i (le_trans hi0i3 hi3i))) := sorry

end AlgebraicGeometry
