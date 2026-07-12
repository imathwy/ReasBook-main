import StacksProject_2024.Chap32.Lemma_32_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced mathlib's canonical smoothness owner
-- `AlgebraicGeometry.IsSmooth`; local Chapter 29/32 files use the source-facing abbreviation
-- `Smooth f`, with Lemma 32.22.4 supplying the descended tail morphisms.

/-- Lemma 32.22.7: with notation and assumptions as in Lemma 32.22.4, if the limit
morphism `f` is smooth, then for some later stage `i3 >= i0` every descended stage morphism
`f_i` for `i >= i3` is smooth. -/
@[stacks 0CNU]
theorem exists_eventually_smooth_descendedStageMorphism_of_smooth
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i0 : I}
    {Xsys Ysys : TailIndexCategory i0 ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i0)
    (yToBase : Ysys ⟶ tailBaseDiagram D i0)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : TailIndexCategory i0,
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : TailIndexCategory i0,
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [QuasiCompact xToS] [LocallyOfFiniteType xToS]
    [QuasiSeparated yToS] [QuasiCompact yToS] [LocallyOfFiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i0 Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i0 Ysys yCone yToS)
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    (hφ : φ.IsLimitMorphism xCone yCone f) (hf_smooth : Smooth f) :
    ∃ (i3 : I) (hi0i3 : i0 ≤ i3), ∀ ⦃i : I⦄ (hi3i : i3 ≤ i),
      Smooth (φ.hom.app (tailObject i (le_trans hi0i3 hi3i))) := sorry

end AlgebraicGeometry
