import StacksProject_2024.stacks_project.Chap32.Lemma_32_22_4
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism flatness owner
-- `AlgebraicGeometry.Flat`. Local Chapter 32 precedent keeps the Lemma 32.22.4 setup as tail
-- inverse systems over `OrderDual I`, with finite-presentation approximation systems and
-- cartesian conclusions expressed by `IsPullback`.

/-- The category of indices in the tail of a preorder above `i₀`, viewed inside the order-dual
index category used by inverse systems. -/
abbrev TailIndexCategory {I : Type u} [Preorder I] (i₀ : I) : Type u :=
  let j : OrderDual I := i₀
  Over j

/-- Fixed-stage descent conclusion for a flat finite-presentation limit morphism. -/
structure FlatFinitePresentationLimitMorphismDescentAtStage
    {I : Type u} [Preorder I] {i₀ i₃ : I}
    {D : OrderDual I ⥤ Scheme.{u}}
    {Xsys Ysys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i₀}
    {yToBase : Ysys ⟶ tailBaseDiagram D i₀}
    (hi₀i₃ : i₀ ≤ i₃)
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) : Prop where
  /-- Every sufficiently later descended morphism is flat. -/
  flat_stage : ∀ (i : I) (hi₃i : i₃ ≤ i),
    Flat (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
  /-- The square comparing the `i`-stage to the fixed `i₃`-stage is cartesian. -/
  stage_isPullback : ∀ (i : I) (hi₃i : i₃ ≤ i),
    IsPullback
      (Xsys.map (Over.homMk (homOfLE hi₃i) :
        tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
      (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
      (φ.hom.app (tailObject i₃ hi₀i₃))
      (Ysys.map (Over.homMk (homOfLE hi₃i) :
        tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
  /-- The limit square over the fixed `i₃`-stage is cartesian. -/
  limit_isPullback :
    IsPullback
      (xCone.π.app (tailObject i₃ hi₀i₃))
      f
      (φ.hom.app (tailObject i₃ hi₀i₃))
      (yCone.π.app (tailObject i₃ hi₀i₃))

/-- Lemma 32.22.6: in the setup and notation of Lemma 32.22.4, if the limit morphism
`f : X ⟶ Y` is flat and of finite presentation, then after passing to a later stage `i₃ ≥ i₀`
the descended morphisms `f_i : X_i ⟶ Y_i` are flat for all `i ≥ i₃`, each square
`X_i ⟶ X_{i₃}` over `Y_i ⟶ Y_{i₃}` is cartesian, and the limit square
`X ⟶ X_{i₃}` over `Y ⟶ Y_{i₃}` is cartesian. -/
@[stacks 0CNT]
theorem exists_eventually_flat_stage_isPullback_of_flat_finitePresentation_limitMorphism
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₀ : I}
    {Xsys Ysys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₀)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₀)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : TailIndexCategory i₀,
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : TailIndexCategory i₀,
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [QuasiCompact xToS] [LocallyOfFiniteType xToS]
    [QuasiSeparated yToS] [QuasiCompact yToS] [LocallyOfFiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₀ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₀ Ysys yCone yToS)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    (hf_limit : φ.IsLimitMorphism xCone yCone f)
    (hflat : Flat f) (hfp : Scheme.Hom.FinitePresentation f) :
    ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃),
      FlatFinitePresentationLimitMorphismDescentAtStage hi₀i₃ xCone yCone φ f := sorry

end AlgebraicGeometry
