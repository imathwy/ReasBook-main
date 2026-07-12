import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine-transition-limit Hom comparison API,
-- but no existing global owner for "morphism of inverse systems over a tail of `(S_i)`" was
-- available. Local Chapter 32 precedent keeps directed scheme limits as `OrderDual I ⥤ Scheme`
-- with explicit cones, so the source-facing tail morphism below is a natural transformation over
-- the restricted base system.

/-- The base inverse system restricted to stages `j >= i0`. -/
abbrev tailBaseDiagram {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (i0 : I) :
    Over (show OrderDual I from i0) ⥤ Scheme.{u} :=
  Over.forget (show OrderDual I from i0) ⋙ D

/-- The object of the tail category represented by a stage `j >= i0`. -/
abbrev tailObject {I : Type u} [Preorder I] {i0 : I} (j : I) (h : i0 ≤ j) :
    Over (show OrderDual I from i0) :=
  Over.mk (homOfLE h : (show OrderDual I from j) ⟶ (show OrderDual I from i0))

/-- Restrict an inverse system starting at `i` to a later tail starting at `i0`. -/
abbrev restrictTail {I : Type u} [Preorder I]
    {i i0 : I} (h : i ≤ i0)
    (Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}) :
    Over (show OrderDual I from i0) ⥤ Scheme.{u} :=
  Over.map (homOfLE h : (show OrderDual I from i0) ⟶ (show OrderDual I from i)) ⋙ Xsys

/-- Restrict the structural map from an inverse system to the base system to a later tail. -/
abbrev restrictTailToBase {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) {i i0 : I} (h : i ≤ i0)
    {Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}}
    (xToBase : Xsys ⟶ tailBaseDiagram D i) :
    restrictTail h Xsys ⟶ tailBaseDiagram D i0 :=
  Functor.whiskerLeft
    (Over.map (homOfLE h : (show OrderDual I from i0) ⟶ (show OrderDual I from i)))
    xToBase

/-- The stagewise base-change system `j ↦ S_j ×_{S_i} W` over the tail `j >= i`. -/
abbrev finitePresentationApproximationBaseChangeDiagram {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (i : OrderDual I) {W : Scheme.{u}}
    (toSi : W ⟶ D.obj i) : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback toSi ⋙ Over.forget _

/-- A factorization through the scheme-theoretic image used by the approximation stages. -/
structure ApproximationStageSchemeTheoreticImage {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) : Prop where
  /-- The factorization composes back to the original morphism. -/
  fac : toImage ≫ ι = g
  /-- The image object is a closed subscheme of the target. -/
  isClosedImmersion : IsClosedImmersion ι
  /-- Minimality among closed subschemes through which the morphism factors. -/
  universal : ∀ ⦃Z' : Scheme.{u}⦄ (toZ' : X ⟶ Z') (closed : Z' ⟶ Y),
    IsClosedImmersion closed → toZ' ≫ closed = g →
      ∃! lift : Z ⟶ Z', lift ≫ closed = ι ∧ toImage ≫ lift = toZ'

/-- A morphism of inverse systems over the same tail of the base system. -/
structure InverseSystemMorphismOverBase {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (i0 : I)
    (Xsys Ysys : Over (show OrderDual I from i0) ⥤ Scheme.{u})
    (xToBase : Xsys ⟶ tailBaseDiagram D i0)
    (yToBase : Ysys ⟶ tailBaseDiagram D i0) where
  /-- The underlying natural transformation of inverse systems. -/
  hom : Xsys ⟶ Ysys
  /-- The natural transformation is over the base system. -/
  over_base : hom ≫ yToBase = xToBase

/-- A morphism of inverse systems induces the specified morphism on the limit cones. -/
def InverseSystemMorphismOverBase.IsLimitMorphism {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I}
    {Xsys Ysys : Over (show OrderDual I from i0) ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (xCone : Cone Xsys) (yCone : Cone Ysys) (f : xCone.pt ⟶ yCone.pt) : Prop :=
  ∀ j : Over (show OrderDual I from i0),
    f ≫ yCone.π.app j = xCone.π.app j ≫ φ.hom.app j

/-- A finite-presentation approximation system whose cone is the limit, with each stage the
scheme-theoretic image in the base-change system from Lemma 32.22.3. -/
structure FinitePresentationApproximationLimitSystem {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt) where
  /-- The scheme used at the finite-presentation stage. -/
  W : Scheme.{u}
  /-- The map from the limit object to the finite-presentation stage. -/
  toW : xCone.pt ⟶ W
  /-- The structural morphism from the finite-presentation stage to `S_i`. -/
  toSi : W ⟶ D.obj i
  /-- The finite-presentation stage is quasi-compact over `S_i`. -/
  quasiCompact_toSi : QuasiCompact toSi
  /-- The finite-presentation stage is locally of finite presentation over `S_i`. -/
  locallyOfFinitePresentation_toSi : LocallyOfFinitePresentation toSi
  /-- The defining square over `S_i` commutes. -/
  square : CommSq toW toS toSi (c.π.app i)
  /-- The induced map to the base change `S ×_{S_i} W`. -/
  toLimitBaseChange : xCone.pt ⟶ pullback (c.π.app i) toSi
  /-- The induced map to the base change has first projection `X ⟶ S`. -/
  toLimitBaseChange_fst :
    toLimitBaseChange ≫ pullback.fst (c.π.app i) toSi = toS
  /-- The induced map to the base change has second projection `X ⟶ W`. -/
  toLimitBaseChange_snd :
    toLimitBaseChange ≫ pullback.snd (c.π.app i) toSi = toW
  /-- The map to the base change is a closed immersion. -/
  closedImmersion_toLimitBaseChange : IsClosedImmersion toLimitBaseChange
  /-- The maps from `X` to the stagewise base changes. -/
  toBaseChange :
    (Functor.const (Over (show OrderDual I from i))).obj xCone.pt ⟶
      finitePresentationApproximationBaseChangeDiagram D (show OrderDual I from i) toSi
  /-- Compatibility of the stagewise base-change maps with the first projections. -/
  toBaseChange_fst : ∀ j : Over (show OrderDual I from i),
    toBaseChange.app j ≫ pullback.fst (D.map j.hom) toSi = toS ≫ c.π.app j.left
  /-- Compatibility of the stagewise base-change maps with the second projections. -/
  toBaseChange_snd : ∀ j : Over (show OrderDual I from i),
    toBaseChange.app j ≫ pullback.snd (D.map j.hom) toSi = toW
  /-- The stage system maps into the stagewise base-change system. -/
  toImage : Xsys ⟶ finitePresentationApproximationBaseChangeDiagram D (show OrderDual I from i) toSi
  /-- Each stage is the scheme-theoretic image of `X` in the corresponding base change. -/
  image : ∀ j : Over (show OrderDual I from i),
    ApproximationStageSchemeTheoreticImage (toBaseChange.app j) (xCone.π.app j) (toImage.app j)
  /-- The cone with vertex `X` is the limit cone for the approximation system. -/
  isLimit : IsLimit xCone

/-- Lemma 32.22.4: in Situation 32.22.1, a morphism between two quasi-separated finite-type
schemes over `S = lim_i S_i`, together with finite-presentation approximation limit systems from
Lemma 32.22.3, descends after passing to a common tail to a morphism of inverse systems over
`(S_i)`. Any two such descended morphisms that induce the original morphism agree at all
sufficiently large stages. -/
@[stacks 0CNR]
theorem exists_eventually_morphismOfInverseSystemsOverBase_of_finiteTypeApproximationLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (show OrderDual I from i₁) ⥤ Scheme.{u}}
    {Ysys : Over (show OrderDual I from i₂) ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (show OrderDual I from i₁),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (show OrderDual I from i₂),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [QuasiCompact xToS] [LocallyOfFiniteType xToS]
    [QuasiSeparated yToS] [QuasiCompact yToS] [LocallyOfFiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS) :
    ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
      ∃ φ : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
        (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
        φ.IsLimitMorphism (Cone.whisker
          (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
          xCone)
          (Cone.whisker
            (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
            yCone) f ∧
        ∀ ψ : InverseSystemMorphismOverBase D i₀
            (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
            (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
          ψ.IsLimitMorphism (Cone.whisker
            (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
            xCone)
            (Cone.whisker
              (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
              yCone) f →
            ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ ⦃j : I⦄ (hij : i ≤ j),
              φ.hom.app (tailObject j (le_trans hi₀i hij)) =
                ψ.hom.app (tailObject j (le_trans hi₀i hij)) := sorry

end AlgebraicGeometry
