import Mathlib
import stacks_project.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

section

variable {X Y : LCCat.{u}}

/-- Sheaves of types on the small Zariski site of an `LC` object. -/
abbrev SmallTypeSheaf (X : LCCat.{u}) :=
  TopCat.Sheaf (Type u) X.obj

/-- The inverse-image functor `π_X^{-1}` from the small Zariski site of `X` to a chosen
Grothendieck topology on `Over X`. -/
abbrev piInverseType
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint] :
    SmallTypeSheaf X ⥤ Sheaf J (Type u) :=
  π.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) J

/-- The inverse-image functor `ε_X^{-1}` for the topology comparison
`ε_X : Sh(LC_{qc}/X) ⟶ Sh(LC_{Zar}/X)`, represented by the identity functor on `Over X`. -/
abbrev epsilonInverseType
    (JZar JQc : GrothendieckTopology (Over X))
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    Sheaf JZar (Type u) ⥤ Sheaf JQc (Type u) :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) JZar JQc := hε_cont
  let _ :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint := hε_adj
  (𝟭 (Over X)).sheafPullback (Type u) JZar JQc

-- Proof sketch: unfold `epsilonInverseType`; it is introduced precisely as the sheaf pullback
-- functor attached to the identity-on-objects site morphism from `LC_{Zar}/X` to `LC_{qc}/X`.
/-- The comparison inverse image `ε_X^{-1}` is the sheaf pullback along the identity functor on
`Over X`. -/
theorem epsilonInverseType_eq
    (JZar JQc : GrothendieckTopology (Over X))
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    epsilonInverseType JZar JQc hε_cont hε_adj =
      (𝟭 (Over X)).sheafPullback (Type u) JZar JQc := sorry

/-- The inverse-image functor `a_X^{-1}` for the composite morphism of topoi
`a_X = π_X ∘ ε_X : Sh(LC_{qc}/X) ⟶ Sh(X)`. -/
abbrev aInverseType
    (JZar JQc : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) JZar]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZar).IsRightAdjoint]
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    SmallTypeSheaf X ⥤ Sheaf JQc (Type u) :=
  piInverseType JZar π ⋙ epsilonInverseType JZar JQc hε_cont hε_adj

-- Proof sketch: unfold `aInverseType`; by definition it is the composite of the small-to-big
-- Zariski inverse image `π_X^{-1}` with the qc/Zariski comparison inverse image `ε_X^{-1}`.
/-- The inverse image `a_X^{-1}` is the composite `ε_X^{-1} ∘ π_X^{-1}` on sheaves of types. -/
theorem aInverseType_eq
    (JZar JQc : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) JZar]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZar).IsRightAdjoint]
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    aInverseType JZar JQc π hε_cont hε_adj =
      piInverseType JZar π ⋙ epsilonInverseType JZar JQc hε_cont hε_adj := sorry

-- Proof sketch: the localized pullback functors on `LC_{Zar}` and `LC_{qc}` are both induced by
-- `Over.pullback f`, while `ε_X` and `ε_Y` come from the identity functors on the slice
-- categories. The compatibility of these continuous functors gives the desired canonical
-- isomorphism between the two composites of inverse-image functors.
/-- Lemma 21.31.8 (1): for a morphism `f : X ⟶ Y` in `LC`, the comparison morphisms
`ε_X : Sh(LC_{qc}/X) ⟶ Sh(LC_{Zar}/X)` and `ε_Y : Sh(LC_{qc}/Y) ⟶ Sh(LC_{Zar}/Y)` fit into the
canonical commutative square of topoi with horizontal arrows given by the localized morphisms
`f_{qc}` and `f_{Zar}`. -/
theorem lcQc_lcZar_topoi_square_isomorphic
    (f : X ⟶ Y)
    (JZarX JQcX : GrothendieckTopology (Over X))
    (JZarY JQcY : GrothendieckTopology (Over Y))
    (hεX_cont : Functor.IsContinuous (𝟭 (Over X)) JZarX JQcX)
    (hεY_cont : Functor.IsContinuous (𝟭 (Over Y)) JZarY JQcY)
    (hεX_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZarX JQcX).IsRightAdjoint)
    (hεY_adj :
      ((𝟭 (Over Y)).sheafPushforwardContinuous (Type u) JZarY JQcY).IsRightAdjoint)
    [HasLimitsOfShape WalkingCospan LCCat.{u}]
    [(Over.pullback f).IsContinuous JZarY JZarX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JZarY JZarX).IsRightAdjoint]
    [(Over.pullback f).IsContinuous JQcY JQcX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JQcY JQcX).IsRightAdjoint] :
    IsIsomorphic
      (((Over.pullback f).sheafPullback (Type u) JZarY JZarX) ⋙
        epsilonInverseType JZarX JQcX hεX_cont hεX_adj)
      ((epsilonInverseType JZarY JQcY hεY_cont hεY_adj) ⋙
        ((Over.pullback f).sheafPullback (Type u) JQcY JQcX)) := sorry

-- Proof sketch: compose the inverse-image identification for the small/big Zariski square from
-- Lemma `21.31.7 (5)` with the qc/Zariski comparison square from clause `(1)`. Since
-- `a_X^{-1}` and `a_Y^{-1}` are defined as `ε_X^{-1} ∘ π_X^{-1}` and `ε_Y^{-1} ∘ π_Y^{-1}`,
-- this yields the commutative square relating `Sh(LC_{qc}/X)`, `Sh(LC_{qc}/Y)`, `Sh(X)`, and
-- `Sh(Y)`.
/-- Lemma 21.31.8 (2): with `a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`, the localized qc topoi and
the small topoi fit into the canonical commutative square over a morphism `f : X ⟶ Y` in `LC`. -/
theorem lcQc_small_topoi_square_isomorphic
    (f : X ⟶ Y)
    (JZarX JQcX : GrothendieckTopology (Over X))
    (JZarY JQcY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JZarX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JZarY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZarX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JZarY).IsRightAdjoint]
    (hεX_cont : Functor.IsContinuous (𝟭 (Over X)) JZarX JQcX)
    (hεY_cont : Functor.IsContinuous (𝟭 (Over Y)) JZarY JQcY)
    (hεX_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZarX JQcX).IsRightAdjoint)
    (hεY_adj :
      ((𝟭 (Over Y)).sheafPushforwardContinuous (Type u) JZarY JQcY).IsRightAdjoint)
    [HasLimitsOfShape WalkingCospan LCCat.{u}]
    [(Over.pullback f).IsContinuous JQcY JQcX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JQcY JQcX).IsRightAdjoint] :
    IsIsomorphic
      ((TopCat.Sheaf.pullback (Type u) f.hom) ⋙
        aInverseType JZarX JQcX πX hεX_cont hεX_adj)
      ((aInverseType JZarY JQcY πY hεY_cont hεY_adj) ⋙
        ((Over.pullback f).sheafPullback (Type u) JQcY JQcX)) := sorry

-- Proof sketch: first apply the proper base-change comparison from Lemma `21.31.7 (7)` to the
-- composite `π_Y^{-1} ∘ f_*`. Then use that `ε_{Y,*}` reflects isomorphisms and that
-- `a_X^{-1} = ε_X^{-1} ∘ π_X^{-1}` and `a_Y^{-1} = ε_Y^{-1} ∘ π_Y^{-1}` to descend the
-- comparison to the qc topologies.
/-- Lemma 21.31.8 (3): if `f : X ⟶ Y` is proper, then the inverse image `a_Y^{-1}` composed with
small direct image along `f` is canonically isomorphic to the qc direct image along `f_{qc}`
composed with `a_X^{-1}`. -/
theorem proper_smallPushforward_aInverse_isomorphic_lcQcPushforward_aInverse
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (JZarX JQcX : GrothendieckTopology (Over X))
    (JZarY JQcY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JZarX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JZarY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZarX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JZarY).IsRightAdjoint]
    (hεX_cont : Functor.IsContinuous (𝟭 (Over X)) JZarX JQcX)
    (hεY_cont : Functor.IsContinuous (𝟭 (Over Y)) JZarY JQcY)
    (hεX_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZarX JQcX).IsRightAdjoint)
    (hεY_adj :
      ((𝟭 (Over Y)).sheafPushforwardContinuous (Type u) JZarY JQcY).IsRightAdjoint)
    [HasLimitsOfShape WalkingCospan LCCat.{u}]
    [(Over.pullback f).IsContinuous JQcY JQcX] :
    IsIsomorphic
      ((TopCat.Sheaf.pushforward (Type u) f.hom) ⋙
        aInverseType JZarY JQcY πY hεY_cont hεY_adj)
      ((aInverseType JZarX JQcX πX hεX_cont hεX_adj) ⋙
        ((Over.pullback f).sheafPushforwardContinuous (Type u) JQcY JQcX)) := sorry

end
