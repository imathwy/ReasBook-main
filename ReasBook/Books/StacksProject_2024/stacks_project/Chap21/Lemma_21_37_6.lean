import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y')
variable (f : X ⟶ Y) (g : Y' ⟶ Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify X'.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y'.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [X'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} f'.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g'.structureSheafMap.hom).IsRightAdjoint]

variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f'.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g'.structureSheafMap)]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]

/- Domain-style sampling for Lemma 21.37.6:
- primary domain: unbounded derived base change for pushforward against exact pullback functors on
  module sheaves over ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.unboundedBaseChangeMap`,
  `RingedSite.Hom.IsUnboundedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`;
- best owner abstraction: the chapter already owns the unbounded base-change morphism as
  `RingedSite.Hom.unboundedBaseChangeMap`, while the core categorical owner remains
  `CategoryTheory.derivedBaseChangeMap`; exact pullback should therefore enter only as a theorem
  hypothesis on the canonical pullback square `L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*`, rather than
  through a parallel exact-model wrapper for the same derived pullback owner;
- primitive vs derived:
  primitive data are the exactness witnesses for `g^*` and `(g')^*` and the canonical pullback
  comparison;
  invertibility of the resulting canonical base-change morphism is derived API.

Source/core/bridge triage:
- `source-facing`: invertibility of the canonical unbounded base-change map;
- `core/canonical`: `CategoryTheory.derivedBaseChangeMap` and
  `CategoryTheory.IsDerivedBaseChangeMap`;
- `bridge/view`: the exactness hypotheses and the pullback comparison are already stated on the
  canonical pullback owners, so this file needs no additional wrapper layer. -/

/-- Helper for Lemma 21.37.6: the canonical pullback square has the expected mate under the
derived pullback-pushforward adjunctions. -/
private noncomputable def exact_pullback_square_comparison
    (hpull :
      L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*) :
    R(f)_* ⋙ L(g)^* ⟶ L(g')^* ⋙ R(f')_* :=
  (((mateEquiv
      (modulePullbackDerived_pushforward_adjunction f)
      (modulePullbackDerived_pushforward_adjunction f'))
      (TwoSquare.mk
        (L(g)^*)
        (L(f)^*)
        (L(f')^*)
        (L(g')^*)
        hpull.hom)).natTrans)

/-- Helper for Lemma 21.37.6: transposing the chosen mate recovers the pullback of the adjunction
counit prescribed by `hpull`. -/
private theorem exact_pullback_square_comparison_spec
    (hpull :
      L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : ModuleDerived X) :
    ((modulePullbackDerived_pushforward_adjunction f').homEquiv
        ((L(g)^*).obj ((R(f)_*).obj K))
        ((L(g')^*).obj K)).symm
        ((exact_pullback_square_comparison g' f' f g hpull).app K) =
      hpull.hom.app ((R(f)_*).obj K) ≫
        (L(g')^*).map
          ((modulePullbackDerived_pushforward_adjunction f).counit.app K) := by
  sorry

/- Route correction: the comparison should come directly from the mate of the canonical pullback
square `hpull`, viewed through the Chapter 21 source-facing owner
`IsUnboundedBaseChangeMap`. -/
private theorem exact_pullback_square_comparison_isUnboundedBaseChangeMap
    (hpull :
      L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : ModuleDerived X) :
    IsUnboundedBaseChangeMap g' f' f g hpull K
      ((exact_pullback_square_comparison g' f' f g hpull).app K) := by
  simpa [IsUnboundedBaseChangeMap, IsDerivedBaseChangeMap, Category.assoc] using
    exact_pullback_square_comparison_spec g' f' f g hpull K

/- Route correction: after identifying the chosen comparison with the canonical base-change mate,
the invertibility question is reduced to that mate for the canonical pullback square. -/
private theorem exact_pullback_square_comparison_app_isIso
    (hexact_g : exactFunctor _ _ (g^*))
    (hexact_g' : exactFunctor _ _ (g'^*))
    (hpull :
      L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : ModuleDerived X) :
    IsIso ((exact_pullback_square_comparison g' f' f g hpull).app K) := by
  -- TODO: the current abstraction only exposes the left-adjoint square `hpull`, but `mateEquiv`
  -- alone does not preserve isomorphisms. The remaining step needs either a concrete inverse built
  -- from the underived Beck-Chevalley data, or a stronger owner lemma identifying this mate with a
  -- conjugate/iterated mate that is known to preserve isomorphisms.
  let _ := hexact_g
  let _ := hexact_g'
  sorry

/--
Lemma 21.37.6: for a commutative square of ringed topoi
`X' ⟶ X`, `X' ⟶ Y'`, `X ⟶ Y`, `Y' ⟶ Y`,
if the horizontal pullbacks are exact on module sheaves and one is given the corresponding
canonical pullback comparison, then the canonical unbounded base-change map
`L(g)^* (R(f)_* K) ⟶ R(f')_* (L(g')^* K)` is an isomorphism for every
`K : D(𝒪_X)`. -/
@[stacks 0FN6]
instance unboundedBaseChangeMap_isIso_of_exact_pullback_square
    (hexact_g : exactFunctor _ _ (g^*))
    (hexact_g' : exactFunctor _ _ (g'^*))
    (hpull :
      L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : ModuleDerived X) :
    IsIso (unboundedBaseChangeMap g' f' f g hpull K) := by
  -- Rewrite the canonical source-facing map to the chosen mate of `hpull`.
  rw [← (exact_pullback_square_comparison_isUnboundedBaseChangeMap
    g' f' f g hpull K).eq_unboundedBaseChangeMap]
  -- The chosen mate is an isomorphism because it comes from the pullback isomorphism.
  exact exact_pullback_square_comparison_app_isIso g' f' f g hexact_g hexact_g' hpull K

end

end RingedSite.Hom
