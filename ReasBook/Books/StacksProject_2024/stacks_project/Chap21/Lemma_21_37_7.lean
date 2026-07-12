import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_15_1
import StacksProject_2024.Chap21.Lemma_21_37_6

open CategoryTheory
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-
Domain-style sampling for Lemma 21.37.7:
- primary domain: derived base change for module sheaves on commutative squares of ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.module_pushforward_pullback_square_eq`,
  `RingedSite.Hom.exact_abelian_lowerShriek_pullback_square_isomorphic`,
  `RingedSite.Hom.unboundedBaseChangeMap_isIso_of_exact_pullback_square`,
  `modulePullbackDerived_pushforward_adjunction`;
- best owner abstraction:
  `source-facing`: the two Stacks-project clauses recorded below, with clause `(1)` already owned
    by the site-level comparison `module_pushforward_pullback_square_eq`, while clause `(2)`
    is the canonical unbounded base-change isomorphism under the exact `g'_!` hypothesis,
    obtained from the exact-lower-shriek pullback-square bridge and the upstream owner
    `unboundedBaseChangeMap_isIso_of_exact_pullback_square`;
  `core/canonical`: the unbounded pullback/pushforward owners `L(g)^*` and `R(f)_*`, the
    categorical owner `CategoryTheory.derivedBaseChangeMap`, and the Chapter 21 theorem
    `unboundedBaseChangeMap_isIso_of_exact_pullback_square`;
  `bridge/view`: the restriction of the unbounded composites
    `R(f)_* ⋙ L(g)^*` and `L(g')^* ⋙ R(f')_*` to the bounded-below subcategories, and the
    pullback-square `IsIsomorphic` comparison on `L(g)^* ⋙ L(f')^*` and `L(f)^* ⋙ L(g')^*`
    extracted from the exact lower-shriek hypothesis.

Primitive data:
- the commutative square of ringed-site morphisms;
- the underived square data from `18.41.3` and the exact lower-shriek criterion from the Stacks
  proof;
- the structure-sheaf identifications forcing module pullback to agree with inverse image, and the
  exact lower-shriek hypothesis for clause `(2)`.

Derived API:
- the source-facing bounded-below comparison on `D⁺`, whose objectwise owner is
  the inverse-image/derived-pushforward comparison obtained by passing through `Lemma 18.41.3`
  and the module-to-abelian derived comparison of `Lemma 21.20.7`;
- for clause `(2)`, only the theorem-level exact-lower-shriek pullback-square comparison;
  the canonical `derivedBaseChangeMap` invertibility is reused directly from Lemma `21.37.6`.
-/

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y')
variable (f : X ⟶ Y) (g : Y' ⟶ Y)

section

variable [HasWeakSheafify X'.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y'.siteTopology AddCommGrpCat.{max u v}]
variable [X'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Functor.IsCocontinuous f.base Y.siteTopology X.siteTopology]
variable [Functor.IsCocontinuous f'.base Y'.siteTopology X'.siteTopology]
variable [Functor.IsCocontinuous g.base Y.siteTopology Y'.siteTopology]
variable [Functor.IsCocontinuous g'.base X.siteTopology X'.siteTopology]
variable [Functor.Additive f.modulePushforward]
variable [Functor.Additive f'.modulePushforward]
variable [(SheafOfModules.pushforward g.structureSheafMap).IsRightAdjoint]
variable [(SheafOfModules.pushforward g'.structureSheafMap).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g'.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (g^*)]
variable [Functor.Additive (g'^*)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]

/- Lemma 21.37.7 (1): the bounded-below comparison on `D⁺` is already the Chapter 21 owner
`boundedBelow_baseChange_isomorphic` from Lemma `21.15.1`, so this file reuses that statement
directly rather than keeping a second local chosen functor isomorphism. -/
recall boundedBelow_baseChange_isomorphic

end

section

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify X'.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y'.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [X'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} f'.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g'.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f'.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g'.structureSheafMap)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]

-- Proof sketch: clause `(2)` contributes only the source-facing exact-lower-shriek comparison on
-- derived pullbacks. The canonical `derivedBaseChangeMap` consequence is already owned by Lemma
-- `21.37.6`, which consumes any such pullback-square isomorphism.
/- Lemma 21.37.7 (2): for the same commutative square of ringed topoi, if the abelian lower
shriek `g'_!` on sheaves of abelian groups is exact, then the corresponding exact pullback-square
comparison holds on derived pullbacks. The canonical
invertibility statement for `derivedBaseChangeMap` is already owned by Lemma `21.37.6`, so this
file keeps only the source-facing theorem-level `IsIsomorphic` bridge extracted from the
lower-shriek exactness hypothesis on the canonical Chapter 18 owner
`g'.base.sheafPullback AddCommGrpCat X.siteTopology X'.siteTopology`. -/

/-- Lemma 21.37.7 (2), bridge form: the exact lower-shriek hypothesis produces the canonical
pullback-square isomorphism on the derived pullback functors. This is the public bridge/view input
extracted from the exact lower-shriek hypothesis before applying the canonical owner
`CategoryTheory.derivedBaseChangeMap`. -/
@[stacks 0FN7]
theorem exact_abelian_lowerShriek_pullback_square_isomorphic
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (hexact_g'_shriek :
      exactFunctor
        (Sheaf X.siteTopology AddCommGrpCat.{max u v})
        (Sheaf X'.siteTopology AddCommGrpCat.{max u v})
        (g'.base.sheafPullback AddCommGrpCat.{max u v}
          X.siteTopology X'.siteTopology)) :
    IsIsomorphic (L(g)^* ⋙ L(f')^*) (L(f)^* ⋙ L(g')^*) := by
  sorry

section

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]

/-- Lemma 21.37.7 (2): under the flatness hypotheses from clause `(1)`, if the abelian lower
shriek `g'_!` on sheaves of abelian groups is exact, then for every `K : D(𝒪_X)` the unbounded
base-change objects `L(g)^* ((R(f)_*).obj K)` and `(R(f')_*).obj ((L(g')^*).obj K)` are
isomorphic. This is the source-facing consequence obtained by applying the canonical owner
`unboundedBaseChangeMap` from Lemma `21.37.6` to the pullback-square bridge above. -/
@[stacks 0FN7]
theorem unboundedBaseChange_isomorphic_of_exact_abelian_lowerShriek
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (hg_flat : IsFlat g) (hg'_flat : IsFlat g')
    (hexact_g'_shriek :
      exactFunctor
        (Sheaf X.siteTopology AddCommGrpCat.{max u v})
        (Sheaf X'.siteTopology AddCommGrpCat.{max u v})
        (g'.base.sheafPullback AddCommGrpCat.{max u v}
          X.siteTopology X'.siteTopology))
    (K : ModuleDerived X) :
    IsIsomorphic
      ((R(f)_* ⋙ L(g)^*).obj K)
      ((L(g')^* ⋙ R(f')_*).obj K) := by
  let hpull :=
    exact_abelian_lowerShriek_pullback_square_isomorphic
      g' f' f g hcomm hcofinal hO_g hO_g' hg hg' hexact_g'_shriek
  let squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^* := Classical.choice hpull
  let φ := unboundedBaseChangeMap g' f' f g squareIso K
  let hφ : IsIso φ :=
    unboundedBaseChangeMap_isIso_of_exact_pullback_square
      g' f' f g
      (IsFlat.pullback_exact g hg_flat)
      (IsFlat.pullback_exact g' hg'_flat)
      squareIso
      K
  exact ⟨(fun (hinst : IsIso φ) ↦
    letI : IsIso φ := hinst
    asIso φ) hφ⟩

end

end

end

end RingedSite.Hom
