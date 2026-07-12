import StacksProject_2024.Chap21.Remark_21_19_3_core
import StacksProject_2024.Chap21.Remark_21_35_11

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

variable {DC : Type u} [Category.{v} DC]
variable {DC' : Type u} [Category.{v} DC']
variable {DD : Type u} [Category.{v} DD]
variable {DD' : Type u} [Category.{v} DD']

variable [MonoidalCategory DC]
variable [BraidedCategory DC]
variable [MonoidalClosed DC]
variable [MonoidalCategory DC']
variable [BraidedCategory DC']
variable [MonoidalClosed DC']

/- Domain-style sampling for Remark 21.35.12:
- primary domain: derived base change for internal Hom, with the internal-Hom side already owned
  by the pullback/internal-Hom comparison from Remark `21.35.11`;
- sampled owner declarations:
  `CategoryTheory.derivedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap_spec`,
  `Adjunction.homEquiv`,
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`;
- best owner abstraction:
  `source-facing`: the comparison morphism
    `Lg^* Rf_* RHom(K, L) ⟶ R(f')_* RHom(Lh^* K, Lh^* L)`;
  `core/canonical`: `CategoryTheory.derivedBaseChangeMap`, specialized to the object `RHom(K, L)`;
  `bridge/view`: compose that generic base-change map with the target-side internal-Hom
    comparison from Remark `21.35.11`.
- primitive data: the chosen pullback/pushforward functors, the square isomorphism, the chosen
  adjunctions, and the pullback-tensor comparison inducing the target-side internal-Hom map.

This item is a bridge/view declaration. The downstream reusable surface is the comparison morphism
itself together with its adjunction-side specification theorem.
-/

variable
  (leftDerivedPullback_h : DC ⥤ DC')
  (leftDerivedPullback_g : DD ⥤ DD')
  (leftDerivedPullback_f : DD ⥤ DC)
  (leftDerivedPullback_f' : DD' ⥤ DC')
  (rightDerivedPushforward_f : DC ⥤ DD)
  (rightDerivedPushforward_f' : DC' ⥤ DD')

/-- Remark 21.35.12: for a commutative square of ringed topoi, encoded here by the four derived
categories, chosen derived pullbacks `Lh^*`, `Lg^*`, `Lf^*`, `L(f')^*`, chosen derived
pushforwards `Rf_*`, `R(f')_*`, the pullback-tensor comparison for `Lh^*`, and a commutativity isomorphism
`Lg^* ⋙ L(f')^* ≅ Lf^* ⋙ Lh^*`, there is a canonical base-change morphism
`Lg^* Rf_* RHom(K, L) ⟶ R(f')_* RHom(Lh^* K, Lh^* L)`. -/
@[stacks 08JG]
noncomputable def derivedPushforwardInternalHomBaseChangeMap
    (pullbackTensorComparison_h :
      ∀ K L : DC,
        leftDerivedPullback_h.obj (K ⊗ L) ≅
          (leftDerivedPullback_h.obj K ⊗ leftDerivedPullback_h.obj L))
    (hpull :
      leftDerivedPullback_g ⋙ leftDerivedPullback_f' ≅
        leftDerivedPullback_f ⋙ leftDerivedPullback_h)
    (adj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (adj_f' : leftDerivedPullback_f' ⊣ rightDerivedPushforward_f')
    (K L : DC) :
    leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj (K ⟹ L)) ⟶
      rightDerivedPushforward_f'.obj (leftDerivedPullback_h.obj K ⟹ leftDerivedPullback_h.obj L) :=
  derivedBaseChangeMap
      leftDerivedPullback_f leftDerivedPullback_f'
      leftDerivedPullback_g leftDerivedPullback_h
      rightDerivedPushforward_f rightDerivedPushforward_f'
      adj_f adj_f' hpull (K ⟹ L) ≫
    rightDerivedPushforward_f'.map
      (pullbackDerivedInternalHomComparison
        leftDerivedPullback_h pullbackTensorComparison_h K L)

-- Proof sketch: unfold `derivedPushforwardInternalHomBaseChangeMap`. By definition it is the
-- generic derived base-change map for `RHom(K, L)`, followed by the target-side internal-Hom
-- comparison from Remark `21.35.11`.
/-- Applying `leftDerivedPullback_f' ⊣ rightDerivedPushforward_f'` to
`derivedPushforwardInternalHomBaseChangeMap` recovers the composite used to define it. -/
theorem derivedPushforwardInternalHomBaseChangeMap_spec
    (pullbackTensorComparison_h :
      ∀ K L : DC,
        leftDerivedPullback_h.obj (K ⊗ L) ≅
          (leftDerivedPullback_h.obj K ⊗ leftDerivedPullback_h.obj L))
    (hpull :
      leftDerivedPullback_g ⋙ leftDerivedPullback_f' ≅
        leftDerivedPullback_f ⋙ leftDerivedPullback_h)
    (adj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (adj_f' : leftDerivedPullback_f' ⊣ rightDerivedPushforward_f')
    (K L : DC) :
    (adj_f'.homEquiv
        (leftDerivedPullback_g.obj (rightDerivedPushforward_f.obj (K ⟹ L)))
        (leftDerivedPullback_h.obj K ⟹ leftDerivedPullback_h.obj L)).symm
        (derivedPushforwardInternalHomBaseChangeMap
          leftDerivedPullback_h leftDerivedPullback_g
          leftDerivedPullback_f leftDerivedPullback_f'
          rightDerivedPushforward_f rightDerivedPushforward_f' pullbackTensorComparison_h
          hpull adj_f adj_f' K L) =
      hpull.hom.app (rightDerivedPushforward_f.obj (K ⟹ L)) ≫
        leftDerivedPullback_h.map (adj_f.counit.app (K ⟹ L)) ≫
        pullbackDerivedInternalHomComparison
          leftDerivedPullback_h pullbackTensorComparison_h K L := by
  rw [derivedPushforwardInternalHomBaseChangeMap, adj_f'.homEquiv_naturality_right_symm]
  simpa [derivedBaseChangeMap] using
    derivedBaseChangeMap_spec
      leftDerivedPullback_f leftDerivedPullback_f'
      leftDerivedPullback_g leftDerivedPullback_h
      rightDerivedPushforward_f rightDerivedPushforward_f'
      adj_f adj_f' hpull (K ⟹ L)

end

end SheafOfModules.RingedSite
