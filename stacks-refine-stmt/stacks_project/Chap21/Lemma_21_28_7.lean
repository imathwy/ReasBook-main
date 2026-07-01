import Mathlib
import stacks_project.Chap18.Lemma_18_24_4
import stacks_project.Chap21.Lemma_21_25_6
import stacks_project.Chap21.Lemma_21_28_4

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable [Abelian ModX] [Abelian ModY]
variable [f.IsFlat]
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A']
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A]

local notation "PX" => moduleDerivedCohomologyInProperty (X := X) A
local notation "PY" => moduleDerivedCohomologyInProperty (X := Y) A'
local notation "DX" => moduleDerivedWithCohomologyIn (X := X) A
local notation "DY" => moduleDerivedWithCohomologyIn (X := Y) A'

/-- A module sheaf on a ringed site, viewed as a derived object concentrated in degree `0`. -/
abbrev moduleObjectAsDerivedDegreeZero (Z : RingedSite.{u, v}) (ℱ : ModuleCat Z) :
    ModuleDerived Z :=
  (DerivedCategory.singleFunctor (ModuleCat Z) (0 : ℤ)).obj ℱ

/-- Pullback on module sheaves induces a functor between the weak Serre full subcategories cut out
by `A'` and `A`. -/
abbrev modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.lift A (A'.ι ⋙ f.modulePullback) (fun ℱ' ↦ hpull_mem ℱ'.property)

-- Proof sketch: pullback along a flat morphism is exact, so it commutes with cohomology objects on
-- the derived category. The hypothesis `hpull_mem` then transports membership in `A'` of each
-- cohomology sheaf of `K` to membership in `A` of the corresponding cohomology sheaf of `f^* K`.
/-- Exact pullback along a flat morphism of ringed sites sends
`D_{\mathcal A'}(\mathcal O')` to `D_\mathcal A(\mathcal O)`. -/
theorem modulePullbackDerivedOfFlat_obj_mem_weakSerreCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    (K : DY) :
    PX ((ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f).obj K) := sorry

/-- The pullback functor on the unbounded derived subcategories cut out by the weak Serre
cohomology conditions. -/
abbrev modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    DY ⥤ DX :=
  ObjectProperty.lift PX
    (ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f)
    (modulePullbackDerivedOfFlat_obj_mem_weakSerreCohomologyIn
      f A' A hpull_mem)

-- Proof sketch: use the equivalence on `A'` together with the unit-isomorphism hypothesis to
-- identify the higher direct images of objects of `A` with the corresponding vanishing and
-- degree-zero statements transported from `A'`. Apply the source-side bounded-cohomology basis and
-- the along-`f` bounded-cohomology basis from Situation `21.25.5` through Lemma `21.25.6` to pass
-- from bounded-below truncations to arbitrary unbounded objects, and conclude that `Rf_* K` has
-- all cohomology sheaves in `A'`.
/-- Under the hypotheses of Lemma `21.28.7`, the right derived pushforward sends
`D_\mathcal A(\mathcal O)` to `D_{\mathcal A'}(\mathcal O')`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn_of_local_bounded_cohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj)))
    (K : DX) :
    PY ((ObjectProperty.ι PX ⋙ modulePushforwardDerived f).obj K) := sorry

/-- The restricted right derived pushforward used as the quasi-inverse in Lemma `21.28.7`. -/
abbrev modulePushforwardDerivedWithCohomologyInOfLocalBoundedCohomology
    (_hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A _hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (_basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj))) :
    DX ⥤ DY :=
  ObjectProperty.lift PY
    (ObjectProperty.ι PX ⋙ modulePushforwardDerived f)
    (modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn_of_local_bounded_cohomology
      f A' A _hpull_mem _basisX _basisf adj _hunit)

-- Proof sketch: the bounded-below equivalence from Lemma `21.28.5` controls every truncation
-- `τ_{\ge -n} K`, while Lemma `21.25.6` gives the comparison isomorphisms
-- `H^j(Rf_* K) → H^j(Rf_*(τ_{\ge -n} K))` under the Situation `21.25.1` and `21.25.5`
-- hypotheses. Passing to the limit over truncations upgrades the bounded-below unit and counit
-- isomorphisms to all objects of the unbounded derived subcategories, so the restricted pullback
-- is an equivalence with quasi-inverse the restricted `Rf_*`.
/-- Lemma 21.28.7: let `f : (\mathcal C, \mathcal O) \to (\mathcal C', \mathcal O')` be a
morphism of ringed sites, let `\mathcal A \subset \operatorname{Mod}(\mathcal O)` and
`\mathcal A' \subset \operatorname{Mod}(\mathcal O')` be weak Serre subcategories, assume `f` is
flat, assume `f^* : \mathcal A' \to \mathcal A` is an equivalence, assume
`\mathcal F' \to Rf_* f^* \mathcal F'` is an isomorphism for `\mathcal F' \in \operatorname{Ob}
(\mathcal A')`, assume `(\mathcal C, \mathcal O, \mathcal A)` satisfies Situation `21.25.1`, and
assume `f` and `\mathcal A` satisfy Situation `21.25.5`. Then
`f^* : D_{\mathcal A'}(\mathcal O') \to D_\mathcal A(\mathcal O)` is an equivalence of
categories. The restricted right derived pushforward defined above is the intended quasi-inverse. -/
theorem modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn_isEquivalence_of_local_bounded_cohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn f A' A hpull_mem) := sorry

/-- The equivalence instance attached to the restricted pullback functor of Lemma `21.28.7`. -/
noncomputable instance
    instModulePullbackDerivedOfFlatWithWeakSerreCohomologyInIsEquivalenceOfLocalBoundedCohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (_basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn f A' A hpull_mem) :=
  modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn_isEquivalence_of_local_bounded_cohomology
    f A' A hpull_mem _basisX _basisf adj _hunit

end

end RingedSite.Hom
