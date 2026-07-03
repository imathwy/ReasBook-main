import Mathlib
import StacksProject_2024.Chap18.Lemma_18_24_4
import StacksProject_2024.Chap21.Situation_21_25_1
import StacksProject_2024.Chap21.Lemma_21_25_6
import StacksProject_2024.Chap21.Lemma_21_28_4

-- Declarations for this item will be appended below by the statement pipeline.

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
abbrev moduleObjectAsDerived (Z : RingedSite.{u, v}) (ℱ : ModuleCat Z) :
    ModuleDerived Z :=
  (DerivedCategory.singleFunctor (ModuleCat Z) (0 : ℤ)).obj ℱ

/-- Pullback on module sheaves induces a functor between the weak LinearRepresentations_Serre_1977 full subcategories cut out
by `A'` and `A`. -/
abbrev modulePullbackOnWeakSerreSubcategory
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.lift A (A'.ι ⋙ f.modulePullback) (fun ℱ' ↦ hpull_mem ℱ'.property)

-- Proof sketch: pullback along a flat morphism is exact, so on the derived category it commutes
-- with cohomology objects. If every cohomology sheaf of `K` lies in `A'`, then the hypothesis
-- `hpull_mem` implies every cohomology sheaf of `f^* K` lies in `A`.
/-- Exact pullback along a flat morphism of ringed sites sends
`D_{\mathcal A'}(\mathcal O_Y)` to `D_\mathcal A(\mathcal O_X)`. -/
theorem modulePullbackDerivedOfFlat_obj_mem_derivedCategoryWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    (K : DY) :
    PX ((ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f).obj K) := sorry

/-- The pullback functor on unbounded derived categories with cohomology in the chosen weak LinearRepresentations_Serre_1977
subcategories. -/
abbrev modulePullbackDerivedOfFlatWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    DY ⥤ DX :=
  ObjectProperty.lift PX
    (ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f)
    (modulePullbackDerivedOfFlat_obj_mem_derivedCategoryWithCohomologyIn
      f A' A hpull_mem)

-- Proof sketch: first use the equivalence on `A'` together with the unit-isomorphism hypothesis
-- to obtain the degree-zero pushforward statements `R^0 f_* (f^* \mathcal F') ∈ A'` and
-- `R^p f_* (f^* \mathcal F') = 0` for `p > 0`. Essential surjectivity of pullback on `A'`
-- transfers these bounds to arbitrary objects of `A`. Then Lemma `21.25.4` with `N = 0`,
-- combined with the bounded-cohomology-basis hypotheses on `X` and `Y`, shows that `Rf_*`
-- carries every object of `D_\mathcal A(\mathcal O_X)` into `D_{\mathcal A'}(\mathcal O_Y)`.
/-- The right derived pushforward restricted to the full subcategory with cohomology in
`\mathcal A`. This is the candidate quasi-inverse in Lemma `21.28.6`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj)))
    (K : DX) :
    PY ((ObjectProperty.ι PX ⋙ modulePushforwardDerived f).obj K) := sorry

/-- The right derived pushforward on the unbounded derived subcategory with cohomology in
`\mathcal A`. In Lemma `21.28.6` this is the quasi-inverse to the restricted pullback functor. -/
abbrev modulePushforwardDerivedWithCohomologyIn
    (_hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A _hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (_basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    DX ⥤ DY :=
  ObjectProperty.lift PY
    (ObjectProperty.ι PX ⋙ modulePushforwardDerived f)
    (modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn
      f A' A _hpull_mem _basisX _basisY adj _hunit)

-- Proof sketch: exact pullback commutes with the truncation functors `τ_{\ge -n}`, so the
-- restricted pullback on `D_{\mathcal A'}` and the restricted pushforward on `D_\mathcal A`
-- are compatible with truncations. Lemma `21.28.5` identifies these truncations as quasi-inverse
-- equivalences on the bounded-below subcategories, while Lemma `21.25.6` gives the truncation
-- control for `Rf_*` on unbounded objects. Passing to the limit over truncations shows that both
-- the unit `K' ⟶ Rf_* f^* K'` and the counit `f^* Rf_* K ⟶ K` are isomorphisms on the unbounded
-- derived subcategories, hence the restricted pullback is an equivalence with quasi-inverse the
-- restricted `Rf_*`.
/-- Lemma 21.28.6: let `f : X ⟶ Y` be a flat morphism of ringed topoi formalized by a flat
morphism of ringed sites, let `\mathcal A \subset \operatorname{Mod}(\mathcal O_X)` and
`\mathcal A' \subset \operatorname{Mod}(\mathcal O_Y)` be weak LinearRepresentations_Serre_1977 subcategories, assume that
pullback induces an equivalence `\mathcal A' \simeq \mathcal A`, assume
`\mathcal F' \to Rf_* f^* \mathcal F'` is an isomorphism for every
`\mathcal F' \in \operatorname{Ob}(\mathcal A')`, and assume both
`(X, \mathcal O_X, \mathcal A)` and `(Y, \mathcal O_Y, \mathcal A')` satisfy Situation
`21.25.1`. Then the induced exact pullback functor
`f^* : D_{\mathcal A'}(\mathcal O_Y) \to D_\mathcal A(\mathcal O_X)` is an equivalence of
categories. The restricted right derived pushforward defined above is the intended quasi-inverse. -/
theorem modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithCohomologyIn f A' A hpull_mem) := sorry

/-- The equivalence instance attached to the restricted pullback functor of Lemma `21.28.6`. -/
noncomputable instance instModulePullbackDerivedOfFlatWithCohomologyInIsEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (_basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithCohomologyIn f A' A hpull_mem) :=
  modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence
    f A' A hpull_mem _basisX _basisY adj _hunit

end

end RingedSite.Hom
