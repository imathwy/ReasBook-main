import StacksProject_2024.Chap13.Lemma_13_16_4
import StacksProject_2024.Chap20.«20_54_2_1»
import StacksProject_2024.Chap21.Lemma_21_19_1
import StacksProject_2024.Chap21.Definition_21_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u v

namespace RingedSite.Hom

section

/- Domain-style sampling for Lemma 21.50.1:
- primary domain: projection-formula morphisms in monoidal derived categories of module sheaves on
  ringed sites;
- sampled declarations:
  `CategoryTheory.projectionFormulaMorphism`,
  `CategoryTheory.tensoringRight`,
  explicit adjunction data `adj : L(f)^* ⊣ R(f)_*`,
  `RingedSite.DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: the `IsIso` statement below for the canonical projection-formula morphism on
    the chapter owner surface `L(f)^*`, `R(f)_*`, and the ringed-site perfectness owner from
    `Definition_21_47_1`;
  `core/canonical`: `projectionFormulaMorphism`,
    explicit adjunction data `adj : L(f)^* ⊣ R(f)_*`, `tensoringRight`, and the perfectness
    owner from `Definition_21_47_1`;
  `bridge/view`: the bundled pullback-tensor comparison `modulePullbackDerivedTensorIso`, whose
    objectwise components feed the generic owner `projectionFormulaMorphism`.
- primitive data: the morphism of ringed sites and the functor-level pullback-tensor comparison
  `modulePullbackDerivedTensorIso`;
- derived API: the canonical instance
  `projectionFormulaMorphism_isIso_of_isPerfect`. -/

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [HasBinaryProducts Y.carrier]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : Y, (localizedRestriction Y U).Additive]
variable [∀ U : Y, PreservesFiniteLimits (localizedRestriction Y U)]
variable [∀ U : Y, PreservesFiniteColimits (localizedRestriction Y U)]
variable [CategoryWithHomology (ModuleCat Y)]
variable [∀ U : Y, CategoryWithHomology (ModuleCat (Y.localization U))]

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable (modulePullbackDerived_pushforward_adjunction : L(f)^* ⊣ R(f)_*)

variable
  (modulePullbackDerivedTensorIso :
    ∀ L : DModY,
      (tensoringRight DModY).obj L ⋙ L(f)^* ≅
        L(f)^* ⋙ (tensoringRight DModX).obj ((L(f)^*).obj L))

/-- Helper for Lemma 21.50.1: tensoring the adjunction unit with the fixed object `R(f)_* E`
preserves naturality in the source variable. -/
private lemma projection_formula_unit_tensor_naturality
    (E : DModX) {K L : DModY} (φ : K ⟶ L) :
    (φ ▷ (R(f)_*).obj E) ≫
        ((modulePullbackDerived_pushforward_adjunction.unit.app L) ▷ (R(f)_*).obj E) =
      ((modulePullbackDerived_pushforward_adjunction.unit.app K) ▷ (R(f)_*).obj E) ≫
        (R(f)_*.map ((L(f)^*).map φ) ▷ (R(f)_*).obj E) := by
  sorry

/-- Helper for Lemma 21.50.1: a morphism of abelian sheaves is an isomorphism once every object
admits a cover whose members see isomorphisms on sections. -/
private theorem sheaf_map_isIso_of_cover_by_componentwise_isIso
    {A B : Sheaf Y.siteTopology AddCommGrpCat.{max u v}}
    (φ : A ⟶ B)
    (hcoverIso :
      ∀ V : Y, ∃ S : Y.siteTopology.Cover V, ∀ I : S.Arrow,
        IsIso (((sheafToPresheaf Y.siteTopology AddCommGrpCat.{max u v}).map φ).app
          (Opposite.op I.Y))) :
    IsIso φ := by
  sorry

/-- Helper for Lemma 21.50.1: a morphism of `𝒪_Y`-modules is an isomorphism once every
object admits a cover whose members see isomorphisms on sections. -/
private theorem module_map_isIso_of_cover_by_componentwise_isIso
    {M N : ModuleCat Y} (φ : M ⟶ N)
    (hcoverIso :
      ∀ V : Y, ∃ S : Y.siteTopology.Cover V, ∀ I : S.Arrow,
        IsIso ((((sheafToPresheaf Y.siteTopology AddCommGrpCat.{max u v}).map
          ((SheafOfModules.toSheaf Y.structureSheaf).map φ)).app (Opposite.op I.Y)))) :
    IsIso φ := by
  sorry

/-
Helper for Lemma 21.50.1: evaluating a module map at `U` is the same as evaluating its
localized restriction at the terminal object of `Y/U`. -/
omit [MonoidalCategory DModY]
  [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
  [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ U : Y, (localizedRestriction Y U).Additive]
  [∀ U : Y, PreservesFiniteLimits (localizedRestriction Y U)]
  [∀ U : Y, PreservesFiniteColimits (localizedRestriction Y U)]
  [CategoryWithHomology (ModuleCat Y)]
  [∀ U : Y, CategoryWithHomology (ModuleCat (Y.localization U))] in
private theorem evaluation_map_eq_terminal_localizedRestriction_map
    (U : Y) {M N : ModuleCat Y} (φ : M ⟶ N) :
    (SheafOfModules.evaluation Y.structureSheaf (Opposite.op U)).map φ =
      (SheafOfModules.evaluation (Y.localization U).structureSheaf
        (Opposite.op (Over.mk (𝟙 U)))).map ((localizedRestriction Y U).map φ) := by
  -- Both sides are definitionally the same terminal evaluation of the restricted module morphism.
  rfl

/-- Helper for Lemma 21.50.1: a morphism of `𝒪_Y`-modules is an isomorphism once every
object admits a cover whose localized restrictions are isomorphisms. -/
private lemma module_map_isIso_of_coverwise_localized_isIso
    {M N : ModuleCat Y} (φ : M ⟶ N)
    (hcoverIso :
      ∀ V : Y, ∃ S : Y.siteTopology.Cover V, ∀ I : S.Arrow,
        IsIso ((localizedRestriction Y I.Y).map φ)) :
    IsIso φ := by
  sorry

/-- Helper for Lemma 21.50.1: a morphism in `DModY` is an isomorphism once
each homology map becomes an isomorphism after passing to a cover and localizing on every object
of `Y`. -/
private lemma derived_map_isIso_of_coverwise_homology_localized_isIso
    {K L : DModY} (φ : K ⟶ L)
    (hcoverIso :
      ∀ i : ℤ, ∀ V : Y, ∃ S : Y.siteTopology.Cover V, ∀ I : S.Arrow,
        IsIso ((localizedRestriction Y I.Y).map
          ((DerivedCategory.homologyFunctor (ModuleCat Y) i).map φ))) :
    IsIso φ := by
  -- Reduce the derived claim to the homology sheaves, then apply the module-level local descent
  -- criterion degreewise.
  rw [CategoryTheory.derivedCategory_isIso_iff_homology_map_isIso]
  intro i
  exact module_map_isIso_of_coverwise_localized_isIso
    ((DerivedCategory.homologyFunctor (ModuleCat Y) i).map φ)
    (hcoverIso i)

-- Proof sketch: the statement is local on the target ringed topos, so for a perfect object `K`
-- one works on a cover where `K` is represented by a strictly perfect complex. The projection
-- formula is immediate for finite free summands and stable under finite direct sums, summands, and
-- stupid truncations, reducing to the case `K = 𝒪_Y[n]`.
/-- Lemma 21.50.1: for a morphism of ringed topoi formalized by the ringed-site morphism `f`, if
`K` is a perfect object of `DModY`, then the canonical projection-formula morphism
`K ⊗ R(f)_* E ⟶ R(f)_*((L(f)^*).obj K ⊗ E)`
is an isomorphism in `DModY`. -/
@[stacks 0944]
private theorem projectionFormulaMorphism_isIso_of_isPerfect_aux
    (modulePullbackDerived_pushforward_adjunction : L(f)^* ⊣ R(f)_*)
    (modulePullbackDerivedTensorIso :
      ∀ L : DModY,
        (tensoringRight DModY).obj L ⋙ L(f)^* ≅
          L(f)^* ⋙ (tensoringRight DModX).obj ((L(f)^*).obj L))
    (E : DModX) (K : DModY) (hK : K.IsPerfect) :
    IsIso
      (projectionFormulaMorphism
        (L(f)^*)
        (R(f)_*)
        (modulePullbackDerived_pushforward_adjunction)
        (fun K L ↦ (modulePullbackDerivedTensorIso L).app K)
        E
        K) := by
  sorry

end

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [HasBinaryProducts Y.carrier]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : Y, (localizedRestriction Y U).Additive]
variable [∀ U : Y, PreservesFiniteLimits (localizedRestriction Y U)]
variable [∀ U : Y, PreservesFiniteColimits (localizedRestriction Y U)]
variable [CategoryWithHomology (ModuleCat Y)]
variable [∀ U : Y, CategoryWithHomology (ModuleCat (Y.localization U))]

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

/-- Lemma 21.50.1: for a morphism of ringed topoi formalized by the ringed-site morphism `f`, if
`K` is a perfect object of `DModY`, then the projection-formula morphism attached to the canonical
derived adjunction data `adj : L(f)^* ⊣ R(f)_*` is an isomorphism. The pullback-tensor comparison remains
primitive bridge data in this ringed-site formalization. -/
@[stacks 0944]
instance projectionFormulaMorphism_isIso_of_isPerfect
    (adj : L(f)^* ⊣ R(f)_*)
    (pullbackTensorIso :
      ∀ L : DModY,
        (tensoringRight DModY).obj L ⋙ L(f)^* ≅
          L(f)^* ⋙ (tensoringRight DModX).obj ((L(f)^*).obj L))
    (E : DModX) (K : DModY) (hK : K.IsPerfect) :
    IsIso
      (projectionFormulaMorphism
        (L(f)^*)
        (R(f)_*)
        adj
        (fun A B ↦ (pullbackTensorIso B).app A)
        E
        K) := by
  simpa using
    (projectionFormulaMorphism_isIso_of_isPerfect_aux
      f
      adj
      pullbackTensorIso
      E
      K
      hK)

end

end RingedSite.Hom
