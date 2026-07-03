import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_31_1 (from Chap06) -/
open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe u v

section

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 6.31.1:
- primary domain: restriction / inverse image of presheaves and sheaves along an open inclusion in
  `TopCat`;
- sampled owner declarations:
  `TopCat.Presheaf.pullbackObjObjOfImageOpen`,
  `Topology.IsOpenEmbedding.sheafPullbackIso`,
  `TopCat.Sheaf.stalkPullbackIso`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `Adjunction.isIso_counit_of_iso`;
- owner abstraction: the canonical owners are the pullback and stalk comparison APIs for open maps
  and open embeddings, together with the pullback-pushforward adjunction and the explicit functor
  isomorphism `j_* ⋙ j⁻¹ ≅ 𝟭` for an open inclusion; the source-facing counit-is-iso statements
  should therefore be thin companions to that owner-level comparison;
- primitive data: an open subset `U : Opens X`, together with a presheaf or sheaf on `X`;
- derived API: the objectwise and stalkwise identifications for restriction to `U`, and the
  resulting counit isomorphisms.

Source/core/bridge triage:
- `source-facing`: the Stacks specialization to the inclusion `j : U ↪ X`;
- `core/canonical`: the mathlib and chapter owners above;
- `bridge/view`: only the counit-is-iso clauses remain as local declarations. -/

/- Lemma 6.31.1 (1): for an open inclusion `j : U ↪ X`, the presheaf pullback of `ℱ` evaluates on
an open `V ⊆ U` as the value of `ℱ` on the same open subset viewed in `X`. This is exactly the
open-inclusion specialization of the canonical owner
`TopCat.Presheaf.pullbackObjObjOfImageOpen`. -/
recall TopCat.Presheaf.pullbackObjObjOfImageOpen

/- Lemma 6.31.1 (2): for a sheaf `𝒢` on `X`, the inverse-image sheaf along the open inclusion
`j : U ↪ X` is given on an open `V ⊆ U` by the sections of `𝒢` on the same open viewed in `X`.
This is the objectwise specialization of the open-embedding owner
`Topology.IsOpenEmbedding.sheafPullbackIso`. -/
recall Topology.IsOpenEmbedding.sheafPullbackIso

/- Lemma 6.31.1 (3): for `x ∈ U`, the stalk of the inverse-image sheaf `j⁻¹𝒢` at `x` is
canonically identified with the stalk of `𝒢` at the corresponding point of `X`. This is exactly
the chapter owner `TopCat.Sheaf.stalkPullbackIso`, specialized to `Opens.inclusion' U`. -/
recall TopCat.Sheaf.stalkPullbackIso

private noncomputable def openSubsetPresheafPushforwardPullbackIso
    {C : Type v} [Category.{u} C] [CategoryTheory.Limits.HasColimits C] (U : Opens X) :
    TopCat.Presheaf.pushforward C U.inclusion' ⋙ TopCat.Presheaf.pullback C U.inclusion' ≅
      𝟭 ((TopCat.of U).Presheaf C) := by
  let openFunctor : Opens (TopCat.of U) ⥤ Opens X := U.isOpenEmbedding.functor
  let eComp : openFunctor.op ⋙ (Opens.map U.inclusion').op ≅
      𝟭 ((Opens (TopCat.of U))ᵒᵖ) :=
    NatIso.ofComponents
      (fun V ↦ eqToIso (by simp [openFunctor]))
      (fun {V W} i ↦ by
        apply Subsingleton.elim)
  change (Functor.whiskeringLeft _ _ _).obj (Opens.map U.inclusion').op ⋙
      TopCat.Presheaf.pullback C U.inclusion' ≅ _
  exact
    Functor.isoWhiskerLeft _ (IsOpenMap.pullbackIso U.isOpenEmbedding.isOpenMap) ≪≫
      (Functor.whiskeringLeftObjCompIso openFunctor.op
        (Opens.map U.inclusion').op).symm ≪≫
      (Functor.whiskeringLeft _ _ _).mapIso eComp ≪≫
      Functor.whiskeringLeftObjIdIso

private noncomputable def openSubsetSheafPushforwardSheafPullbackIso
    (U : Opens X) :
    TopCat.Sheaf.pushforward (Type u) U.inclusion' ⋙ U.isOpenEmbedding.sheafPullback (Type u) ≅
      𝟭 ((TopCat.of U).Sheaf (Type u)) := by
  let openFunctor : Opens (TopCat.of U) ⥤ Opens X := U.isOpenEmbedding.functor
  let inclusionMap : Opens X ⥤ Opens (TopCat.of U) := Opens.map U.inclusion'
  let J : GrothendieckTopology (Opens (TopCat.of U)) := Opens.grothendieckTopology (TopCat.of U)
  let K : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  haveI : openFunctor.IsContinuous J K := by
    simpa [openFunctor, J, K] using U.isOpenEmbedding.functor_isContinuous
  haveI : inclusionMap.IsContinuous K J := by
    apply Functor.isContinuous_of_coverPreserving
    · simpa [inclusionMap, J, K] using compatiblePreserving_opens_map U.inclusion'
    · simpa [inclusionMap, J, K] using coverPreserving_opens_map U.inclusion'
  haveI : (openFunctor ⋙ inclusionMap).IsContinuous J J := by
    simpa [openFunctor, inclusionMap, J, K] using
      (Functor.isContinuous_comp openFunctor inclusionMap J K J)
  let eComp : openFunctor ⋙ inclusionMap ≅ 𝟭 (Opens (TopCat.of U)) :=
    NatIso.ofComponents
      (fun V ↦ eqToIso (by
        change inclusionMap.obj (openFunctor.obj V) = V
        exact map_functor_eq V))
      (fun {V W} i ↦ by
        apply Subsingleton.elim)
  simpa [TopCat.Sheaf.pushforward, Topology.IsOpenEmbedding.sheafPullback, openFunctor,
    inclusionMap, J, K] using
    (openFunctor.sheafPushforwardContinuousComp inclusionMap (Type u) J K J ≪≫
      Functor.sheafPushforwardContinuousId' eComp (Type u) J)

private noncomputable def openSubsetSheafPushforwardPullbackIso
    (U : Opens X) :
    TopCat.Sheaf.pushforward (Type u) U.inclusion' ⋙ TopCat.Sheaf.pullback (Type u) U.inclusion' ≅
      𝟭 ((TopCat.of U).Sheaf (Type u)) :=
  Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type u) U.inclusion')
    (U.isOpenEmbedding.sheafPullbackIso (Type u)) ≪≫
      openSubsetSheafPushforwardSheafPullbackIso U

/-- Lemma 6.31.1 (1): on presheaves over `U`, the counit `j_p j_* ⟶ 𝟭` is an isomorphism. -/
theorem openSubsetPresheafPullbackPushforwardCounit_isIso
    {C : Type v} [Category.{u} C] [CategoryTheory.Limits.HasColimits C] (U : Opens X) :
    IsIso
      (TopCat.Presheaf.pullbackPushforwardAdjunction C U.inclusion').counit := by
  let _ :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction C U.inclusion').isIso_counit_of_iso
      (openSubsetPresheafPushforwardPullbackIso U)
  infer_instance

/-- Lemma 6.31.1 (2): on sheaves over `U`, the counit `j⁻¹ j_* ⟶ 𝟭` is an isomorphism. -/
theorem openSubsetSheafPullbackPushforwardCounit_isIso
    (U : Opens X) :
    IsIso
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) U.inclusion').counit := by
  let _ :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) U.inclusion').isIso_counit_of_iso
      (openSubsetSheafPushforwardPullbackIso U)
  infer_instance

end

/-! ### Definition_6_31_2 (from Chap06) -/
open CategoryTheory Opposite TopCat TopologicalSpace CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

/-
Domain-style sampling for Definition 6.31.2:
- primary domain: restriction / inverse image of presheaves, sheaves, and ringed-space objects
  along the inclusion of an open subset;
- sampled owner declarations:
  `TopCat.Presheaf.pullback`,
  `TopCat.Sheaf.pullback`,
  `PresheafOfModules.pullback`,
  `SheafedSpace.restrict`;
- best owner abstraction: restriction is the canonical pullback/restriction along the open
  inclusion `U.inclusion'`; source-facing open-subset notation should be the only thin bridge,
  while the module-valued restriction functor should be exposed through the canonical owner
  `PresheafOfModules.pullback` rather than a parallel wrapper object;
- primitive data: the open inclusion `U.inclusion'`;
- derived API: restriction notation for sheaves and morphisms, and the module-valued pullback
  induced by the adjunction unit.

Source/core/bridge triage:
- `source-facing`: the open-subset restriction surface `𝒢 ↾ U` and `φ ↾ₘ U`;
- `core/canonical`: `TopCat.Presheaf.pullback`, `TopCat.Sheaf.pullback`,
  `PresheafOfModules.pullback`, and the inherited restriction construction
  `X.restrict U.isOpenEmbedding`;
- `bridge/view`: the open-subset specializations obtained by evaluating those owners at
  `U.inclusion'`.
-/

/-
Definition 6.31.2 (presheaf restriction): the restriction of a presheaf to an open subset is the
canonical pullback along the open inclusion. The owner declaration is `TopCat.Presheaf.pullback`.
-/
recall TopCat.Presheaf.pullback

/-
Definition 6.31.2 (sheaf restriction): the restriction of a sheaf to an open subset is the
canonical pullback along the open inclusion. The owner declaration is `TopCat.Sheaf.pullback`.
-/
recall TopCat.Sheaf.pullback

end

-- Sheaf restriction notation, specialized directly from the canonical pullback owner.
namespace TopCat

set_option quotPrecheck false in
scoped notation:80 𝒢:80 " ↾ " U:80 =>
  (TopCat.Sheaf.pullback _ (Opens.inclusion' U)).obj 𝒢

-- Restriction notation for sheaf morphisms, specialized directly from the same owner.
set_option quotPrecheck false in
scoped notation:80 φ:80 " ↾ₘ " U:80 =>
  (TopCat.Sheaf.pullback _ (Opens.inclusion' U)).map φ

end TopCat

noncomputable section

variable {X : TopCat.{u}}
variable (U : Opens X) (𝒪 : X.Presheaf RingCat.{u})

/- Definition 6.31.2 (presheaf-module restriction): for an open inclusion `j : U ↪ X`,
restriction of `𝒪`-modules is the canonical owner `PresheafOfModules.pullback`. -/
recall PresheafOfModules.pullback

/- Companion specialization to the open-subset inclusion `U.inclusion'`. -/
#check
  (PresheafOfModules.pullback
      ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪) :
    PresheafOfModules 𝒪 ⥤
      PresheafOfModules ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪))

/- Definition 6.31.2 (ringed-space restriction): the core owner is the inherited restriction
construction `SheafedSpace.restrict`; for ringed spaces this specializes to `X.restrict
U.isOpenEmbedding`. -/
recall SheafedSpace.restrict

/- Companion ringed-space specialization. -/
#check fun (X : RingedSpace.{u}) (U : Opens X.carrier) ↦ X.restrict U.isOpenEmbedding

end

/-! ### Definition_6_31_3 (from Chap06) -/
open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe v

/-
Domain-style sampling for Definition 6.31.3:
- primary domain: extension by zero / by the initial object along the inclusion `j : U ↪ X` of an
  open subset, specialized to set-valued presheaves and sheaves;
- sampled owner declarations:
  `extensionByZeroOpenSubsetSpace`,
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`;
- owner abstraction: the canonical owners are the presheaf and sheaf functors above on the open
  subspace `extensionByZeroOpenSubsetSpace U`; this file should specialize those owners to
  `Type v` rather than introduce a parallel set-specific wrapper;
- primitive data versus derived API: the primitive input is the open subset `U`, together with the
  canonical open-subspace object and the upstream extension-by-initial-object owners. The
  set-valued “extension by the empty set” phrasing is derived from the fact that the initial object
  of `Type v` is the empty type, and the sheaf-level construction is derived by sheafifying the
  presheaf-level owner.

Source/core/bridge triage:
- `source-facing`: the Stacks set-valued phrasing “extension by the empty set” on an open subset;
- `core/canonical`: `openSubsetPresheafExtensionByInitialObject` and
  `openSubsetSheafExtensionByInitialObject`;
- `bridge/view`: the specialization `C = Type v`, where the initial object is the empty type.
-/

section

variable {X : TopCat.{v}}

section PresheafCase

variable (U : Opens X)

/- Definition 6.31.3, core/canonical recall: the owner construction for extension by zero along an
open subset is `openSubsetPresheafExtensionByInitialObject`. -/
recall openSubsetPresheafExtensionByInitialObject

/- Definition 6.31.3, source-facing specialization: for presheaves of sets on an open subset
`U ⊆ X`, extension by the empty set is the `Type v` specialization `jₚ! U`; in `Type v`, the
initial object is the empty type. -/
#check
  (jₚ! U :
    (extensionByZeroOpenSubsetSpace U).Presheaf (Type v) ⥤ X.Presheaf (Type v))

end PresheafCase

section SheafCase

variable (U : Opens X)

/- Definition 6.31.3, core/canonical recall: the owner construction for sheaf-level extension by
the initial object along an open subset is `openSubsetSheafExtensionByInitialObject`. -/
recall openSubsetSheafExtensionByInitialObject

/- Definition 6.31.3, source-facing specialization: for sheaves of sets on an open subset
`U ⊆ X`, extension by the empty set is the `Type v` specialization `j! U`; by definition it is
obtained by sheafifying the presheaf-level construction. -/
#check
  (j! U :
    (extensionByZeroOpenSubsetSpace U).Sheaf (Type v) ⥤ X.Sheaf (Type v))

end SheafCase

end

/-! ### Lemma_6_31_4 (from Chap06) -/
open TopCat

noncomputable section

universe u

/- 
Domain-style sampling for Lemma 6.31.4:
- primary domain: extension by the initial object along the inclusion `j : U ↪ X` of an open
  subset, specialized to presheaves and sheaves of sets;
- sampled owner declarations:
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`,
  `OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`;
- owner abstraction: the Chapter 6 owner is `OpenSubsetExtensionByInitial`; this file should stay
  `source-facing` and reuse that owner directly rather than restating set-specific wrappers;
- primitive data: the open subset `U`, the point `x`, and the upstream owner functors on
  `extensionByZeroOpenSubsetSpace U`;
- derived API: the `Type u` specialization of the adjunctions, stalk description, and unit
  isomorphisms.

Source/core/bridge triage:
- `source-facing`: the five Stacks-project statements about extension by the empty set on
  presheaves and sheaves of sets;
- `core/canonical`: the owner declarations in `OpenSubsetExtensionByInitial`;
- `bridge/view`: the specialization `C = Type u`, where the initial object is the empty type.
-/

section

variable {X : TopCat.{u}}

/- Lemma 6.31.4 (1): on presheaves of sets over an open subset `U ⊆ X`, extension by the empty
set is left adjoint to restriction to `U`. This is the specialization of the canonical
presheaf-level extension-by-initial-object adjunction to `Type u`, where the initial object is the
empty type. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction

/- Lemma 6.31.4 (2): on sheaves of sets over an open subset `U ⊆ X`, extension by the empty set
is left adjoint to restriction to `U`. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction

/- Lemma 6.31.4 (3): for a point `x` of `X`, the stalk of the extension-by-empty sheaf `j_! ℱ`
is canonically identified with the stalk of `ℱ` when `x ∈ U`, and with the empty set when
`x ∉ U`. The owner stalk-description theorem is `sheafExtensionByInitial_stalkIso` (the canonical
by-cases stalk iso), with branch identifications `_stalkIso_comp_eq_of_mem` / `_of_not_mem`. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso

/- Lemma 6.31.4 (4): on presheaves over `U`, the unit
`𝟭 ⟶ j_p j_{p!}` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialUnitIso

/- Lemma 6.31.4 (5): on sheaves over `U`, the unit
`𝟭 ⟶ j⁻¹ j_!` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso

end

/-! ### Definition_6_31_5 (from Chap06) -/
open CategoryTheory TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u v

/-
Domain-style sampling for Definition 6.31.5:
- primary domain: extension by zero / extension by the initial object along the inclusion
  `j : U ↪ X` of an open subset, for presheaves, sheaves, and modules;
- sampled owner declarations:
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`,
  `openSubsetModulePresheafExtensionByZero`,
  `openSubsetModuleSheafExtensionByZero`;
- source/core/bridge triage:
  `source-facing`: the six Stacks variants of extension by zero along an open immersion;
  `core/canonical`: the owner functors above, built on `extensionByZeroOpenSubsetSpace U` and the
  canonical pullback functors along `extensionByZeroOpenSubsetInclusion U`;
  `bridge/view`: the abelian specialization `C = AddCommGrpCat` of extension by the initial
  object, and the module-valued specializations obtained from the ambient ring object on `X`;
- primitive data versus derived API: the primitive inputs are the open subset `U`, the target
  category together with the initial-object and sheafification hypotheses needed by the owner
  functors, and in the module case the ambient ring-valued presheaf or sheaf `𝒪`. The abelian and
  module statements here are derived specializations of those owners, so this file should recall or
  check the canonical upstream declarations directly rather than keep parallel local wrappers.
-/

section

variable {X : TopCat.{u}}

section AbelianExtensionByZero

variable (U : Opens X)

/- Definition 6.31.5 (1), source-facing specialization: for an abelian presheaf `ℱ` on `U`,
extension by zero is the `AddCommGrpCat` specialization `jₚ! U` of the canonical presheaf owner
`openSubsetPresheafExtensionByInitialObject`. -/
#check
  (jₚ! U :
    (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u} ⥤ X.Presheaf AddCommGrpCat.{u})

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Definition 6.31.5 (2), source-facing specialization: for an abelian sheaf `ℱ` on `U`,
extension by zero is the `AddCommGrpCat` specialization `j! U` of the canonical sheaf owner
`openSubsetSheafExtensionByInitialObject`. -/
#check
  (j! U :
    (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u})

end AbelianExtensionByZero

section PresheafExtensionByInitial

variable {C : Type v} [Category.{v} C] [HasInitial C]
variable (U : Opens X)

/- Definition 6.31.5 (3): for a category `C` with an initial object, extension by the initial
object along `U ↪ X` is the canonical presheaf functor
`openSubsetPresheafExtensionByInitialObject U`. -/
recall openSubsetPresheafExtensionByInitialObject

end PresheafExtensionByInitial

section SheafExtensionByInitial

variable {C : Type v} [Category.{v} C] [HasInitial C]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]
variable (U : Opens X)

/- Definition 6.31.5 (4): for sheaves valued in a category with an initial object and
sheafification, extension by the initial object along `U ↪ X` is the canonical sheaf functor
`openSubsetSheafExtensionByInitialObject U`. -/
recall openSubsetSheafExtensionByInitialObject

end SheafExtensionByInitial

section ModulePresheafExtensionByZero

variable (U : Opens X)
variable (𝒪 : X.Presheaf RingCat.{u})

/- Definition 6.31.5 (5): for a presheaf of rings `𝒪` on `X`, extension by zero on
`𝒪|_U`-modules is the canonical module-valued presheaf functor
`openSubsetModulePresheafExtensionByZero U 𝒪`. -/
recall openSubsetModulePresheafExtensionByZero

/- Companion specialization to the ambient ring-valued presheaf `𝒪`. -/
#check
  ((openSubsetModulePresheafExtensionByZero U 𝒪) :
    PresheafOfModules
        ((Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      PresheafOfModules 𝒪)

end ModulePresheafExtensionByZero

section ModuleSheafExtensionByZero

variable (U : Opens X)
variable (𝒪 : X.Sheaf RingCat.{u})

/- Definition 6.31.5 (6): for a sheaf of rings `𝒪` on `X`, extension by zero on `𝒪|_U`-modules
is the canonical module-valued sheaf functor `openSubsetModuleSheafExtensionByZero U 𝒪`. -/
recall openSubsetModuleSheafExtensionByZero

/- Companion specialization to the ambient ring-valued sheaf `𝒪`. -/
#check
  ((openSubsetModuleSheafExtensionByZero U 𝒪) :
    SheafOfModules
        ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      SheafOfModules 𝒪)

end ModuleSheafExtensionByZero

end

/-! ### Lemma_6_31_6 (from Chap06) -/
open CategoryTheory TopCat
open TopologicalSpace.Opens

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.6:
- primary domain: extension by zero / extension by the initial object for presheaves and sheaves of
  abelian groups along an open immersion;
- sampled owner declarations:
  `OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso`;
- owner abstraction: the Chapter 6 owner is the generic
  `OpenSubsetExtensionByInitial` API for extension by the initial object along
  `extensionByZeroOpenSubsetInclusion U`;
- primitive data: the open subset `U`, the point `x`, and the abelian sheaf or presheaf on the
  open subspace `extensionByZeroOpenSubsetSpace U`;
- derived API: the abelian-group specialization of the owner adjunction, stalk description, and
  unit isomorphisms.

Source/core/bridge triage:
- `source-facing`: the five Stacks-project statements about extension by zero for abelian sheaves
  and presheaves;
- `core/canonical`: the owner declarations in `OpenSubsetExtensionByInitial`;
- `bridge/view`: this file’s `AddCommGrpCat` specialization of those owner declarations.

The file should therefore reuse the owner declarations directly and avoid keeping a second public
stalk-isomorphism wrapper with the same interface.
-/

section Presheaf

variable {X : TopCat.{u}}

/- Lemma 6.31.6 (1): for an open subset `U ⊆ X`, extension by zero on presheaves of abelian
groups is left adjoint to restriction to `U`. This is the `AddCommGrpCat` specialization of the
canonical extension-by-initial-object adjunction. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction

/- Lemma 6.31.6 (4): on presheaves of abelian groups over `U`, the unit
`𝟭 ⟶ j_p j_{p!}` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialUnitIso

end Presheaf

section Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Lemma 6.31.6 (2): for an open subset `U ⊆ X`, extension by zero on sheaves of abelian groups
is left adjoint to restriction to `U`. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction

/- Lemma 6.31.6 (3): for a point `x` of `X`, the stalk of the extension-by-zero sheaf `j_! ℱ`
is canonically identified with the stalk of `ℱ` when `x ∈ U`, and with the zero object when
`x ∉ U`. This is the `AddCommGrpCat` specialization of the owner stalk iso
`OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso` (branch identifications
`_stalkIso_comp_eq_of_mem` / `_of_not_mem`). -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso

/- Lemma 6.31.6 (5): on sheaves of abelian groups over `U`, the unit
`𝟭 ⟶ j⁻¹ j_!` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso

end Sheaf
