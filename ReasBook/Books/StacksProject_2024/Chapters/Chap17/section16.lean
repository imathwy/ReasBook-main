import Mathlib
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_16_1 (from Chap17) -/
open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

local infixr:70 " ⊗ " => moduleTensor

/-
Domain-style sampling for Lemma 17.16.1:
- primary domain: sheaves of modules on a ringed space, their sheaf tensor product, and stalks
- inspected owner declarations:
  `RingedSpace.stalkModuleCat`,
  `moduleTensor`,
  `CategoryTheory.toSheafify`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`,
  `PresheafOfModules.germ_smul`
- best owner abstraction:
  the bundled stalk-module owner `RingedSpace.stalkModuleCat` together with the canonical sheaf tensor
  product `moduleTensor`
- primitive data:
  two `\mathcal O_X`-modules `ℱ`, `𝒢` and a point `x : X`
- derived API:
  the canonical `\mathcal O_{X, x}`-linear comparison morphism from
  `RingedSpace.stalkModuleCat (ℱ ⊗ 𝒢) x` to the tensor product of the bundled stalk modules,
  together with the resulting isomorphism

Layer triage:
- `source-facing`: the stalkwise tensor-product comparison from the source
- `core/canonical`: `(RingedSpace.Modules X)`, `moduleTensor`, and `RingedSpace.stalkModuleCat`
- `bridge/view`: the explicit presheaf-level filtered-colimit comparison used to define the public
  module morphism
-/

private abbrev tensorPresheaf (ℱ 𝒢 : (RingedSpace.Modules X)) :=
  PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val

private abbrev stalkRing (x : X) :=
  X.presheaf.stalk x

private abbrev stalkRingGerm (U : Opens X) (x : X) (hx : x ∈ U) :=
  X.presheaf.germ U x hx

private abbrev stalkTensor (ℱ 𝒢 : (RingedSpace.Modules X)) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (↑(stalkModuleCat ℱ x) ⊗[X.presheaf.stalk x]
      ↑(stalkModuleCat 𝒢 x))

private def stalkGermLinear (ℱ : (RingedSpace.Modules X)) (x : X) (U : Opens X) (hx : x ∈ U) :
    ↑(ℱ.val.obj (op U)) →ₛₗ[(stalkRingGerm U x hx).hom]
      ↑(stalkModuleCat ℱ x) where
  toFun := fun s ↦ (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) s
  map_add' := by
    intro s t
    simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add s t
  map_smul' := by
    intro r s
    simpa using (PresheafOfModules.germ_smul ℱ.val x U hx r s)

private abbrev tensorGermHom (ℱ 𝒢 : (RingedSpace.Modules X)) (x : X) (U : Opens X) (hx : x ∈ U) :
    (tensorPresheaf ℱ 𝒢).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkTensor ℱ 𝒢 x) :=
  AddCommGrpCat.ofHom <|
    (TensorProduct.map (stalkGermLinear ℱ x U hx) (stalkGermLinear 𝒢 x U hx)).toAddMonoidHom

private def presheafTensorStalkComparison (ℱ 𝒢 : (RingedSpace.Modules X)) (x : X) :
    TopCat.Presheaf.stalk (tensorPresheaf ℱ 𝒢).presheaf x ⟶ AddCommGrpCat.of ↑(stalkTensor ℱ 𝒢 x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (tensorPresheaf ℱ 𝒢).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ by
          exact tensorGermHom ℱ 𝒢 x (Opposite.unop U).1 (Opposite.unop U).2
        naturality := by
          intro U V i
          sorry }

-- Proof sketch: the unit map from the presheaf tensor product to its sheafification becomes an
-- isomorphism on stalks by `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`; composing its
-- inverse with the explicit filtered-colimit map from the stalk of the presheaf tensor product to
-- the tensor product of the two stalks yields the canonical `\mathcal O_{X, x}`-linear
-- comparison morphism.
/-- The canonical `\mathcal O_{X, x}`-linear comparison from the stalk of the sheaf tensor product
to the tensor product of the two stalk modules. -/
noncomputable def tensorProductStalkComparison (ℱ 𝒢 : (RingedSpace.Modules X)) (x : X) :
    stalkModuleCat (ℱ ⊗ 𝒢) x ⟶
      ModuleCat.of (X.presheaf.stalk x)
        (↑(stalkModuleCat ℱ x) ⊗[X.presheaf.stalk x]
          ↑(stalkModuleCat 𝒢 x)) := by
  let η :
      TopCat.Presheaf.stalk (tensorPresheaf ℱ 𝒢).presheaf x ⟶
        TopCat.Presheaf.stalk (ℱ ⊗ 𝒢).val.presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (tensorPresheaf ℱ 𝒢).presheaf)
  haveI : IsIso η := by
    simpa [η] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (tensorPresheaf ℱ 𝒢).presheaf)
  let comparison :
      TopCat.Presheaf.stalk (ℱ ⊗ 𝒢).val.presheaf x ⟶ AddCommGrpCat.of ↑(stalkTensor ℱ 𝒢 x) :=
    inv η ≫ presheafTensorStalkComparison ℱ 𝒢 x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

/-- The canonical stalk comparison for the sheaf tensor product is an isomorphism. -/
instance tensorProductStalkComparison_isIso (ℱ 𝒢 : (RingedSpace.Modules X)) (x : X) :
    IsIso (tensorProductStalkComparison ℱ 𝒢 x) := sorry

/-- Lemma 17.16.1: the stalk of the sheaf tensor product `\mathcal F \otimes_{\mathcal O_X}
\mathcal G` is canonically isomorphic to the tensor product of the stalks
`\mathcal F_x \otimes_{\mathcal O_{X, x}} \mathcal G_x`. -/
noncomputable abbrev tensorProductStalkIso (ℱ 𝒢 : (RingedSpace.Modules X)) (x : X) :
    stalkModuleCat (ℱ ⊗ 𝒢) x ≅
      ModuleCat.of (X.presheaf.stalk x)
        (↑(stalkModuleCat ℱ x) ⊗[X.presheaf.stalk x]
          ↑(stalkModuleCat 𝒢 x)) :=
  asIso (tensorProductStalkComparison ℱ 𝒢 x)

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_16_2 (from Chap17) -/
open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-
Domain-style sampling for Lemma 17.16.2:
- primary domain: sheaf tensor products of modules over the structure sheaf of a ringed space,
  built from the ambient sheaf-of-rings tensor product and module-sheafification functor;
- inspected owner declarations:
  `RingedSpace.ringCatSheaf`,
  `_root_.moduleTensor`,
  `_root_.moduleSheafification`,
  `_root_.moduleSheafificationTensorComparison`,
  `_root_.moduleSheafificationTensorIso`;
- best owner abstraction:
  the core/canonical owner is the site-level sheaf-of-rings API on
  `SheafOfModules (ringSheaf (Opens.grothendieckTopology X) X.sheaf)`, while the ringed-space
  surface is `SheafOfModules (RingedSpace.ringCatSheaf X)`;
- primitive data:
  two presheaves of `\mathcal O_X`-modules;
- derived API:
  the ringed-space specialization of the canonical tensor-sheafification comparison and its
  associated isomorphism.

Layer triage:
- `source-facing`: the canonical isomorphism between the tensor product of the sheafifications and
  the sheafification of the presheaf tensor product;
- `core/canonical`: the Chapter 18 owners `_root_.moduleTensor` and `_root_.moduleSheafification`;
- `bridge/view`: the specialization from a sheaf of commutative rings to the structure sheaf
  `X.sheaf`.
-/

/- Lemma 17.16.2: for presheaves of `\mathcal O_X`-modules `ℱ'` and `𝒢'`, the tensor product of
their sheafifications is canonically identified with the sheafification of their presheaf tensor
product. This is the ringed-space specialization of
`_root_.moduleSheafificationTensorIso`. -/
#check
  (moduleSheafificationTensorIso X.sheaf :
    ∀ (ℱ' 𝒢' : PresheafOfModules (RingedSpace.ringCatSheaf X).obj),
      (moduleSheafification X.sheaf).obj ℱ' ⊗ (moduleSheafification X.sheaf).obj 𝒢' ≅
        (moduleSheafification X.sheaf).obj (PresheafOfModules.Monoidal.tensorObj ℱ' 𝒢'))

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_16_3 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "ModX" => SheafOfModules (ringCatSheaf X)

/-
Domain-style sampling for Lemma 17.16.3:
- primary domain: tensoring sheaves of modules on a ringed space on the right, viewed as an
  endofunctor of the ambient module category and measured by the canonical exactness owners;
- inspected owner declarations:
  `moduleTensorMap`,
  `sheafModuleTensorRightFunctor`,
  `rightExactFunctor`,
  `rightExactFunctor_iff`;
- best owner abstraction: the chapter/project owner for right tensoring is the site-level functor
  `sheafModuleTensorRightFunctor`, specialized to the opens-site ringed space
  `(RingedSpace.ringCatSheaf X)`;
- primitive data: only the fixed right tensor factor `𝒢 : RingedSpace.Modules X`;
- derived API: the right-exactness statement for that owner functor.

Source/core/bridge triage:
- `source-facing`: tensoring an exact sequence
  `\mathcal F_1 \to \mathcal F_2 \to \mathcal F_3 \to 0` on the right by `\mathcal G` preserves
  exactness and the terminal epimorphism;
- `core/canonical`: `sheafModuleTensorRightFunctor` together with the owner predicate
  `rightExactFunctor`;
- `bridge/view`: the ringed-space specialization from sheaves of modules on a ringed site to
  `(RingedSpace.Modules X)`.

Primitive-vs-derived check:
- the local Chapter 17 wrappers `moduleTensorRightMap` and `moduleTensorRightFunctor` were exact
  interface copies of the Chapter 18 owners `moduleTensorMap` and
  `sheafModuleTensorRightFunctor`;
- this file should therefore expose the source-facing result directly through the canonical owner
  instead of keeping a parallel wrapper API.
-/

-- Proof sketch: the Stacks lemma is exactly the right-exactness of the canonical tensor-right
-- endofunctor on `Mod(\mathcal O_X)`.
/-- Lemma 17.16.3: tensoring `\mathcal O_X`-modules on a ringed space on the right by a fixed
`\mathcal O_X`-module is right exact. -/
theorem moduleTensor_rightExact
    (𝒢 : ModX) :
    rightExactFunctor ModX ModX (sheafModuleTensorRightFunctor 𝒢) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_16_4 (from Chap17) -/
open CategoryTheory
open Functor.OplaxMonoidal
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for pullback and tensor product of sheaves of modules on a ringed space:
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `CategoryTheory.Functor.OplaxMonoidal.δ`,
  `Lemma_18_26_2`'s `IsIso (δ fStar ℱ 𝒢)` owner instance;
- best owner abstraction:
  for a morphism of ringed spaces `f`, the source-facing pullback-tensor comparison is the
  canonical oplax-monoidal comparison morphism `δ (f^*) ℱ 𝒢`; its isomorphism is already supplied
  by the Chapter 18 owner instance, so the public surface here should recall that comparison and
  its canonical `asIso` bridge directly instead of restating a generic monoidal-functor tensorator;
- primitive data:
  a morphism of ringed spaces `f : X ⟶ Y` and module sheaves `ℱ 𝒢 : Y.Modules`;
- derived API:
  the comparison morphism `δ (f^*) ℱ 𝒢` and the resulting isomorphism `asIso (δ (f^*) ℱ 𝒢)`.

Layer triage:
- `source-facing`: the pullback-tensor comparison for a fixed morphism of ringed spaces;
- `core/canonical`: the owner pullback functor `f^*` together with the oplax-monoidal comparison
  morphism `CategoryTheory.Functor.OplaxMonoidal.δ`;
- `bridge/view`: the isomorphism `asIso (δ (f^*) ℱ 𝒢)` obtained from the established Chapter 18
  `IsIso` instance.
-/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable (ℱ 𝒢 : Y.Modules)

/- Lemma 17.16.4: pullback of the tensor product of two `\mathcal O_Y`-modules is canonically
isomorphic to the tensor product of their pullbacks. In the project owner API this is the
canonical pullback-tensor comparison morphism for `f^*`. -/
#check δ (f^*) ℱ 𝒢

/- Companion bridge: the source-facing isomorphism itself is the canonical `asIso` of that
comparison morphism. -/
#check asIso (δ (f^*) ℱ 𝒢)

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_16_5 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable (ℱ : RingedSpace.Modules X)

/-
Domain-style sampling for Lemma 17.16.5:
- primary domain: tensor products of sheaves of modules on a ringed space and their colimit
  behavior;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `moduleTensor`,
  `tensorLeft`,
  the canonical instance `PreservesColimits (tensorLeft ℱ)`,
  the Chapter 18 site-level specialization in `Lemma_18_27_7`;
- best owner abstraction:
  the source-facing ringed-space tensor product is the chapter/project owner `moduleTensor`; once
  the ambient monoidal closed owner structure on `RingedSpace.Modules X` has been established
  upstream via the Chapter 18 ringed-site tensor calculus, the left tensor functor
  `𝒢 ↦ moduleTensor ℱ 𝒢` is exactly `tensorLeft ℱ`, and the colimit-preservation statement is the
  canonical instance `PreservesColimits (tensorLeft ℱ)`;
- primitive data:
  the ambient monoidal closed structure on `RingedSpace.Modules X` and a fixed
  `\mathcal O_X`-module `ℱ`;
- derived API:
  the fact that the concrete left tensor functor with `ℱ` preserves arbitrary colimits.

Source/core/bridge triage:
- `source-facing`: the ringed-space formulation of Stacks Project Lemma 17.16.5;
- `core/canonical`: `moduleTensor`, `tensorLeft ℱ`, and the canonical
  `PreservesColimits (tensorLeft ℱ)` instance on `RingedSpace.Modules X`;
- `bridge/view`: specialization from sheaves of modules over a sheaf of rings on the opens site to
  the structure sheaf of a ringed space.
-/

/- Lemma 17.16.5: for any `\mathcal O_X`-module `\mathcal F`, the functor
`\mathcal G \mapsto \mathcal F \otimes_{\mathcal O_X} \mathcal G` on `Mod(\mathcal O_X)`
commutes with arbitrary colimits. In the concrete tensor-product owner subtree, this is the
ringed-space specialization of the Chapter 18 owner result on ringed sites, expressed here as the
canonical owner instance `PreservesColimits (tensorLeft ℱ)` on `RingedSpace.Modules X` under the
ambient monoidal closed owner structure. -/
#synth PreservesColimits (tensorLeft ℱ)

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_16_6 (from Chap17) -/
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules}

local infixr:70 " ⊗ " => _root_.moduleTensor

private abbrev IsLocallyGeneratedBySectionsOnRingedSpace (ℱ : X.Modules) : Prop :=
  SheafOfModules.RingedSite.IsLocallyGeneratedBySections ℱ

/- Domain-style sampling for Lemma 17.16.6:
- primary domain: tensor products of `\mathcal O_X`-modules on a ringed space and stability of the
  standard finiteness and local freeness properties;
- inspected owner declarations:
  `SheafOfModules.LocalGeneratorsData`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsCoherent`,
  `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.RingedSite.isFiniteType_ringedSiteModuleTensor`,
  `SheafOfModules.RingedSite.isQuasicoherent_ringedSiteModuleTensor`,
  `SheafOfModules.RingedSite.isFinitePresentation_ringedSiteModuleTensor`,
  `SheafOfModules.RingedSite.isCoherent_ringedSiteModuleTensor_of_isFinitePresentation_left`,
  `SheafOfModules.RingedSite.isCoherent_ringedSiteModuleTensor`,
  `SheafOfModules.RingedSite.isLocallyFree_ringedSiteModuleTensor`;
- best owner abstraction:
  on ringed spaces the source-facing owners are `Nonempty ℱ.LocalGeneratorsData`,
  `ℱ.IsFiniteType`, `ℱ.IsQuasicoherent`, `ℱ.IsFinitePresentation`, `ℱ.IsCoherent`, and
  `ℱ.IsLocallyFree`; clause `(1)` remains a source-facing bridge at the Chapter 17 owner
  `Nonempty ℱ.LocalGeneratorsData`, while clauses `(2)` through `(7)` are exact-interface reuse of
  the Chapter 18 tensor owners and should therefore be recall-only;
- primitive data:
  two module sheaves `ℱ 𝒢 : X.Modules`;
- derived API:
  the tensor-closure statements for the six owner predicates above.

Source/core/bridge triage:
- `source-facing`: the Stacks assertions that tensor products preserve local generation, finite
  type, quasi-coherence, finite presentation, coherence, and local freeness on a ringed space;
- `core/canonical`: the owner predicates on `X.Modules` together with the Chapter 18 tensor
  theorems on `SheafOfModules.RingedSite`;
- `bridge/view`: the ringed-space specialization of the Chapter 18 owner theorems, plus the local
  generator and local freeness statements kept at the Chapter 17 owner level rather than as raw
  neighbourhood data.
-/

-- Proof sketch: refine the local generators data for `ℱ` and `𝒢` to a common cover and apply the
-- tensor construction on generating families on each member of that cover.
private theorem isLocallyGeneratedBySections_of_nonempty_localGeneratorsData
    (hℱ : Nonempty ℱ.LocalGeneratorsData) :
    IsLocallyGeneratedBySectionsOnRingedSpace ℱ := by
  match hℱ with
  | ⟨σ⟩ =>
      exact
        (SheafOfModules.RingedSite.isLocallyGeneratedBySections_iff_exists_cover_isGloballyGenerated_over
          ℱ).2
          ⟨σ.I, σ.X, σ.coversTop, fun i ↦ ⟨σ.generators i⟩⟩

private theorem nonempty_localGeneratorsData_of_isLocallyGeneratedBySections
    (hℱ : IsLocallyGeneratedBySectionsOnRingedSpace ℱ) :
    Nonempty ℱ.LocalGeneratorsData := by
  rcases
      (SheafOfModules.RingedSite.isLocallyGeneratedBySections_iff_exists_cover_isGloballyGenerated_over
        ℱ).1 hℱ
    with ⟨I, Y, hY, hgen⟩
  exact
    ⟨{ I := I
       X := Y
       coversTop := hY
       generators := fun i ↦ Classical.choice (hgen i) }⟩

/-- Lemma 17.16.6 (1): if `\mathcal F` and `\mathcal G` are locally generated by sections, then
`\mathcal F \otimes_{\mathcal O_X} \mathcal G` is locally generated by sections. -/
theorem moduleTensor_nonempty_localGeneratorsData
    (hℱ : Nonempty ℱ.LocalGeneratorsData) (h𝒢 : Nonempty 𝒢.LocalGeneratorsData) :
    Nonempty ((ℱ ⊗ 𝒢).LocalGeneratorsData) := by
  letI := isLocallyGeneratedBySections_of_nonempty_localGeneratorsData hℱ
  letI := isLocallyGeneratedBySections_of_nonempty_localGeneratorsData h𝒢
  have hLocGenTensor :
      IsLocallyGeneratedBySectionsOnRingedSpace (ℱ ⊗ 𝒢) :=
    -- The ringed-space specialization leaves the final universe parameter underconstrained unless
    -- we pin the canonical Chapter 18 theorem to the ambient universe `u`.
    SheafOfModules.RingedSite.isLocallyGeneratedBySections_ringedSiteModuleTensor.{u, u, u, u, u}
      ℱ 𝒢
  exact nonempty_localGeneratorsData_of_isLocallyGeneratedBySections hLocGenTensor

-- Proof sketch: this is exactly the ringed-space specialization of the Chapter 18 owner theorem
-- on tensor products preserving finite type, so no parallel Chapter 17 theorem should remain.
/- Lemma 17.16.6 (2): if `\mathcal F` and `\mathcal G` are of finite type, then
`\mathcal F \otimes_{\mathcal O_X} \mathcal G` is of finite type. This is exactly the canonical
owner theorem `SheafOfModules.RingedSite.isFiniteType_ringedSiteModuleTensor`. -/
recall SheafOfModules.RingedSite.isFiniteType_ringedSiteModuleTensor

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on tensor
-- products preserving quasi-coherence, so the Chapter 18 owner should be recalled directly.
/- Lemma 17.16.6 (3): if `\mathcal F` and `\mathcal G` are quasi-coherent, then
`\mathcal F \otimes_{\mathcal O_X} \mathcal G` is quasi-coherent. This is exactly the canonical
owner theorem `SheafOfModules.RingedSite.isQuasicoherent_ringedSiteModuleTensor`. -/
recall SheafOfModules.RingedSite.isQuasicoherent_ringedSiteModuleTensor

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on tensor
-- products preserving finite presentation, so this clause is recall-only.
/- Lemma 17.16.6 (4): if `\mathcal F` and `\mathcal G` are of finite presentation, then
`\mathcal F \otimes_{\mathcal O_X} \mathcal G` is of finite presentation. This is exactly the
canonical owner theorem `SheafOfModules.RingedSite.isFinitePresentation_ringedSiteModuleTensor`. -/
recall SheafOfModules.RingedSite.isFinitePresentation_ringedSiteModuleTensor

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem for
-- tensoring a finitely presented sheaf with a coherent sheaf, so the canonical owner should be
-- reused directly.
/- Lemma 17.16.6 (5): if `\mathcal F` is of finite presentation and `\mathcal G` is coherent,
then `\mathcal F \otimes_{\mathcal O_X} \mathcal G` is coherent. This is exactly the canonical
owner theorem
`SheafOfModules.RingedSite.isCoherent_ringedSiteModuleTensor_of_isFinitePresentation_left`. -/
recall SheafOfModules.RingedSite.isCoherent_ringedSiteModuleTensor_of_isFinitePresentation_left

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on
-- tensor products preserving coherence, so no parallel local theorem is needed.
/- Lemma 17.16.6 (6): if `\mathcal F` and `\mathcal G` are coherent, then
`\mathcal F \otimes_{\mathcal O_X} \mathcal G` is coherent. This is exactly the canonical owner
theorem `SheafOfModules.RingedSite.isCoherent_ringedSiteModuleTensor`. -/
recall SheafOfModules.RingedSite.isCoherent_ringedSiteModuleTensor

-- Proof sketch: choose local free models for `ℱ` and `𝒢`, refine to a common neighbourhood, and
-- identify the tensor product of the two local free sheaves with a free local model; this is
-- already the canonical Chapter 18 owner theorem and should be recalled directly.
/- Lemma 17.16.6 (7): if `\mathcal F` and `\mathcal G` are locally free, then
`\mathcal F \otimes_{\mathcal O_X} \mathcal G` is locally free. This is exactly the canonical
owner theorem `SheafOfModules.RingedSite.isLocallyFree_ringedSiteModuleTensor`. -/
recall SheafOfModules.RingedSite.isLocallyFree_ringedSiteModuleTensor

end AlgebraicGeometry.RingedSpace
