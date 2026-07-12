import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksProject_2024.Chap20.«20_10_0_1»
import StacksProject_2024.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace HomologicalComplex PresheafOfModules
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open CategoryTheory.Limits.FormalCoproduct

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "TopOpen" => (⊤ : Opens X.carrier)
local notation "ΓModX" => ModuleCat (X.presheaf.obj (op TopOpen))

private abbrev forgetΓX : ΓModX ⥤ AddCommGrpCat :=
  forget₂ ΓModX AddCommGrpCat

private abbrev openCoverOverTop (𝒰 : ι → Opens X.carrier) : ι → Over TopOpen :=
  fun i ↦ Over.mk (Opens.leTop (𝒰 i))

/- Domain-style sampling for Lemma 20.10.3:
- primary domain: Čech complexes of presheaf `𝒪_X`-modules and the canonical cover chain
  complex built from formal coproducts of free representable presheaf modules, compared with the
  chapter owner `ringedSpaceModuleCechComplexFunctor` over `Over (⊤ : Opens X.carrier)`;
- sampled owner declarations:
  `ringedSpaceModuleCechComplexFunctor`,
  `CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf`,
  `CategoryTheory.FormalCoproduct.eval`,
  `preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction: the source-facing owner in this file is the cover chain complex
  `openCoverChainComplex 𝒰`, obtained by evaluating the canonical Čech formal coproduct
  `(FormalCoproduct.mk _ 𝒰).cech` with `FormalCoproduct.eval` on the free-representable module
  functor `yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj`; the canonical
  `Hom(K•, -)` cochain functor is then obtained by applying `preadditiveCoyoneda` to `K.op`
  and viewing the resulting complex of functors via `HomologicalComplex.asFunctor`. The Čech side
  should not be rebuilt on raw opens: it is the chapter owner
  `ringedSpaceModuleCechComplexFunctor TopOpen (fun i ↦ Over.mk (Opens.leTop (𝒰 i)))`, followed by
  the thin forgetful bridge `forgetΓX.mapHomologicalComplex (ComplexShape.up ℕ)`.

Primitive data is only the ringed space `X` and the indexed open family `𝒰`. The formal-coproduct
realization of the cover is derived bridge data, and the `Hom(K•, -)` cochain construction
should be reused from the owner-level homological-complex API rather than rebuilt degreewise in
this file.

Source/core/bridge triage:
- `source-facing`: `openCoverChainComplex 𝒰`, the Hom functor `openCoverHomFunctor 𝒰`, and the
  canonical comparison morphism from `Hom(K(𝒰)•, -)` to the underlying additive
  view of the chapter Čech owner at `TopOpen`;
- `core/canonical`: `ringedSpaceModuleCechComplexFunctor`,
  `CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf`,
  `CategoryTheory.FormalCoproduct.eval`,
  `preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`,
  `Functor.mapHomologicalComplex`;
- `bridge/view`: the free-representable presheaf-module functor on opens, evaluated on formal
  coproducts, together with the canonical `Hom(K•, -)` functor obtained from
  `preadditiveCoyoneda.mapHomologicalComplex` and `HomologicalComplex.asFunctor`, and the
  coefficient-forgetting bridge from the module-valued Čech complex at `TopOpen` to
  `AddCommGrpCat`. -/

/-- The simplicial presheaf-module object attached to an indexed open covering. -/
private noncomputable abbrev openCoverSimplicialObject (𝒰 : ι → Opens X.carrier) :
    SimplicialObject X.PresheafModules :=
  (FormalCoproduct.mk _ 𝒰).cech ⋙
    (FormalCoproduct.eval.{u} (Opens X.carrier) X.PresheafModules).obj
      (yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj)

/-- The chain complex of presheaf modules associated with an indexed open covering. -/
noncomputable abbrev openCoverChainComplex (𝒰 : ι → Opens X.carrier) :
    ChainComplex X.PresheafModules ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex X.PresheafModules).obj
    (openCoverSimplicialObject 𝒰)

/-- The canonical cochain-complex functor `Hom(K(𝒰)•, -)` attached to the open-cover
chain complex. -/
noncomputable abbrev openCoverHomFunctor (𝒰 : ι → Opens X.carrier) :
    X.PresheafModules ⥤ CochainComplex AddCommGrpCat ℕ :=
  (((preadditiveCoyoneda.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (openCoverChainComplex 𝒰).op).asFunctor)

/-- The module-valued Čech complex functor of the open family `𝒰`, specialized from the Chapter
20 owner at `⊤`. -/
private noncomputable abbrev openCoverModuleCechComplexFunctor (𝒰 : ι → Opens X.carrier) :
    X.PresheafModules ⥤ CochainComplex ΓModX ℕ :=
  ringedSpaceModuleCechComplexFunctor TopOpen (openCoverOverTop 𝒰)

/-- The additive-group-valued Čech complex functor of the open family `𝒰`, obtained from the
module-valued Chapter 20 owner by forgetting the `Γ(X, 𝒪_X)`-module structure degreewise. -/
noncomputable abbrev openCoverCechComplexFunctor (𝒰 : ι → Opens X.carrier) :
    X.PresheafModules ⥤ CochainComplex AddCommGrpCat ℕ :=
  openCoverModuleCechComplexFunctor 𝒰 ⋙ forgetΓX.mapHomologicalComplex (ComplexShape.up ℕ)

/-- The formal coproduct of the `(n + 1)`-fold intersections in the Čech nerve of the open
cover `𝒰`. -/
abbrev openCoverPowerObject (𝒰 : ι → Opens X.carrier) (n : ℕ) :
    FormalCoproduct (Opens X.carrier) :=
  ((FormalCoproduct.mk _ 𝒰).cech).obj (op (SimplexCategory.mk n))

private abbrev openCoverOverPowerObject (𝒰 : ι → Opens X.carrier) (n : ℕ) :
    FormalCoproduct (Over TopOpen) :=
  ((FormalCoproduct.mk _ (openCoverOverTop 𝒰)).cech).obj (op (SimplexCategory.mk n))

/-- The index type of the degree-`n` summands in `openCoverChainComplex 𝒰`. -/
abbrev openCoverPowerIndex (𝒰 : ι → Opens X.carrier) (n : ℕ) :=
  (openCoverPowerObject 𝒰 n).I

/-- The open subset corresponding to an index in the degree-`n` term of the cover chain
complex. -/
abbrev openCoverPowerOpen (𝒰 : ι → Opens X.carrier) (n : ℕ)
    (i : openCoverPowerIndex 𝒰 n) : Opens X.carrier :=
  (Over.forget TopOpen).obj ((openCoverOverPowerObject 𝒰 n).obj i)

/-- The `i`th summand of the degree-`n` term of `openCoverChainComplex 𝒰`. -/
abbrev openCoverChainSummand (𝒰 : ι → Opens X.carrier) (n : ℕ)
    (i : openCoverPowerIndex 𝒰 n) :
    X.PresheafModules :=
  (yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj).obj
    (openCoverPowerOpen 𝒰 n i)

/-- The degree-`n` term of `openCoverChainComplex 𝒰` is the coproduct of the free representable
summands indexed by the `(n + 1)`-fold intersections of the cover. -/
theorem openCoverChainDegree_eq
    (𝒰 : ι → Opens X.carrier) (n : ℕ) :
    (openCoverChainComplex 𝒰).X n = ∐ openCoverChainSummand 𝒰 n := by
  change
    (∐
        fun i : openCoverPowerIndex 𝒰 n ↦
          (yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj).obj
            ((openCoverPowerObject 𝒰 n).obj i)) =
      ∐ openCoverChainSummand 𝒰 n
  congr 1
  funext i
  refine congrArg ((yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj).obj) ?_
  change (∏ᶜ 𝒰 ∘ i) = (∏ᶜ openCoverOverTop 𝒰 ∘ i).left
  let S : Over TopOpen := Over.mk (Opens.leTop (∏ᶜ 𝒰 ∘ i))
  apply le_antisymm
  · simpa [S] using leOfHom
      ((Pi.lift fun j : Fin (n + 1) ↦
          let f : S ⟶ openCoverOverTop 𝒰 (i j) :=
            Over.homMk (Pi.π (𝒰 ∘ i) j) (by
              change Pi.π (𝒰 ∘ i) j ≫ (openCoverOverTop 𝒰 (i j)).hom = S.hom
              apply Subsingleton.elim)
          f).left)
  · exact leOfHom (Pi.lift fun j : Fin (n + 1) ↦ (Pi.π (openCoverOverTop 𝒰 ∘ i) j).left)

private abbrev openCoverSectionsOnOverModule (F : X.PresheafModules) :
    (Over TopOpen)ᵒᵖ ⥤ ΓModX :=
  (ringedSpaceModuleSectionsOnOverPresheaf TopOpen).obj F

private abbrev openCoverCechModuleSummand (𝒰 : ι → Opens X.carrier)
    (F : X.PresheafModules) (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    ΓModX :=
  (openCoverSectionsOnOverModule F).obj (op ((openCoverOverPowerObject 𝒰 n).obj i))

private abbrev openCoverCechSummand (𝒰 : ι → Opens X.carrier)
    (F : X.PresheafModules) (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    AddCommGrpCat :=
  forgetΓX.obj (openCoverCechModuleSummand 𝒰 F n i)

private theorem openCoverOverPowerObject_forget_obj
    (𝒰 : ι → Opens X.carrier) (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    (Over.forget TopOpen).obj ((openCoverOverPowerObject 𝒰 n).obj i) =
      openCoverPowerOpen 𝒰 n i := by
  rfl

private theorem openCoverCechSummand_carrier_eq
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    ↥(F.obj (op (openCoverPowerOpen 𝒰 n i))) =
      ↥(openCoverCechSummand 𝒰 F n i) := by
  rfl

private theorem openCoverModuleCechDegree_eq
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    ((openCoverModuleCechComplexFunctor 𝒰).obj F).X n = ∏ᶜ openCoverCechModuleSummand 𝒰 F n := by
  rfl

private noncomputable def openCoverCechDegreeIso
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    ∏ᶜ openCoverCechSummand 𝒰 F n ≅ ((openCoverCechComplexFunctor 𝒰).obj F).X n :=
  (PreservesProduct.iso forgetΓX (openCoverCechModuleSummand 𝒰 F n)).symm ≪≫
    eqToIso (by
      simpa [openCoverCechComplexFunctor] using
        congrArg forgetΓX.obj (openCoverModuleCechDegree_eq 𝒰 F n))

/-- Helper for Lemma 20.10.3: after transporting the target Čech degree to the product model,
the inverse comparison map followed by one projection is just the forgotten module-valued product
projection. -/
private theorem openCoverCechDegreeIso_inv_π
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    (openCoverCechDegreeIso 𝒰 F n).inv ≫
        Pi.π (openCoverCechSummand 𝒰 F n) i =
      forgetΓX.map (Pi.π (openCoverCechModuleSummand 𝒰 F n) i) := by
  -- Proof comment: once the module-valued Čech degree is identified with the product object, the
  -- remaining iso is the universal product comparison preserved by `forgetΓX`.
  cases openCoverModuleCechDegree_eq 𝒰 F n
  change
    (PreservesProduct.iso forgetΓX (openCoverCechModuleSummand 𝒰 F n)).hom ≫
        Pi.π (openCoverCechSummand 𝒰 F n) i =
      forgetΓX.map (Pi.π (openCoverCechModuleSummand 𝒰 F n) i)
  simpa [openCoverCechDegreeIso, openCoverCechSummand] using
    CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp
      (CategoryTheory.Limits.isLimitOfHasProductOfPreservesLimit forgetΓX
        (openCoverCechModuleSummand 𝒰 F n))
      (CategoryTheory.Limits.limit.isLimit
        (CategoryTheory.Discrete.functor (openCoverCechSummand 𝒰 F n)))
      (CategoryTheory.Discrete.mk i)

/-- Helper for Lemma 20.10.3: on underlying additive groups, the restricted-sections functor maps
one overlap component by the same function as the original presheaf-module morphism. -/
private theorem openCoverSectionsOnOverPresheaf_map_app_apply
    (𝒰 : ι → Opens X.carrier) {F G : X.PresheafModules}
    (φ : F ⟶ G) (n : ℕ) (i : openCoverPowerIndex 𝒰 n)
    (x : openCoverCechSummand 𝒰 F n i) :
    AddCommGrpCat.Hom.hom
        (forgetΓX.map
          (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
            (op ((openCoverOverPowerObject 𝒰 n).obj i))))
        x =
      cast (openCoverCechSummand_carrier_eq 𝒰 G n i)
        ((ConcreteCategory.hom (φ.app (op (openCoverPowerOpen 𝒰 n i))))
          (cast (openCoverCechSummand_carrier_eq 𝒰 F n i).symm x)) := by
  -- Proof comment: `ringedSpaceModuleSectionsOnOverPresheaf` evaluates the original presheaf
  -- module on the underlying open, so after forgetting scalars both sides are definitionally the
  -- same underlying function.
  cases openCoverCechSummand_carrier_eq 𝒰 F n i
  cases openCoverCechSummand_carrier_eq 𝒰 G n i
  rfl

/-- Helper for Lemma 20.10.3: projecting the degree-`n` map of the module-valued Čech complex
exposes the corresponding overlap map on sections. -/
private theorem openCoverModuleCechMap_component
    (𝒰 : ι → Opens X.carrier) {F G : X.PresheafModules}
    (φ : F ⟶ G) (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    (((openCoverModuleCechComplexFunctor 𝒰).map φ).f n) ≫
        Pi.π (openCoverCechModuleSummand 𝒰 G n) i =
      Pi.π (openCoverCechModuleSummand 𝒰 F n) i ≫
        ((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
          (op ((openCoverOverPowerObject 𝒰 n).obj i)) := by
  -- Proof comment: the module-valued Čech map is a product map, so one projection sees exactly
  -- the chosen overlap component.
  change
    CategoryTheory.Limits.Pi.map
        (fun i : openCoverPowerIndex 𝒰 n ↦
          ((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
            (op ((openCoverOverPowerObject 𝒰 n).obj i))) ≫
        Pi.π (openCoverCechModuleSummand 𝒰 G n) i =
      _
  simpa only using
    (CategoryTheory.Limits.Pi.map_π
      (fun i : openCoverPowerIndex 𝒰 n ↦
        ((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
          (op ((openCoverOverPowerObject 𝒰 n).obj i)))
      i)

/-- Helper for Lemma 20.10.3: after transporting the additive Čech map to the product model, one
coordinate is postcomposition by the corresponding overlap map of `φ`. -/
private theorem openCoverCechMap_component
    (𝒰 : ι → Opens X.carrier) {F G : X.PresheafModules}
    (φ : F ⟶ G) (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    (((openCoverCechComplexFunctor 𝒰).map φ).f n) ≫
        (openCoverCechDegreeIso 𝒰 G n).inv ≫
        Pi.π (openCoverCechSummand 𝒰 G n) i =
      (openCoverCechDegreeIso 𝒰 F n).inv ≫
        Pi.π (openCoverCechSummand 𝒰 F n) i ≫
        forgetΓX.map
          (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
            (op ((openCoverOverPowerObject 𝒰 n).obj i))) := by
  -- Proof comment: rewrite both transported projections through
  -- `openCoverCechDegreeIso_inv_π`, then appeal to the product-coordinate formula on the
  -- module-valued Čech complex before forgetting scalars.
  rw [show (((openCoverCechComplexFunctor 𝒰).map φ).f n) =
      forgetΓX.map (((openCoverModuleCechComplexFunctor 𝒰).map φ).f n) by
        simpa [openCoverCechComplexFunctor] using
          (CategoryTheory.Functor.mapHomologicalComplex_map_f forgetΓX (ComplexShape.up ℕ)
            ((openCoverModuleCechComplexFunctor 𝒰).map φ) n)]
  calc
    forgetΓX.map (((openCoverModuleCechComplexFunctor 𝒰).map φ).f n) ≫
        (openCoverCechDegreeIso 𝒰 G n).inv ≫
        Pi.π (openCoverCechSummand 𝒰 G n) i =
      forgetΓX.map (((openCoverModuleCechComplexFunctor 𝒰).map φ).f n) ≫
        forgetΓX.map (Pi.π (openCoverCechModuleSummand 𝒰 G n) i) := by
      exact congrArg
        (fun m ↦ forgetΓX.map (((openCoverModuleCechComplexFunctor 𝒰).map φ).f n) ≫ m)
        (openCoverCechDegreeIso_inv_π 𝒰 G n i)
    _ = forgetΓX.map ((((openCoverModuleCechComplexFunctor 𝒰).map φ).f n) ≫
          Pi.π (openCoverCechModuleSummand 𝒰 G n) i) := by
      rw [← forgetΓX.map_comp]
    _ = forgetΓX.map
          (Pi.π (openCoverCechModuleSummand 𝒰 F n) i ≫
            ((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
              (op ((openCoverOverPowerObject 𝒰 n).obj i))) := by
      exact congrArg forgetΓX.map (openCoverModuleCechMap_component 𝒰 φ n i)
    _ = forgetΓX.map (Pi.π (openCoverCechModuleSummand 𝒰 F n) i) ≫
          forgetΓX.map
            (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
              (op ((openCoverOverPowerObject 𝒰 n).obj i))) := by
      rw [forgetΓX.map_comp]
    _ = (openCoverCechDegreeIso 𝒰 F n).inv ≫
          Pi.π (openCoverCechSummand 𝒰 F n) i ≫
          forgetΓX.map
            (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
              (op ((openCoverOverPowerObject 𝒰 n).obj i))) := by
      rw [openCoverCechDegreeIso_inv_π 𝒰 F n i]

private def openCoverDegreeComparisonComponentToFun
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    ((openCoverChainComplex 𝒰).X n ⟶ F) →
      openCoverCechSummand 𝒰 F n i :=
  fun α ↦ by
    let α' : (∐ openCoverChainSummand 𝒰 n) ⟶ F :=
      (eqToHom (openCoverChainDegree_eq 𝒰 n).symm) ≫ α
    exact cast (openCoverCechSummand_carrier_eq 𝒰 F n i)
      (freeYonedaEquiv (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫ α'))

private theorem freeYonedaEquiv_zero
    {U : Opens X.carrier} {F : X.PresheafModules} :
    freeYonedaEquiv (0 : (yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj).obj U ⟶ F) = 0 := by
  let G := (yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj).obj U
  calc
    freeYonedaEquiv (0 : G ⟶ F)
      = (ConcreteCategory.hom ((0 : G ⟶ F).app (op U))) (freeYonedaEquiv (𝟙 G)) := by
            simpa using
              (PresheafOfModules.freeYonedaEquiv_comp (𝟙 G) (0 : G ⟶ F))
    _ = 0 := by
      change (ConcreteCategory.hom (0 : G.obj (op U) ⟶ F.obj (op U)))
          (freeYonedaEquiv (𝟙 G)) = 0
      rfl

private theorem freeYonedaEquiv_add
    {U : Opens X.carrier} {F : X.PresheafModules}
    (a b : (yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj).obj U ⟶ F) :
    freeYonedaEquiv (a + b) = freeYonedaEquiv a + freeYonedaEquiv b := by
  let G := (yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj).obj U
  calc
    freeYonedaEquiv (a + b)
      = (ConcreteCategory.hom ((a + b).app (op U))) (freeYonedaEquiv (𝟙 G)) := by
            simpa using
              (PresheafOfModules.freeYonedaEquiv_comp (𝟙 G) (a + b))
    _ = (ConcreteCategory.hom (a.app (op U))) (freeYonedaEquiv (𝟙 G)) +
          (ConcreteCategory.hom (b.app (op U))) (freeYonedaEquiv (𝟙 G)) := by
            change (ConcreteCategory.hom (a.app (op U) + b.app (op U)))
                (freeYonedaEquiv (𝟙 G)) =
              (ConcreteCategory.hom (a.app (op U))) (freeYonedaEquiv (𝟙 G)) +
                (ConcreteCategory.hom (b.app (op U))) (freeYonedaEquiv (𝟙 G))
            change ((ConcreteCategory.hom (a.app (op U)) + ConcreteCategory.hom (b.app (op U))))
                (freeYonedaEquiv (𝟙 G)) =
              (ConcreteCategory.hom (a.app (op U))) (freeYonedaEquiv (𝟙 G)) +
                (ConcreteCategory.hom (b.app (op U))) (freeYonedaEquiv (𝟙 G))
            rfl
    _ = freeYonedaEquiv (𝟙 G ≫ a) + freeYonedaEquiv (𝟙 G ≫ b) := by
      rw [← PresheafOfModules.freeYonedaEquiv_comp (𝟙 G) a]
      rw [← PresheafOfModules.freeYonedaEquiv_comp (𝟙 G) b]
    _ = freeYonedaEquiv a + freeYonedaEquiv b := by
      simpa using congrArg₂ HAdd.hAdd
        (show freeYonedaEquiv (𝟙 G ≫ a) = freeYonedaEquiv a by
          exact congrArg (fun z ↦ freeYonedaEquiv z) (Category.id_comp a))
        (show freeYonedaEquiv (𝟙 G ≫ b) = freeYonedaEquiv b by
          exact congrArg (fun z ↦ freeYonedaEquiv z) (Category.id_comp b))

private theorem openCoverDegreeComparisonComponentToFun_map_zero
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    openCoverDegreeComparisonComponentToFun 𝒰 F n i 0 = 0 := by
  cases openCoverCechSummand_carrier_eq 𝒰 F n i
  change freeYonedaEquiv
      (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
        ((eqToHom (openCoverChainDegree_eq 𝒰 n).symm) ≫
          (0 : (openCoverChainComplex 𝒰).X n ⟶ F))) = 0
  have hzero :
      Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫
            (0 : (openCoverChainComplex 𝒰).X n ⟶ F) =
        (0 : openCoverChainSummand 𝒰 n i ⟶ F) := by
    simpa [Category.assoc] using
      (comp_zero :
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
            eqToHom (openCoverChainDegree_eq 𝒰 n).symm) ≫
          (0 : (openCoverChainComplex 𝒰).X n ⟶ F) = 0)
  have hzero' : freeYonedaEquiv (0 : openCoverChainSummand 𝒰 n i ⟶ F) = 0 :=
    freeYonedaEquiv_zero
  simpa [hzero] using hzero'

private theorem openCoverDegreeComparisonComponentToFun_map_add
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n)
    (α β : (openCoverChainComplex 𝒰).X n ⟶ F) :
    openCoverDegreeComparisonComponentToFun 𝒰 F n i (α + β) =
      openCoverDegreeComparisonComponentToFun 𝒰 F n i α +
        openCoverDegreeComparisonComponentToFun 𝒰 F n i β := by
  cases openCoverCechSummand_carrier_eq 𝒰 F n i
  change
    freeYonedaEquiv
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          ((eqToHom (openCoverChainDegree_eq 𝒰 n).symm) ≫ (α + β))) =
      freeYonedaEquiv
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          ((eqToHom (openCoverChainDegree_eq 𝒰 n).symm) ≫ α)) +
        freeYonedaEquiv
          (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
            ((eqToHom (openCoverChainDegree_eq 𝒰 n).symm) ≫ β))
  have hadd :
      Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ (α + β) =
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
            eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α) +
          (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
            eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ β) := by
    simpa [Category.assoc] using
      (Preadditive.comp_add _ _ _
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          eqToHom (openCoverChainDegree_eq 𝒰 n).symm)
        α β)
  have hadd' :
      freeYonedaEquiv
          ((Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
              eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α) +
            (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
              eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ β)) =
        freeYonedaEquiv
            (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
              eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α) +
          freeYonedaEquiv
            (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
              eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ β) :=
    freeYonedaEquiv_add _ _
  simpa [hadd] using hadd'

/-- Helper for Lemma 20.10.3: the Hom functor `openCoverHomFunctor 𝒰` acts in degree `n` by
postcomposition with the coefficient morphism. -/
private theorem openCoverHomFunctor_map_apply
    (𝒰 : ι → Opens X.carrier) {F G : X.PresheafModules}
    (φ : F ⟶ G) (n : ℕ) (α : (openCoverChainComplex 𝒰).X n ⟶ F) :
    AddCommGrpCat.Hom.hom (((openCoverHomFunctor 𝒰).map φ).f n) α = α ≫ φ := by
  rfl

/-- Helper for Lemma 20.10.3: one degreewise comparison component is natural in the coefficient
presheaf after identifying the target coordinate with evaluation on the chosen overlap. -/
private theorem openCoverDegreeComparisonComponent_postcompose
    (𝒰 : ι → Opens X.carrier) {F G : X.PresheafModules}
    (φ : F ⟶ G) (n : ℕ) (i : openCoverPowerIndex 𝒰 n)
    (α : (openCoverChainComplex 𝒰).X n ⟶ F) :
    openCoverDegreeComparisonComponentToFun 𝒰 G n i (α ≫ φ) =
      cast (openCoverCechSummand_carrier_eq 𝒰 G n i)
        ((ConcreteCategory.hom (φ.app (op (openCoverPowerOpen 𝒰 n i))))
          (cast (openCoverCechSummand_carrier_eq 𝒰 F n i).symm
            (openCoverDegreeComparisonComponentToFun 𝒰 F n i α))) := by
  -- Proof comment: rewrite both sides through `freeYonedaEquiv`; the result is exactly the
  -- naturality formula `freeYonedaEquiv_comp` on the chosen overlap summand.
  cases openCoverCechSummand_carrier_eq 𝒰 F n i
  cases openCoverCechSummand_carrier_eq 𝒰 G n i
  change freeYonedaEquiv
      (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
        (eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α ≫ φ)) =
    (ConcreteCategory.hom (φ.app (op (openCoverPowerOpen 𝒰 n i))))
      (freeYonedaEquiv
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          (eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α)))
  simpa [Category.assoc] using
    (PresheafOfModules.freeYonedaEquiv_comp
      (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
        eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α)
      φ)

private abbrev openCoverHomDegree
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    AddCommGrpCat :=
  AddCommGrpCat.of ((openCoverChainComplex 𝒰).X n ⟶ F)

private noncomputable def openCoverDegreeComparisonComponent
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    openCoverHomDegree 𝒰 F n ⟶ openCoverCechSummand 𝒰 F n i :=
  AddCommGrpCat.ofHom
    { toFun := openCoverDegreeComparisonComponentToFun 𝒰 F n i
      map_zero' := openCoverDegreeComparisonComponentToFun_map_zero 𝒰 F n i
      map_add' := openCoverDegreeComparisonComponentToFun_map_add 𝒰 F n i }

/-- The canonical degree-`n` comparison map from `Hom(K(𝒰)•, F)` to the degree-`n` Čech cochains
of `F` for the cover `𝒰`. -/
noncomputable def openCoverDegreeComparison
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    AddCommGrpCat.of ((openCoverChainComplex 𝒰).X n ⟶ F) ⟶
      ((openCoverCechComplexFunctor 𝒰).obj F).X n :=
  Pi.lift (fun i : openCoverPowerIndex 𝒰 n ↦
      openCoverDegreeComparisonComponent 𝒰 F n i) ≫
    (openCoverCechDegreeIso 𝒰 F n).hom

/-- Helper for Lemma 20.10.3: after transporting the target Čech degree to the product model,
projecting the degreewise comparison recovers the chosen component map. -/
private theorem openCoverDegreeComparison_comp_inv_π
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    openCoverDegreeComparison 𝒰 F n ≫
        (openCoverCechDegreeIso 𝒰 F n).inv ≫
        Pi.π (openCoverCechSummand 𝒰 F n) i =
      openCoverDegreeComparisonComponent 𝒰 F n i := by
  -- Proof comment: the only transport on the target side is `openCoverCechDegreeIso`; once it is
  -- canceled, `Pi.lift` immediately exposes the selected coordinate map.
  simpa [openCoverDegreeComparison, Category.assoc] using
    (Pi.lift_π
      (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i)
      i)

private abbrev openCoverCechDegreeProduct
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :=
  ∏ᶜ openCoverCechSummand 𝒰 F n

private noncomputable def openCoverDegreeComparisonComponentInvToFun
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    openCoverCechSummand 𝒰 F n i → (openCoverChainSummand 𝒰 n i ⟶ F) :=
  fun x ↦
    freeYonedaEquiv.symm (cast (openCoverCechSummand_carrier_eq 𝒰 F n i).symm x)

private theorem openCoverDegreeComparisonComponentInvToFun_map_zero
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n) :
    openCoverDegreeComparisonComponentInvToFun 𝒰 F n i 0 = 0 := by
  cases openCoverCechSummand_carrier_eq 𝒰 F n i
  refine freeYonedaEquiv.injective ?_
  rw [show openCoverDegreeComparisonComponentInvToFun 𝒰 F n i 0 = freeYonedaEquiv.symm 0 by
        rfl]
  rw [Equiv.apply_symm_apply, freeYonedaEquiv_zero]

private theorem openCoverDegreeComparisonComponentInvToFun_map_add
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules)
    (n : ℕ) (i : openCoverPowerIndex 𝒰 n)
    (x y : openCoverCechSummand 𝒰 F n i) :
    openCoverDegreeComparisonComponentInvToFun 𝒰 F n i (x + y) =
      openCoverDegreeComparisonComponentInvToFun 𝒰 F n i x +
        openCoverDegreeComparisonComponentInvToFun 𝒰 F n i y := by
  cases openCoverCechSummand_carrier_eq 𝒰 F n i
  refine freeYonedaEquiv.injective ?_
  rw [show openCoverDegreeComparisonComponentInvToFun 𝒰 F n i (x + y) =
        freeYonedaEquiv.symm (x + y) by rfl]
  rw [show openCoverDegreeComparisonComponentInvToFun 𝒰 F n i x = freeYonedaEquiv.symm x by rfl]
  rw [show openCoverDegreeComparisonComponentInvToFun 𝒰 F n i y = freeYonedaEquiv.symm y by rfl]
  rw [freeYonedaEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl

private noncomputable def openCoverDegreeComparisonInvFromProductToFun
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    openCoverCechDegreeProduct 𝒰 F n → ((openCoverChainComplex 𝒰).X n ⟶ F) :=
  fun x ↦
    eqToHom (openCoverChainDegree_eq 𝒰 n) ≫
      Sigma.desc fun i ↦
        openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
          (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x)

private theorem openCoverDegreeComparisonInvFromProductToFun_map_zero
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    openCoverDegreeComparisonInvFromProductToFun 𝒰 F n 0 = 0 := by
  have hSigma :
      Sigma.desc
          (fun i ↦
            openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
              (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) 0)) =
        (0 : ∐ openCoverChainSummand 𝒰 n ⟶ F) := by
    refine Sigma.hom_ext _ _ (fun i ↦ ?_)
    rw [Sigma.ι_desc]
    simp [openCoverDegreeComparisonComponentInvToFun_map_zero]
    rfl
  rw [openCoverDegreeComparisonInvFromProductToFun, hSigma]
  simp
  rfl

private theorem openCoverDegreeComparisonInvFromProductToFun_map_add
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ)
    (x y : openCoverCechDegreeProduct 𝒰 F n) :
    openCoverDegreeComparisonInvFromProductToFun 𝒰 F n (x + y) =
      openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x +
        openCoverDegreeComparisonInvFromProductToFun 𝒰 F n y := by
  have hSigma :
      Sigma.desc
          (fun i ↦
            openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
              (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) (x + y))) =
        Sigma.desc
            (fun i ↦
              openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
                (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x)) +
          Sigma.desc
            (fun i ↦
              openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
                (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) y)) := by
    refine Sigma.hom_ext _ _ (fun i ↦ ?_)
    rw [Preadditive.comp_add, Sigma.ι_desc, Sigma.ι_desc, Sigma.ι_desc]
    rw [show AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) (x + y) =
          AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x +
            AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) y by
          exact (Pi.π (openCoverCechSummand 𝒰 F n) i).hom.map_add x y]
    exact openCoverDegreeComparisonComponentInvToFun_map_add 𝒰 F n i _ _
  calc
    openCoverDegreeComparisonInvFromProductToFun 𝒰 F n (x + y)
        = eqToHom (openCoverChainDegree_eq 𝒰 n) ≫
            (Sigma.desc
                (fun i ↦
                  openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
                    (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x)) +
              Sigma.desc
                (fun i ↦
                  openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
                    (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) y))) := by
          rw [openCoverDegreeComparisonInvFromProductToFun, hSigma]
    _ = openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x +
          openCoverDegreeComparisonInvFromProductToFun 𝒰 F n y := by
          rw [Preadditive.comp_add]
          rfl

private noncomputable def openCoverDegreeComparisonInvFromProduct
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    openCoverCechDegreeProduct 𝒰 F n ⟶ openCoverHomDegree 𝒰 F n :=
  AddCommGrpCat.ofHom
    { toFun := openCoverDegreeComparisonInvFromProductToFun 𝒰 F n
      map_zero' := openCoverDegreeComparisonInvFromProductToFun_map_zero 𝒰 F n
      map_add' := openCoverDegreeComparisonInvFromProductToFun_map_add 𝒰 F n }

private noncomputable def openCoverDegreeComparisonInv
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    ((openCoverCechComplexFunctor 𝒰).obj F).X n ⟶ openCoverHomDegree 𝒰 F n :=
  (openCoverCechDegreeIso 𝒰 F n).inv ≫ openCoverDegreeComparisonInvFromProduct 𝒰 F n

/-- Helper for Lemma 20.10.3: after transporting the source degree to its coproduct model,
precomposing the explicit inverse with one coproduct injection recovers the chosen summand map. -/
private theorem openCoverDegreeComparisonInvFromProduct_component
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ)
    (x : openCoverCechDegreeProduct 𝒰 F n) (i : openCoverPowerIndex 𝒰 n) :
    Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
        eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫
        openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x =
      openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
        (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x) := by
  -- Proof comment: expand the explicit inverse once and then use the coproduct universal
  -- property on the chosen injection.
  calc
    Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
        eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫
        openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x =
      Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
        Sigma.desc
          (fun i ↦
            openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
              (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x)) := by
      simp [openCoverDegreeComparisonInvFromProductToFun]
    _ = openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
          (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x) := by
      simpa using
        (Limits.Sigma.ι_desc
          (fun i ↦
            openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
              (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x))
          i)

/-- Helper for Lemma 20.10.3: evaluating one comparison component on the explicit inverse recovers
the chosen product coordinate. -/
private theorem openCoverDegreeComparisonComponent_apply_invFromProduct
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ)
    (x : openCoverCechDegreeProduct 𝒰 F n) (i : openCoverPowerIndex 𝒰 n) :
    openCoverDegreeComparisonComponentToFun 𝒰 F n i
      (openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x) =
    AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x := by
  -- Proof comment: the summandwise inverse was chosen using `freeYonedaEquiv.symm`, so applying
  -- the forward comparison on the same overlap collapses by `Equiv.apply_symm_apply`.
  cases openCoverCechSummand_carrier_eq 𝒰 F n i
  change
    freeYonedaEquiv
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫
          openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x) =
      AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x
  calc
    freeYonedaEquiv
        (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
          eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫
          openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x) =
      freeYonedaEquiv
        (openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
          (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x)) := by
      exact congrArg freeYonedaEquiv
        (openCoverDegreeComparisonInvFromProduct_component 𝒰 F n x i)
    _ = AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x := by
      rw [show openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
            (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x) =
          freeYonedaEquiv.symm
            (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x) by
            rfl]
      exact Equiv.apply_symm_apply freeYonedaEquiv _

/-- Helper for Lemma 20.10.3: on the product model, the degreewise comparison and its explicit
inverse satisfy both triangle identities. -/
private theorem openCoverDegreeComparisonProduct_inverse_spec
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    Pi.lift (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i) ≫
        openCoverDegreeComparisonInvFromProduct 𝒰 F n =
      𝟙 _ ∧
      openCoverDegreeComparisonInvFromProduct 𝒰 F n ≫
          Pi.lift (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i) =
        𝟙 _ := by
  constructor
  · -- Proof comment: compare the two source-side maps after transporting to the coproduct model
    -- and checking each coproduct leg separately.
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro α
    change
      openCoverDegreeComparisonInvFromProductToFun 𝒰 F n
          ((Pi.lift
                (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i))
            α) =
        α
    have hcancel :
        eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫
            openCoverDegreeComparisonInvFromProductToFun 𝒰 F n
              ((Pi.lift
                    (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i))
                α) =
          eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α := by
      refine Sigma.hom_ext _ _ (fun i ↦ ?_)
      have hπ :
          Pi.lift
              (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i) ≫
              Pi.π (openCoverCechSummand 𝒰 F n) i =
            openCoverDegreeComparisonComponent 𝒰 F n i := by
        simpa using
          (Pi.lift_π
            (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i)
            i)
      have hπα :
          AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i)
              ((Pi.lift
                    (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i))
                α) =
            openCoverDegreeComparisonComponentToFun 𝒰 F n i α := by
        simpa using congrArg
          (fun m ↦ AddCommGrpCat.Hom.hom m α)
          hπ
      calc
        Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
            eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫
            openCoverDegreeComparisonInvFromProductToFun 𝒰 F n
              ((Pi.lift
                    (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i))
                α) =
          openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
            (AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i)
              ((Pi.lift
                    (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i))
                α)) := by
          exact openCoverDegreeComparisonInvFromProduct_component 𝒰 F n _ i
        _ = openCoverDegreeComparisonComponentInvToFun 𝒰 F n i
              (openCoverDegreeComparisonComponentToFun 𝒰 F n i α) := by
          exact congrArg (openCoverDegreeComparisonComponentInvToFun 𝒰 F n i) hπα
        _ = Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
              eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α := by
          cases openCoverCechSummand_carrier_eq 𝒰 F n i
          change freeYonedaEquiv.symm
              (freeYonedaEquiv
                (Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
                  eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α)) =
            Sigma.ι (openCoverChainSummand 𝒰 n) i ≫
              eqToHom (openCoverChainDegree_eq 𝒰 n).symm ≫ α
          exact Equiv.symm_apply_apply freeYonedaEquiv _
    exact (cancel_epi (eqToHom (openCoverChainDegree_eq 𝒰 n).symm)).1 hcancel
  · -- Proof comment: compare the two product-side maps after one projection and use the
    -- summandwise forward/inverse cancellation just proved.
    apply Pi.hom_ext
    intro i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    have hπ :
        Pi.lift (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i) ≫
            Pi.π (openCoverCechSummand 𝒰 F n) i =
          openCoverDegreeComparisonComponent 𝒰 F n i := by
      simpa using
        (Pi.lift_π
          (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i)
          i)
    have hπx :
        AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i)
            ((Pi.lift
                  (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i))
              (openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x)) =
          openCoverDegreeComparisonComponentToFun 𝒰 F n i
            (openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x) := by
      simpa using congrArg
        (fun m ↦ AddCommGrpCat.Hom.hom m
          (openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x))
        hπ
    calc
      AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i)
          ((Pi.lift
                (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i))
            (openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x)) =
        openCoverDegreeComparisonComponentToFun 𝒰 F n i
          (openCoverDegreeComparisonInvFromProductToFun 𝒰 F n x) := hπx
      _ = AddCommGrpCat.Hom.hom (Pi.π (openCoverCechSummand 𝒰 F n) i) x := by
        exact openCoverDegreeComparisonComponent_apply_invFromProduct 𝒰 F n x i

/-- Helper for Lemma 20.10.3: the degreewise comparison followed by its inverse is the identity. -/
private theorem openCoverDegreeComparison_hom_inv_id
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    openCoverDegreeComparison 𝒰 F n ≫ openCoverDegreeComparisonInv 𝒰 F n = 𝟙 _ := by
  -- Proof comment: cancel the Čech/product comparison isomorphism and use the product-side
  -- inverse identity just proved.
  simpa [openCoverDegreeComparison, openCoverDegreeComparisonInv, Category.assoc] using
    (openCoverDegreeComparisonProduct_inverse_spec 𝒰 F n).1

/-- Helper for Lemma 20.10.3: the degreewise inverse followed by the comparison is the identity. -/
private theorem openCoverDegreeComparison_inv_hom_id
    (𝒰 : ι → Opens X.carrier) (F : X.PresheafModules) (n : ℕ) :
    openCoverDegreeComparisonInv 𝒰 F n ≫ openCoverDegreeComparison 𝒰 F n = 𝟙 _ := by
  -- Proof comment: move to the Čech product model, check each projection there, and then
  -- reinsert the canonical product comparison isomorphism.
  calc
    openCoverDegreeComparisonInv 𝒰 F n ≫ openCoverDegreeComparison 𝒰 F n =
        (openCoverCechDegreeIso 𝒰 F n).inv ≫
          (openCoverDegreeComparisonInvFromProduct 𝒰 F n ≫
            Pi.lift (fun i : openCoverPowerIndex 𝒰 n ↦ openCoverDegreeComparisonComponent 𝒰 F n i)) ≫
          (openCoverCechDegreeIso 𝒰 F n).hom := by
            rw [openCoverDegreeComparison, openCoverDegreeComparisonInv]
            repeat rw [Category.assoc]
    _ = (openCoverCechDegreeIso 𝒰 F n).inv ≫ 𝟙 _ ≫ (openCoverCechDegreeIso 𝒰 F n).hom := by
          rw [(openCoverDegreeComparisonProduct_inverse_spec 𝒰 F n).2]
    _ = 𝟙 _ := by simp

/-- The degreewise comparison maps are natural in the presheaf module. -/
private theorem openCoverDegreeComparison_natural
    (𝒰 : ι → Opens X.carrier) {F G : X.PresheafModules} (φ : F ⟶ G) (n : ℕ) :
    CommSq
      (openCoverDegreeComparison 𝒰 F n)
      (((openCoverHomFunctor 𝒰).map φ).f n)
      (((openCoverCechComplexFunctor 𝒰).map φ).f n)
      (openCoverDegreeComparison 𝒰 G n) := by
  -- Proof comment: cancel the Čech/product bridge on the target, project to one overlap, and
  -- compare both sides as postcomposition by the same section map.
  refine CommSq.mk ?_
  apply (cancel_mono ((openCoverCechDegreeIso 𝒰 G n).inv)).1
  apply Pi.hom_ext
  intro i
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro α
  have hleft :
      AddCommGrpCat.Hom.hom
          (openCoverDegreeComparison 𝒰 F n ≫
            (((openCoverCechComplexFunctor 𝒰).map φ).f n) ≫
            (openCoverCechDegreeIso 𝒰 G n).inv ≫
            Pi.π (openCoverCechSummand 𝒰 G n) i)
          α =
        cast (openCoverCechSummand_carrier_eq 𝒰 G n i)
          ((ConcreteCategory.hom (φ.app (op (openCoverPowerOpen 𝒰 n i))))
            (cast (openCoverCechSummand_carrier_eq 𝒰 F n i).symm
              (openCoverDegreeComparisonComponentToFun 𝒰 F n i α))) := by
    calc
      AddCommGrpCat.Hom.hom
          (openCoverDegreeComparison 𝒰 F n ≫
            (((openCoverCechComplexFunctor 𝒰).map φ).f n) ≫
            (openCoverCechDegreeIso 𝒰 G n).inv ≫
            Pi.π (openCoverCechSummand 𝒰 G n) i)
          α =
        AddCommGrpCat.Hom.hom
          (openCoverDegreeComparison 𝒰 F n ≫
            (openCoverCechDegreeIso 𝒰 F n).inv ≫
            Pi.π (openCoverCechSummand 𝒰 F n) i ≫
            forgetΓX.map
              (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
                (op ((openCoverOverPowerObject 𝒰 n).obj i))))
          α := by
        exact congrArg (fun m ↦ AddCommGrpCat.Hom.hom m α) <| by
          simpa [Category.assoc] using
            congrArg (fun m ↦ openCoverDegreeComparison 𝒰 F n ≫ m)
              (openCoverCechMap_component 𝒰 φ n i)
      _ =
        AddCommGrpCat.Hom.hom
          (openCoverDegreeComparisonComponent 𝒰 F n i ≫
            forgetΓX.map
              (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
                (op ((openCoverOverPowerObject 𝒰 n).obj i))))
          α := by
        exact congrArg (fun m ↦ AddCommGrpCat.Hom.hom m α) <| by
          simpa [Category.assoc] using
            congrArg
              (fun m ↦
                m ≫
                  forgetΓX.map
                    (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
                      (op ((openCoverOverPowerObject 𝒰 n).obj i))))
              (openCoverDegreeComparison_comp_inv_π 𝒰 F n i)
      _ =
        cast (openCoverCechSummand_carrier_eq 𝒰 G n i)
          ((ConcreteCategory.hom (φ.app (op (openCoverPowerOpen 𝒰 n i))))
            (cast (openCoverCechSummand_carrier_eq 𝒰 F n i).symm
              (openCoverDegreeComparisonComponentToFun 𝒰 F n i α))) := by
        change
          AddCommGrpCat.Hom.hom
              (forgetΓX.map
                (((ringedSpaceModuleSectionsOnOverPresheaf TopOpen).map φ).app
                  (op ((openCoverOverPowerObject 𝒰 n).obj i))))
              (openCoverDegreeComparisonComponentToFun 𝒰 F n i α) =
            _
        exact openCoverSectionsOnOverPresheaf_map_app_apply 𝒰 φ n i
          (openCoverDegreeComparisonComponentToFun 𝒰 F n i α)
  have hright :
      AddCommGrpCat.Hom.hom
          ((((openCoverHomFunctor 𝒰).map φ).f n ≫ openCoverDegreeComparison 𝒰 G n) ≫
            (openCoverCechDegreeIso 𝒰 G n).inv ≫
            Pi.π (openCoverCechSummand 𝒰 G n) i)
          α =
        cast (openCoverCechSummand_carrier_eq 𝒰 G n i)
          ((ConcreteCategory.hom (φ.app (op (openCoverPowerOpen 𝒰 n i))))
            (cast (openCoverCechSummand_carrier_eq 𝒰 F n i).symm
              (openCoverDegreeComparisonComponentToFun 𝒰 F n i α))) := by
    calc
      AddCommGrpCat.Hom.hom
          ((((openCoverHomFunctor 𝒰).map φ).f n ≫ openCoverDegreeComparison 𝒰 G n) ≫
            (openCoverCechDegreeIso 𝒰 G n).inv ≫
            Pi.π (openCoverCechSummand 𝒰 G n) i)
          α =
        AddCommGrpCat.Hom.hom
          (openCoverDegreeComparison 𝒰 G n ≫
            (openCoverCechDegreeIso 𝒰 G n).inv ≫
            Pi.π (openCoverCechSummand 𝒰 G n) i)
          (AddCommGrpCat.Hom.hom (((openCoverHomFunctor 𝒰).map φ).f n) α) := by
        rfl
      _ =
        AddCommGrpCat.Hom.hom
          (openCoverDegreeComparison 𝒰 G n ≫
            (openCoverCechDegreeIso 𝒰 G n).inv ≫
            Pi.π (openCoverCechSummand 𝒰 G n) i)
          (α ≫ φ) := by
        rw [openCoverHomFunctor_map_apply 𝒰 φ n α]
      _ = openCoverDegreeComparisonComponentToFun 𝒰 G n i (α ≫ φ) := by
        exact congrArg
          (fun m ↦ AddCommGrpCat.Hom.hom m (α ≫ φ))
          (openCoverDegreeComparison_comp_inv_π 𝒰 G n i)
      _ =
        cast (openCoverCechSummand_carrier_eq 𝒰 G n i)
          ((ConcreteCategory.hom (φ.app (op (openCoverPowerOpen 𝒰 n i))))
            (cast (openCoverCechSummand_carrier_eq 𝒰 F n i).symm
              (openCoverDegreeComparisonComponentToFun 𝒰 F n i α))) := by
        exact openCoverDegreeComparisonComponent_postcompose 𝒰 φ n i α
  exact hleft.trans hright.symm

end AlgebraicGeometry.RingedSpace
