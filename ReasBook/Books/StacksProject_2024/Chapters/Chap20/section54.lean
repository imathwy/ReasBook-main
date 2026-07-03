import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_54_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [BraidedCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 20.54.1:
- primary domain: tensoring sheaves of `\mathcal O_X`-modules with a finite locally free factor
  and preservation of injective objects;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `tensorRightAdjunction`,
  `BraidedCategory.tensorLeftIsoTensorRight`,
  the `ExactPairing ((ihom ℰ).obj (𝟙_ ModX)) ℰ` instance from Example 17.18.1;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical tensor endofunctor
  `tensorLeft ℰ`, derived from the exact-pairing owner attached to the finite locally free sheaf
  `ℰ`;
- primitive data: the ambient module category `(RingedSpace.Modules X)` and the finite locally free sheaf
  `ℰ`;
- derived API: preservation of injective objects by `tensorLeft ℰ`, and the source-facing
  specialization to `ℰ ⊗ ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that `ℰ ⊗ \mathcal I` is injective when `ℰ` is finite
  locally free and `\mathcal I` is injective;
- `core/canonical`: `Functor.PreservesInjectiveObjects`, `tensorRightAdjunction`, and the exact
  pairing `ExactPairing ((ihom ℰ).obj (𝟙_ ModX)) ℰ`;
- `bridge/view`: the braided identification of left and right tensoring used to move from the
  canonical right-adjoint owner to the source-facing left-tensor statement. -/

/-- Tensoring on the left by a finite locally free sheaf preserves injective objects. -/
instance tensorLeft_preservesInjectiveObjects_of_isFiniteLocallyFree
    (ℰ : ModX) [ℰ.IsFiniteLocallyFree] :
    (tensorLeft ℰ).PreservesInjectiveObjects := by
  let dual := (ihom ℰ).obj (𝟙_ ModX)
  letI : ExactPairing dual ℰ := by
    simpa [dual] using
      (inferInstance : ExactPairing ((ihom ℰ).obj (𝟙_ ModX)) ℰ)
  letI : PreservesLimits (tensorLeft dual) :=
    (tensorLeftAdjunction dual ℰ).rightAdjoint_preservesLimits
  letI : (tensorLeft dual).PreservesMonomorphisms := inferInstance
  letI : (tensorRight dual).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms.of_iso (BraidedCategory.tensorLeftIsoTensorRight dual)
  letI : (tensorRight ℰ).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (tensorRightAdjunction dual ℰ)
  refine ⟨fun hℐ ↦ ?_⟩
  exact Injective.of_iso
    ((BraidedCategory.tensorLeftIsoTensorRight ℰ).symm.app _)
    ((tensorRight ℰ).injective_obj_of_injective hℐ)

/-- Lemma 20.54.1: if `X` is a ringed space, `ℐ` is an injective `\mathcal O_X`-module, and `ℰ`
is a finite locally free `\mathcal O_X`-module, then `ℰ \otimes_{\mathcal O_X} ℐ` is injective. -/
theorem moduleTensor_injective_of_isFiniteLocallyFree
    (ℰ ℐ : ModX) [ℰ.IsFiniteLocallyFree] (hℐ : Injective ℐ) :
    Injective (ℰ ⊗ ℐ) :=
  (tensorLeft ℰ).injective_obj_of_injective hℐ

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_54_2 (from Chap20) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces, after forgetting commutativity. -/
noncomputable abbrev projectionFormulaPushforwardStructureSheafHom (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map
    (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.hom.base).obj X.sheaf from
      ⟨f.hom.c⟩)

/-- The direct-image functor on `\mathcal O_X`-modules induced by `f`. -/
noncomputable abbrev projectionFormulaModulePushforward (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (projectionFormulaPushforwardStructureSheafHom f)

/-- The pullback functor on `\mathcal O_Y`-modules induced by `f`. -/
noncomputable abbrev projectionFormulaModulePullback (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (projectionFormulaPushforwardStructureSheafHom f)

-- Proof sketch: resolve `ℱ` by injectives on `X`; tensoring that resolution with the finite
-- locally free pullback `f^*ℰ` stays injective, so the higher direct images of
-- `f^*ℰ ⊗ \mathcal F` can be computed after tensoring the chosen resolution. The underived
-- identity `f_*(f^*ℰ ⊗ -) ≅ ℰ ⊗ f_*(-)` then yields the claimed isomorphism degreewise.
/-- Lemma 20.54.2: if `f : X ⟶ Y` is a morphism of ringed spaces, `ℱ` is an `\mathcal O_X`-module,
and `ℰ` is a finite locally free `\mathcal O_Y`-module, then for every `q ≥ 0` there is an
isomorphism
`ℰ \otimes_{\mathcal O_Y} R^q f_* \mathcal F \cong
R^q f_* (f^* \mathcal E \otimes_{\mathcal O_X} \mathcal F)`. -/
theorem finiteLocallyFree_projectionFormula_higherDirectImage
    (f : X ⟶ Y) [(projectionFormulaModulePushforward f).Additive]
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    [MonoidalCategory (RingedSpace.Modules X)] [MonoidalCategory (RingedSpace.Modules Y)]
    (ℰ : (RingedSpace.Modules Y)) [SheafOfModules.IsFiniteLocallyFree ℰ] (ℱ : (RingedSpace.Modules X)) (q : ℕ) :
    IsIsomorphic
      (ℰ ⊗ (((projectionFormulaModulePushforward f).rightDerived q).obj ℱ))
      (((projectionFormulaModulePushforward f).rightDerived q).obj
        (((projectionFormulaModulePullback f).obj ℰ) ⊗ ℱ)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_54_3 (from Chap20) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.54.3:
- primary domain: projection-formula morphisms for derived pullback and derived pushforward of
  module sheaves, with the intrinsic owner living on ringed sites and the ringed-space statement
  as its opens-site specialization;
- sampled owner declarations:
  `RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect`,
  `RingedSite.Hom.projectionFormulaMorphism`,
  `CategoryTheory.projectionFormulaMorphism`,
  `modulePullbackDerived`,
  `modulePushforwardDerived`;
- best owner abstraction:
  `source-facing`: the ringed-space specialization for a morphism `f : X ⟶ Y`;
  `core/canonical`: `RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect`;
  `bridge/view`: the morphism of ringed sites on the opens topologies induced by `f`, whose
  projection-formula morphism specializes definitionally to the Chapter 20 ringed-space one.
- primitive data: the ringed-space morphism `f`, the chosen derived adjunction for `f`, the
  pullback-tensor comparison for `f`, and the perfectness hypothesis on `K`;
- derived API: the `IsIso` conclusion for the canonical ringed-space projection-formula morphism,
  obtained by specialization from the ringed-site owner theorem. -/

section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

private abbrev opensRingedSite (X : RingedSpace.{u}) :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

private noncomputable abbrev opensRingedSiteHom (f : X ⟶ Y) :
    opensRingedSite X ⟶ opensRingedSite Y where
  base := Opens.map f.hom.base
  structureSheafMap :=
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
      (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
        ⟨f.hom.c⟩)

private instance opensRingedSiteLocalizedRestrictionPreservesZeroMorphisms
    (U : opensRingedSite Y) :
    (RingedSite.Hom.localizedRestriction U).PreservesZeroMorphisms where
  map_zero _ _ := by
    rfl

private theorem siteIsPerfect_of_ringedSpaceIsPerfect
    (K : DModY) (hK : AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect K) :
    _root_.RingedSite.DerivedCategory.IsPerfect
      (show RingedSite.Hom.ModuleDerived (opensRingedSite Y) from K) := by
  sorry

variable (f : X ⟶ Y)

variable [CategoryWithHomology X.Modules] [CategoryWithHomology Y.Modules]
variable [(modulePullback f).Additive]
variable [(RingedSpace.Hom.pushforward f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived f) (ModuleQis X)]
variable [MonoidalCategory (DerivedCategory X.Modules)]
variable [MonoidalCategory (DerivedCategory Y.Modules)]
variable
  (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
  (tensorIso :
    ∀ (A B : DModY),
      (modulePullbackDerived f).obj (A ⊗ B) ≅
        ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))

-- Proof sketch: this is exactly the projection-formula argument from the Stacks Project. Work
-- locally on `Y` and represent the perfect object `K` by a strictly perfect complex. The claim is
-- stable under finite direct sums, shifts, and direct summands, so stupid truncations reduce to
-- the case `K = \mathcal O_Y[n]`, where the projection-formula morphism is immediate.
/-- Lemma 20.54.3: for a morphism of ringed spaces `f : X ⟶ Y`, an object `E ∈ D(\mathcal O_X)`,
and a perfect object `K ∈ D(\mathcal O_Y)`, the projection-formula morphism
`K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* E ⟶
Rf_*(Lf^* K \otimes_{\mathcal O_X}^{\mathbf L} E)` is an isomorphism in `D(\mathcal O_Y)`. -/
theorem projectionFormulaMorphism_isIso_of_isPerfect
    (E : DModX) (K : DModY)
    (hK : AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect K) :
    IsIso (projectionFormulaMorphism
      (modulePullbackDerived f)
      (modulePushforwardDerived f)
      adj
      tensorIso
      E
      K) := by
  have siteTensorIso :
      ∀ (A B : RingedSite.Hom.ModuleDerived (opensRingedSite Y)),
        (RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj
            (((curriedTensor (RingedSite.Hom.ModuleDerived (opensRingedSite Y))).obj B).obj A) ≅
          (((curriedTensor (RingedSite.Hom.ModuleDerived (opensRingedSite X))).obj
                ((RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj B)).obj
            ((RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj A)) := by
    intro A B
    sorry
  simpa only [opensRingedSite, opensRingedSiteHom, modulePushforwardDerived, modulePullbackDerived,
    modulePullbackToDerived, modulePushforwardToDerived, ModuleQis,
    RingedSite.Hom.modulePushforwardDerived, RingedSite.Hom.modulePullbackDerived,
    RingedSite.Hom.modulePullbackToDerived, RingedSite.Hom.modulePushforwardToDerived,
    RingedSite.Hom.ModuleQis, RingedSite.Hom.projectionFormulaMorphism,
    RingedSite.Hom.ModuleDerived, RingedSite.Hom.ModuleCat] using
    RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect
      (opensRingedSiteHom f) adj siteTensorIso E K
      (siteIsPerfect_of_ringedSpaceIsPerfect K hK)

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_54_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

variable (f : X ⟶ Y)

variable [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(modulePullback f).Additive]
variable [(modulePushforward f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]

variable
  (adj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
  (pullbackTensorIso :
    ∀ (A B : DModY),
      (modulePullbackDerived f).obj (A ⊗ B) ≅
        ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))

-- Proof sketch: because `f` identifies `X` with a closed subset of `Y`, pushforward on module
-- sheaves is exact, so `Rf_*` is computed by ordinary pushforward on complexes. Pullback of a
-- K-flat representative computes `Lf^*`, and the stalkwise tensor identity for a closed subset
-- inclusion identifies the two complexes representing the source and target of the projection
-- formula map.
/-- Lemma 20.54.4: if `f : X ⟶ Y` identifies `X` homeomorphically with a closed subset of `Y`,
then the projection-formula morphism
`K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* E ⟶
Rf_*(Lf^* K \otimes_{\mathcal O_X}^{\mathbf L} E)` is an isomorphism for all
`E ∈ D(\mathcal O_X)` and `K ∈ D(\mathcal O_Y)`. -/
theorem projectionFormulaMorphism_isIso_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding f.hom.base)
    (E : DModX) (K : DModY) :
    IsIso (projectionFormulaMorphism
      (modulePullbackDerived f)
      (moduleDerivedPushforward f)
      adj
      pullbackTensorIso
      E
      K) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_54_5 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X X' Y Y' : RingedSpace.{u}}

variable
  (Lf : ModuleDerived Y ⥤ ModuleDerived X)
  (Lf' : ModuleDerived Y' ⥤ ModuleDerived X')
  (Lg : ModuleDerived Y ⥤ ModuleDerived Y')
  (Lg' : ModuleDerived X ⥤ ModuleDerived X')
  (Rf : ModuleDerived X ⥤ ModuleDerived Y)
  (Rf' : ModuleDerived X' ⥤ ModuleDerived Y')

variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')]
variable [MonoidalCategory (ModuleDerived Y)]
variable [MonoidalCategory (ModuleDerived Y')]

variable
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

variable
  (pullbackTensorIso_f :
    ∀ (A B : ModuleDerived Y),
      Lf.obj (A ⊗ B) ≅
        (Lf.obj A ⊗ Lf.obj B))
  (pullbackTensorIso_f' :
    ∀ (A B : ModuleDerived Y'),
      Lf'.obj (A ⊗ B) ≅
        (Lf'.obj A ⊗ Lf'.obj B))
  (pullbackTensorIso_g :
    ∀ (A B : ModuleDerived Y),
      Lg.obj (A ⊗ B) ≅
        (Lg.obj A ⊗ Lg.obj B))
  (pullbackTensorIso_g' :
    ∀ (A B : ModuleDerived X),
      Lg'.obj (A ⊗ B) ≅
        (Lg'.obj A ⊗ Lg'.obj B))

local notation "DModX" => ModuleDerived X
local notation "DModX'" => ModuleDerived X'
local notation "DModY" => ModuleDerived Y
local notation "DModY'" => ModuleDerived Y'

/-- A morphism `Lg^* Rf_* A ⟶ R(f')_* L(g')^* A` is the base-change map for the square if its
transpose across `Lf' ⊣ Rf'` is the pullback of the counit `Lf^* Rf_* A ⟶ A` transported through
the commutativity isomorphism `Lg ⋙ Lf' ≅ Lf ⋙ Lg'`. -/
def IsBaseChangeMapInDerivedSquare
    (A : DModX)
    (η : Lg.obj (Rf.obj A) ⟶ Rf'.obj (Lg'.obj A)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj A)) (Lg'.obj A)).symm η) =
    (squareIso.hom.app (Rf.obj A) ≫ Lg'.map (adj_f.counit.app A))

-- Proof sketch: expand the top and bottom arrows by the definition of
-- `projectionFormulaMorphism`.
-- Naturality of the
-- adjunction units makes the tensor-with-unit part commute with the base-change map for `E`, and
-- Lemma `20.31.8` gives the corresponding compatibility for the relative cup-product part. The
-- final comparison `c` is the tensor-level transport induced by `squareIso.inv.app K`.
/-- Remark 20.54.5: for a commutative square of ringed spaces, the projection-formula morphism
`(20.54.2.1)` is compatible with the base-change morphism of Remark `20.28.3`. In the abstract
derived-category formulation, if `ηE` and `ηTensor` are the base-change maps for `E` and for
`Lf^* K \otimes_{\mathcal O_X}^{\mathbf L} E`, then the rectangle comparing the pullback of the
projection-formula map for `f` with the projection-formula map for `f'` commutes. -/
theorem projectionFormulaMorphism_baseChange_commSq
    (E : DModX)
    (K : DModY)
    (ηE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (ηTensor :
      Lg.obj (Rf.obj (Lf.obj K ⊗ E)) ⟶
        Rf'.obj (Lg'.obj (Lf.obj K ⊗ E)))
    (hηE :
      IsBaseChangeMapInDerivedSquare Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso E ηE)
    (hηTensor :
      IsBaseChangeMapInDerivedSquare
        Lf
        Lf'
        Lg
        Lg'
        Rf
        Rf'
        adj_f
        adj_f'
        squareIso
        (Lf.obj K ⊗ E)
        ηTensor) :
    CommSq
      (Lg.map (projectionFormulaMorphism Lf Rf adj_f pullbackTensorIso_f E K))
      ((pullbackTensorIso_g K (Rf.obj E)).hom ≫
        (𝟙 (Lg.obj K) ⊗ₘ ηE))
      (ηTensor ≫
        Rf'.map
          ((pullbackTensorIso_g' (Lf.obj K) E).hom ≫
            (squareIso.inv.app K ⊗ₘ 𝟙 (Lg'.obj E))))
      (projectionFormulaMorphism Lf' Rf' adj_f' pullbackTensorIso_f' (Lg'.obj E) (Lg.obj K)) :=
  sorry

end

end AlgebraicGeometry.RingedSpace
