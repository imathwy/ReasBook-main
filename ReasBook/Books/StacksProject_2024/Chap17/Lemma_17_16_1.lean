import Mathlib
import StacksProject_2024.Chap17.Definition_17_4_1
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap17.Lemma_17_16_2

-- Declarations for this item will be appended below by the statement pipeline.

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
