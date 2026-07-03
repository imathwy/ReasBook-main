import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory

noncomputable section

universe u

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

local infixr:70 " ⊗ " => moduleTensor

/-
Domain-style sampling for Lemma 18.26.1:
- primary domain: sheafification of presheaves of modules over a fixed sheaf of commutative rings,
  together with the induced tensor comparison;
- sampled owner declarations:
  `moduleSheafification`,
  `moduleTensor`,
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.Monoidal.tensorHom`;
- best owner abstraction:
  the source-facing owner is the canonical tensor/sheafification comparison attached to the
  sheafification functor `moduleSheafification 𝒪`, with the isomorphism surface obtained as
  `asIso` of that comparison;
- primitive data:
  a sheaf of commutative rings `𝒪` and two presheaves of `𝒪`-modules `ℱ`, `𝒢`;
- derived API:
  the comparison morphism, its `IsIso` instance, and the resulting tensor/sheafification
  isomorphism.

Layer triage:
- `source-facing`: the canonical identification
  `ℱ^# ⊗ 𝒢^# ≅ (ℱ ⊗ 𝒢)^#`;
- `core/canonical`: `moduleSheafification 𝒪`, `moduleTensor`, and
  `PresheafOfModules.sheafificationAdjunction`;
- `bridge/view`: the comparison morphism whose inverse is the source-facing isomorphism. -/

-- Proof sketch: adjoint transpose the tensor of the two unit morphisms into the tensor of the
-- sheafifications, then follow with the sheafification unit for the presheaf tensor of the two
-- underlying sheaves.
/-- The canonical comparison morphism from the sheafification of a presheaf tensor product to the
tensor product of the individual sheafifications. -/
noncomputable def moduleSheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    (moduleSheafification 𝒪).obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) ⟶
      (moduleSheafification 𝒪).obj ℱ ⊗ (moduleSheafification 𝒪).obj 𝒢 :=
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J 𝒪).obj)
  let unitToSheafification
      (ℋ : PresheafOfModules (ringSheaf J 𝒪).obj) :
      ℋ ⟶ (SheafOfModules.forget (ringSheaf J 𝒪)).obj ((moduleSheafification 𝒪).obj ℋ) := by
    simpa [moduleSheafification] using adj.unit.app ℋ
  let tensorUnit :
      PresheafOfModules.Monoidal.tensorObj
          ((moduleSheafification 𝒪).obj ℱ).val
          ((moduleSheafification 𝒪).obj 𝒢).val ⟶
        (SheafOfModules.forget (ringSheaf J 𝒪)).obj
          (((moduleSheafification 𝒪).obj ℱ) ⊗ ((moduleSheafification 𝒪).obj 𝒢)) := by
    simpa [moduleTensor, moduleSheafification] using
      adj.unit.app
        (PresheafOfModules.Monoidal.tensorObj
          ((moduleSheafification 𝒪).obj ℱ).val
          ((moduleSheafification 𝒪).obj 𝒢).val)
  (adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢)
      (((moduleSheafification 𝒪).obj ℱ) ⊗ ((moduleSheafification 𝒪).obj 𝒢))).symm
    (PresheafOfModules.Monoidal.tensorHom
        (unitToSheafification ℱ)
        (unitToSheafification 𝒢) ≫
      tensorUnit)

/-- The canonical tensor/sheafification comparison morphism is an isomorphism. -/
instance moduleSheafificationTensorComparison_isIso
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    IsIso (moduleSheafificationTensorComparison 𝒪 ℱ 𝒢) := by
  sorry

/-- Lemma 18.26.1: for presheaves of `\mathcal O`-modules `ℱ` and `𝒢`, the tensor product of
their sheafifications is canonically isomorphic to the sheafification of their presheaf tensor
product. -/
noncomputable abbrev moduleSheafificationTensorIso
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    (moduleSheafification 𝒪).obj ℱ ⊗ (moduleSheafification 𝒪).obj 𝒢 ≅
      (moduleSheafification 𝒪).obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) :=
  (asIso (moduleSheafificationTensorComparison 𝒪 ℱ 𝒢)).symm
