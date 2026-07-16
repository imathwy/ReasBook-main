import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]

local notation "ModX" => SheafOfModules X.ringCatSheaf
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

-- Semantic recall: `lean_leansearch` surfaced the ideal-sheaf-data and affine-ideal owners but
-- not a ready-made scheme-level owner for the `I`-torsion subsheaf of a quasi-coherent module.
-- The local Chapter 17/31 precedents already provide the needed tensor-unit comparison,
-- restriction/stalk maps, and the closed-immersion ideal subobject attached to ideal sheaf data,
-- so this item keeps the source-facing torsion owner on the scheme module category and makes the
-- `IdealSheafData → Subobject 𝒪_X` bridge explicit.

/-- The quasi-coherent ideal-sheaf subobject of `\mathcal O_X` attached to ideal sheaf data `I`.
-/
noncomputable abbrev idealSheafSubobject (I : X.IdealSheafData) : Subobject 𝒪X :=
  closedImmersionIdealSubobject I.subschemeι

/-- The action map `I \otimes_{\mathcal O_X} \mathcal F \to \mathcal F` induced by the ideal
sheaf inclusion attached to `I`. -/
noncomputable def idealTensorAction (I : X.IdealSheafData) (ℱ : ModX) :
    tensorObj (show ModX from Subobject.underlying.obj (idealSheafSubobject I)) ℱ ⟶ ℱ :=
  tensorHom (idealSheafSubobject I).arrow (𝟙 ℱ) ≫
    ((SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ).hom

/-- The subsheaf of sections of `ℱ` annihilated by the ideal sheaf data `I`. -/
noncomputable abbrev idealTorsionSubsheaf (I : X.IdealSheafData) (ℱ : ModX) : ModX :=
  kernel (MonoidalClosed.curry (idealTensorAction I ℱ))

/-- The canonical inclusion of the ideal-torsion subsheaf into the ambient module sheaf `ℱ`. -/
noncomputable abbrev idealTorsionSubsheafι (I : X.IdealSheafData) (ℱ : ModX) :
    idealTorsionSubsheaf I ℱ ⟶ ℱ :=
  kernel.ι (MonoidalClosed.curry (idealTensorAction I ℱ))

/-- The stalk ideal `I_x \subset \mathcal O_{X, x}` cut out by ideal sheaf data `I`. -/
noncomputable def idealSheafStalkIdeal (I : X.IdealSheafData) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  LinearMap.range
    ((RingedSpace.moduleStalkHom x (idealSheafSubobject I).arrow ≫
        RingedSpace.unitStalkLinearMap x).hom)

/-- Lemma 28.24.2 (1): if `I` is a finite type quasi-coherent ideal sheaf on a scheme `X` and
`ℱ` is a quasi-coherent `\mathcal O_X`-module, then the subsheaf `ℱ[I]` of sections annihilated
by `I` is quasi-coherent. -/
@[stacks 01PO]
theorem idealTorsionSubsheaf_isQuasicoherent
    (ℱ : ModX) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData)
    [((show ModX from Subobject.underlying.obj (idealSheafSubobject I)).IsFiniteType)] :
    (idealTorsionSubsheaf I ℱ).IsQuasicoherent := sorry

/-- Lemma 28.24.2 (2): on an affine open `U`, the image of the canonical inclusion
`ℱ[I](U) \hookrightarrow ℱ(U)` is exactly the submodule of sections annihilated by `I(U)`. -/
@[stacks 01PO]
theorem range_idealTorsionSubsheafι_app_eq_affine_annihilatedSections
    (ℱ : ModX) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData)
    [((show ModX from Subobject.underlying.obj (idealSheafSubobject I)).IsFiniteType)]
    (U : X.affineOpens) :
    Set.range (((idealTorsionSubsheafι I ℱ).val.app (op U.1)).hom) =
      {s : Γ(ℱ, U.1) | ∀ a : Γ(X, U.1), a ∈ I.ideal U → a • s = 0} := sorry

/-- Lemma 28.24.2 (3): on every stalk `x`, the image of the canonical map
`(ℱ[I])_x \to ℱ_x` is exactly the submodule of stalk sections annihilated by the stalk ideal
`I_x`. -/
@[stacks 01PO]
theorem range_idealTorsionSubsheafι_stalk_eq_annihilatedStalkSections
    (ℱ : ModX) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData)
    [((show ModX from Subobject.underlying.obj (idealSheafSubobject I)).IsFiniteType)]
    (x : X) :
    Set.range ((RingedSpace.moduleStalkHom x (idealTorsionSubsheafι I ℱ)).hom) =
      {s : RingedSpace.stalkModuleCat ℱ x |
        ∀ a : X.presheaf.stalk x, a ∈ idealSheafStalkIdeal I x → a • s = 0} := sorry

end AlgebraicGeometry.Scheme.Modules
