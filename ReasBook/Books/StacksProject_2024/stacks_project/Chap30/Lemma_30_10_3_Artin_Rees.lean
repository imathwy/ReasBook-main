import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import StacksProject_2024.stacks_project.Chap30.AffineOpenSubsheafSections
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.stacks_project.Chap31.ClosedImmersionIdealSubobject

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the ring-level Artin-Rees theorem
-- `Ideal.exists_pow_inf_eq_pow_smul`. The project already exposes affine-open ideal-sheaf sections
-- through `Scheme.IdealSheafData.ideal` and subsheaves as `Subobject`s of `X.Modules`, so the
-- source statement is recorded on affine sections rather than through a new global wrapper for
-- ideal-power intersections of subsheaves.

private abbrev idealSheafPowerData
    (I : X.IdealSheafData) (n : ℕ) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦ I.ideal U ^ n

/-- The affine-open section submodule `I(U)^n \mathcal F(U)` associated to an ideal sheaf and a
module sheaf. -/
def affineOpenIdealPowTopSubmodule
    (ℱ : X.Modules) (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    Submodule Γ(X, U.1) (ℱ.val.obj (op U.1)) :=
  I.ideal U ^ n • ⊤

/-- Unfold the affine-open submodule `I(U)^n \mathcal F(U)`. -/
theorem affineOpenIdealPowTopSubmodule_def
    (ℱ : X.Modules) (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    affineOpenIdealPowTopSubmodule ℱ I U n =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) (ℱ.val.obj (op U.1))) :=
  rfl

section Monoidal

variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]

local notation "ModX" => SheafOfModules X.ringCatSheaf
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

private noncomputable abbrev idealSheafSubobject (I : X.IdealSheafData) : Subobject 𝒪X :=
  closedImmersionIdealSubobject I.subschemeι

private noncomputable def idealTensorAction (I : X.IdealSheafData) (ℱ : ModX) :
    tensorObj (show ModX from Subobject.underlying.obj (idealSheafSubobject I)) ℱ ⟶ ℱ :=
  tensorHom (idealSheafSubobject I).arrow (𝟙 ℱ) ≫
    ((SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ).hom

/-- The subobject `I^n \subset \mathcal O_X` attached to an ideal sheaf datum `I`. -/
noncomputable abbrev idealPowerSubobject
    (I : X.IdealSheafData) (n : ℕ) : Subobject 𝒪X :=
  idealSheafSubobject (idealSheafPowerData I n)

/-- The subobject `I^n \mathcal G \subset \mathcal F` obtained by letting `I^n` act on a
subsheaf `\mathcal G \subset \mathcal F`. -/
noncomputable def idealPowerSmulSubobject
    {ℱ : X.Modules} (I : X.IdealSheafData) (𝒢 : Subobject ℱ) (n : ℕ) : Subobject ℱ :=
  imageSubobject (idealTensorAction (idealSheafPowerData I n) (𝒢 : X.Modules) ≫ 𝒢.arrow)

/-- The subobject `I^n \mathcal F \subset \mathcal F` obtained by letting `I^n` act on all of
`\mathcal F`. -/
noncomputable abbrev idealPowerProductSubobject
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) : Subobject ℱ :=
  idealPowerSmulSubobject I (⊤ : Subobject ℱ) n

/-- On affine opens, the sections of `I^n \mathcal G` are `I(U)^n \mathcal G(U)`. -/
theorem affineOpenSubsheafSectionsSubmodule_idealPowerSmulSubobject
    {ℱ : X.Modules} (I : X.IdealSheafData) (𝒢 : Subobject ℱ) (U : X.affineOpens) (n : ℕ) :
    affineOpenSubsheafSectionsSubmodule (idealPowerSmulSubobject I 𝒢 n) U =
      I.ideal U ^ n • affineOpenSubsheafSectionsSubmodule 𝒢 U := sorry

/-- On affine opens, the sections of `I^n \mathcal F` are `I(U)^n \mathcal F(U)`. -/
theorem affineOpenSubsheafSectionsSubmodule_idealPowerProductSubobject
    (ℱ : X.Modules) (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    affineOpenSubsheafSectionsSubmodule (idealPowerProductSubobject I ℱ n) U =
      affineOpenIdealPowTopSubmodule ℱ I U n := sorry

/-- On affine opens, the sections of `I^n \subset \mathcal O_X` are exactly `I(U)^n`. -/
theorem affineOpenSubsheafSectionsSubmodule_idealPowerSubobject
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    affineOpenSubsheafSectionsSubmodule (idealPowerSubobject I n) U =
      affineOpenIdealPowTopSubmodule
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) I U n := sorry

/-- The family `n ↦ I^n \mathcal F` is descending. -/
theorem idealPowerProductSubobject_antitone
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerProductSubobject I ℱ (n + 1) ≤ idealPowerProductSubobject I ℱ n := sorry

/-- The family `n ↦ I^n` is descending. -/
theorem idealPowerSubobject_antitone
    (I : X.IdealSheafData) (n : ℕ) :
    idealPowerSubobject I (n + 1) ≤ idealPowerSubobject I n := sorry

/-- Lemma 30.10.3 (Artin-Rees): for a Noetherian scheme `X`, a coherent `\mathcal O_X`-module
`\mathcal F`, a quasi-coherent subsheaf `\mathcal G \subset \mathcal F`, and an ideal sheaf
`\mathcal I`, there is a uniform constant `c` such that for every `n \ge c` one has the sheaf
identity `\mathcal I^{n-c}(\mathcal I^c \mathcal F \cap \mathcal G) =
\mathcal I^n \mathcal F \cap \mathcal G`. -/
theorem exists_artinReesConstant
    [IsNoetherian X]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (𝒢 : Subobject ℱ)
    [((𝒢 : X.Modules)).IsQuasicoherent]
    (I : X.IdealSheafData) :
    ∃ c : ℕ, ∀ n ≥ c,
      idealPowerSmulSubobject I ((idealPowerProductSubobject I ℱ c) ⊓ 𝒢) (n - c) =
        idealPowerProductSubobject I ℱ n ⊓ 𝒢 := sorry

/-- The affine-open bridge for Lemma 30.10.3, obtained by evaluating the Artin-Rees identity on
sections over affine opens. -/
theorem exists_artinReesConstant_affine
    [IsNoetherian X]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (𝒢 : Subobject ℱ)
    [((𝒢 : X.Modules)).IsQuasicoherent]
    (I : X.IdealSheafData) :
    ∃ c : ℕ, ∀ U : X.affineOpens, ∀ n ≥ c,
      affineOpenSubsheafSectionsSubmodule
          (idealPowerSmulSubobject I ((idealPowerProductSubobject I ℱ c) ⊓ 𝒢) (n - c)) U =
        affineOpenSubsheafSectionsSubmodule
          (idealPowerProductSubobject I ℱ n ⊓ 𝒢) U := sorry

end Monoidal

end AlgebraicGeometry.Scheme.Modules
