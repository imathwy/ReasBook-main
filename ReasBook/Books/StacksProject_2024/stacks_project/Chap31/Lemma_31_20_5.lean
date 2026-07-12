import Mathlib
import StacksProject_2024.Chap31.Definition_31_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite
open RingTheory
open RingTheory.Sequence
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

-- Semantic recall: `lean_leansearch` surfaced the locally-ringed-space residue-field owners, and
-- the Chapter 31 owner file `Definition_31_20_2` now fixes the helper owners
-- `idealSheafStalkIdeal`, `idealSectionToRingSection`, and
-- `IsGeneratedByIdealSectionFamilyOn` used by this stalk-to-neighborhood spreading lemma.

section

variable {X : LocallyRingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X.toRingedSpace)

/-- Lemma 31.20.5 (1): if `\mathcal J` is quasi-regular and the given germs generate
`\mathcal J_x / \mathfrak m_x \mathcal J_x`, then after shrinking around `x` they lift to a
quasi-regular sequence generating `\mathcal J|_U`. -/
@[stacks 067N]
theorem exists_quasiRegularSequence_of_stalk_basis
    (I : Subobject 𝒪X) (hI : IsQuasiRegularIdealSheaf I)
    (x : X) {r : ℕ}
    (f : Fin r → idealSheafStalkIdeal I x)
    (hf_basis : ∃ b : Module.Basis (Fin r)
        ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ((idealSheafStalkIdeal I x) ⧸
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x) (idealSheafStalkIdeal I x)))),
      ∀ i,
        (Submodule.mkQ
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
              (⊤ : Submodule (X.presheaf.stalk x) (idealSheafStalkIdeal I x))))
          (f i) = b i) :
    ∃ (U : Opens X) (hxU : x ∈ U) (g : Fin r → (I : ModX).val.obj (op U)),
      (∀ i,
        (idealSheafStalkToRing I x).hom
          (TopCat.Presheaf.germ (I : ModX).val.presheaf U x hxU (g i)) = f i) ∧
        IsGeneratedByIdealSectionFamilyOn I U g ∧
        IsQuasiRegular (X.presheaf.obj (op U))
          (List.ofFn fun i ↦ idealSectionToRingSection I U (g i)) := sorry

/-- Lemma 31.20.5 (2): if `\mathcal J` is `H_1`-regular and the given germs generate
`\mathcal J_x / \mathfrak m_x \mathcal J_x`, then after shrinking around `x` they lift to an
`H_1`-regular sequence generating `\mathcal J|_U`. -/
@[stacks 067N]
theorem exists_h1RegularSequence_of_stalk_basis
    (I : Subobject 𝒪X) (hI : IsH1RegularIdealSheaf I)
    (x : X) {r : ℕ}
    (f : Fin r → idealSheafStalkIdeal I x)
    (hf_basis : ∃ b : Module.Basis (Fin r)
        ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ((idealSheafStalkIdeal I x) ⧸
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x) (idealSheafStalkIdeal I x)))),
      ∀ i,
        (Submodule.mkQ
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
              (⊤ : Submodule (X.presheaf.stalk x) (idealSheafStalkIdeal I x))))
          (f i) = b i) :
    ∃ (U : Opens X) (hxU : x ∈ U) (g : Fin r → (I : ModX).val.obj (op U)),
      (∀ i,
        (idealSheafStalkToRing I x).hom
          (TopCat.Presheaf.germ (I : ModX).val.presheaf U x hxU (g i)) = f i) ∧
        IsGeneratedByIdealSectionFamilyOn I U g ∧
        IsH1RegularSequence
          (fun i ↦ idealSectionToRingSection I U (g i)) := sorry

/-- Lemma 31.20.5 (3): if `\mathcal J` is Koszul-regular and the given germs generate
`\mathcal J_x / \mathfrak m_x \mathcal J_x`, then after shrinking around `x` they lift to a
Koszul-regular sequence generating `\mathcal J|_U`. -/
@[stacks 067N]
theorem exists_koszulRegularSequence_of_stalk_basis
    (I : Subobject 𝒪X) (hI : IsKoszulRegularIdealSheaf I)
    (x : X) {r : ℕ}
    (f : Fin r → idealSheafStalkIdeal I x)
    (hf_basis : ∃ b : Module.Basis (Fin r)
        ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ((idealSheafStalkIdeal I x) ⧸
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x) (idealSheafStalkIdeal I x)))),
      ∀ i,
        (Submodule.mkQ
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
              (⊤ : Submodule (X.presheaf.stalk x) (idealSheafStalkIdeal I x))))
          (f i) = b i) :
    ∃ (U : Opens X) (hxU : x ∈ U) (g : Fin r → (I : ModX).val.obj (op U)),
      (∀ i,
        (idealSheafStalkToRing I x).hom
          (TopCat.Presheaf.germ (I : ModX).val.presheaf U x hxU (g i)) = f i) ∧
        IsGeneratedByIdealSectionFamilyOn I U g ∧
        IsKoszulRegularSequence
          (fun i ↦ idealSectionToRingSection I U (g i)) := sorry

end

end AlgebraicGeometry.RingedSpace
