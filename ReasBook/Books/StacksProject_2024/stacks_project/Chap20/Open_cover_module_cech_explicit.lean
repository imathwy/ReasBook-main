import Mathlib.CategoryTheory.Limits.Lattice
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_pushforward_core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory Opposite
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "ModX" => RingedSpace.Modules X

/-- The tuple-indexed pushed-forward restriction whose product over all `(p + 1)`-tuples is the
degree-`p` term `openCoverModuleCechTerm 𝒰 ℱ p`. This is the canonical summand family underlying
the module-valued Čech term owner. -/
noncomputable abbrev openCoverModuleCechSummand
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ) :
    (Fin (p + 1) → ι) → ModX :=
  fun σ ↦
    (modulePushforwardFromOpen (cechIntersection 𝒰 σ)).obj
      ((moduleRestrictionToOpen X (cechIntersection 𝒰 σ)).obj ℱ)

/-- The degree-`p` term expected in the module-valued Čech resolution of `ℱ` for the open cover
`𝒰`. It is the product over all `(p + 1)`-tuples `σ` of the pushed-forward restriction
`(j_σ)_*(ℱ|_{U_{i₀} ∩ ⋯ ∩ U_{iₚ}})`. -/
noncomputable abbrev openCoverModuleCechTerm
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ)
    [HasProduct (openCoverModuleCechSummand 𝒰 ℱ p)] :
    ModX :=
  ∏ᶜ fun σ : Fin (p + 1) → ι ↦
    openCoverModuleCechSummand 𝒰 ℱ p σ

/-- Omitting one entry of a Čech tuple induces the corresponding restriction map between the
associated pushed-forward module summands. -/
private noncomputable abbrev openCoverModuleCechRestriction
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) {p : ℕ}
    (σ : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    openCoverModuleCechSummand 𝒰 ℱ p (σ ∘ j.succAboveEmb) ⟶
      openCoverModuleCechSummand 𝒰 ℱ (p + 1) σ :=
  modulePushforwardFromOpenRestrictionMap (cechIntersection_le_succAbove 𝒰 σ j) ℱ

/-- The degree-`p` differential in the module-valued Čech complex of `ℱ` for the open cover
`𝒰`. -/
noncomputable def openCoverModuleCechDifferential
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ)
    [HasProduct (openCoverModuleCechSummand 𝒰 ℱ p)]
    [HasProduct (openCoverModuleCechSummand 𝒰 ℱ (p + 1))] :
    openCoverModuleCechTerm 𝒰 ℱ p ⟶ openCoverModuleCechTerm 𝒰 ℱ (p + 1) :=
  Pi.lift fun σ : Fin (p + 2) → ι ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) •
        (Pi.π
            (openCoverModuleCechSummand 𝒰 ℱ p)
            (σ ∘ j.succAboveEmb) ≫
          openCoverModuleCechRestriction 𝒰 ℱ σ j)

/-- The explicit module-valued Čech differential squares to zero. -/
theorem openCoverModuleCechDifferential_comp
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ) :
    openCoverModuleCechDifferential 𝒰 ℱ p ≫
      openCoverModuleCechDifferential 𝒰 ℱ (p + 1) = 0 := by
  sorry

/-- The degree-zero Čech augmentation map from `ℱ` to the product of the pushed-forward
restrictions on the members of the open cover `𝒰`. -/
noncomputable def openCoverModuleCechAugmentationMap
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX)
    [HasProduct (openCoverModuleCechSummand 𝒰 ℱ 0)] :
    ℱ ⟶ openCoverModuleCechTerm 𝒰 ℱ 0 :=
  Pi.lift fun σ : Fin 1 → ι ↦
    moduleRestrictionToOpenUnit (cechIntersection 𝒰 σ) ℱ

/-- Each degree-zero component of `openCoverModuleCechAugmentationMap 𝒰 ℱ` is the canonical
restriction map to the corresponding member of the open cover. -/
@[simp] theorem openCoverModuleCechAugmentationMap_π
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (σ : Fin 1 → ι) :
    openCoverModuleCechAugmentationMap 𝒰 ℱ ≫
        Pi.π (openCoverModuleCechSummand 𝒰 ℱ 0) σ =
      moduleRestrictionToOpenUnit (cechIntersection 𝒰 σ) ℱ := by
  simpa [openCoverModuleCechAugmentationMap, openCoverModuleCechTerm] using
    (Pi.lift_π
      (fun τ : Fin 1 → ι ↦ moduleRestrictionToOpenUnit (cechIntersection 𝒰 τ) ℱ) σ)

section

variable [HasProducts ModX]

private theorem moduleRestrictionToOpenUnit_comp_openCoverModuleCechRestriction
    {W U : Opens X.carrier} (h : W ≤ U) (ℱ : ModX) :
    moduleRestrictionToOpenUnit U ℱ ≫
      modulePushforwardFromOpenRestrictionMap h ℱ =
    moduleRestrictionToOpenUnit W ℱ := by
  sorry

/-- The degree-zero Čech augmentation is a cocycle in degree `0` for the explicit term model. -/
theorem openCoverModuleCechAugmentationMap_comp_d_zero_one
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) :
    openCoverModuleCechAugmentationMap 𝒰 ℱ ≫
      openCoverModuleCechDifferential 𝒰 ℱ 0 = 0 := by
  sorry

end

end AlgebraicGeometry.RingedSpace
