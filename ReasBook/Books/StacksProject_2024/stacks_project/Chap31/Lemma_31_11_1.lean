import StacksProject_2024.stacks_project.Chap31.TorsionSectionImage

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open Opposite
open scoped AlgebraicGeometry

attribute [local instance] Classical.propDecidable

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

-- Semantic recall: `lean_leansearch` was attempted for the generic-point / skyscraper owner
-- choice here, but the service returned HTTP 429, so the owner surface below is verified against
-- local Chapter 31 precedent plus the canonical stalk/skyscraper adjunction APIs.

private abbrev moduleUnderlyingStalk (ℱ : X.Modules) (η : X) :=
  (((moduleUnderlyingSheaf X.toRingedSpace).obj ℱ).presheaf).stalk η

/-- Helper for Lemma 31.11.1: the image of `s` in the underlying additive sheaf of `j_* ℱ_η`. -/
def genericPointUnderlyingSkyscraperSectionImage
    (ℱ : X.Modules) (η : X)
    {U : X.Opens} (s : ℱ.val.obj (op U)) :
    (skyscraperSheaf η (moduleUnderlyingStalk ℱ η)).presheaf.obj (op U) :=
  (((stalkSkyscraperSheafAdjunction η).unit.app
      ((moduleUnderlyingSheaf X.toRingedSpace).obj ℱ)).hom.app (op U)) s

/-- Lemma 31.11.1 (1): let `X` be an integral scheme with generic point `η`, let `ℱ` be a
quasi-coherent `\mathcal O_X`-module, let `U ⊆ X` be nonempty open, and let `s ∈ ℱ(U)`. Then the
image of `s` is torsion in `ℱ_x` for some `x ∈ U` if and only if its image in `ℱ_η` is zero. -/
theorem exists_sectionImageIsTorsionAt_iff_genericSectionImage_eq_zero
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X))
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    (∃ x : U, sectionImageIsTorsionAt ℱ s x) ↔
      genericSectionImage ℱ η hη hU s = 0 := sorry

/-- Lemma 31.11.1 (2): let `X` be an integral scheme with generic point `η`, let `ℱ` be a
quasi-coherent `\mathcal O_X`-module, let `U ⊆ X` be nonempty open, and let `s ∈ ℱ(U)`. Then the
image of `s` is torsion in `ℱ_x` for every `x ∈ U` if and only if its image in `ℱ_η` is zero. -/
theorem forall_sectionImageIsTorsionAt_iff_genericSectionImage_eq_zero
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X))
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    (∀ x : U, sectionImageIsTorsionAt ℱ s x) ↔
      genericSectionImage ℱ η hη hU s = 0 := sorry

/-- Lemma 31.11.1 (3): let `X` be an integral scheme with generic point `η`, let `ℱ` be a
quasi-coherent `\mathcal O_X`-module, let `U ⊆ X` be nonempty open, and let `s ∈ ℱ(U)`. Then the
image of `s` in `ℱ_η` is zero if and only if its image in the underlying additive sheaf of
`j_* ℱ_η` is zero, where `j : η → X` is the point inclusion. -/
theorem genericSectionImage_eq_zero_iff_genericPointUnderlyingSkyscraperSectionImage_eq_zero
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X))
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    genericSectionImage ℱ η hη hU s = 0 ↔
      genericPointUnderlyingSkyscraperSectionImage ℱ η s = 0 := sorry

/-- Lemma 31.11.1 (1), canonical generic-point form: on a nonempty open of an integral scheme, a
section is torsion at some point exactly when its image in the generic stalk vanishes. -/
theorem exists_sectionImageIsTorsionAt_iff_sectionImageAt_genericPoint_eq_zero
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    (∃ x : U, sectionImageIsTorsionAt ℱ s x) ↔
      sectionImageAtGenericPoint ℱ hU s = 0 := by
  simpa using
    exists_sectionImageIsTorsionAt_iff_genericSectionImage_eq_zero
      ℱ (genericPoint X) (genericPoint_spec X) hU s

/-- Lemma 31.11.1 (2), canonical generic-point form: on a nonempty open of an integral scheme, a
section is torsion at every point exactly when its image in the generic stalk vanishes. -/
theorem forall_sectionImageIsTorsionAt_iff_sectionImageAt_genericPoint_eq_zero
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    (∀ x : U, sectionImageIsTorsionAt ℱ s x) ↔
      sectionImageAtGenericPoint ℱ hU s = 0 := by
  simpa using
    forall_sectionImageIsTorsionAt_iff_genericSectionImage_eq_zero
      ℱ (genericPoint X) (genericPoint_spec X) hU s

/-- Lemma 31.11.1 (3), canonical generic-point form: vanishing in the generic stalk is equivalent
to vanishing in the underlying additive sheaf of the pushforward of that stalk from the generic
point. -/
theorem sectionImageAt_genericPoint_eq_zero_iff_genericPointUnderlyingSkyscraperSectionImage_eq_zero
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    sectionImageAtGenericPoint ℱ hU s = 0 ↔
      genericPointUnderlyingSkyscraperSectionImage ℱ (genericPoint X) s = 0 := by
  simpa using
    genericSectionImage_eq_zero_iff_genericPointUnderlyingSkyscraperSectionImage_eq_zero
      ℱ (genericPoint X) (genericPoint_spec X) hU s

end AlgebraicGeometry.Scheme.Modules
