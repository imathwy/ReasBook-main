import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_2
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_1
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open Functor

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (p : S ⥤ D)

/- Domain-style sampling for Lemma 8.12.3:
- primary domain: stacks in groupoids over sites and their pullback along a continuous functor.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `continuous_pullback_isStackOnSite`,
  the canonical `IsFibered` instance on `CategoricalPullback.π₁ u p`,
  `IsFibredInGroupoids`.
- best owner abstraction: the source-facing result should stay the canonical owner statement
  `IsStackInGroupoids J (CategoricalPullback.π₁ u p)`, assembled from the already-canonical
  stack-on-site pullback theorem and the fibred-in-groupoids owner on the pullback projection.
- primitive data: the functor `u`, the projection `p`, and the owner hypothesis
  `[IsStackInGroupoids K p]`.
- derived API: the pulled-back stack-in-groupoids structure on `CategoricalPullback.π₁ u p`.

Source/core/bridge triage:
- `source-facing`: `continuous_pullback_hasStackInGroupoidsStructure`.
- `core/canonical`: `IsStackInGroupoids`, `IsFibredInGroupoids`,
  `continuous_pullback_isStackOnSite`, and `CategoricalPullback.π₁`.
- `bridge/view`: `continuous_pullback_isFibredInGroupoids`, obtained from the canonical owner
  theorem `isFibredInGroupoids_of_isFibered_and_fiber_groupoid` after checking that each pullback
  fiber is a groupoid. -/

private theorem pullbackProjection_fiberHom_isIso [IsFibredInGroupoids p]
    (U : C) {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    IsIso φ := by
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) φ.1 := φ.2
  have hfst := IsHomLift.fac' (CategoricalPullback.π₁ u p) (𝟙 U) φ.1
  letI : IsIso φ.1.fst := by
    change IsIso ((CategoricalPullback.π₁ u p).map φ.1)
    rw [hfst]
    infer_instance
  have hsnd : p.map φ.1.snd = X.1.iso.inv ≫ u.map φ.1.fst ≫ Y.1.iso.hom := by
    calc
      p.map φ.1.snd = X.1.iso.inv ≫ (X.1.iso.hom ≫ p.map φ.1.snd) := by
        simp
      _ = X.1.iso.inv ≫ (u.map φ.1.fst ≫ Y.1.iso.hom) := by
        rw [← φ.1.w]
      _ = X.1.iso.inv ≫ u.map φ.1.fst ≫ Y.1.iso.hom := by
        simp
  letI : IsIso (p.map φ.1.snd) := by
    rw [hsnd]
    infer_instance
  letI : IsIso φ.1.snd :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map φ.1.snd) φ.1.snd
  letI : IsIso φ.1 :=
    (Limits.CategoricalPullback.isIso_iff u p φ.1).2 ⟨inferInstance, inferInstance⟩
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) (asIso φ.1).hom := by
    simpa using (φ.2 : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) φ.1)
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) (inv φ.1) := by
    simpa using
      (IsHomLift.lift_id_inv (CategoricalPullback.π₁ u p) U (asIso φ.1))
  refine ⟨?_⟩
  use ⟨inv φ.1, inferInstance⟩
  constructor
  · apply Functor.Fiber.hom_ext
    change φ.1 ≫ inv φ.1 = 𝟙 X.1
    simp
  · apply Functor.Fiber.hom_ext
    change inv φ.1 ≫ φ.1 = 𝟙 Y.1
    simp

private instance pullbackProjection_fiber_isGroupoid [IsFibredInGroupoids p] (U : C) :
    IsGroupoid ((CategoricalPullback.π₁ u p).Fiber U) where
  all_isIso := pullbackProjection_fiberHom_isIso u p U

/-- The pullback of a category fibred in groupoids along `u` is again fibred in groupoids. -/
theorem continuous_pullback_isFibredInGroupoids [IsFibredInGroupoids p] :
    IsFibredInGroupoids (CategoricalPullback.π₁ u p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (CategoricalPullback.π₁ u p) inferInstance ?_
  intro U
  infer_instance

instance [IsFibredInGroupoids p] :
    IsFibredInGroupoids (CategoricalPullback.π₁ u p) :=
  continuous_pullback_isFibredInGroupoids u p

/-- Lemma 8.12.3: if `u : C ⥤ D` is a continuous functor of sites and `p : S ⥤ D` is a stack in
groupoids over `(D, K)`, then the pullback category `u^p S`, modeled by
`CategoricalPullback.π₁ u p`, is a stack in groupoids over `(C, J)`. -/
theorem continuous_pullback_hasStackInGroupoidsStructure
    [Functor.IsContinuous u J K] [IsStackInGroupoids K p] :
    IsStackInGroupoids J (CategoricalPullback.π₁ u p) := by
  letI : IsFibredInGroupoids (CategoricalPullback.π₁ u p) :=
    continuous_pullback_isFibredInGroupoids u p
  let h :
      (q : S ⥤ D) → [IsStackOnSite K q] → IsStackOnSite J (CategoricalPullback.π₁ u q) :=
    continuous_pullback_isStackOnSite u
  letI : IsStackOnSite J (CategoricalPullback.π₁ u p) := h p
  infer_instance

end

end CategoryTheory
