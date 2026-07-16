import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_2
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-
Domain-style sampling for Lemma 8.5.2:
- primary domain: stacks in groupoids over a site, viewed through the canonical parent owners
  `IsStackOnSite` and `IsFibredInGroupoids`.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `IsStackOnSite`,
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- best owner abstraction: `IsStackInGroupoids J p` remains the source-facing owner; this file is a
  bridge/view lemma unpacking that owner into the site-theoretic stack condition and the
  fiberwise groupoid condition.
- primitive data: the parent owner data `IsStackOnSite J p` and `IsFibredInGroupoids p`.
- derived API: the fiberwise groupoid condition, obtained canonically from the Chapter 4 owner
  theorem rather than by a parallel local reconstruction.

Source/core/bridge triage:
- `source-facing`: `IsStackInGroupoids J p`.
- `core/canonical`: `IsStackOnSite J p`, `IsFibredInGroupoids p`, and
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`.
- `bridge/view`: `isStackInGroupoids_iff_isStackOnSite_and_fiber_groupoid`. -/

-- Proof sketch: combine the canonical unpacking of `IsStackInGroupoids` with Lemma `4.35.2`,
-- which identifies fibred-in-groupoids functors with fibered functors whose fibers are groupoids.
/-- Lemma 8.5.2: a category over a site is a stack in groupoids exactly when it is a stack and
all of its fiber categories are groupoids. -/
theorem isStackInGroupoids_iff_isStackOnSite_and_fiber_groupoid :
    IsStackInGroupoids J p ↔ IsStackOnSite J p ∧ ∀ U : C, IsGroupoid (p.Fiber U) := by
  constructor
  · intro h
    letI : IsStackInGroupoids J p := h
    exact ⟨inferInstance, fun _ ↦ inferInstance⟩
  · rintro ⟨hstack, hfiber⟩
    letI : IsStackOnSite J p := hstack
    letI : IsFibredInGroupoids p :=
      isFibredInGroupoids_of_isFibered_and_fiber_groupoid p inferInstance hfiber
    infer_instance

end

end CategoryTheory
