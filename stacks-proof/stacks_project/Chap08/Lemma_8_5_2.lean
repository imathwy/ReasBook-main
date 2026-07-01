import Mathlib
import stacks_project.Chap04.Lemma_4_35_2
import stacks_project.Chap08.Definition_8_5_1

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

/-- Helper for Lemma 8.5.2: a stack in groupoids has groupoid fibers. -/
lemma fiber_groupoid_of_isStackInGroupoids
    (h : IsStackInGroupoids J p) : ∀ U : C, IsGroupoid (p.Fiber U) := by
  -- Read the fiberwise groupoid condition from the Chapter 4 characterization of
  -- `IsFibredInGroupoids`, applied to the inherited owner field.
  exact
    (isFibredInGroupoids_iff_isFibered_and_fiber_groupoid p).mp h.toIsFibredInGroupoids |>.2

/-- Helper for Lemma 8.5.2: a site-theoretic stack with groupoid fibers is fibred in groupoids. -/
lemma isFibredInGroupoids_of_isStackOnSite_and_fiber_groupoid
    (hstack : IsStackOnSite J p) (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    IsFibredInGroupoids p := by
  -- The stack-on-site owner already carries the needed `p.IsFibered` field.
  exact isFibredInGroupoids_of_isFibered_and_fiber_groupoid p hstack.toIsFibered hfiber

/-- Helper for Lemma 8.5.2: the stack condition together with groupoid fibers repackages into a
stack in groupoids. -/
lemma isStackInGroupoids_of_isStackOnSite_and_fiber_groupoid
    (hstack : IsStackOnSite J p) (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    IsStackInGroupoids J p := by
  -- Package the two canonical owner fields directly into the Chapter 8 structure.
  exact
    { toIsStackOnSite := hstack
      toIsFibredInGroupoids :=
        isFibredInGroupoids_of_isStackOnSite_and_fiber_groupoid
          (J := J) (p := p) hstack hfiber }

/-
Proof sketch: combine the canonical unpacking of `IsStackInGroupoids` with Lemma `4.35.2`,
which identifies fibred-in-groupoids functors with fibered functors whose fibers are groupoids.
-/
/-- Lemma 8.5.2: a category over a site is a stack in groupoids exactly when it is a stack and
all of its fiber categories are groupoids. -/
theorem isStackInGroupoids_iff_isStackOnSite_and_fiber_groupoid :
    IsStackInGroupoids J p ↔ IsStackOnSite J p ∧ ∀ U : C, IsGroupoid (p.Fiber U) := by
  constructor
  · intro h
    -- Unpack the source-facing owner into its stack component and its fiberwise groupoid data.
    exact
      ⟨h.toIsStackOnSite,
        fiber_groupoid_of_isStackInGroupoids (J := J) (p := p) h⟩
  · rintro ⟨hstack, hfiber⟩
    -- Repackage the two canonical components into the stack-in-groupoids owner.
    exact
      isStackInGroupoids_of_isStackOnSite_and_fiber_groupoid
        (J := J) (p := p) hstack hfiber

end

end CategoryTheory
