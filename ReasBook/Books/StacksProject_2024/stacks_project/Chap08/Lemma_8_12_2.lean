import Mathlib
import StacksProject_2024.Chap08.Definition_8_4_1
import StacksProject_2024.Chap08.Definition_8_4_5
import StacksProject_2024.Chap08.Definition_8_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/- Domain-style sampling for Lemma 8.12.2:
- primary domain: stacks over sites and their pullback along a continuous functor.
- inspected owner-level declarations:
  `IsStackOnSite`,
  `StackOver.pullback`,
  `FibredCategoryOver.pullback`,
  `CategoricalPullback.π₁`.
- best owner abstraction: the source-facing statement is the stack-structure theorem on the
  canonical pullback projection `CategoricalPullback.π₁ u p`; the bundled stack-level direct
  image remains a thin bridge over the canonical fibred-category pullback owner
  `FibredCategoryOver.pullback`.
- primitive data: a continuous functor `u : C ⥤ D`, a projection `p : S ⥤ D`, and the stack
  structure on `p`.
- derived API: the lightweight bridge `StackOver.pullback`, whose underlying fibred category is
  definitionally `FibredCategoryOver.pullback u X.toFibredCategoryOver`.

Source/core/bridge triage:
- `source-facing`: `continuous_pullback_isStackOnSite`.
- `core/canonical`: `IsStackOnSite`, `FibredCategoryOver.pullback`, `CategoricalPullback.π₁`.
- `bridge/view`: `StackOver.pullback`. -/
/-- Lemma 8.12.2: if `u : C ⥤ D` is a continuous functor of sites and `X` is a stack over
`(D, K)` with projection `p : S ⥤ D`, then the pullback category `u^p S`, modeled by the
categorical pullback `CategoricalPullback u p`, is a stack over `(C, J)`. -/
-- Proof sketch: Lemma `8.12.1` gives that the pullback projection to `C` is fibred. For a cover
-- in `J`, continuity sends it to a cover in `K`, and the fibers and pullback functors of the
-- pullback category identify with those of `p` along `u`. Hence descent data for the pullback
-- projection are the same as descent data for `p`, so the stack condition transports from `p`.
theorem continuous_pullback_isStackOnSite
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] :
    IsStackOnSite J (CategoricalPullback.π₁ u p) := sorry

end

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

open scoped FibredCategoryOver

namespace StackOver

/-- The pullback of a stack `X` along the continuous functor `u`, bundled again as a stack over
`(C, J)`. This is a thin bridge to the canonical pullback fibred category
`u ᵖ X.toFibredCategoryOver`; keeping this exact underlying bundle avoids downstream universe
noise in morphism categories. -/
abbrev pullback (X : StackOver K) (u : C ⥤ D) [Functor.IsContinuous u J K] : StackOver J :=
  let Y : FibredCategoryOver C := u ᵖ X.toFibredCategoryOver
  let p : X.S ⥤ D := X.p
  letI : IsStackOnSite K p := by
    simpa [p] using (X.property : IsStackOnSite K X.p)
  let h :
      (q : X.S ⥤ D) → [IsStackOnSite K q] → IsStackOnSite J (CategoricalPullback.π₁ u q) :=
    continuous_pullback_isStackOnSite u
  have hpull : IsStackOnSite J (CategoricalPullback.π₁ u p) := h p
  letI : IsStackOnSite J Y.p := by
    simpa [Y, FibredCategoryOver.pullback_p] using hpull
  ⟨Y, (by infer_instance : IsStackOnSite J Y.p)⟩

end StackOver

end

end CategoryTheory
