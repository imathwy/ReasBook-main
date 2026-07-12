import Mathlib
import StacksProject_2024.Chap04.Definition_4_33_9
import StacksProject_2024.Chap08.Lemma_8_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]
variable (u : C ⥤ D) (X : FibredCategoryOver D)

/- Domain-style sampling for Definition 8.12.4:
- primary domain: fibred categories under pullback along a functor, modeled by categorical
  pullbacks.
- inspected owner-level declarations:
  `FibredCategoryOver.ofFunctor`,
  `CategoricalPullback`,
  `CategoricalPullback.π₁`,
  the canonical instance on `CategoricalPullback.π₁ u X.p`.
- best owner abstraction: `FibredCategoryOver.pullback u X`, the bundled fibred category over `C`
  built directly from the canonical pullback projection `π₁ u X.p`.
- primitive data: the canonical pullback projection `π₁ u X.p`.
- derived API: the scoped notation `uᵖ X` and the projection lemma
  `FibredCategoryOver.pullback_p`.

Source/core/bridge triage:
- `source-facing`: `FibredCategoryOver.pullback u X`, notation `uᵖ X`.
- `core/canonical`: `FibredCategoryOver.ofFunctor (CategoricalPullback.π₁ u X.p)`.
- `bridge/view`: the scoped notation `uᵖ X`. -/

namespace FibredCategoryOver

/-- Definition 8.12.4: the pullback fibred category `uᵖ X` of a fibred category `X` over `D`
along a functor `u : C ⥤ D` is the canonical bundled fibred category built from the first
projection `π₁ u X.p`. In the setting of a morphism of sites, this is the fibred category
denoted `f_* X` in the Stacks Project. -/
abbrev pullback (u : C ⥤ D) (X : FibredCategoryOver D) : FibredCategoryOver C :=
  let p := CategoricalPullback.π₁ u X.p
  letI : p.IsFibered := pullback_projection_is_fibered u X.p
  ofFunctor p

-- Proof sketch: unfold `pullback`; it is the canonical fibred category over `C` obtained from
-- the pullback projection `CategoricalPullback.π₁ u X.p` via `ofFunctor`.
/-- Unfolding `pullback` identifies it with the canonical fibred category attached to the
pullback projection `π₁ u X.p`. -/
theorem pullback_def (u : C ⥤ D) (X : FibredCategoryOver D) :
    pullback u X = ofFunctor (CategoricalPullback.π₁ u X.p) := sorry

/- Textbook notation for the pullback fibred category of `X` along `u`. -/
scoped infixr:100 " ᵖ " => pullback

end FibredCategoryOver

open scoped FibredCategoryOver

namespace FibredCategoryOver

/-- The projection of `FibredCategoryOver.pullback u X`, written `uᵖ X`, is the canonical
pullback projection `π₁ u X.p`. -/
@[simp] theorem pullback_p :
    (pullback u X).p = CategoricalPullback.π₁ u X.p := rfl

end FibredCategoryOver

end

end CategoryTheory
