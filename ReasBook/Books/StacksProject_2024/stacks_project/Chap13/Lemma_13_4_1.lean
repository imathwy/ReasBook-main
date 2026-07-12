import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated

universe v u

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/- Domain-style sampling:
- primary domain: distinguished triangles in pretriangulated categories;
- sampled canonical declarations:
  `Pretriangulated.distinguishedTriangles`,
  `comp_distTriang_mor_zero₁₂`,
  `comp_distTriang_mor_zero₂₃`,
  `comp_distTriang_mor_zero₃₁`;
- best owner abstraction: the canonical owner declaration is
  `Pretriangulated.distinguishedTriangles`, with project-facing notation `distTriang C`, so the
  owner-level hypothesis is `hT : T ∈ distTriang C`;
- primitive data: a triangle `T` together with the owner-level hypothesis `hT : T ∈ distTriang C`;
- derived API: the three vanishing composites of consecutive morphisms in a distinguished triangle;
- source/core/bridge triage:
  `source-facing`: Stacks Lemma 13.4.1, asserting that the three consecutive composites in a
    distinguished triangle vanish;
  `core/canonical`: the owner `Pretriangulated.distinguishedTriangles`, surfaced as `distTriang C`,
    and the three canonical vanishing theorems above;
  `bridge/view`: none needed, because the textbook statements already coincide with the canonical
    owner-level API.

Primitive data already lives upstream in `Pretriangulated`, so this file should expose the owner
directly and recall the three canonical consequences rather than introducing any parallel local
lemma wrappers.
-/

/- The owner for Lemma 13.4.1 is the canonical distinguished-triangle predicate `distTriang`. -/
#check (distTriang C)

/- Lemma 13.4.1 (1): if `(X, Y, Z, f, g, h)` is a distinguished triangle in a pretriangulated
category, then `g ∘ f = 0`. This is exactly the canonical theorem
`comp_distTriang_mor_zero₁₂`. -/
recall comp_distTriang_mor_zero₁₂

/- Lemma 13.4.1 (2): if `(X, Y, Z, f, g, h)` is a distinguished triangle in a pretriangulated
category, then `h ∘ g = 0`. This is exactly the canonical theorem
`comp_distTriang_mor_zero₂₃`. -/
recall comp_distTriang_mor_zero₂₃

/- Lemma 13.4.1 (3): if `(X, Y, Z, f, g, h)` is a distinguished triangle in a pretriangulated
category, then `f[1] ∘ h = 0`, which in Lean is the vanishing
`T.mor₃ ≫ T.mor₁⟦1⟧' = 0`. This is exactly the canonical theorem
`comp_distTriang_mor_zero₃₁`. -/
recall comp_distTriang_mor_zero₃₁

end
