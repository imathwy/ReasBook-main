import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` was unavailable here (`HTTP 429: Too Many Requests`).
-- Local Section 29.57 precedent in `Definition_29_57_1` already provides the canonical owners
-- `Scheme.Hom.degreesOfFibresBoundedBy` and `Scheme.Hom.universallyBoundedFibres`.

variable {X Y Y' : Scheme.{u}}

/-- A fixed fibre-degree bound on a surjective base change also bounds the original morphism. -/
theorem degreesOfFibresBoundedBy_of_surjective_baseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g] {n : ℕ}
    (h : degreesOfFibresBoundedBy (pullback.snd f g) n) :
    degreesOfFibresBoundedBy f n := sorry

/-- Lemma 29.57.6: if `g : Y' ⟶ Y` is surjective and the base change of `f` to `Y'` has
universally bounded fibres, then `f` has universally bounded fibres. -/
@[stacks 03J8]
theorem universallyBoundedFibres_of_surjective_baseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g]
    (h : universallyBoundedFibres (pullback.snd f g)) :
    universallyBoundedFibres f := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, degreesOfFibresBoundedBy_of_surjective_baseChange f g hn⟩

end Scheme.Hom
end AlgebraicGeometry
