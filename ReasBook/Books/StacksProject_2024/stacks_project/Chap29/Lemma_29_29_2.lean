import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_29_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / verified owner check:
- `lean_leansearch` recalled base-change stability theorems for nearby morphism properties such as
  `IsSmoothOfRelativeDimension`, confirming that the right source-facing layer here is the scheme
  morphism itself under the canonical pullback projection `pullback.snd`;
- local project precedent fixes the owners `RelativeDimensionLE` and `RelativeDimension` in
  `Definition_29_29_1.lean`, while `Lemma_29_28_3.lean` supplies the fibre-dimension comparison
  under pullback used by the source.
-/

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) {d : ℕ}

/-- Lemma 29.29.2 (1): if a locally finite type morphism `f : X ⟶ S` has relative dimension `d`,
then any base change `pullback.snd f g : pullback f g ⟶ S'` also has relative dimension `d`. -/
@[stacks 02NK]
theorem relativeDimension_baseChange [RelativeDimension f d] :
    RelativeDimension (pullback.snd f g) d := sorry

/-- Any base change of a relative-dimension-`d` morphism again has relative dimension `d`. -/
@[stacks 02NK]
instance instRelativeDimensionPullbackSndOfRelativeDimension [RelativeDimension f d] :
    RelativeDimension (pullback.snd f g) d :=
  relativeDimension_baseChange f g

/-- Lemma 29.29.2 (2): if a locally finite type morphism `f : X ⟶ S` has relative dimension at
most `d`, then any base change `pullback.snd f g : pullback f g ⟶ S'` also has relative dimension
at most `d`. -/
@[stacks 02NK]
theorem relativeDimensionLE_baseChange [RelativeDimensionLE f d] :
    RelativeDimensionLE (pullback.snd f g) d := sorry

/-- Any base change of a relative-dimension-at-most-`d` morphism again has the same bound. -/
@[stacks 02NK]
instance instRelativeDimensionLEPullbackSndOfRelativeDimensionLE [RelativeDimensionLE f d] :
    RelativeDimensionLE (pullback.snd f g) d :=
  relativeDimensionLE_baseChange f g

end

end Scheme.Hom
end AlgebraicGeometry
