import StacksProject_2024.Chap29.Lemma_29_44_6
import StacksProject_2024.Chap29.Lemma_29_25_8
import StacksProject_2024.Chap29.Lemma_29_48_2
import StacksProject_2024.Chap29.Lemma_29_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

-- Semantic recall:
-- - Lemma 29.48.2 already packages the Chapter 29 source-facing owner `IsFiniteLocallyFree`
--   through the explicit conjunction `IsFinite ∧ Flat ∧ LocallyOfFinitePresentation`;
-- - the present item is the base-change stability statement for that owner on the canonical
--   projection `pullback.snd`.

/-- A finite locally free morphism remains finite locally free after pullback. -/
theorem IsFiniteLocallyFree.pullback_snd (hf : IsFiniteLocallyFree f) :
    IsFiniteLocallyFree (pullback.snd f g) := by
  letI : IsFinite f := hf.isFinite
  letI : Flat f := hf.flat
  letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  exact isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
    inferInstance (flat_pullback_snd f g) inferInstance

/-- Lemma 29.48.4: the pullback of a finite locally free morphism along any base change is finite
locally free. -/
@[stacks 04MG]
theorem finiteLocallyFree_pullback_snd (hf : IsFiniteLocallyFree f) :
    IsFiniteLocallyFree (pullback.snd f g) :=
  IsFiniteLocallyFree.pullback_snd f g hf

/-- Any base change of a finite locally free morphism is finite locally free. -/
@[stacks 04MG, instance]
instance instIsFiniteLocallyFreePullbackSndOfIsFiniteLocallyFree
    [IsFiniteLocallyFree f] :
    IsFiniteLocallyFree (pullback.snd f g) :=
  finiteLocallyFree_pullback_snd f g inferInstance

end

end AlgebraicGeometry
