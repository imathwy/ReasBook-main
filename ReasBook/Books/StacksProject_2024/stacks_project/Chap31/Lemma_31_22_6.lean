import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_22_2
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `LocallyOfFinitePresentation`; local Chapter 31 precedent uses `RelativeH1RegularImmersion`,
-- `Scheme.Opens.ι`, open-subscheme factorization, `Flat (U.ι ≫ f)`, and
-- `pullback.snd i (pullback.fst f g)`.

/-- Lemma 31.22.6 (1): if `i : Z ⟶ X` is a relative `H_1`-regular immersion over
`f : X ⟶ S` and `f` is locally of finite presentation, then there is an open subscheme
`U ⊆ X` through which `i` factors and such that the restricted morphism `U ⟶ S` is flat. -/
@[stacks 063V]
theorem RelativeH1RegularImmersion.exists_flat_openFactorization_of_locallyOfFinitePresentation
    {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [RelativeH1RegularImmersion f i] [LocallyOfFinitePresentation f] :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, j ≫ U.ι = i ∧ Flat (U.ι ≫ f) := sorry

/-- Lemma 31.22.6 (2): under the hypotheses of Lemma 31.22.6, the immersion
`i : Z ⟶ X` is a regular immersion. -/
@[stacks 063V]
theorem RelativeH1RegularImmersion.isRegularImmersion_of_locallyOfFinitePresentation
    {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [RelativeH1RegularImmersion f i] [LocallyOfFinitePresentation f] :
    IsRegularImmersion i := sorry

/-- Lemma 31.22.6 (3): under the hypotheses of Lemma 31.22.6, regularity of
`i : Z ⟶ X` remains true after any base change `g : S' ⟶ S`. -/
@[stacks 063V]
theorem RelativeH1RegularImmersion.isRegularImmersion_pullback_snd_of_locallyOfFinitePresentation
    {X S S' Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [RelativeH1RegularImmersion f i] [LocallyOfFinitePresentation f] (g : S' ⟶ S) :
    IsRegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

end AlgebraicGeometry
