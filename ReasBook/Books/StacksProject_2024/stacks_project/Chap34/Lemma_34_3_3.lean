import StacksProject_2024.stacks_project.Chap34.Definition_34_3_4

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: Chapter 34 already packages finite basic-open coverings of an affine scheme as
-- `Scheme.StandardZariskiCover`, extending the canonical mathlib owner `Scheme.OpenCover`. The
-- source-facing statement here should therefore return that standard-cover owner together with the
-- canonical refinement morphism to the given open cover. The pointwise subordination clause is
-- kept below as a companion source-facing specification.

/-- Lemma 34.3.3: a Zariski covering of an affine scheme admits a finite refinement by standard
opens of the target. In the canonical cover API, this refinement is expressed by a morphism from
the standard-open cover to the given Zariski cover whose component maps are open immersions. -/
theorem existsFiniteBasicOpenRefinementOfOpenCover
    {T : Scheme.{u}} [IsAffine T] (𝒰 : T.OpenCover) :
    ∃ (𝒱 : T.StandardZariskiCover) (f : 𝒱.toOpenCover ⟶ 𝒰),
      ∀ j : 𝒱.I₀, IsOpenImmersion (f.h₀ j) := sorry

/-- Companion source-facing subordination statement for Lemma 34.3.3: each chosen standard open in
the finite basic-open refinement can be taken inside one member of the original Zariski cover. -/
theorem existsFiniteBasicOpenRefinementOfOpenCover_subordinate
    {T : Scheme.{u}} [IsAffine T] (𝒰 : T.OpenCover) :
    ∃ 𝒱 : T.StandardZariskiCover,
      ∀ j : 𝒱.I₀, ∃ i : 𝒰.I₀, (𝒱.f j).opensRange ≤ (𝒰.f i).opensRange := sorry

end AlgebraicGeometry
