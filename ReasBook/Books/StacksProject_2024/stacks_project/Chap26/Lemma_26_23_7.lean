import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

-- Source/core/bridge triage:
-- - source-facing: injective on points together with stalkwise surjectivity.
-- - core/canonical: `SurjectiveOnStalks` and `SurjectiveOnStalks.mono_of_injective`.
-- - bridge/view: `Scheme.Hom.surjectiveOnStalks_of_stalkMap_surjective`.

/-- Source-to-owner bridge for Lemma 26.23.7: stalkwise surjectivity is the canonical
`SurjectiveOnStalks` condition. -/
theorem Scheme.Hom.surjectiveOnStalks_of_stalkMap_surjective {X Y : Scheme} (j : X ⟶ Y)
    (hj_stalkMap_surjective : ∀ x : X, Function.Surjective (j.stalkMap x)) :
    SurjectiveOnStalks j :=
  ⟨hj_stalkMap_surjective⟩

/-- Lemma 26.23.7: if a morphism of schemes is injective on points and each induced map on stalks
is surjective, then it is a monomorphism. -/
@[stacks 01L6]
theorem Scheme.Hom.mono_of_injective_of_stalkMap_surjective {X Y : Scheme} (j : X ⟶ Y)
    (hj_injective : Function.Injective j)
    (hj_stalkMap_surjective : ∀ x : X, Function.Surjective (j.stalkMap x)) :
    Mono j := by
  letI : SurjectiveOnStalks j := j.surjectiveOnStalks_of_stalkMap_surjective hj_stalkMap_surjective
  exact SurjectiveOnStalks.mono_of_injective hj_injective

end AlgebraicGeometry
