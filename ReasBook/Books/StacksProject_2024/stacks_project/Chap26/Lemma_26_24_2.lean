import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme owner
-- `AlgebraicGeometry.IsClosedImmersion` and its closed-embedding/stalk-surjectivity criterion.
-- This source-facing lemma uses `SurjectiveOnStalks f` for the Stacks hypothesis that the
-- pushforward-form structure-sheaf map is surjective.

/-- Lemma 26.24.2: let `f : X ⟶ Y` be a morphism of schemes. If `f` induces a
homeomorphism of `X` with a closed subset of `Y`, and the pushforward-form structure sheaf map
`f^\sharp : \mathcal O_Y \to f_* \mathcal O_X` is surjective, then `f` is a closed immersion
of schemes. -/
@[stacks 01LD]
theorem Scheme.Hom.isClosedImmersion_of_isClosedEmbedding_of_surjectiveOnStalks
    {X Y : Scheme} (f : X ⟶ Y) (hf_base : Topology.IsClosedEmbedding f)
    [SurjectiveOnStalks f] :
    IsClosedImmersion f := sorry

end AlgebraicGeometry
