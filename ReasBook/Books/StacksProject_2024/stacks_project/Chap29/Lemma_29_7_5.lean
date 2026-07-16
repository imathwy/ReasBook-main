import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `IsOpenImmersion` and the open-immersion structure
-- sheaf API; local inspection confirmed that `Definition_29_7_1` owns
-- `schemeTheoreticallyDense`. The tag evidence is consistent: item tag `01RE` matches the source
-- URL `/tag/01RE`.

/-- Lemma 29.7.5: for an open immersion `j : U ⟶ X`, the open subscheme `j.opensRange`
is scheme theoretically dense in `X` if and only if the canonical structure sheaf map
`𝒪_X ⟶ j_*𝒪_U` is injective. -/
@[stacks 01RE]
theorem schemeTheoreticallyDense_opensRange_iff_mono_structureSheafToPushforward
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    schemeTheoreticallyDense j.opensRange ↔ Mono j.c := sorry

end AlgebraicGeometry
