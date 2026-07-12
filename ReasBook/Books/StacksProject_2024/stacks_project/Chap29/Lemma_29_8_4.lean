import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- - `lean_leansearch` recalled the canonical dominant-morphism owner `AlgebraicGeometry.IsDominant`.
-- - Earlier Chapter 29 files use `GeneralizingMap f.base` for "generalizations lift along `f`".
-- - The base-changed morphism is canonically the pullback projection `pullback.snd f g`.

/-- Lemma 29.8.4: let `f : X ⟶ S` be a quasi-compact dominant morphism of schemes, let
`g : S' ⟶ S` be a morphism of schemes, and let `pullback.snd f g : pullback f g ⟶ S'` be the
base change of `f` by `g`. If generalizations lift along `g`, then the base change is dominant. -/
@[stacks 0H3F]
theorem isDominant_pullbackSnd_of_isDominant_of_generalizingMap
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [QuasiCompact f] [IsDominant f]
    (hg : GeneralizingMap g.base) :
    IsDominant (pullback.snd f g) := sorry

end AlgebraicGeometry
