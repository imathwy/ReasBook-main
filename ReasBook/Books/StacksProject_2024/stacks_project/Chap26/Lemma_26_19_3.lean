import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u

/- Source/core/bridge triage for Lemma 26.19.3:
- `source-facing`: the base change of a quasi-compact morphism of schemes is quasi-compact.
- `core/canonical`: the canonical base-change instance
  `AlgebraicGeometry.instQuasiCompactSndScheme`.
- `bridge/view`: the scheme-level pullback projection statement
  `AlgebraicGeometry.QuasiCompact (pullback.snd f g)`. -/

/- Lemma 26.19.3: if `f : X ⟶ S` is quasi-compact, then for any `g : Y ⟶ S` the pullback
projection `X ×[S] Y ⟶ Y` is quasi-compact. Canonically, this is the specialized base-change
instance `AlgebraicGeometry.instQuasiCompactSndScheme`. -/
recall AlgebraicGeometry.instQuasiCompactSndScheme

section

variable {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.QuasiCompact f]

#check (inferInstance : AlgebraicGeometry.QuasiCompact (pullback.snd f g))

end
