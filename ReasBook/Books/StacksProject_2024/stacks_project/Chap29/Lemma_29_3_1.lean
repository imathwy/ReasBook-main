import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-side owners
  `IsImmersion.of_comp`, `QuasiCompact.of_comp`, and `IsClosedImmersion.of_comp`.
- This item is therefore a pure recall bundle: each source clause is already present in mathlib
  with the source-faithful hypotheses and conclusion. -/

/- Lemma 29.3.1 (1): if `Z ⟶ X` is an immersion, then `Z ⟶ Y` is an immersion. -/
#check AlgebraicGeometry.IsImmersion.of_comp

/- Lemma 29.3.1 (2): if `Z ⟶ X` is a quasi-compact immersion and `Y ⟶ X` is quasi-separated,
then `Z ⟶ Y` is quasi-compact; together with clause (1), this recovers that `Z ⟶ Y` is a
quasi-compact immersion. -/
#check AlgebraicGeometry.QuasiCompact.of_comp

/- Lemma 29.3.1 (3): if `Z ⟶ X` is a closed immersion and `Y ⟶ X` is separated, then `Z ⟶ Y` is
a closed immersion. -/
#check AlgebraicGeometry.IsClosedImmersion.of_comp
