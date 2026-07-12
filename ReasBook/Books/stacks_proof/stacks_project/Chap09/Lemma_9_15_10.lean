import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.15.2:
- primary domain: normality in towers of algebraic field extensions;
- sampled owner declarations:
  `Normal`,
  `normal_iff`,
  `Normal.tower_top_of_normal`,
  `IntermediateField.normal`;
- best owner abstraction: the canonical owner is the mathlib typeclass `Normal` together with its
  tower theorem `Normal.tower_top_of_normal`;
- primitive data: none locally beyond the ambient field tower and the normality instance on the top
  extension;
- derived API: `Normal.tower_top_of_normal` is the theorem-level owner, and
  `IntermediateField.normal` is its intermediate-field specialization.

Source/core/bridge triage:
- `source-facing`: normality ascends from the base field to the middle field in a tower
  `F → E → K`;
- `core/canonical`: `Normal.tower_top_of_normal`;
- `bridge/view`: `IntermediateField.normal`.

This item adds no new mathematics beyond the canonical theorem, so the file remains a pure recall
surface rather than introducing a redundant local wrapper theorem. -/

/- Lemma 9.15.2: let `K/E/F` be a tower of algebraic field extensions. If `K` is normal over `F`,
then `K` is normal over `E`; this is the canonical theorem `Normal.tower_top_of_normal`. -/
recall Normal.tower_top_of_normal
