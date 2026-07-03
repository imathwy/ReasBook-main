import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

namespace FieldExtensionDegree
end FieldExtensionDegree

/- Domain-style sampling for Definition 9.14.7:
- primary domain: separable closure and separable / inseparable degrees of field extensions;
- sampled owner declarations:
  `separableClosure`,
  `eq_separableClosure_iff`,
  `Field.sepDegree`,
  `Field.insepDegree`;
- best owner abstraction: the textbook degrees are canonically owned by the mathlib declarations
  `Field.sepDegree F E` and `Field.insepDegree F E`, both defined from the intermediate field
  `separableClosure F E` identified in Lemma 9.14.6;
- primitive data: none locally, since the underlying intermediate field and both degree
  constructions are already owned upstream in mathlib;
- derived API: the bridge from the textbook subextension `E_sep` to `separableClosure F E` comes
  from Lemma 9.14.6 via `eq_separableClosure_iff`, while later tower laws and finite-degree
  consequences are downstream theorems on `Field.sepDegree` and `Field.insepDegree`.

Source/core/bridge triage:
- `source-facing`: the textbook separable degree `[E : F]_s = [E_sep : F]` and inseparable degree
  `[E : F]_i = [E : E_sep]`;
- `core/canonical`: `Field.sepDegree F E` and `Field.insepDegree F E`;
- `bridge/view`: Lemma 9.14.6, which identifies the source field `E_sep` with the canonical owner
  `separableClosure F E`.

This file should therefore remain a pure recall surface. Any local abbreviation or restated degree
definition would only duplicate the existing owner declarations. -/

/- Definition 9.14.7: the textbook separable degree notation `[E : F]_s` is the canonical owner
`Field.sepDegree F E`. -/
scoped[FieldExtensionDegree] notation:max "[" E " : " F "]_s" => Field.sepDegree F E

/- Companion notation: the textbook inseparable degree notation `[E : F]_i` is the canonical owner
`Field.insepDegree F E`. -/
scoped[FieldExtensionDegree] notation:max "[" E " : " F "]_i" => Field.insepDegree F E

open scoped FieldExtensionDegree

/- Source-facing checks: the textbook degree notations `[E : F]_s` and `[E : F]_i` denote the
canonical cardinal-valued degree owners. -/
#check ([E : F]_s : Cardinal)
#check ([E : F]_i : Cardinal)

/- Definition 9.14.7: for an algebraic field extension `E / F`, with `E_sep` identified in
Lemma 9.14.6 as `separableClosure F E`, the textbook separable degree `[E : F]_s = [E_sep : F]`
is the canonical mathlib notion `Field.sepDegree F E`. -/
recall Field.sepDegree

/- Companion recall: for the same extension, the textbook inseparable degree `[E : F]_i =
[E : E_sep]` is the canonical mathlib notion `Field.insepDegree F E`. -/
recall Field.insepDegree
