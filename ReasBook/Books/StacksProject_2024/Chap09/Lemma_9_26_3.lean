import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Lemma 9.26.3:
- primary domain: transcendence bases for field extensions;
- sampled owner declarations:
  `IsTranscendenceBasis`,
  `exists_isTranscendenceBasis`,
  `exists_isTranscendenceBasis'`,
  `IsTranscendenceBasis.cardinalMk_eq`;
- best owner abstraction: `IsTranscendenceBasis`;
- primitive data: the field extension `F ⟶ E`;
- derived API: existence of a transcendence basis and invariance of the cardinality of any two
  transcendence bases.

Source/core/bridge triage:
- `source-facing`: existence of a transcendence basis of `E/F` and equality of the cardinalities
  of any two transcendence bases;
- `core/canonical`: the owner predicate `IsTranscendenceBasis F x`;
- `bridge/view`: the type-indexed variant `exists_isTranscendenceBasis'`;
- `layer`: `source-facing`.

The source lemma adds no new owner object beyond the canonical predicate
`IsTranscendenceBasis`, so the file should recall the exact existence and uniqueness-of-cardinality
theorems rather than a local wrapper or a type-indexed surrogate.
-/

/- Lemma 9.26.3 (1): for a field extension `E/F`, a transcendence basis exists. This is the
canonical source-facing mathlib theorem `exists_isTranscendenceBasis`. -/
recall exists_isTranscendenceBasis

/- Lemma 9.26.3 (2): any two transcendence bases of `E/F` have the same cardinality. This is the
canonical mathlib theorem `IsTranscendenceBasis.cardinalMk_eq`. -/
recall IsTranscendenceBasis.cardinalMk_eq
