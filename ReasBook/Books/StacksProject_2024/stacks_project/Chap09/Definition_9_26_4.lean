import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
variable {ι : Type v} {x : ι → K}

/- Source/core/bridge triage for Definition 9.26.4:
- sampled owner declarations: `IsTranscendenceBasis`, `exists_isTranscendenceBasis`,
  `Algebra.trdeg`, `IsTranscendenceBasis.cardinalMk_eq_trdeg`;
- `source-facing`: the transcendence degree of a field extension `K/k`
- `core/canonical`: `Algebra.trdeg k K`
- `bridge/view`: `IsTranscendenceBasis.cardinalMk_eq_trdeg`, identifying the cardinality of any
  transcendence basis with that invariant
- `layer`: `core/canonical`

Primitive data are only the field extension and its canonical `k`-algebra structure on `K`. A
choice of transcendence basis and the equality between its cardinality and the invariant are
derived API, so the owner file should recall `Algebra.trdeg` directly and keep the basis
cardinality statement as a companion.
-/

/- Definition 9.26.4: for a field extension `K / k`, the transcendence degree of `K` over `k`
is the canonical mathlib cardinal-valued invariant `Algebra.trdeg k K`. -/
recall Algebra.trdeg

/- Companion recall: `IsTranscendenceBasis.cardinalMk_eq_trdeg` identifies the cardinality of any
transcendence basis with `Algebra.trdeg`. -/
recall IsTranscendenceBasis.cardinalMk_eq_trdeg
