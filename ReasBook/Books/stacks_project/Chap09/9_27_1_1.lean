import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain triage:
- primary domain: field extensions and intermediate fields;
- sampled owner declarations: `IntermediateField`, `IntermediateField.sup_def`,
  `IntermediateField.map`, and `IntermediateField.comap`;
- core/canonical owner abstraction: `IntermediateField k Ω`;
- layer: `source-facing` recall of a `core/canonical` owner;
- primitive data: a base field `k`, an overfield `Ω`, and an `Algebra k Ω` structure;
- derived API: inclusion via the order on `IntermediateField k Ω`, compositum via `⊔`, and
  transport along field embeddings via `map` and `comap`.
-/

/- 9.27.1.1: the displayed commutative square of fields inside `Ω` is modeled in Lean by taking
`K` and `L` to be intermediate fields of the extension `Ω/k`; each such field is an object of
`IntermediateField k Ω`. -/
recall IntermediateField (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] : Type u
