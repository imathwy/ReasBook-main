import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IntermediateField

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.16.4:
- primary domain: normal closures of field extensions;
- sampled canonical declarations:
  `IntermediateField.normalClosure`,
  `normalClosure_def`,
  `isNormalClosure_normalClosure`,
  `normalClosure.is_finiteDimensional`;
- best owner abstraction: `IntermediateField.normalClosure`, specialized here to the ambient field
  `AlgebraicClosure E`.

Source/core/bridge triage:
- `source-facing`: the textbook name "the normal closure of `E` over `F`";
- `core/canonical`: the intermediate field `normalClosure F E (AlgebraicClosure E)`;
- `bridge/view`: Lemma 9.16.3 and its companion recalls, which provide the normal-closure
  specification, normality, and finiteness properties of this canonical field.

Primitive data are only the fields `F`, `E`, the `F`-algebra structure on `E`, and the ambient
field `AlgebraicClosure E`. The `IsNormalClosure` witness and finiteness/normality statements are
derived API. In particular, the source's finite-extension hypothesis is not primitive data of the
owner itself, so this file should remain a direct recall of the owner specialization rather than
introducing any local wrapper or alias.
-/

/- Definition 9.16.4: for a finite field extension `E/F`, the field
`normalClosure F E (AlgebraicClosure E)` constructed in Lemma 9.16.3 is called the normal
closure of `E` over `F`. -/
#check normalClosure F E (AlgebraicClosure E)

/- Companion recall: `IntermediateField.normalClosure` is the owner-level relative normal closure
for any field extension `E/F`; Definition 9.16.4 is its specialization to `AlgebraicClosure E`. -/
recall IntermediateField.normalClosure
