import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

noncomputable section

section

variable {k : Type u} [Field k]

/- 
Domain-style sampling for Example 9.6.4:
- primary domain: simple algebraic extensions presented by adjoining a root of a polynomial;
- sampled owner API:
  `AdjoinRoot`,
  `AdjoinRoot.instField`,
  `AdjoinRoot.instAlgebra`,
  `finrank_quotient_span_eq_natDegree`;
- best owner abstraction: the quotient owner `AdjoinRoot P`, with its canonical field and
  `k`-algebra structures supplied upstream.

Primitive-vs-derived split:
- primitive data: the polynomial `P : k[X]` and the quotient owner `AdjoinRoot P`;
- derived API: the field structure under irreducibility and the ambient `k`-algebra structure.

Source/core/bridge triage:
- `source-facing`: the simple extension `k[t]/(P)` viewed as an extension field of `k`;
- `core/canonical`: `AdjoinRoot`, `AdjoinRoot.instField`, `AdjoinRoot.instAlgebra`;
- `bridge/view`: the quotient spelling `k[X] ⧸ Ideal.span {P}` from Example 9.3.3.

This example adds no new data, so the canonical owner instances should be recalled directly, with
the quotient spelling used only as a source-facing bridge check.
-/

section

variable (P : k[X]) [Fact (Irreducible P)]

/- Example 9.6.4: the simple extension `k[t]/(P)` is formalized by `AdjoinRoot P`, which is
definitionally the quotient `k[X] ⧸ Ideal.span {P}`. The key step is to recall the canonical
field instance supplied upstream for irreducible `P`. -/
recall AdjoinRoot.instField (P : k[X]) [Fact (Irreducible P)] :
    Field (k[X] ⧸ Ideal.span {P})

end

section

variable (P : k[X])

/- The extension structure is the second canonical ingredient: the quotient spelling inherits the
ambient `k`-algebra structure from `AdjoinRoot.instAlgebra`. -/
recall AdjoinRoot.instAlgebra

/- Combining the previous field recall with this algebra recall is exactly the textbook claim that
`k[X] / (P)` is an extension of `k`. We record that bridge by checking the induced algebra
structure on the quotient spelling. -/
#check (inferInstance : Algebra k (k[X] ⧸ Ideal.span {P}))

end

end
