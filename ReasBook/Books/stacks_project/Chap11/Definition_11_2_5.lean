import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain triage:
- primary domain: opposite algebras of `k`-algebras.
- sampled owner declarations:
  `Aᵐᵒᵖ`,
  `MulOpposite.instAlgebra`,
  `MulOpposite.op_mul`,
  `AlgEquiv.toOpposite`;
- best owner abstraction: the primitive owner object is the canonical type expression `Aᵐᵒᵖ`;
  the induced `k`-algebra structure and the reversed-multiplication laws are derived upstream.
- primitive data vs derived API: only the opposite type itself is primitive here; the algebra
  structure and computation rules are companion recalls, not local data.

Source/core/bridge triage:
- `source-facing`: the opposite algebra `A^{op}` from the source text;
- `core/canonical`: the mathlib owner `Aᵐᵒᵖ`;
- `bridge/view`: for commutative algebras, `AlgEquiv.toOpposite` identifies `A` with `Aᵐᵒᵖ`. -/

section

variable {k : Type u} {A : Type v} [CommRing k] [Ring A] [Algebra k A]

/- Definition 11.2.5: for a `k`-algebra `A`, the opposite algebra `A^{op}` is the canonical
`MulOpposite` type expression `Aᵐᵒᵖ`. This is the primitive owner object; the `k`-algebra
structure and the reversed-multiplication formula are derived upstream and recalled below. -/
#check Aᵐᵒᵖ

/- Companion recall: the opposite type `Aᵐᵒᵖ` carries the canonical `k`-algebra structure
`MulOpposite.instAlgebra`. -/
recall MulOpposite.instAlgebra

/- Companion recall: multiplication in the opposite algebra is reversed, as expressed by
`MulOpposite.op_mul`. -/
recall MulOpposite.op_mul

end
