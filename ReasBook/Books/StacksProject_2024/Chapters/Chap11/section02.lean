import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_2_1 (from Chap11) -/
universe u v

section

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/- Domain-style sampling for Definition 11.2.1:
- primary domain: finiteness of algebras over a field, expressed through the underlying module;
- sampled owner declarations:
  `FiniteDimensional`,
  `Module.finrank`,
  `Module.Finite`;
- best owner abstraction: `FiniteDimensional k A`, the canonical field-specialized owner matching
  the source definition of a finite `k`-algebra;
- primitive data: none beyond the ambient `k`-algebra structure on `A`;
- derived API: the degree invariant `Module.finrank k A`;
- bridge/view: the underlying finitely generated-module spelling `Module.Finite k A`.

Source/core/bridge triage:
- `source-facing`: the textbook notion that a `k`-algebra is finite over `k`, namely
  `FiniteDimensional k A`;
- `core/canonical`: the same owner `FiniteDimensional k A`, whose mathlib implementation is the
  finitely generated-module condition;
- `bridge/view`: `Module.finrank k A` for the degree notation `[A : k]`, and `Module.Finite k A`
  for finitely generated-module arguments.

Since this item only recalls a canonical owner already present in mathlib, the public surface
should stay recall-first rather than introducing any chapter-local alias or wrapper. -/

/- Definition 11.2.1: a `k`-algebra `A` is finite over `k` when it is finite-dimensional as a
vector space over `k`. This is exactly the canonical owner `FiniteDimensional k A`. -/
recall FiniteDimensional

/- Companion recall: when `A` is finite over `k`, the degree `[A : k]` is represented by the
canonical derived natural-number invariant `Module.finrank k A`. -/
recall Module.finrank

/- Bridge recall: mathlib implements `FiniteDimensional k A` as the underlying finitely
generated-module condition `Module.Finite k A`, which remains available for downstream module-level
arguments. -/
recall Module.Finite

end

/-! ### Definition_11_2_2 (from Chap11) -/
/- Definition 11.2.2: a skew field is the canonical mathlib typeclass `DivisionRing`, namely a
possibly noncommutative ring with identity, with `1 ≠ 0`, in which every nonzero element admits a
multiplicative inverse. -/
recall DivisionRing

/-! ### Definition_11_2_3 (from Chap11) -/
universe u v

/-
Domain triage:
- primary domain: simple modules and simple rings.
- `source-facing`: the textbook notions “simple right `A`-module” and “simple ring”.
- `core/canonical`: `IsSimpleModule Aᵐᵒᵖ M` and `IsSimpleRing A`.
- `bridge/view`: the Chapter 10 source-facing reformulation
  `isSimpleModule_iff_nontrivial_and_submodule_eq_bot_or_eq_top` for modules, and
  `isSimpleRing_iff_isTwoSided_imp` for rings.
- Primitive data vs derived API: there is no extra source-defined data here; the owner predicates are
  primitive, while the lattice and two-sided-ideal formulations are derived API.
-/

section

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M]

/- Definition 11.2.3 (1): in this chapter an `A`-module means a right `A`-module, modeled in
Lean as a left module over `Aᵐᵒᵖ`; the canonical owner notion of simplicity is
`IsSimpleModule Aᵐᵒᵖ M`. -/
#check IsSimpleModule Aᵐᵒᵖ M

/- Companion recall: Chapter 10 already provides the source-facing reformulation of module
simplicity, and here it is reused for right `A`-modules by viewing them as left `Aᵐᵒᵖ`-modules. -/
recall isSimpleModule_iff_nontrivial_and_submodule_eq_bot_or_eq_top

end

section

variable {A : Type u} [Ring A]

/- Definition 11.2.3 (2): a ring `A` is simple exactly when it is the canonical typeclass
`IsSimpleRing A`. -/
#check IsSimpleRing A

/- Companion recall: for a unital ring, simplicity is equivalent to nontriviality together with
the statement that every two-sided ideal of `A` is `⊥` or `⊤`. -/
recall isSimpleRing_iff_isTwoSided_imp

end

/-! ### Definition_11_2_4 (from Chap11) -/
universe u v

variable {k : Type u} {A : Type v} [CommRing k] [Ring A] [Algebra k A]

/- 
Domain triage:
- primary domain: central algebras and centers.
- `source-facing`: the textbook notion that a `k`-algebra `A` is central.
- `core/canonical`: `Algebra.IsCentral k A`.
- `bridge/view`: `Algebra.IsCentral.mem_center_iff`.
- Primitive data vs derived API: the owner class `Algebra.IsCentral k A` is the primitive
  notion; the pointwise center characterization is derived API.
-/

/- Definition 11.2.4: a `k`-algebra `A` is central when its center is exactly the image of the
structure map `k → A`; this is the canonical mathlib class `Algebra.IsCentral k A`. -/
#check Algebra.IsCentral k A

/- Companion recall: for a central `k`-algebra, an element lies in the center exactly when it lies
in the image of the structure map `k → A`. -/
recall Algebra.IsCentral.mem_center_iff

/-! ### Definition_11_2_5 (from Chap11) -/
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
