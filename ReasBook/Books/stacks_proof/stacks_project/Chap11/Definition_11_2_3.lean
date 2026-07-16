import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Definition_10_52_9

-- Declarations for this item will be appended below by the statement pipeline.

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
