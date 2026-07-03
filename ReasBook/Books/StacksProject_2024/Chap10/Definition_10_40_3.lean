import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/- Definition 10.40.3: given `m : M`, the annihilator of `m` is the canonical ideal
`Ideal.torsionOf R M m = {r : R | r • m = 0}`. -/
recall Ideal.torsionOf

/- Companion recall: membership in the annihilator of an element is exactly the textbook condition
`r • m = 0`. -/
recall Ideal.mem_torsionOf_iff

/- Companion recall: `Module.annihilator R M` is the canonical annihilator ideal of the module
`M`. -/
recall Module.annihilator

/- Companion recall: this is the standard membership characterization of the annihilator of a
module. -/
recall Module.mem_annihilator

end
