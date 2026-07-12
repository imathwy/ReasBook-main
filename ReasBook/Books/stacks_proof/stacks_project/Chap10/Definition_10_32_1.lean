import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommSemiring R]

namespace Ideal

/-
Definition 10.32.1 (1), source-facing layer: the chapter vocabulary "locally nilpotent ideal"
names the canonical containment `I ≤ nilradical R`.

Primitive data: only the ideal `I`.
Core/canonical owner: the raw proposition `I ≤ nilradical R`.
Bridge/view: `isLocallyNilpotent_iff` below rewrites this to the textbook elementwise form.
-/
@[stacks 00IL]
abbrev IsLocallyNilpotent (I : Ideal R) : Prop :=
  I ≤ nilradical R

/-- Definition 10.32.1 (1), textbook wording: an ideal is locally nilpotent exactly when every
element of it is nilpotent. -/
@[simp] theorem isLocallyNilpotent_iff (I : Ideal R) :
    I.IsLocallyNilpotent ↔ ∀ x ∈ I, IsNilpotent x := by
  simp [IsLocallyNilpotent, SetLike.le_def, mem_nilradical]

end Ideal

/- Definition 10.32.1 (2): nilpotent ideals are governed by the canonical predicate
`IsNilpotent : Ideal R → Prop`; for an ideal `I`, this is definitionally the assertion that some
power `I ^ n` is zero. -/
#check (IsNilpotent : Ideal R → Prop)

end
