module

import Init

/- Notation 1.8: Lean writes “P implies Q” as `P → Q`; the contrapositive
of `P → Q` is written `(¬ Q) → (¬ P)`. -/
#check fun P Q : Prop ↦ P → Q
#check fun P Q : Prop ↦ (¬ Q) → (¬ P)
