module

import Init

/- Notation 1.9: Lean writes “P holds if and only if Q holds” as `P ↔ Q`,
which consists of the implications `P → Q` and `Q → P`. -/
#check fun P Q : Prop ↦ P ↔ Q
