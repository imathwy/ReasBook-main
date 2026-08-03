module

import Init

/- Remark 1.5. Everyday “if P, then Q” can mean merely `P → Q`, or more
strongly both `P → Q` and `¬P → ¬Q`, according to context. -/
#check fun P Q : Prop ↦ P → Q
#check fun P Q : Prop ↦ (P → Q) ∧ (¬P → ¬Q)
