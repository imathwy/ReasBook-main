module

import Init

/- Definition 1.7: In `P → Q`, the proposition `P` is called the hypothesis,
and the proposition `Q` is called the conclusion. -/
#check fun P Q : Prop ↦ P → Q
