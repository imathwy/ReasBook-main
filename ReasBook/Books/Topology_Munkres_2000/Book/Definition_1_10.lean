module

import Init

/- Definition 1.10: The converse of `P → Q` is the proposition `Q → P`. -/
#check (fun P Q : Prop ↦ Q → P)
