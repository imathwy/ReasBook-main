module

import Init

/- Definition 1.9: The contrapositive of `P → Q` is the proposition
`¬ Q → ¬ P`. -/
#check (fun P Q : Prop ↦ ¬ Q → ¬ P)

/- The canonical implication from a statement to its contrapositive. -/
#check mt
