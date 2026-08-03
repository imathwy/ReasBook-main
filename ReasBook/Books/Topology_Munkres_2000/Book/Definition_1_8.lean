module

import Init

/- Definition 1.8: A conditional statement `P → Q` is vacuously true when
its hypothesis cannot hold: from `¬ P`, any assumed proof of `P` yields a proof
of every conclusion `Q`. -/
#check fun (P Q : Prop) (hP : ¬ P) (p : P) ↦ (False.elim (hP p) : Q)
