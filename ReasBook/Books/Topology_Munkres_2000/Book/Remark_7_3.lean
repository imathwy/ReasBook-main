module

import Mathlib.Data.PNat.Basic

/- Remark 7.3: A recursively defined function cannot be presupposed in an
induction predicate before it has been constructed. The recursor `PNat.recOn`
instead constructs the function directly from its initial and successor data. -/
#check PNat.recOn
