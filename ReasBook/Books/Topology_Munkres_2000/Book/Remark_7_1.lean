module

import Mathlib.Data.PNat.Basic

/- Remark 7.1: Defining a function on all positive integers “by induction,” as
in the preceding proof and in the definition of positive powers, uses more than
the proposition-valued induction principle alone. In Lean, the corresponding
dependent recursor `PNat.recOn` constructs values from initial and successor
data. -/
#check PNat.recOn
