module

import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

public section

/- Theorem 51.2 (1): Composition of path-homotopy classes is associative. -/
#check Path.Homotopic.Quotient.trans_assoc

/- Theorem 51.2 (2), right identity: the constant path at the terminal point is a
right identity. -/
#check Path.Homotopic.Quotient.trans_refl

/- Theorem 51.2 (2), left identity: the constant path at the initial point is a
left identity. -/
#check Path.Homotopic.Quotient.refl_trans

/- Theorem 51.2 (3), first inverse identity: a path-homotopy class followed by its
reverse is the constant class at its initial point. -/
#check Path.Homotopic.Quotient.trans_symm

/- Theorem 51.2 (3), second inverse identity: the reverse followed by the original
path-homotopy class is the constant class at its terminal point. -/
#check Path.Homotopic.Quotient.symm_trans
