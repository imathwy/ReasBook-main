module

import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/- Definition 51.6: Composition of path-homotopy classes is defined only when
the terminal endpoint of the first class is the initial endpoint of the second.
The resulting typed composition is the composition law of the fundamental
groupoid. -/
#check Path.Homotopic.Quotient.trans
#check FundamentalGroupoid.instGroupoid
#check FundamentalGroupoid.comp_eq
