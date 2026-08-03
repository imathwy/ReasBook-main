module

import Mathlib.Data.Rel

/- Definition 2.3 (1): The domain of a rule of assignment `r : SetRel C D`
is the set of first coordinates occurring in `r`. -/
#check SetRel.dom
#check SetRel.mem_dom

/- Definition 2.3 (2): The image set of a rule of assignment `r : SetRel C D`
is the set `r.cod` of second coordinates occurring in `r`. -/
#check SetRel.cod
#check SetRel.mem_cod
