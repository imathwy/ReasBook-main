module

import Init

/- Definition 7.3. A recursive definition specifies a function by a recursion
formula expressing each value in terms of its values at predecessors. The
canonical recursion formula for well-founded recursion is `WellFounded.fix_eq`. -/
#check WellFounded.fix_eq

/- `WellFounded.fix` is the corresponding recursive construction. -/
#check WellFounded.fix
