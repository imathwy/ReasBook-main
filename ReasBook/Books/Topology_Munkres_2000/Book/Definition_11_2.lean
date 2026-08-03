module

import Mathlib.Order.Preorder.Chain

public section

/- Definition 11.2: For a strict partial order `r` on `α`, a subset `B : Set α`
is simply ordered by `r` exactly when `IsChain r B`; this requires every pair of
distinct elements of `B` to be comparable under `r`. -/
#check IsChain

end
