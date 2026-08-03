module

public import Topology_Munkres_2000.Book.Theorem_52_4.Functoriality

public section

open FundamentalGroup.LeftToRight

/- Theorem 52.4 (1). The homomorphism induced by a composite of continuous maps
is the composite of their induced homomorphisms. -/
#check map_comp

/- Theorem 52.4 (2). The identity continuous map on `X` induces the identity
homomorphism on the fundamental group at `x₀`. -/
#check map_id

end
