module

public import Topology_Munkres_2000.Book.Definition_60_4.FundamentalGroup

public section

/- Proposition 60.3 (1): In every positive dimension, the canonical projection
from `Sⁿ` to real projective `n`-space is a covering map in Munkres's
surjective sense. -/
#check RealProjectiveSpace.quotientMap_isMunkresCoveringMap

/- Proposition 60.3 (2): In dimensions at least two, the fundamental group of
real projective `n`-space at every basepoint has exactly two elements. -/
#check RealProjectiveSpace.fundamentalGroup_card
