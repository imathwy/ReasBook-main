module

public import Topology_Munkres_2000.Book.Definition_9_0_2

public section

/- Definition 52.7. A space is simply connected when it is path connected and its
fundamental group at some, equivalently every, basepoint is trivial; triviality is
represented by `Subsingleton (FundamentalGroup X x₀)`. -/
#check SimplyConnectedSpace
#check simplyConnectedSpace_iff_subsingleton_fundamentalGroup
