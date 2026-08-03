module

public import Topology_Munkres_2000.Book.Theorem_13_99_1

public section

/- Exercise 13.99.2. A path-connected, locally path-connected, semilocally simply
connected regular space with a countable basis has countable fundamental group at
every basepoint. Here textbook regularity is represented by `T3Space`, and a
countable basis by `SecondCountableTopology`. -/
#check FundamentalGroup.instCountableOfSemilocallySimplyConnected
