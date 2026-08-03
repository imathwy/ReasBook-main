import Topology_Munkres_2000.Book.Exercise_13_99_5.Instances

/-
Exercise 13.99.5 (1): The infinite earring is compact.
-/
#synth CompactSpace InfiniteEarring.Space

/-
Exercise 13.99.5 (2): The infinite earring is Hausdorff.
-/
#synth T2Space InfiniteEarring.Space

/-
Exercise 13.99.5 (3): The infinite earring has a countable topological basis.
-/
#synth SecondCountableTopology InfiniteEarring.Space

/-
Exercise 13.99.5 (4): The fundamental group of the infinite earring at its common
origin is uncountable.
-/
#synth Uncountable (FundamentalGroup InfiniteEarring.Space InfiniteEarring.origin)
