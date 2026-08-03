module

public import Topology_Munkres_2000.Book.Exercise_33_11

public section

/- Exercise 33.12: The proof of the Urysohn lemma cannot be generalized from normal spaces
to regular spaces because the preceding counterexample is `T₃` but not `T₃.₅`. -/
#check (inferInstance : T3Space RegularCounterexample.Space)
#check ((fun h : T35Space RegularCounterexample.Space ↦
  RegularCounterexample.not_completelyRegularSpace h.toCompletelyRegularSpace) :
  ¬ T35Space RegularCounterexample.Space)

end
