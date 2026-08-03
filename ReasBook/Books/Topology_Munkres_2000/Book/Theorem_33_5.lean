module

public import Topology_Munkres_2000.Book.Exercise_33_5

public section

/- Theorem 33.5 (Strong form of the Urysohn lemma): in a normal space, a continuous
map `f : C(X, Set.Icc (0 : ℝ) 1)` equal to `0` on `A`, equal to `1` on `B`, and
strictly between `0` and `1` outside `A ∪ B` exists if and only if `A` and `B` are
disjoint closed `Gδ` sets. Here `T4Space` expresses the book's convention for a
normal space. -/
#check ContinuousMap.exists_separatesPrecisely_iff
