module

public import Topology_Munkres_2000.Book.Lemma_43_3

public section

universe u v

/- Theorem 46.1: a sequence of functions converges in the topology of pointwise
convergence if and only if it converges at each point of the domain. This is the
constant-family specialization of Lemma 43.3. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace Y]
    (F : ℕ → X → Y) (f : X → Y) ↦ tendsto_pi_sequence_iff F f

end
