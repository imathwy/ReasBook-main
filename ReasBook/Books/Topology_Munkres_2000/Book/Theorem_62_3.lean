module

public import Topology_Munkres_2000.Book.Theorem_62_1

public section

/-- Theorem 62.3 (Invariance of domain). If `U` is an open subset of the real plane and
`f : U → EuclideanSpace ℝ (Fin 2)` is continuous and injective, then `f` is an open
embedding. Thus its range is open and its inverse on the range is continuous. -/
theorem invarianceOfDomainPlane {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (f : U → EuclideanSpace ℝ (Fin 2)) (hf_continuous : Continuous f)
    (hf_injective : Function.Injective f) : Topology.IsOpenEmbedding f :=
  invarianceOfDomain hU f hf_continuous hf_injective

end
