module

public import Topology_Munkres_2000.Book.Definition_76_1.Cut

public section

/- Definition 76.1: Cutting a cyclic polygonal region at a vertex `pₖ`, where
`1 < k` and `k < n - 1`, gives cyclic polygonal regions with successive vertices
`p₀, p₁, …, pₖ, p₀` and `p₀, pₖ, …, pₙ = p₀`. They share the diagonal edge `p₀pₖ`,
and their filled regions unite to the original region. -/
#check CyclicPolygon.Cut.left
#check CyclicPolygon.Cut.right
#check CyclicPolygon.Cut.commonEdge
#check CyclicPolygon.Cut.region_eq_union
