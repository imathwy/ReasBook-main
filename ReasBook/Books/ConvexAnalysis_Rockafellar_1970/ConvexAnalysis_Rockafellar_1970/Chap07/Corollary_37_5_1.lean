import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3

noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable {YU : Type*} {YV : Type*}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 37.5.1 says that for a closed proper concave-convex saddle-function
  `K`, the graph of its saddle subdifferential `dK` is closed and is homeomorphic to the ambient
  product space under the map `(u, v, u⋆, v⋆) ↦ (u - u⋆, v + v⋆)`.
- `core/canonical`: graph-valued multivalued mappings in the project are organized as `SetRel`,
  while the saddle subdifferential owner itself is already `Bifunction.subdifferentialAt` from
  Chapter 35.
- `bridge/view`: this file therefore adds a pairing-level graph owner
  `Bifunction.subdifferentialGraphPairing K : SetRel (U × V) (YU × YV)` and its notation surface
  `gphd[YU, YV](K)`, and states the corollary directly on that owner layer instead of
  introducing a second packaged saddle-mapping wrapper.

Domain-style sampling used here:
- `Bifunction.subdifferentialAt` and `Bifunction.mem_subdifferentialAt` from
  `Chap07.Text_35_6_3`;
- `Function.subdifferentialGraph` from `Chap05.Definition_5_24_3`, which fixes `SetRel` as the
  canonical graph owner layer for subdifferentials;
- `Function.isClosed_subdifferentialGraph` from `Chap05.Theorem_5_24_7`, the upstream closed-graph
  owner theorem in the pure convex setting;
- `SaddleFunction.IsConcaveConvex`, `SaddleFunction.IsClosed`, and
  `SaddleFunction.IsProper`, which are the chapter's primitive owner-level hypotheses at codomain
  layer `WithTopBot`.

Primitive data vs derived API:
- primitive owner reused from upstream: `Bifunction.subdifferentialAt K u v`;
- derived bridge API introduced here: the graph relation
  `Bifunction.subdifferentialGraphPairing K`, its pointwise membership lemma, and the explicit
  Minty map on the self-pairing specialization `gphd[U, V](K)`;
- derived source-facing conclusions: graph closedness and the homeomorphism theorem for the
  textbook Minty-style coordinate map.

Layer target: `bridge/view`.

Ambient-assumption minimization:
- the graph relation and its pointwise membership theorem live exactly at the ambient layer of the
  existing owner `Bifunction.subdifferentialAt`, so they stay on the intrinsic pairing-based
  layer;
- the self-pairing specialization `gphd[U, V](K)` and the explicit Minty map below stay at the
  same pairing-level scalar layer as `subdifferentialGraphPairing`;
- the closed-graph clause is first stated on the pairing-level owner
  `subdifferentialGraphPairing` and only then specialized to the self-pairing specialization
  `gphd[U, V](K)`, while the Minty-homeomorphism clause remains on the explicit self-pairing map
  where subtraction/addition is intrinsically typed.
-/

/-- The graph of the saddle subdifferential, expressed on the chapter's canonical `SetRel`
owner layer for multivalued mappings. -/
abbrev subdifferentialGraphPairing (K : U → V → WithTopBot 𝕜) : SetRel (U × V) (YU × YV) :=
  {p | p.2 ∈ d(K ; p.1.1, p.1.2)}

scoped[Rockafellar] notation "gphd[" YU ", " YV "](" K ")" =>
  Bifunction.subdifferentialGraphPairing (YU := YU) (YV := YV) K

/-- Pointwise membership in the graph of the saddle subdifferential is exactly membership of the
second pair in `d(K ; u, v)`. -/
@[simp] theorem mem_subdifferentialGraphPairing
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : YU} {vStar : YV} :
    (u, v) ~[gphd[YU, YV](K)] (uStar, vStar) ↔
      (uStar, vStar) ∈ d(K ; u, v) :=
  Iff.rfl

end

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]

/-- Pointwise membership in the self-pairing saddle-subdifferential graph. -/
@[simp] theorem mem_subdifferentialGraph
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : U} {vStar : V} :
    (u, v) ~[gphd[U, V](K)] (uStar, vStar) ↔
      (uStar, vStar) ∈ d(K ; u, v) :=
  Iff.rfl

variable [Add V]

/-- The textbook Minty map on the graph of the saddle subdifferential. -/
def subdifferentialGraphMintyMap
    (K : U → V → WithTopBot 𝕜) :
    (gphd[U, V](K) : SetRel (U × V) (U × V)) → U × V
  | ⟨((u, v), (uStar, vStar)), _⟩ => (u - uStar, v + vStar)

@[simp] theorem subdifferentialGraphMintyMap_apply
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : U} {vStar : V}
    (hp : (u, v) ~[gphd[U, V](K)] (uStar, vStar)) :
    subdifferentialGraphMintyMap K ⟨((u, v), (uStar, vStar)), hp⟩ = (u - uStar, v + vStar) :=
  rfl

end

section

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable {YU : Type*} {YV : Type*}
variable [TopologicalSpace YU] [TopologicalSpace YV]
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]

/-- Corollary 37.5.1, closed-graph clause on the pairing-level graph owner of the saddle
subdifferential. -/
theorem isClosed_subdifferentialGraphPairing
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K) :
    IsClosed (gphd[YU, YV](K)) := by
  let _ := hK_shape
  let _ := hK_closed
  sorry

end

section

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]

/-- Corollary 37.5.1, self-pairing specialization of
`isClosed_subdifferentialGraphPairing`. -/
theorem isClosed_subdifferentialGraph
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K) :
    IsClosed (gphd[U, V](K) : SetRel (U × V) (U × V)) := by
  simpa using
    (isClosed_subdifferentialGraphPairing (K := K) hK_shape hK_closed)

end

section

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]
variable {K : U → V → WithTopBot 𝕜}

/-- Corollary 37.5.1, homeomorphism clause: for a closed proper concave-convex saddle-function,
the explicit Minty map on the graph of the saddle subdifferential is a homeomorphism onto the
ambient product space. -/
theorem isHomeomorph_subdifferentialGraphMintyMap
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K) :
    IsHomeomorph (subdifferentialGraphMintyMap K) := by
  let _ := hK_shape
  let _ := hK_closed
  let _ := hK_proper
  sorry

end

end Bifunction
