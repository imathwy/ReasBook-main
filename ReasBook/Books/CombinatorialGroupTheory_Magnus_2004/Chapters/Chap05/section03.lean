import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_3_1 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: planar `(p, q)`-type degree conditions on finite planar maps.

Layer triage:
- `source-facing`: the textbook notions `[p, q]` and `(p, q)` for a planar map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsPlanarMap`,
  `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex`,
  `TwoComplex.TwoManifoldEmbedding.IsInteriorRegion`,
  `OneComplex.vertexDegree`, and `TwoComplex.regionDegree`.
- `bridge/view`: the square-bracket notion implies the round-bracket notion by restricting the
  region lower bound from all regions to interior regions.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner hypothesis for finite planar maps.
2. `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex` is the owner predicate for interior vertices.
3. `TwoComplex.TwoManifoldEmbedding.IsInteriorRegion` is the owner predicate for interior regions.
4. `OneComplex.vertexDegree` and `TwoComplex.regionDegree` are nat-valued owner
   degree maps, so the `[p, q]` and `(p, q)` bounds should be stated directly in `ℕ`.

Primitive vs. derived:
- primitive data for a `[p, q]` map: nonempty support, an interior-vertex degree lower bound, and
  an all-region degree lower bound;
- primitive data for a `(p, q)` map: nonempty support, an interior-vertex degree lower bound, and
  an interior-region degree lower bound;
- derived API: every `[p, q]` map is canonically a `(p, q)` map.
-/

/-- Definition 5-3-1 (1): the positive integral solutions of `1 / p + 1 / q = 1 / 2` are exactly
`(3, 6)`, `(4, 4)`, and `(6, 3)`. -/
-- Proof sketch: clear denominators to rewrite the equation as `(p - 2) * (q - 2) = 4`, then
-- inspect the positive factorisations of `4`.
theorem positive_integral_reciprocal_sum_eq_half_iff
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (1 : ℚ) / p + 1 / q = 1 / 2 ↔
      (p, q) = (3, 6) ∨ (p, q) = (4, 4) ∨ (p, q) = (6, 3) := sorry

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- Definition 5-3-1 (2): a `[p, q]` map is a nonempty planar map whose interior vertices have
degree at least `p` and whose regions all have degree at least `q`. -/
def IsSquareBracketPQMap (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p q : ℕ) : Prop :=
  embedding.support.Nonempty ∧
    embedding.HasInteriorVertexDegreeAtLeast p ∧
    ∀ D : GeometricFace C, q ≤ C.regionDegree D

/-- Definition 5-3-1 (3): a `(p, q)` map is a nonempty planar map whose interior vertices have
degree at least `p` and whose interior regions have degree at least `q`. -/
def IsRoundBracketPQMap (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p q : ℕ) : Prop :=
  embedding.support.Nonempty ∧
    embedding.HasInteriorVertexDegreeAtLeast p ∧
    ∀ D : GeometricFace C, embedding.IsInteriorRegion D → q ≤ C.regionDegree D

end

end TwoManifoldEmbedding
end TwoComplex

/-- Source-facing notation for the textbook notion that `embedding` is a `[p, q]` map. -/
syntax:max term:max " Is[" term:max ", " term:max "]" : term

/-- Source-facing notation for the textbook notion that `embedding` is a `(p, q)` map. -/
syntax:max term:max " Is(" term:max ", " term:max ")" : term

macro_rules
  | `($embedding Is[$p, $q]) =>
      `(TwoComplex.TwoManifoldEmbedding.IsSquareBracketPQMap $embedding $p $q)
  | `($embedding Is($p, $q)) =>
      `(TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap $embedding $p $q)

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

namespace IsSquareBracketPQMap

/-- A `[p, q]` map has nonempty support. -/
theorem nonempty_support {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap]
    {p q : ℕ} (h : embedding Is[p, q]) :
    embedding.support.Nonempty := by
  rcases h with ⟨hnonempty, -, -⟩
  exact hnonempty

/-- Every `[p, q]` map is a `(p, q)` map, since the square-bracket condition bounds the degree of
all regions in particular. -/
-- Proof sketch: reuse the nonemptiness and interior-vertex bounds, then restrict the region bound
-- from all regions to interior regions.
theorem toIsRoundBracketPQMap {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap]
    {p q : ℕ} (h : embedding Is[p, q]) :
    embedding Is(p, q) := by
  rcases h with ⟨hnonempty, hvertex, hregion⟩
  exact ⟨hnonempty, hvertex, fun D _ ↦ hregion D⟩

end IsSquareBracketPQMap

namespace IsRoundBracketPQMap

/-- A `(p, q)` map has nonempty support. -/
theorem nonempty_support {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap]
    {p q : ℕ} (h : embedding Is(p, q)) :
    embedding.support.Nonempty := by
  rcases h with ⟨hnonempty, -, -⟩
  exact hnonempty

end IsRoundBracketPQMap

/-- A `[p, q]` map has nonempty support. -/
instance {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] {p q : ℕ}
    (h : embedding Is[p, q]) : embedding.support.Nonempty :=
  h.nonempty_support

/-- A `(p, q)` map has nonempty support. -/
instance {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] {p q : ℕ}
    (h : embedding Is(p, q)) : embedding.support.Nonempty :=
  h.nonempty_support

/-- A `[p, q]` map is canonically a `(p, q)` map. -/
instance {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] {p q : ℕ}
    (h : embedding Is[p, q]) : embedding Is(p, q) :=
  h.toIsRoundBracketPQMap

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Theorem_5_3_2 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: Euler-characteristic and degree-counting formulas for finite planar maps.

Layer triage:
- `source-facing`: a finite planar map together with positive integers `p` and `q` satisfying
  `1 / p + 1 / q = 1 / 2`, and the degree sums over boundary vertices, interior vertices, and
  regions that appear in the basic formulas of Section `5.3`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` together with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for a planar map,
  `TwoComplex.TwoManifoldEmbedding.IsBoundaryVertex` / `IsInteriorVertex` and
  `IsBoundaryEdge` are the owner predicates for the boundary/interior decomposition, and
  `OneComplex.vertexDegree` / `TwoComplex.regionDegree` / `boundaryInteriorEdgeCount`
  are the owner degree-counting functions.
- `bridge/view`: the textbook counts `V`, `E`, `F`, `V^•`, `E^•`, and the degree-defect sums are
  realized here as cardinalities and finite sums built from those owner predicates and degree
  functions.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding C 𝔼²` from Definition `5-1-1` is the established owner for the
   planar realization of a map.
2. `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner hypothesis supplying finiteness of the
   vertex, edge, and face types.
3. `TwoComplex.TwoManifoldEmbedding.IsBoundaryVertex`, `IsInteriorVertex`, and `IsBoundaryEdge` from
   Definition `5-2-7` are the owner predicates for the boundary/interior language used in the
   formulas.
4. `OneComplex.vertexDegree`, `TwoComplex.regionDegree`, and
   `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` from Definition `5-2-8`
   are the owner degree-counting maps whose total sums enter the theorem and its later
   boundary-region corollaries.
5. `positive_integral_reciprocal_sum_eq_half_iff` from Definition `5-3-1` is the chapter owner
   for the positive-integral reciprocal relation, so the source-facing theorem should keep
   explicit positivity on both parameters rather than relying on totalized division in `ℚ`.

Primitive vs. derived:
- primitive public data: a finite planar map `embedding` together with positive integers `p` and
  `q` satisfying `1 / p + 1 / q = 1 / 2`;
- derived API: the rationalized counts `V`, `E`, `F`, `V^•`, `E^•`, the Euler term `V - E + F`,
  the four defect sums used to state the two formulas in `ℚ`, and the selected-region
  curvature sum used later for boundary-region curvature estimates.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

open OneComplex

variable {C : TwoComplex}

/-- The number `V` of vertices of a finite planar map, viewed in `ℚ`. -/
abbrev vertexCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card C.skeleton

/-- The number `E` of geometric edges of a finite planar map, viewed in `ℚ`. -/
abbrev edgeCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card (OneComplex.GeometricEdge C.skeleton)

/-- The number `F` of geometric regions of a finite planar map, viewed in `ℚ`. -/
abbrev regionCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card (GeometricFace C)

/-- The number `V^•` of boundary vertices of a finite planar map, viewed in `ℚ`. -/
abbrev boundaryVertexCount (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] : ℚ :=
  Nat.card { v : C.skeleton // embedding.IsBoundaryVertex v }

/-- The number `E^•` of boundary edges of a finite planar map, viewed in `ℚ`. -/
abbrev boundaryEdgeCount (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] : ℚ :=
  Nat.card { e : OneComplex.GeometricEdge C.skeleton // embedding.IsBoundaryEdge e }

/-- The boundary-vertex defect sum `∑^• [p - d(v)]`. -/
abbrev boundaryVertexDefectSum (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p : ℚ) : ℚ :=
  let _ : Finite C.skeleton := (inferInstance : embedding.IsPlanarMap).finite_vertex
  let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
  let _ : Fintype { v : C.skeleton // embedding.IsBoundaryVertex v } := Fintype.ofFinite _
  ∑ v : { v : C.skeleton // embedding.IsBoundaryVertex v }, (p - (C.skeleton.vertexDegree v : ℚ))

/-- The interior-vertex defect sum `∑^∘ [p - d(v)]`. -/
abbrev interiorVertexDefectSum (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p : ℚ) : ℚ :=
  let _ : Finite C.skeleton := (inferInstance : embedding.IsPlanarMap).finite_vertex
  let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
  let _ : Fintype { v : C.skeleton // embedding.IsInteriorVertex v } := Fintype.ofFinite _
  ∑ v : { v : C.skeleton // embedding.IsInteriorVertex v }, (p - (C.skeleton.vertexDegree v : ℚ))

/-- The region-degree defect sum `∑ [q - d(D)]`. -/
abbrev regionDegreeDefectSum (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (q : ℚ) : ℚ :=
  let _ : Finite (GeometricFace C) := (inferInstance : embedding.IsPlanarMap).finite_face
  let _ : Fintype (GeometricFace C) := Fintype.ofFinite (GeometricFace C)
  ∑ D : GeometricFace C, (q - (C.regionDegree D : ℚ))

/-- The adjusted boundary-vertex defect sum `∑^• [p / q + 2 - d(v)]` from formula `(3.2)`. -/
abbrev boundaryVertexAdjustedDefectSum (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] (p q : ℚ) : ℚ :=
  let _ : Finite C.skeleton := (inferInstance : embedding.IsPlanarMap).finite_vertex
  let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
  let _ : Fintype { v : C.skeleton // embedding.IsBoundaryVertex v } := Fintype.ofFinite _
  ∑ v : { v : C.skeleton // embedding.IsBoundaryVertex v },
    (p / q + 2 - (C.skeleton.vertexDegree v : ℚ))

/-- The curvature sum `∑ [p / q + 2 - i(D)]` attached to a selected family of regions in a planar
map. -/
abbrev adjustedInteriorEdgeDefectSum
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (P : GeometricFace C → Prop) (p q : ℚ) : ℚ :=
  let _ : Finite (GeometricFace C) := (inferInstance : embedding.IsPlanarMap).finite_face
  let _ : Fintype { D : GeometricFace C // P D } := Fintype.ofFinite _
  let _ : DecidableEq { D : GeometricFace C // P D } := Classical.decEq _
  ∑ D : { D : GeometricFace C // P D },
    (p / q + 2 - (embedding.boundaryInteriorEdgeCount D : ℚ))

-- Proof sketch: expand the canonical Euler term `V - E + F`, use the standard degree-counting
-- identities `2E = ∑ d(v)` and `2E = ∑ d(D) + E^•`, rewrite `V` and `F` as sums of constant
-- terms over vertices and regions, and use `1 / p + 1 / q = 1 / 2` for positive integers `p`
-- and `q` to cancel the remaining edge contribution. Then split the vertex sum into boundary and
-- interior parts, and finally separate the constant `p / q` over the boundary vertices to obtain
-- formula `(3.2)`.
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

/-- Theorem 5-3-2: for a finite planar map, the two basic curvature formulas are the identities
obtained by expanding the canonical Euler term `V - E + F` for positive integers `p` and `q`
satisfying `1 / p + 1 / q = 1 / 2`. -/
theorem basic_formulas_of_planar_map
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hReciprocal : (1 : ℚ) / p + 1 / q = (1 : ℚ) / 2) :
    (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
        embedding.boundaryVertexDefectSum p + embedding.interiorVertexDefectSum p +
          ((p : ℚ) / q) * embedding.regionDegreeDefectSum q -
            ((p : ℚ) / q) * embedding.boundaryEdgeCount ∧
      (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
        embedding.boundaryVertexAdjustedDefectSum p q + embedding.interiorVertexDefectSum p +
          ((p : ℚ) / q) * embedding.regionDegreeDefectSum q +
            ((p : ℚ) / q) * (embedding.boundaryVertexCount - embedding.boundaryEdgeCount) := by
  sorry

/-- Formula `(3.1)` from `basic_formulas_of_planar_map`. -/
theorem basic_formula_3_1_of_planar_map
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hReciprocal : (1 : ℚ) / p + 1 / q = (1 : ℚ) / 2) :
    (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
      embedding.boundaryVertexDefectSum p + embedding.interiorVertexDefectSum p +
        ((p : ℚ) / q) * embedding.regionDegreeDefectSum q -
          ((p : ℚ) / q) * embedding.boundaryEdgeCount :=
  (basic_formulas_of_planar_map embedding p q hp hq hReciprocal).1

/-- Formula `(3.2)` from `basic_formulas_of_planar_map`. -/
theorem basic_formula_3_2_of_planar_map
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hReciprocal : (1 : ℚ) / p + 1 / q = (1 : ℚ) / 2) :
    (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
      embedding.boundaryVertexAdjustedDefectSum p q + embedding.interiorVertexDefectSum p +
        ((p : ℚ) / q) * embedding.regionDegreeDefectSum q +
          ((p : ℚ) / q) * (embedding.boundaryVertexCount - embedding.boundaryEdgeCount) :=
  (basic_formulas_of_planar_map embedding p q hp hq hReciprocal).2

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Lemma_5_3_3 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: basic combinatorial inequalities for interior cells of a planar map.

Layer triage:
- `source-facing`: the inequality comparing the numbers of interior vertices and interior edges
  under the hypothesis that each interior vertex has degree at least `2`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex` and
  `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` from Definition `5-2-7` are the owner predicates
  for interior cells, while `OneComplex.vertexDegree` from Definition `5-2-8`
  is the owner for vertex degree.
- `bridge/view`: the interior-cell counts are realized as finite-cardinality counts of the
  subtypes of interior vertices and interior geometric edges of the chosen planar embedding.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex` is the chapter owner for interior vertices.
2. `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` is the chapter owner for interior
   geometric edges.
3. `OneComplex.vertexDegree` is the canonical degree attached to a vertex of a
   finite planar map.
4. `Nat.card` is the canonical finite-cardinality owner for counting subtype-defined finite sets.

Primitive vs. derived:
- primitive public data: a planar embedding `embedding : TwoComplex.TwoManifoldEmbedding C 𝔼²`;
- derived API: the interior-vertex and interior-edge counts are best expressed directly as
  `Nat.card` of the corresponding interior subtypes, while the hypothesis is the direct owner-side
  lower bound `2 ≤ C.skeleton.vertexDegree v` on each interior vertex.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

open OneComplex

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: sum the degrees of the interior vertices. The hypothesis gives a lower bound `2`
-- on each summand, while each interior geometric edge contributes at most two incident interior
-- endpoints, yielding twice the interior-vertex count `≤` twice the interior-edge count and hence
-- the desired inequality.
/-- Lemma 5-3-3: if every interior vertex of a planar map has degree at least `2`, then the
number of interior vertices is at most the number of interior edges. -/
theorem interiorVertexCount_le_interiorEdgeCount_of_interiorVertexDegree_ge_two
    (hdegree : embedding.HasInteriorVertexDegreeAtLeast 2) :
    Nat.card { v : C.skeleton // embedding.IsInteriorVertex v } ≤
      Nat.card { e : GeometricEdge C.skeleton // embedding.IsInteriorEdge e } := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Corollary_5_3_4 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for connected simply connected planar `[p, q]` maps.

Layer triage:
- `source-facing`: Corollary `5-3-4`, which lower-bounds the boundary curvature sum of a
  connected simply connected `[p, q]` map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for the planar map itself,
  `TwoComplex.TwoManifoldEmbedding.IsSquareBracketPQMap` is the owner for the `[p, q]` condition,
  `Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)` and
  `TwoComplex.IsSimplyConnected` are the canonical owners for the connected and simply connected
  parts of the textbook hypothesis, and
  `TwoComplex.TwoManifoldEmbedding.basic_formula_3_2_of_planar_map` is the owner formula whose
  boundary term is `boundaryVertexAdjustedDefectSum`.
- `bridge/view`: this corollary specializes the owner formula to the connected simply connected
  case, where the Euler term is `1`, and then uses the `[p, q]` lower bounds to control the
  remaining defect sums.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` from Definition `5-1-1` is the ambient owner
   hypothesis for finite planar maps.
2. `positive_integral_reciprocal_sum_eq_half_iff` from Definition `5-3-1` is the chapter-level
   owner for the positive-integral solutions of `1 / p + 1 / q = 1 / 2`, so this corollary
   should keep the positivity hypotheses explicit rather than treating the rational equation over
   `ℕ` as sufficient by itself.
3. `TwoComplex.TwoManifoldEmbedding.IsSquareBracketPQMap` from Definition `5-3-1` is the owner
   abstraction for the textbook `[p, q]` condition.
4. `TwoComplex.TwoManifoldEmbedding.boundaryVertexAdjustedDefectSum` and
  `TwoComplex.TwoManifoldEmbedding.basic_formula_3_2_of_planar_map` from Theorem `5-3-2` are the
  canonical owner API for the curvature formula used here.
5. `Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)` is the canonical owner for the
   connectedness part of the textbook “simply connected planar map” hypothesis.
6. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner abstraction for the
   trivial-`π₁` input that turns the Euler term into `1` once connectedness is also assumed.

Primitive vs. derived:
- primitive public data: a planar embedding `embedding`, the connected and simply connected
  hypotheses, the source-facing `[p, q]` hypothesis, the positivity of `p` and `q`, the
  reciprocal relation on `p` and `q`, and the hypothesis that the map has more than one vertex;
- derived API: the curvature sum `boundaryVertexAdjustedDefectSum p q` and its lower bound.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: apply the basic formula `(3.2)` to the connected simply connected `[p, q]` map,
-- so the Euler term is `1`; then use the `[p, q]` lower bounds to show the interior-vertex and
-- region-defect contributions are nonpositive, and use the “more than one vertex” hypothesis
-- together with the deletion-of-isolated-vertices argument of the text to control the remaining
-- boundary term.
/-- Corollary 5-3-4: the curvature sum `∑_M^• [p / q + 2 - d(v)]` of a connected simply connected
`[p, q]` map with more than one vertex is at least `p`. -/
theorem curvature_formula_lower_bound_of_simplyConnected_squareBracketPQMap
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [IsSimplyConnected C] (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hPQ : embedding Is[p, q])
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hmoreThanOneVertex : (1 : ℚ) < embedding.vertexCount) :
    (p : ℚ) ≤ embedding.boundaryVertexAdjustedDefectSum p q := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Corollary_5_3_5 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for connected simply connected planar `(q, p)` maps.

Layer triage:
- `source-facing`: Corollary `5-3-5`, which lower-bounds the boundary-region curvature sum of a
  connected simply connected `(q, p)` map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for the planar map itself,
  `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner for the `(q, p)` condition,
  `TwoComplex.TwoManifoldEmbedding.adjustedInteriorEdgeDefectSum` is the owner construction for the
  curvature sum attached to any selected family of regions, while
  `Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)` and
  `TwoComplex.IsSimplyConnected` are the canonical owners for the connected and simply connected
  parts of the textbook hypothesis, while
  `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` and
  `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` are the owner inputs for the
  boundary-region specialization, and the square-bracket lower-bound corollary from
  `Corollary_5_3_4.lean` is the upstream dual boundary-vertex result.
- `bridge/view`: the textbook sum over boundary regions is realized directly as a finite sum over
  `adjustedInteriorEdgeDefectSum` specialized to the owner predicate `IsBoundaryRegion`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` from
   `Definition_5_3_1.lean`
   is the chapter owner for `(q, p)` maps.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` from
   `Definition_5_2_7.lean`
   is the owner predicate selecting the boundary regions.
3. `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` from
   `Definition_5_2_8.lean`
   is the owner map for the source quantity `i(D)`.
4. `TwoComplex.TwoManifoldEmbedding.adjustedInteriorEdgeDefectSum` from
   `Theorem_5_3_2.lean`
   is the canonical owner for the selected-region curvature sum, so this file should keep only
   the boundary-region specialization rather than a second local owner.

Primitive vs. derived:
- primitive public data: a planar embedding `embedding`, the connected and simply connected
  hypotheses, the source-facing `(q, p)` hypothesis, the positivity of `p` and `q`, the
  reciprocal relation on `p` and `q`, and the hypothesis that the map has more than one region;
- derived API: the boundary-region curvature sum built from `IsBoundaryRegion` and
  `boundaryInteriorEdgeCount`, and its lower bound.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

/-- The curvature sum `∑_M^• [p / q + 2 - i(D)]` over the boundary regions of a planar map. -/
abbrev boundaryRegionAdjustedInteriorEdgeDefectSum (p q : ℚ) : ℚ :=
  embedding.adjustedInteriorEdgeDefectSum embedding.IsBoundaryRegion p q

/-- Source-facing notation for the textbook quantity `σ'(M)`. -/
syntax:max "σ'(" term:max ")[" term:max ", " term:max "]" : term

macro_rules
  | `(σ'($embedding)[$p, $q]) =>
      `(TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum
        $embedding $p $q)

-- Proof sketch: pass to the dual planar map, which is a connected simply connected `[p, q]` map
-- with more than one vertex. Boundary regions of `embedding` correspond to boundary vertices of
-- the dual, and the degree of the dual vertex corresponding to `D` is `i(D)`; then apply
-- Corollary `5-3-4` to the dual map.
/-- Corollary 5-3-5: the curvature sum `∑_M^• [p / q + 2 - i(D)]` over the boundary regions of a
connected simply connected `(q, p)` map with more than one region is at least `p`. -/
theorem curvature_formula_lower_bound_of_simplyConnected_roundBracketQPMap
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [IsSimplyConnected C] (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hQP : embedding Is(q, p))
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hmoreThanOneRegion : (1 : ℚ) < embedding.regionCount) :
    (p : ℚ) ≤ σ'(embedding)[p, q] := sorry

end

end TwoManifoldEmbedding
end TwoComplex
