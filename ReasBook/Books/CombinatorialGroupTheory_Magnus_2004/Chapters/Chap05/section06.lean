import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_6_1 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature estimates for planar `[p, q]` maps whose connected components are discs
or annuli.

Layer triage:
- `source-facing`: `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents`,
  expressing that the planar map itself admits a finite connected-component decomposition whose
  components are either simply connected or annular in the induced planar embedding.
- `core/canonical`: `TwoComplex.Subcomplex.IsComponentDecomposition` is the owner abstraction for
  the primitive component data, while `TwoComplex.IsSimplyConnected` and
  `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` are the owner predicates for the two
  allowed component shapes.
- `bridge/view`: `TwoComplex.fullSubcomplex` is the intrinsic ambient subcomplex on which the
  component decomposition lives, and `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` is the
  canonical restriction bridge to the induced embedding on each listed component.

Domain sampling:
1. `TwoComplex.Subcomplex.IsComponentDecomposition` from Proposition `3-9-1` is the owner
   abstraction for the finite component decomposition.
2. `TwoComplex.fullSubcomplex` from Definition `5-1-5` is the canonical ambient subcomplex
   carrying all cells of the map, so the whole-map component decomposition should live there
   rather than behind an extra `S`.
3. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1` is the
   canonical restriction bridge for the induced embedding on each listed component.
4. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for the
   simply connected components.
5. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the owner
   predicate for annular boundary components in a planar realization.

Primitive vs. derived:
- primitive public data: the planar embedding `embedding`, positive integers `p` and `q`
  satisfying `1 / p + 1 / q = 1 / 2`, the `[p, q]` hypothesis, and the existence of a finite
  component decomposition of the ambient map whose pieces satisfy one of the two owner
  component-shape hypotheses;
- derived API: the two inequalities `(6.1)` and `(6.2)` bounding boundary edges and boundary
  vertices by the boundary-vertex defect sum.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- A planar map has simply connected-or-annular components when the full carried subcomplex of
the map admits a finite connected-component decomposition whose induced component embeddings have
one of the two allowed shapes. -/
def HasSimplyConnectedOrAnnularComponents
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (components : ι → Subcomplex C)
    (_ : C.fullSubcomplex.IsComponentDecomposition components),
      ∀ i : ι,
        (components i).complex.IsSimplyConnected ∨
          ∃ σ τ : CyclicPath (components i).complex.skeleton,
            (embedding.restrictToSubcomplex (components i)).HasAnnularBoundaryCycles σ τ

-- Proof sketch: rewrite formula `(3.1)` componentwise using the reciprocal relation
-- `1 / p + 1 / q = 1 / 2`, choose the component decomposition supplied by
-- `embedding.HasSimplyConnectedOrAnnularComponents`, and apply the induced component embedding
-- `embedding.restrictToSubcomplex (components i)` on the annular branch. A simply
-- connected component contributes Euler
-- characteristic `1` while an annular component contributes `0`. The `[p, q]` inequalities make
-- the interior-vertex and region-defect terms nonpositive, giving `(6.1)`; then delete isolated
-- boundary vertices and compare the remaining boundary vertices with boundary edges to obtain
-- `(6.2)`.
/-- Lemma 5-6-1: if a `[p, q]` map admits a finite component decomposition in which every
component is either simply connected or annular in the induced restricted embedding, then the
boundary edge-count and boundary vertex-count satisfy formulas `(6.1)` and `(6.2)`. -/
theorem boundary_edge_and_vertex_counts_le_boundaryVertexDefectSum_of_squareBracketPQMap
    (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2) (hPQ : embedding Is[p, q])
    (hcomponents : embedding.HasSimplyConnectedOrAnnularComponents) :
    embedding.boundaryEdgeCount ≤ ((q : ℚ) / p) * embedding.boundaryVertexDefectSum p ∧
      embedding.boundaryVertexCount ≤ ((q : ℚ) / p) * embedding.boundaryVertexDefectSum p := sorry

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Definition_5_6_2 (from Items/Chap05) -/
set_option autoImplicit false

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: boundary layers in planar map theory.

Layer triage:
- `source-facing`: the boundary layer of a map is given by its boundary vertices, the geometric
  edges incident with boundary vertices, and its boundary regions.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` is the owner of the planar map, and
  the existing predicates
  `TwoManifoldEmbedding.IsBoundaryVertex` / `TwoManifoldEmbedding.IsBoundaryRegion` from Definition
  `5-2-7` are the canonical boundary-cell predicates.
- `bridge/view`: an unoriented geometric edge is represented by an oriented edge of the
  `1`-skeleton, so incidence with a boundary vertex is expressed by checking whether one of the
  two endpoints of any representative is a boundary vertex.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryVertex` from Definition `5-2-7` is the existing owner
   for boundary vertices of a planar map.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` from Definition `5-2-7` is the existing owner
   for boundary regions of a planar map.
3. `OneComplex.GeometricEdge C.skeleton` is the canonical owner for source-level unoriented
   edges, so “incident with a boundary vertex” should be a predicate on geometric edges rather
   than on oriented representatives.
4. `OneComplex.geometricEdgeSetoid` is the quotient relation identifying an oriented edge with
   its inverse, so it is the correct bridge for making endpoint incidence well defined on
   geometric edges.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

open OneComplex

local notation "GeometricEdge" => OneComplex.GeometricEdge C.skeleton

/-- An oriented edge belongs to the boundary layer when one of its endpoints is a boundary
vertex. -/
private def orientedEdgeIsBoundaryLayer
    (embedding : TwoManifoldEmbedding C 𝔼²) (e : C.skeleton.Edge) : Prop :=
  embedding.IsBoundaryVertex (C.skeleton.initial e) ∨
    embedding.IsBoundaryVertex (C.skeleton.terminal e)

/-- Endpoint incidence with a boundary vertex is unchanged when an oriented edge is replaced by
its inverse, so it descends to the corresponding geometric edge. -/
-- Proof sketch: split the geometric-edge relation into equality or inversion. Equality is
-- immediate, while inversion swaps initial and terminal vertices, leaving the disjunction
-- unchanged.
private theorem orientedEdgeIsBoundaryLayer_eq_of_geometricEdgeSetoid
    (embedding : TwoManifoldEmbedding C 𝔼²) (e f : C.skeleton.Edge)
    (h : (geometricEdgeSetoid C.skeleton).r e f) :
    embedding.orientedEdgeIsBoundaryLayer e = embedding.orientedEdgeIsBoundaryLayer f := by
  rcases h with rfl | rfl
  · rfl
  · apply propext
    have hinit : C.skeleton.initial f⁻¹ = C.skeleton.terminal f := C.skeleton.initial_edgeInv f
    have hterm : C.skeleton.terminal f⁻¹ = C.skeleton.initial f := C.skeleton.terminal_edgeInv f
    constructor
    · intro h'
      simpa [orientedEdgeIsBoundaryLayer, hinit, hterm, or_comm] using h'
    · intro h'
      simpa [orientedEdgeIsBoundaryLayer, hinit, hterm, or_comm] using h'

/-- A geometric edge is incident with the boundary of the planar map when one of its endpoints is
a boundary vertex. -/
def IsBoundaryLayerEdge (embedding : TwoManifoldEmbedding C 𝔼²) :
    GeometricEdge → Prop :=
  Quotient.lift
    (embedding.orientedEdgeIsBoundaryLayer)
    (embedding.orientedEdgeIsBoundaryLayer_eq_of_geometricEdgeSetoid)

/-- A geometric edge represented by `e` is incident with a boundary vertex exactly when one of the
endpoints of `e` is a boundary vertex. -/
-- Proof sketch: evaluate the quotient lift on the representative `e`.
@[simp] theorem isBoundaryLayerEdge_mk_iff
    (embedding : TwoManifoldEmbedding C 𝔼²) (e : C.skeleton.Edge) :
    embedding.IsBoundaryLayerEdge ⟦e⟧ ↔
      embedding.IsBoundaryVertex (C.skeleton.initial e) ∨
        embedding.IsBoundaryVertex (C.skeleton.terminal e) :=
  Iff.rfl

/- Definition 5-6-2 reuses the existing owner predicates `IsBoundaryVertex` and
`IsBoundaryRegion` for the vertex and region parts of the boundary layer; only the edge clause
requires the new owner `IsBoundaryLayerEdge` above. -/

end

end TwoManifoldEmbedding
end TwoComplex

/-! ### Theorem_5_6_3 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open FreeGroupBasis

section

variable {X : Type u}

local instance instDecidableEqX_5_6_3 : DecidableEq X := Classical.decEq X

private abbrev basis : FreeGroupBasis X (FreeGroup X) := FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: algorithmic solvability of the word problem for small-cancellation quotients of
finitely generated free groups.

Layer triage:
- `source-facing`: a finitely generated free group `F`, a finite relator set `R`, its normal
  closure `N`, one of the small-cancellation hypotheses `C(6)`, `C(4)` together with `T(4)`, or
  `C(3)` together with `T(6)`, and the conclusion that the quotient `F / N` has solvable word
  problem.
- `core/canonical`: `FreeGroup X` with `[Finite X]` is the project's canonical model of a
  finitely generated free group, `HasSolvableWordProblem R` is the established presentation-level
  owner predicate for solvability of the word problem, and `PresentedGroup R` is the canonical
  quotient by the normal closure of `R`.
- `bridge/view`: `basis = FreeGroupBasis.ofFreeGroup X` is the canonical chosen basis used by the
  Chapter `5` small-cancellation owners `C(p)[basis, R]` and `T(q)[basis, R]`.

Domain sampling:
1. `GroupPresentation.HasSolvableWordProblem R` from Definition `2-1-4` is the owner predicate
   for the conclusion.
2. `FreeGroupBasis.condition_c` from Definition `5-2-2`, with notation `C(p)[basis, R]`, is the
   owner predicate for the `C(p)` hypotheses.
3. `FreeGroupBasis.condition_t` from Definition `5-2-3`, with notation `T(q)[basis, R]`, is the
   owner predicate for the `T(q)` hypotheses.
4. `FreeGroupBasis.ofFreeGroup X` is the canonical basis on the free group `FreeGroup X`, so the
   theorem should use that basis directly rather than introduce a parallel free-group wrapper.

Primitive vs. derived:
- primitive public data: the relator set `R`, finiteness of the generator type and of `R`, and
  the small-cancellation alternative;
- derived API: the presentation-level solvable-word-problem conclusion for the quotient by the
  normal closure of `R`.
- API refinement note: the three source alternatives already live directly in the owner predicates
  `C(p)[basis, R]` and `T(q)[basis, R]`, so this file should state their disjunction directly
  instead of introducing a parallel wrapper proposition.
-/

namespace GroupPresentation

-- Proof sketch: use the small-cancellation hypotheses to derive the Dehn-type reduction or
-- maximum-principle criterion for null-homotopic loops in the Cayley complex of the presentation.
-- Because `X` and `R` are finite, that criterion yields an effective procedure deciding whether a
-- signed word lies in the normal closure of `R`, which is exactly `HasSolvableWordProblem R`.
/-- Theorem 5-6-3: if `R` is a finite relator set in the finitely generated free group
`FreeGroup X` and `R` satisfies `C(6)`, or `C(4)` together with `T(4)`, or `C(3)` together with
`T(6)`, then the quotient by the normal closure of `R` has solvable word problem. This is stated
through the canonical presentation owner `HasSolvableWordProblem R`, and its hypotheses are stated
directly in the chapter owner predicates `C(p)[basis, R]` and `T(q)[basis, R]`. The source
assumption that `R` is symmetrized is absorbed by these owners: `C(p)` is stated on the
symmetrized relator family, while `T(q)` is stated on the corresponding symmetrized relator set
transported back to actual relators through the canonical basis `basis`. -/
theorem hasSolvableWordProblem_of_finite_smallCancellation
    (R : Set (FreeGroup X)) [Finite X] [Primcodable X] (hR : R.Finite)
    (hcase :
      C(6)[basis, R] ∨
        (C(4)[basis, R] ∧ T(4)[basis, R]) ∨
          (C(3)[basis, R] ∧ T(6)[basis, R])) :
    HasSolvableWordProblem R := sorry

end GroupPresentation

end
