import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_5_1 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊¹" => Metric.sphere (0 : 𝔼²) 1

section

variable {X : Type u}

/-!
Primary domain: annular van Kampen diagrams in the plane.

Layer triage:
- `source-facing`: an annular `R`-diagram with chosen outer and inner boundary cycles whose
  labels represent conjugate elements in the presented group.
- `core/canonical`: `GroupDiagram (FreeGroup X)` is the owner of the labelled diagram,
  `GroupDiagram.IsRDiagram` is the owner of the relator condition,
  `TwoComplex.TwoManifoldEmbedding` with `IsPlanarMap` is the owner of the planar realization, and
  `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` is the owner of an individual ambient boundary
  cycle, while `TwoComplex.Subcomplex.HasSimpleBoundary`, used in Lemma `5-4-3` on
  `C.fullSubcomplex`, is the established whole-boundary simple-cycle owner.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.boundaryCycleSupport` is the owner-side planar
  support of a chosen boundary cycle, and
  `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` is the owner-side annular boundary
  decomposition asserting that the actual ambient boundary subset is the union of two disjoint
  simple closed curves carried by the chosen outer and inner boundary cycles.
  `GroupDiagram.AnnularRDiagram` then packages exactly the source-facing annular `R`-diagram
  data built from that geometry and the `R`-diagram hypothesis. `Loop` and `cyclicPath` provide
  the based representatives needed to read boundary labels.

Domain sampling:
1. `GroupDiagram.IsRDiagram` from Definition `5-1-8` is the chapter owner for the `R`-diagram
   hypothesis.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the owner predicate
   for a chosen boundary cycle.
3. `TwoComplex.Subcomplex.HasSimpleBoundary` from Proposition `3-7-5` is the established owner
   shape for saying that a subcomplex boundary is a simple cycle, with Lemma `5-4-3` using it for
   the whole map via `C.fullSubcomplex`.
4. `GroupDiagram.pathLabel` from Definition `5-1-4` is the owner map for reading the label of a
   based boundary loop.

Primitive vs. derived:
- primitive public data: the owner-side planar support `embedding.boundaryCycleSupport c` of a
  chosen boundary cycle, the generic annular boundary decomposition
  `embedding.HasAnnularBoundaryCycles σ τ` asserting that the actual map boundary is the union of
  two disjoint simple closed curves supported by `σ` and `τ`, and the source-facing owner
  `GroupDiagram.AnnularRDiagram R` consisting of a labelled diagram, a planar embedding, chosen
  outer and inner boundary cycles, and the `R`-diagram hypothesis;
- derived API: the conjugacy conclusion in `PresentedGroup R`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

variable {C : TwoComplex}

/-- The planar support of a chosen boundary cycle is the union of the closed geometric edge-images
of the geometric edges traversed by that cycle. -/
def boundaryCycleSupport (embedding : TwoManifoldEmbedding C 𝔼²)
    (c : CyclicPath C.skeleton) : Set 𝔼² :=
  Set.sUnion (embedding.geometricEdgeSet '' { e | c.SupportsGeometricEdge e })

/-- Chosen outer and inner boundary cycles for an annular planar map. They are required to be
simple boundary cycles whose planar supports are disjoint simple closed curves and whose union is
the actual boundary of the map. -/
structure HasAnnularBoundaryCycles
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (σ τ : CyclicPath C.skeleton) : Prop where
  /-- The underlying `1`-skeleton is connected. -/
  skeleton_connected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)
  /-- `σ` is the outer boundary cycle. -/
  outer_isBoundaryCycle : embedding.IsBoundaryCycle σ
  /-- `τ` is the inner boundary cycle. -/
  inner_isBoundaryCycle : embedding.IsBoundaryCycle τ
  /-- The planar support of the outer boundary cycle is a simple closed curve. -/
  outer_support_isSimpleClosedCurve :
    ∃ γ : 𝕊¹ → 𝔼²,
      Continuous γ ∧ Function.Injective γ ∧
        embedding.boundaryCycleSupport σ = Set.range γ
  /-- The planar support of the inner boundary cycle is a simple closed curve. -/
  inner_support_isSimpleClosedCurve :
    ∃ γ : 𝕊¹ → 𝔼²,
      Continuous γ ∧ Function.Injective γ ∧
        embedding.boundaryCycleSupport τ = Set.range γ
  /-- The actual ambient boundary of the planar map is exactly the union of the two boundary
  components carried by the chosen cycles. -/
  boundary_eq_outer_inner :
    embedding.boundary =
      embedding.boundaryCycleSupport σ ∪ embedding.boundaryCycleSupport τ
  /-- The two boundary components are disjoint as subsets of the plane. -/
  outer_inner_disjoint :
    Disjoint (embedding.boundaryCycleSupport σ) (embedding.boundaryCycleSupport τ)

end TwoManifoldEmbedding
end TwoComplex

namespace GroupDiagram

/-- An annular `R`-diagram is a group diagram in the plane with chosen outer and inner boundary
cycles whose planar supports are disjoint simple closed curves and whose union is the actual
ambient boundary of the planar map. -/
structure AnnularRDiagram (R : Set (FreeGroup X)) extends GroupDiagram (FreeGroup X) where
  /-- A planar realization of the underlying labelled map. -/
  embedding : TwoComplex.TwoManifoldEmbedding source 𝔼²
  /-- The chosen realization is planar. -/
  [isPlanarMap : embedding.IsPlanarMap]
  /-- The chosen outer boundary cycle. -/
  outerBoundary : CyclicPath source.skeleton
  /-- The chosen inner boundary cycle. -/
  innerBoundary : CyclicPath source.skeleton
  /-- The two chosen boundary cycles form the annular boundary of the planar map. -/
  annular : embedding.HasAnnularBoundaryCycles outerBoundary innerBoundary
  /-- The labelled map is an `R`-diagram. -/
  isRDiagram : toGroupDiagram.IsRDiagram R

namespace AnnularRDiagram

variable {R : Set (FreeGroup X)}

/-- An annular `R`-diagram is used via its underlying labelled diagram. -/
instance : CoeOut (AnnularRDiagram R) (GroupDiagram (FreeGroup X)) where
  coe := AnnularRDiagram.toGroupDiagram

-- Proof sketch: choose a path in the connected annular diagram from a vertex on the outer
-- boundary cycle to a vertex on the inner boundary cycle. Cutting the annulus open along that
-- path produces a singular disc whose boundary label is
-- `M.pathLabel outer.2 * b * (M.pathLabel inner.2) * b⁻¹`. The van Kampen relation for an
-- `R`-diagram makes this boundary word trivial in `PresentedGroup R`, so the image of the outer
-- boundary label is conjugate to the inverse of the inner boundary label there.
/-- In an annular `R`-diagram, the image of the label of a chosen outer boundary loop is conjugate
to the inverse of the label of a chosen inner boundary loop in the presented group
`PresentedGroup R`. -/
theorem outerBoundaryLabel_isConj_innerBoundaryLabelInv
    (M : AnnularRDiagram R) (outer inner : Loop M.source.skeleton)
    (houter : cyclicPath outer = M.outerBoundary)
    (hinner : cyclicPath inner = M.innerBoundary) :
    IsConj (PresentedGroup.mk R (M.pathLabel outer.2))
      (PresentedGroup.mk R ((M.pathLabel inner.2)⁻¹)) := sorry

end AnnularRDiagram

/-- Lemma 5-5-1: if `M` is an annular `R`-diagram, `u` is the label of an outer boundary cycle of
`M`, and `z⁻¹` is the label of an inner boundary cycle of `M`, then `u` and `z` represent
conjugate elements of the presented group `PresentedGroup R`. -/
theorem outerBoundaryLabel_isConj_of_innerBoundaryInverseLabel
    {R : Set (FreeGroup X)} (M : AnnularRDiagram R)
    (outer inner : Loop M.source.skeleton)
    (houter : cyclicPath outer = M.outerBoundary)
    (hinner : cyclicPath inner = M.innerBoundary)
    (u z : FreeGroup X)
    (hu : M.pathLabel outer.2 = u) (hz : M.pathLabel inner.2 = z⁻¹) :
    IsConj (PresentedGroup.mk R u) (PresentedGroup.mk R z) := by
  simpa [hu, hz] using
    M.outerBoundaryLabel_isConj_innerBoundaryLabelInv outer inner houter hinner

end GroupDiagram

end

/-! ### Lemma_5_5_2 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

section

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: annular small-cancellation diagrams for conjugacy in relator quotients.

Layer triage:
- `source-facing`: two cyclically reduced words `u` and `z` in the free group `F` whose images in
  `G = F / N` are conjugate, together with the existence of a reduced annular `R`-diagram whose
  chosen outer and inner boundary components carry the cyclic words of `u` and `z⁻¹`,
  respectively.
- `core/canonical`: `FreeGroup X` is the owner for the ambient free group,
  `PresentedGroup.mk R` is the canonical quotient map into `G = F / N`,
  `GroupDiagram.AnnularRDiagram` from Lemma `5-5-1` is the chapter owner for annular
  `R`-diagrams,
  `GroupDiagram.IsReduced` is the owner predicate for reduced diagrams, and
  `CyclicWord X` is the chapter owner for cyclically reduced boundary words modulo rotation,
  while `GroupDiagram.pathLabelWord` is the source-facing boundary-word API attached to a chosen
  loop.
- `bridge/view`: `Loop` and `cyclicPath` give based representatives of the chosen outer and inner
  boundary cycles. The based boundary labels remain list words, but the public boundary
  conclusion is recorded through the owner `CyclicWord X` rather than only through raw equalities
  in `Cycle (X × Bool)`.

Domain sampling:
1. `GroupDiagram.IsReduced` from Definition `5-2-5` is the existing owner predicate for reduced
   diagrams.
2. `GroupDiagram.AnnularRDiagram` from Lemma `5-5-1` is the chapter owner for annular
   `R`-diagrams.
3. `PresentedGroup.mk R` from the presentation API is the canonical quotient map used throughout
   the chapter for passing from `FreeGroup X` to the relator quotient.
4. `CyclicWord X` from Definition `1-4-17` is the chapter owner for cyclically reduced boundary
   words modulo rotation.
5. `GroupDiagram.pathLabelWord` from Definition `5-1-5` is the owner boundary-word API for a
   chosen loop; the resulting cyclic boundary data should be exposed via `CyclicWord X`.

Primitive vs. derived:
- primitive public data: the annular `R`-diagram owner together with nonemptiness of regions and
  reducedness of the underlying labelled map;
- derived API: chosen loop representatives of the outer and inner boundary cycles whose read words
  determine the prescribed cyclic boundary words of `u` and `z⁻¹`, stated directly through
  `pathLabelWord` and the owner `CyclicWord X`.
-/

namespace GroupDiagram

private theorem isCyclicallyReduced_invRev {L : List (X × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (FreeGroup.invRev L) := by
  rcases h with ⟨hred, hcyc⟩
  refine ⟨?_, ?_⟩
  ·
    let R : (X × Bool) → (X × Bool) → Prop := fun a b ↦ a.1 = b.1 → a.2 = b.2
    let f : X × Bool → X × Bool := fun x ↦ (x.1, !x.2)
    unfold FreeGroup.IsReduced at hred ⊢
    have hreverse : List.IsChain R L.reverse := by
      rw [List.isChain_reverse]
      change List.IsChain (fun a b : X × Bool ↦ b.1 = a.1 → b.2 = a.2) L
      simpa [R, eq_comm] using hred
    have hmap : List.IsChain R (List.map f L.reverse) := by
      rw [List.isChain_map]
      change List.IsChain
        (fun a b : X × Bool ↦ (f a).1 = (f b).1 → (f a).2 = (f b).2) L.reverse
      simpa [f, R]
    simpa [FreeGroup.invRev, f, Function.comp_def] using hmap
  ·
    rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hab
    have ha' : L.head? = some (a₁, !a₂) := by
      simpa [FreeGroup.invRev] using ha
    have hb' : L.getLast? = some (b₁, !b₂) := by
      simpa [FreeGroup.invRev] using hb
    have h' := hcyc (b₁, !b₂) hb' (a₁, !a₂) ha' hab.symm
    simpa [eq_comm] using h'

-- Proof sketch: choose a minimal relator-conjugate expression witnessing that the images of `u`
-- and `z` are conjugate in `PresentedGroup R`, build the corresponding annular van Kampen
-- diagram, and remove the distinguished `z`-region from the minimal disc diagram. Minimality
-- gives reducedness, while the surviving outer and inner boundary loops read cyclically reduced
-- boundary words whose cyclic words are exactly those of `u` and `z⁻¹`, respectively. If there
-- were no regions left, the annulus would already witness that `u` and `z` are conjugate in the
-- free group, contradicting `h_not_conj`.
/-- Lemma 5-5-2: if `u` and `z` are cyclically reduced words of the free group `F = FreeGroup X`,
`u` and `z` are not conjugate in `F` although their images in `G = F / N` are conjugate, then
there exists a reduced annular
`R`-diagram with at least one region together with chosen outer and inner boundary loops whose
boundary labels realize the cyclic words of `u` and `z⁻¹`, respectively. -/
theorem exists_reduced_annularRDiagram_of_conjugate_in_relator_quotient
    (R : Set (FreeGroup X)) {u z : FreeGroup X}
    (hu_cyclic : FreeGroup.IsCyclicallyReduced u.toWord)
    (hz_cyclic : FreeGroup.IsCyclicallyReduced z.toWord)
    (h_not_conj : ¬ IsConj u z)
    (hconj_quotient : IsConj (PresentedGroup.mk R u) (PresentedGroup.mk R z)) :
    ∃ (M : AnnularRDiagram R) (outer inner : Loop M.source.skeleton)
      (houter : cyclicPath outer = M.outerBoundary)
      (hinner : cyclicPath inner = M.innerBoundary),
      Nonempty M.source.Face ∧
        M.IsReduced ∧
          ∃ houter_cyclic : FreeGroup.IsCyclicallyReduced (M.pathLabelWord basis outer.2),
            ∃ hinner_cyclic : FreeGroup.IsCyclicallyReduced (M.pathLabelWord basis inner.2),
              (⟨(M.pathLabelWord basis outer.2 : Cycle (X × Bool)), houter_cyclic⟩ :
                  CyclicWord X) = ⟨u.toWord, hu_cyclic⟩ ∧
                (⟨(M.pathLabelWord basis inner.2 : Cycle (X × Bool)), hinner_cyclic⟩ :
                    CyclicWord X) =
                  ⟨(z⁻¹).toWord,
                    by
                      simpa [FreeGroup.toWord_inv] using
                        isCyclicallyReduced_invRev hz_cyclic⟩ := sorry

end GroupDiagram

end

/-! ### Theorem_5_5_3 (from Items/Chap05) -/
set_option autoImplicit false

noncomputable section

open Set Quiver.Path FreeGroupBasis GroupPresentation

universe u v

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqX_5_5_3 : DecidableEq X := Classical.decEq X

/-!
Primary domain: suitable annular small-cancellation `R`-diagrams.

Layer triage:
- `source-facing`: a reduced annular `R`-diagram with chosen outer and inner boundary cycles,
  the boundary-arc hypothesis excluding intersections whose labels are longer than half a relator,
  and the resulting structure theorem asserting clauses (i)–(iii).
- `core/canonical`: `GroupDiagram F` is the owner of the labelled diagram,
  `TwoComplex.TwoManifoldEmbedding M.source 𝔼²` with `IsPlanarMap` is the owner of the planar
  realization, `GroupDiagram.IsRDiagram` and `GroupDiagram.IsReduced` are the owners of the
  `R`-diagram and reducedness hypotheses, `IsBoundaryCycle` is the owner of the outer and inner
  boundary cycles, `boundaryInteriorEdgeCount` and `OneComplex.vertexDegree` are the owner degree
  maps, `BoundaryIntersectionIsConsecutivePart` and `faceBoundarySupport` are the chapter owners
  for the boundary-arc geometry of a boundary region, and `HasLongSymmetrizedRelatorPart` is the
  owner of the “longer than half a relator” condition.
- `bridge/view`: `HasAnnularBoundaryCycles` from Lemma `5-5-1` is the chapter owner for the
  annular boundary decomposition, `Quiver.Path.CyclicPath.HasPart` is the owner predicate for a
  consecutive boundary segment, and the source boundary arc `σ₁ = ∂D ∩ σ` is represented by a
  total-edge part occurring both on the chosen boundary cycle `σ` and on a boundary cycle of the
  region `D`, with the actual planar intersection recovered as the support of that segment inside
  the canonical boundary support `embedding.boundaryCycleSupport σ`.

Domain sampling:
1. `GroupDiagram.IsRDiagram` and `GroupDiagram.IsReduced` from Definitions `5-1-8` and `5-2-5`
   are the existing owner predicates for a reduced `R`-diagram.
2. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the chapter
   owner for the annular boundary decomposition.
3. `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` and
   `OneComplex.vertexDegree` from Definition `5-2-8` are the chapter owners for
   the source quantities `i(D)` and `d(v)`.
4. `TwoComplex.TwoManifoldEmbedding.BoundaryIntersectionIsConsecutivePart` from
   Definition `5-4-4` is the chapter owner for the consecutive-boundary-arc shape.
5. `TwoComplex.TwoManifoldEmbedding.faceBoundarySupport`,
   `TwoComplex.TwoManifoldEmbedding.boundaryCycleSupport`, and
   `GroupPresentation.HasLongSymmetrizedRelatorPart` from Definition `5-1-1`, Lemma `5-5-1`, and
   Proposition `3-11-2` are the canonical owner/view API for the source intersection
   `∂D ∩ σ` and for the phrase “`> 1 / 2 R`”.

Primitive vs. derived:
- primitive public data: a basis `basis`, relators `R`, a diagram `M`, a planar embedding
  `embedding`, the annular boundary owner `embedding.HasAnnularBoundaryCycles σ τ`, the
  small-cancellation case, reducedness, the `R`-diagram hypothesis, the boundary-arc exclusion
  hypothesis stated on the canonical face-boundary support of a region, and the prohibition on a
  region meeting both boundary cycles;
- derived API: the three theorem-level clauses asserting that no region boundary has all edges
  interior to the ambient map, every region has `i(D) = p / q + 2`, and every interior vertex
  has degree `q`.
-/

private def totalEdgeListLabel (M : GroupDiagram F)
    (segment : List (Quiver.Total M.source.skeleton)) : F :=
  (segment.map fun e ↦ M.label e.hom.1).prod

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {M : GroupDiagram F}

private def totalEdgeSequenceSupport (embedding : TwoManifoldEmbedding M.source 𝔼²)
    (segment : List (Quiver.Total M.source.skeleton)) : Set 𝔼² :=
  sUnion
    (embedding.geometricEdgeSet ''
      { e | e ∈ segment.map M.source.boundaryArrowGeometricEdge })

private def GeometricFaceHasConsecutiveTotalEdgeSequence
    (D : GeometricFace M.source) (segment : List (Quiver.Total M.source.skeleton)) : Prop :=
  ∃ F : M.source.Face,
    (⟦F⟧ : GeometricFace M.source) = D ∧
      ((M.source.boundary F).HasPart segment ∨
        (M.source.boundary F).HasPart (segment.reverse.map Quiver.Total.reverse))

/-- A region has a boundary intersection with the chosen boundary cycle `c` whose label is longer
than half a relator when the canonical face-boundary support of that region meets the chosen
boundary component exactly in the support of a nonempty consecutive shared boundary segment, and
the label of that segment, read along `c`, is longer than half a symmetrized relator from `R*`.
This packages the source phrase
“if `σ₁ = ∂D ∩ σ` is connected, then `φ(σ₁)` is not `> 1 / 2 R`”. -/
def BoundaryCycleIntersectionLongerThanHalfRelator
    (basis : FreeGroupBasis X F) (R : Set F) (embedding : TwoManifoldEmbedding M.source 𝔼²)
    [embedding.IsPlanarMap]
    (c : CyclicPath M.source.skeleton) (D : GeometricFace M.source) : Prop :=
  ∃ segment : List (Quiver.Total M.source.skeleton),
    segment ≠ [] ∧
      embedding.faceBoundarySupport D ∩ embedding.boundaryCycleSupport c =
        embedding.totalEdgeSequenceSupport segment ∧
      GeometricFaceHasConsecutiveTotalEdgeSequence D segment ∧
        c.HasPart segment ∧
          HasLongSymmetrizedRelatorPart (basis.repr '' R)
            (basis.repr (totalEdgeListLabel M segment)).toWord

/-- A region meets both chosen boundary cycles when its combinatorial boundary contains one
geometric edge lying on `σ` and another geometric edge lying on `τ`. This is the owner-side form
of source hypothesis (C). -/
def RegionMeetsBothBoundaryCycles
    (σ τ : CyclicPath M.source.skeleton) (D : GeometricFace M.source) : Prop :=
  (∃ e : OneComplex.GeometricEdge M.source.skeleton,
      e ∈ M.source.boundaryGeometricEdges D ∧ σ.SupportsGeometricEdge e) ∧
    ∃ e : OneComplex.GeometricEdge M.source.skeleton,
      e ∈ M.source.boundaryGeometricEdges D ∧ τ.SupportsGeometricEdge e

variable (basis : FreeGroupBasis X F) (R : Set F)
variable (embedding : TwoManifoldEmbedding M.source 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: apply the boundary-arc exclusion hypotheses to rule out regions whose boundary
-- misses the ambient boundary or meets one boundary component in more than one arc, then pass to
-- the simply connected discs obtained by cutting the annular map along boundary regions and apply
-- the curvature estimate from Theorem `5-4-5` in the two allowed small-cancellation cases. The
-- resulting nonpositive defect sums force every region to meet the boundary, give the uniform
-- value `i(D) = p / q + 2`, and force every interior vertex to have degree exactly `q`.
/-- Theorem 5-5-3: for a reduced annular `R`-diagram whose outer and inner boundary cycles satisfy
the source boundary-arc hypotheses and whose regions do not meet both boundary components, the two
small-cancellation cases `C'(1 / 6)` with `(q, p) = (3, 6)` and
`C'(1 / 4)` together with `T(4)` and `(q, p) = (4, 4)` force the annular structure conclusions
that no region boundary has all its edges interior to the ambient map, every region has
`i(D) = p / q + 2`, and every interior vertex has degree `q`. -/
theorem suitable_annular_r_diagram_has_uniform_region_and_vertex_structure
    (σ τ : CyclicPath M.source.skeleton) (p q : ℕ)
    (hcase :
      ((q, p) = (3, 6) ∧ C'((1 / 6 : ℝ))[basis, R]) ∨
        ((q, p) = (4, 4) ∧ C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
    (hRDiagram : M.IsRDiagram R) (hReduced : M.IsReduced)
    (hannular : embedding.HasAnnularBoundaryCycles σ τ)
    (houter :
      ∀ D : GeometricFace M.source,
        ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R σ D)
    (hinner :
      ∀ D : GeometricFace M.source,
        ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R τ D)
    (hseparate :
      ∀ D : GeometricFace M.source, ¬ RegionMeetsBothBoundaryCycles σ τ D) :
    (∀ D : GeometricFace M.source,
      ¬ M.source.boundaryGeometricEdges D ⊆
        { e : OneComplex.GeometricEdge M.source.skeleton | embedding.IsInteriorEdge e }) ∧
      (∀ D : GeometricFace M.source,
        (embedding.boundaryInteriorEdgeCount D : ℚ) = (p : ℚ) / q + 2) ∧
        (let S := M.source.skeleton
        let _ : Finite S.Edge := finite_orientedEdge embedding
        ∀ v : S,
          embedding.IsInteriorVertex v →
            S.vertexDegree v = q) :=
              sorry

end

end TwoManifoldEmbedding
end TwoComplex

end

/-! ### Theorem_5_5_4 (from Items/Chap05) -/
universe u

set_option autoImplicit false

noncomputable section

open FreeGroupBasis GroupPresentation

section

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X
local instance instDecidableProp_5_5_4 (p : Prop) : Decidable p := Classical.propDecidable p

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: the conjugacy problem for small-cancellation quotients of free groups.

Layer triage:
- `source-facing`: a relator set `R : Set (FreeGroup X)`, nontrivial cyclically `R`-reduced words
  `u` and `z` that are not conjugate in the free group, and the criterion that conjugacy in the
  quotient is witnessed by a short conjugator built from one or two relator subwords.
- `core/canonical`: `FreeGroup X` is the owner of the ambient free group,
  `PresentedGroup.mk R` is the canonical quotient map into `G = F / N`,
  `IsConj` is the owner predicate for conjugacy,
  `basis.is_cyclically_r_reduced R` is the chapter owner for cyclic `R`-reduction,
  `symmetrizedRelatorFamily R` is the owner of `R*`,
  `CyclicWord.HasPart` is the owner predicate for a cyclic subword of a relator,
  `C'((1 / 6 : ℝ))[basis, R]`, `C'((1 / 4 : ℝ))[basis, R]`, `C'((1 / 8 : ℝ))[basis, R]`, and
  `T(4)[basis, R]` are the chapter owners for the small-cancellation hypotheses, and
  `HasSolvableConjugacyProblem R` is the owner predicate for the algorithmic corollary.
- `bridge/view`: the source subwords `b₁` and `b₂` are represented by signed words
  `part₁`, `part₂ : List (X × Bool)` together with the equalities
  `FreeGroup.mk partᵢ = bᵢ`, while the relator-length bound is read on the supporting cyclic
  relators from `symmetrizedRelatorFamily R`.

Domain sampling:
1. `basis.is_cyclically_r_reduced R` from Definition `5-4-10` is the existing owner for the
   source hypothesis that `u` and `z` are cyclically `R`-reduced.
2. `symmetrizedRelatorFamily R` and `CyclicWord.HasPart` are the canonical owners for saying that
   a word is a subword of a relator from `R*`.
3. `PresentedGroup.mk R` and `IsConj` are the canonical owner interfaces for conjugacy in the
   quotient `G = F / N`.
4. `GroupPresentation.IsRecursive R` and `HasSolvableConjugacyProblem R` from Definitions
   `2-1-3` and `2-1-4` are the established owner predicates for the algorithmic corollary.

Primitive vs. derived:
- primitive public data: the relator set `R`, the elements `u`, `z`, the small-cancellation case,
  the nontriviality and cyclic `R`-reduction hypotheses, and the free-group nonconjugacy
  hypothesis;
- derived API: the quotient conjugacy criterion and the solvable-conjugacy corollary, whose
  short-conjugator clause is stated directly with `symmetrizedRelatorFamily R`,
  `CyclicWord.HasPart`, and `FreeGroup.mk`.
-/

namespace FreeGroup

-- Proof sketch: for the forward implication, start from a reduced annular `R`-diagram for the
-- quotient conjugacy class and apply the annular small-cancellation analysis to a region meeting
-- both boundary components. Reading the corresponding boundary arc yields a conjugator that is one
-- or two relator subwords, with relator lengths bounded by `2q max(|u|, |z|)` and with the
-- `C'(1 / 8)` improvement forcing the one-subword case. The reverse implication is immediate from
-- the displayed quotient equality `u = h⁻¹ z h`.
/-- Theorem 5-5-4 (1): if `R` satisfies either `C'(1 / 6)` or `C'(1 / 4)` together with `T(4)`,
and `u`, `z` are nontrivial cyclically `R`-reduced free-group elements that are not conjugate in
the free group itself, then their images in the quotient `G = F / N` are conjugate if and only if
there exists a conjugator `h` such that the outer small-cancellation hypothesis determines the
relator-length bound `2q max(|u|, |z|)` with `q = 3` in the `C'(1 / 6)` case and `q = 4`
otherwise, the quotient equality `u = h⁻¹ z h` holds, and `h` has the source short factorization
by one or two relator subwords. Because `u` and `z` are already cyclically `R`-reduced, the
criterion is stated directly for `u` and `z` rather than introducing extra witnesses `u*` and
`z*`. -/
theorem quotient_conjugacy_iff_exists_short_smallCancellation_conjugator
    (R : Set (FreeGroup X)) {u z : FreeGroup X}
    (hcase : C'((1 / 6 : ℝ))[basis, R] ∨ (C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
    (hu_ne : u ≠ 1) (hz_ne : z ≠ 1)
    (hu_cyclic : (basis).is_cyclically_r_reduced R u.toWord)
    (hz_cyclic : (basis).is_cyclically_r_reduced R z.toWord)
    (hnotconj : ¬ IsConj u z) :
    IsConj (PresentedGroup.mk R u) (PresentedGroup.mk R z) ↔
      ∃ h : FreeGroup X,
        let qBound := if C'((1 / 6 : ℝ))[basis, R] then 3 else 4;
        let bound := 2 * qBound * max u.toWord.length z.toWord.length;
        let hasShortRelatorPart : List (X × Bool) → Prop := fun part ↦
          ∃ q ∈ symmetrizedRelatorFamily R, q.HasPart part ∧ q.length < bound;
        PresentedGroup.mk R u = PresentedGroup.mk R (h⁻¹ * z * h) ∧
          (((∃ part₁ : List (X × Bool),
              h = FreeGroup.mk part₁ ∧ hasShortRelatorPart part₁) ∨
            ∃ part₁ part₂ : List (X × Bool),
              h = FreeGroup.mk part₁ * FreeGroup.mk part₂ ∧
                hasShortRelatorPart part₁ ∧ hasShortRelatorPart part₂) ∧
            (C'((1 / 8 : ℝ))[basis, R] →
              ∃ part₁ : List (X × Bool),
                h = FreeGroup.mk part₁ ∧ hasShortRelatorPart part₁)) := sorry

end FreeGroup

namespace GroupPresentation

-- Proof sketch: reduce conjugacy in the quotient to cyclically `R`-reduced representatives, apply
-- clause (1) to bound the search to one or two relator parts whose supporting relators have
-- length `< 2q max(|u|, |z|)`, and use the recursive relator predicate together with the finite
-- generator type to enumerate all such candidates effectively. Deciding whether one candidate
-- works yields a decision procedure for quotient conjugacy.
/-- Theorem 5-5-4 (2): if the free group on the finite generator type `X` has recursive relator
set `R` satisfying either `C'(1 / 6)` or `C'(1 / 4)` together with `T(4)`, then the presented
quotient `G = F / N` has solvable conjugacy problem. Here finite generation is recorded by
`[Finite X]`, and recursive presentation is recorded by
`GroupPresentation.IsRecursive R`. -/
theorem hasSolvableConjugacyProblem_of_recursive_smallCancellation
    (R : Set (FreeGroup X)) [Finite X] [Primcodable X]
    (hcase : C'((1 / 6 : ℝ))[basis, R] ∨ (C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
    (hrecursive : IsRecursive R) :
    HasSolvableConjugacyProblem R := sorry

end GroupPresentation

end

/-! ### Theorem_5_5_5 (from Items/Chap05) -/
universe u v

set_option autoImplicit false

noncomputable section

open Quiver.Path FreeGroupBasis

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

section

variable {X : Type u} {F : Type v} [Group F]

/-!
Primary domain: annular small-cancellation `R`-diagrams in the conjugacy theorem.

Layer triage:
- `source-facing`: a reduced annular `R`-diagram with chosen outer and inner boundary cycles, the
  boundary-arc exclusion hypotheses on both boundary components, and the existence of one region
  meeting both boundary components.
- `core/canonical`: `GroupDiagram F` is the owner of the labelled diagram,
  `TwoComplex.TwoManifoldEmbedding M.source 𝔼²` with `IsPlanarMap` is the owner of the planar
  realization, `GroupDiagram.IsRDiagram` and `GroupDiagram.IsReduced` are the diagram hypotheses,
  `IsBoundaryCycle` is the owner of the chosen outer and inner boundary cycles,
  `BoundaryCycleIntersectionLongerThanHalfRelator`, `RegionMeetsBothBoundaryCycles`, and
  `HasAnnularBoundaryCycles` from Lemma `5-5-1` are the owner APIs for the boundary-arc
  exclusion, crossing-region, and annular-boundary data, and `boundaryInteriorEdgeCount` is the
  owner of the source quantity `i(D)`.
- `bridge/view`: `GroupDiagram.AnnularRDiagram` from Lemma `5-5-1` is the concrete `FreeGroup X`
  specialization of this owner package, so at the present basis-general level `F` the theorem
  should stay on the intrinsic owner data `embedding.HasAnnularBoundaryCycles σ τ` rather than
  introduce a second annular wrapper.
  No additional owner is needed here; the theorem should expose its two
  source conclusions directly in the owner APIs `RegionMeetsBothBoundaryCycles` and
  `boundaryInteriorEdgeCount`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the chapter owner for
   the chosen boundary components `σ` and `τ`.
2. `GroupPresentation.HasLongSymmetrizedRelatorPart` from Proposition `3-11-2` is the canonical
   owner of the source phrase “`> 1 / 2 R`”.
3. `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` from Definition `5-2-8` is the
   chapter owner for the interior-edge count `i(D)`.
4. `BoundaryCycleIntersectionLongerThanHalfRelator` and
   `RegionMeetsBothBoundaryCycles` from Theorem `5-5-3`, together with
   `HasAnnularBoundaryCycles` from Lemma `5-5-1`, already package the annular-boundary geometry
   needed here, so this file should reuse them rather than restating the same segment-level data.

Primitive vs. derived:
- primitive public data: the basis `basis`, relator set `R`, diagram `M`, planar embedding
  `embedding`, chosen boundary cycles `σ` and `τ`, the small-cancellation case, reducedness and
  `R`-diagram hypotheses, the two boundary-arc exclusion hypotheses, and one crossing region;
- derived API: the two atomic theorem-level consequences asserting that every region meets both
  boundary cycles and that every region has interior-edge count at most two.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {M : GroupDiagram F}
variable (basis : FreeGroupBasis X F) (R : Set F) (embedding : TwoManifoldEmbedding M.source 𝔼²)
variable [embedding.IsPlanarMap] (σ τ : CyclicPath M.source.skeleton)
variable (hcase : C'((1 / 6 : ℝ))[basis, R] ∨ (C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
variable (hRDiagram : M.IsRDiagram R) (hReduced : M.IsReduced)
variable (hannular : embedding.HasAnnularBoundaryCycles σ τ)
variable
  (houter :
    ∀ D : GeometricFace M.source,
      ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R σ D)
  (hinner :
    ∀ D : GeometricFace M.source,
      ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R τ D)
  (hexists :
    ∃ E : GeometricFace M.source, RegionMeetsBothBoundaryCycles σ τ E)

-- Proof sketch: start with a region meeting both boundary components, cut the annular diagram
-- along a boundary-to-boundary segment of that region, and apply the curvature estimate from
-- Theorem `4-3` to the resulting disc. Greendlinger's lemma rules out the exceptional case, and
-- the remaining degree computation propagates outward through adjacent regions; if islands remain,
-- remove one and conclude by induction on the number of regions.
/-- Theorem 5-5-5: if `R` satisfies either `C'(1 / 6)` or `C'(1 / 4)` together with `T(4)`, and
`M` is a reduced annular `R`-diagram whose outer and inner boundary cycles satisfy the source
boundary-arc exclusion hypotheses, then the existence of one region meeting both boundary
components forces every region to meet both boundary cycles. -/
theorem all_regions_meet_both_boundary_cycles_of_exists_crossing_region
    (D : GeometricFace M.source) : RegionMeetsBothBoundaryCycles σ τ D := sorry

/-- Under the same hypotheses as Theorem `5-5-5`, every region of the annular diagram satisfies
`i(D) ≤ 2`. -/
theorem boundaryInteriorEdgeCount_le_two_of_exists_crossing_region
    (D : GeometricFace M.source) : embedding.boundaryInteriorEdgeCount D ≤ 2 := sorry

end

end TwoManifoldEmbedding
end TwoComplex

end
