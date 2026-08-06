import Mathlib.Data.PNat.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Lemma_13_2_8

noncomputable section

universe u

open Topology
open scoped TopCat Topology

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex.skeleton` is the canonical owner
-- for the chosen CW skeleta, `previousSkeletonQuotientPointed`/`topologicalBoundaryMap` are the
-- current Chapter 13 quotient-boundary owners, and `provisionalReducedGroupSuspensionMap` is the
-- suspension map whose chosen inverse is carried source-faithfully by an explicit equivalence
-- input on the target quotient.

/-- A based map `f : X ⟶ Y` induces the usual map on the positive-degree provisional reduced
group `H'_(n + 1)` for `n : ℕ+`, i.e. on `π_ (n + 1)`. -/
noncomputable def provisionalReducedGroupPositiveMap
    (n : ℕ+) {X Y : PointedCompactlyGenerated} (f : X ⟶ Y) :
    provisionalReducedGroup ((n : ℕ) + 1) X →
      provisionalReducedGroup ((n : ℕ) + 1) Y :=
  match n with
  | ⟨Nat.succ m, _⟩ =>
      fun a ↦
        let g := f.right.hom
        let hpoint : g.hom X.point = Y.point :=
          PointedCompactlyGenerated.Hom.map_point f
        let hcast :
            π_ (m + 2) Y.toCompactlyGenerated.toTop (g.hom X.point) =
              π_ (m + 2) Y.toCompactlyGenerated.toTop Y.point :=
          congrArg
            (fun y : Y.toCompactlyGenerated.toTop ↦
              π_ (m + 2) Y.toCompactlyGenerated.toTop y)
            hpoint
        cast hcast
          (homotopyGroupMap
            g.hom
            (m + 2) X.point a)

/-- The pointed map induced on the degree-`n` provisional reduced groups used on the target side
of Lemma 13.2.9. -/
noncomputable def provisionalReducedGroupPointedMap
    (n : ℕ+) {X Y : PointedCompactlyGenerated} (f : X ⟶ Y) :
    provisionalReducedGroup (n : ℕ) X →
      provisionalReducedGroup (n : ℕ) Y :=
  match n with
  | ⟨Nat.succ 0, _⟩ =>
      fun a ↦
        let g := f.right.hom
        let hpoint : g.hom X.point = Y.point :=
          PointedCompactlyGenerated.Hom.map_point f
        let groupMap :
            π_ 1 X.toCompactlyGenerated.toTop X.point →*
              π_ 1 Y.toCompactlyGenerated.toTop Y.point :=
          (HomotopyGroup.pi1MulEquivFundamentalGroup Y.point).symm.toMonoidHom.comp
            ((FundamentalGroup.mapOfEq g.hom hpoint).comp
              (HomotopyGroup.pi1MulEquivFundamentalGroup X.point).toMonoidHom)
        (Abelianization.map groupMap a : provisionalReducedGroup 1 Y)
  | ⟨Nat.succ (Nat.succ m), _⟩ =>
      fun a ↦
        let g := f.right.hom
        let hpoint : g.hom X.point = Y.point :=
          PointedCompactlyGenerated.Hom.map_point f
        let hcast :
            π_ (m + 2) Y.toCompactlyGenerated.toTop (g.hom X.point) =
              π_ (m + 2) Y.toCompactlyGenerated.toTop Y.point :=
          congrArg
            (fun y : Y.toCompactlyGenerated.toTop ↦
              π_ (m + 2) Y.toCompactlyGenerated.toTop y)
            hpoint
        (cast hcast (homotopyGroupMap g.hom (m + 2) X.point a) :
          provisionalReducedGroup (m + 2) Y)

/-- The source comparison isomorphism type
`C_(n + 1)(X) ≃ H'_(n + 1)(X^(n + 1) / X^n)` used in the Chapter 13 setup for
Lemma 13.2.9. -/
abbrev CellularSourceComparisonIso
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :=
  cellularChainGroup X ((n : ℕ) + 1) ≃
    provisionalReducedGroup ((n : ℕ) + 1) (cellularSourceQuotientPointed X n x_prev)

/-- The target comparison isomorphism type
`C_n(X) ≃ H'_n(X^n / X^(n - 1))` used in the Chapter 13 setup for Lemma 13.2.9. -/
abbrev CellularTargetComparisonIso
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :=
  cellularChainGroup X (n : ℕ) ≃
    provisionalReducedGroup (n : ℕ) (cellularTargetQuotientPointed X n x_prev)

/-- The chosen suspension comparison in the positive-degree case of Lemma 13.2.9: an
equivalence whose inverse is the displayed arrow
`H'_(n + 1)(Σ(X^n / X^(n - 1))) → H'_n(X^n / X^(n - 1))`. -/
abbrev CellularTargetSuspensionComparison
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :=
  provisionalReducedGroup (n : ℕ) (cellularTargetQuotientPointed X n x_prev) ≃
    provisionalReducedGroup ((n : ℕ) + 1) (cellularTargetQuotientSuspension X n x_prev)

/-- The chosen owner for `X^0 / X^(-1)` in the degree-`1` case of Lemma 13.2.9, modeled by the
wedge of `0`-spheres indexed by the `0`-cells of `X`. -/
abbrev cellularDegreeZeroQuotientPointed
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :
    PointedCompactlyGenerated.{u, u} :=
  wedgeOfNSpheres 0 (cellularCell X 0)

/-- The pointed quotient `X¹ / X⁰` used on the source side of the degree-`1` case of
Lemma 13.2.9. -/
abbrev cellularDegreeOneSourceQuotientPointed
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (x_zero : cellularSkeleton X 0) : PointedCompactlyGenerated.{u, u} :=
  cellularSkeletonQuotientPointed X 0 x_zero

/-- The degree-`0` comparison isomorphism type
`C₀(X) ≃ H'_0(X^0 / X^(-1))` used in the degree-`1` case of Lemma 13.2.9, with the chosen owner
`cellularDegreeZeroQuotientPointed X` for `X^0 / X^(-1)`. -/
abbrev CellularDegreeZeroComparisonIso
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :=
  cellularChainGroup X 0 ≃
    provisionalReducedGroup 0 (cellularDegreeZeroQuotientPointed X)

/-- The chosen suspension comparison in the degree-`1` case of Lemma 13.2.9: an equivalence
whose inverse is the displayed arrow `H'_1(Σ(X^0 / X^(-1))) → H'_0(X^0 / X^(-1))`. -/
abbrev CellularDegreeZeroSuspensionComparison
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :=
  provisionalReducedGroup 0 (cellularDegreeZeroQuotientPointed X) ≃
    provisionalReducedGroup 1 (Σ (cellularDegreeZeroQuotientPointed X))

/-- The explicit degree-`1` attaching-degree family determined by the chosen initial and terminal
`0`-cells of each `1`-cell. -/
def cellularDegreeOneAttachingDegree
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (initialVertex terminalVertex : cellularCell X 1 → cellularCell X 0) :
    cellularCell X 1 → cellularCell X 0 →₀ ℤ :=
  fun j ↦
    Finsupp.single (terminalVertex j) 1 -
      Finsupp.single (initialVertex j) 1

/-- The initial endpoint of a `1`-cell, evaluated at `-1` in the standard interval model. -/
def cellularOneCellInitialPoint
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (j : cellularCell X 1) : X :=
  (inferInstance : CWComplex (Set.univ : Set X)).map 1 j (fun _ ↦ (-1 : ℝ))

/-- The terminal endpoint of a `1`-cell, evaluated at `1` in the standard interval model. -/
def cellularOneCellTerminalPoint
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (j : cellularCell X 1) : X :=
  (inferInstance : CWComplex (Set.univ : Set X)).map 1 j (fun _ ↦ (1 : ℝ))

/-- The unique point of the closed `0`-cell indexed by `i`. -/
def cellularZeroCellPoint
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (i : cellularCell X 0) : X :=
  (inferInstance : CWComplex (Set.univ : Set X)).map 0 i ![]

/-- Chosen actual endpoint data for the degree-`1` cellular differential
`d₁ : C₁(X) → C₀(X)`.
Each `1`-cell contributes the difference between the `0`-cell containing its terminal endpoint and
the `0`-cell containing its initial endpoint. -/
structure CellularLowDegreeBoundary
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] where
  initialVertex : cellularCell X 1 → cellularCell X 0
  terminalVertex : cellularCell X 1 → cellularCell X 0
  initialVertex_spec :
    ∀ j : cellularCell X 1,
      cellularOneCellInitialPoint X j = cellularZeroCellPoint X (initialVertex j)
  terminalVertex_spec :
    ∀ j : cellularCell X 1,
      cellularOneCellTerminalPoint X j = cellularZeroCellPoint X (terminalVertex j)

namespace CellularLowDegreeBoundary

/-- The explicit coefficient family on `0`-cells determined by the actual endpoint data of the
`1`-cells. -/
def attachingDegree
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularLowDegreeBoundary X) :
    cellularCell X 1 → cellularCell X 0 →₀ ℤ :=
  cellularDegreeOneAttachingDegree X data.initialVertex data.terminalVertex

end CellularLowDegreeBoundary

/-- The source identification `C_(n + 1)(X) ≃ H'_(n + 1)(X^(n + 1) / X^n)` is source-faithful in
the sense that it is induced from the actual `(n + 1)`-cells of `X` through a chosen
wedge-of-`n`-spheres model for `X^(n + 1) / X^n`. -/
def IsCellularSourceComparisonInSourceDegree
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (sourceWedge :
      cellularSourceQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1)))
    (sourceWedgeCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1))))
    (sourceCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1) (cellularSourceQuotientPointed X n x_prev))
    (sourceComparison : CellularSourceComparisonIso X n x_prev) : Prop :=
  (∀ j : cellularCell X ((n : ℕ) + 1),
      sourceCellClass j =
        provisionalReducedGroupPositiveMap n sourceWedge.inv (sourceWedgeCellClass j)) ∧
    ∀ j : cellularCell X ((n : ℕ) + 1),
      sourceComparison (FreeAbelianGroup.of j) = sourceCellClass j

/-- The target identification `C_n(X) ≃ H'_n(X^n / X^(n - 1))` is source-faithful in the sense
that it is induced from the actual `n`-cells of `X` through a chosen wedge-of-`n`-spheres model
for `X^n / X^(n - 1)`, and the Construction 13.2.3 quotient projections agree with the chosen
sphere-factor projections on that model. -/
def IsCellularTargetComparisonInSourceDegree
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (targetWedge :
      cellularTargetQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ)))
    (targetWedgeCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))))
    (targetSphereFactorProjection :
      cellularCell X (n : ℕ) →
        C((wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetQuotientProjection :
      cellularCell X (n : ℕ) →
        C((cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ) (cellularTargetQuotientPointed X n x_prev))
    (targetComparison : CellularTargetComparisonIso X n x_prev) : Prop :=
  (∀ i : cellularCell X (n : ℕ),
      targetQuotientProjection i =
        (targetSphereFactorProjection i).comp
          (PointedCompactlyGenerated.Hom.hom targetWedge.hom).hom.hom) ∧
    (∀ i : cellularCell X (n : ℕ),
      targetCellClass i =
        provisionalReducedGroupPointedMap n targetWedge.inv (targetWedgeCellClass i)) ∧
    ∀ i : cellularCell X (n : ℕ),
      targetComparison (FreeAbelianGroup.of i) = targetCellClass i

/-- The source-facing comparison data above is induced by the actual Construction 13.2.4
boundary comparison, the actual Construction 13.2.3 attaching-degree family, and the chosen
positive-degree suspension equivalence on the target quotient, whose forward map is the actual
provisional suspension map and which in the intended application comes from Lemma 13.2.8 after
identifying the target quotient with a wedge of `n`-spheres. The compatibility between the
Construction 13.2.3 quotient projections and the chosen target sphere-factor projections is
recorded directly in this predicate rather than through an extra wrapper structure. -/
def IsCellularBoundaryCompositeInSourceDegree
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (boundaryComparison :
      cellularSourceQuotientPointed X n x_prev ⟶
        cellularTargetQuotientSuspension X n x_prev)
    (mapComposite :
      cellularCell X ((n : ℕ) + 1) →
        cellularCell X (n : ℕ) → SphereSelfMap n)
    (attachingDegree :
      cellularCell X ((n : ℕ) + 1) → cellularCell X (n : ℕ) →₀ ℤ)
    (sourceWedge :
      cellularSourceQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1)))
    (sourceWedgeCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1))))
    (sourceCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1) (cellularSourceQuotientPointed X n x_prev))
    (sourceComparison : CellularSourceComparisonIso X n x_prev)
    (suspensionComparison : CellularTargetSuspensionComparison X n x_prev)
    (targetWedge :
      cellularTargetQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ)))
    (targetWedgeCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))))
    (targetSphereFactorProjection :
      cellularCell X (n : ℕ) →
        C((wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetQuotientProjection :
      cellularCell X (n : ℕ) →
        C((cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ) (cellularTargetQuotientPointed X n x_prev))
    (targetComparison : CellularTargetComparisonIso X n x_prev)
    (hAttachingDegree :
      CellularActualAttachingDegreeSpec X n x_prev boundaryComparison
        mapComposite attachingDegree) : Prop :=
  IsCellularSourceComparisonInSourceDegree X n x_prev
      sourceWedge sourceWedgeCellClass sourceCellClass sourceComparison ∧
    suspensionComparison.toFun =
      provisionalReducedGroupSuspensionMap (n : ℕ)
        (cellularTargetQuotientPointed X n x_prev) ∧
    IsCellularTargetComparisonInSourceDegree X n x_prev
      targetWedge targetWedgeCellClass targetSphereFactorProjection
      targetQuotientProjection targetCellClass targetComparison ∧
    hAttachingDegree.quotientProjection = targetQuotientProjection

/-- The positive-degree, index-shifted comparison statement used below: for `d_(n + 1)`,
`cellularDifferentialFromDegrees X (n : ℕ) attachingDegree : C_(n + 1)(X) → C_n(X)` agrees with
the composite
`H'_(n + 1)(X^(n + 1) / X^n) → H'_(n + 1)(Σ(X^n / X^(n - 1))) → H'_n(X^n / X^(n - 1))`
for source-faithful chosen comparison data:

* identifications of `C_(n + 1)(X)` and `C_n(X)` with the provisional reduced groups of the two
  quotient skeleta,
* the source and target quotient models are identified with wedges of `n`-spheres indexed by the
  actual `(n + 1)`-cells and `n`-cells of `X`, and the transported source and target cell classes
  are tied to those chosen wedge decompositions,
* explicit composites `mapComposite j i : S^n ⟶ S^n` witness that `attachingDegree` is the actual
  degree family from Construction 13.2.3 for that same boundary comparison data, and
* the actual quotient projections used in Construction 13.2.3 are exactly the displayed target
  sphere-factor projections on the chosen target wedge model, and
* the second arrow is the inverse carried by a chosen suspension equivalence whose forward map is
  the actual suspension map on `X^n / X^(n - 1)` and which in the intended application comes from
  Lemma 13.2.8 after the displayed wedge-of-spheres identification. -/
theorem cellularDifferentialFromDegrees_agreesWithBoundaryComposite_shifted
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ+)
    (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (boundaryComparison :
      cellularSourceQuotientPointed X n x_prev ⟶
        cellularTargetQuotientSuspension X n x_prev)
    (mapComposite :
      cellularCell X ((n : ℕ) + 1) →
        cellularCell X (n : ℕ) → SphereSelfMap n)
    (attachingDegree :
      cellularCell X ((n : ℕ) + 1) → cellularCell X (n : ℕ) →₀ ℤ)
    (hAttachingDegree :
      CellularActualAttachingDegreeSpec X n x_prev boundaryComparison
        mapComposite attachingDegree)
    (sourceWedge :
      cellularSourceQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1)))
    (sourceWedgeCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1))))
    (sourceCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1) (cellularSourceQuotientPointed X n x_prev))
    (sourceComparison : CellularSourceComparisonIso X n x_prev)
    (suspensionComparison : CellularTargetSuspensionComparison X n x_prev)
    (targetWedge :
      cellularTargetQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ)))
    (targetWedgeCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))))
    (targetSphereFactorProjection :
      cellularCell X (n : ℕ) →
        C((wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetQuotientProjection :
      cellularCell X (n : ℕ) →
        C((cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ) (cellularTargetQuotientPointed X n x_prev))
    (targetComparison : CellularTargetComparisonIso X n x_prev)
    (hcomp :
      IsCellularBoundaryCompositeInSourceDegree X n x_prev
        boundaryComparison mapComposite attachingDegree
        sourceWedge sourceWedgeCellClass sourceCellClass sourceComparison
        suspensionComparison targetWedge targetWedgeCellClass
        targetSphereFactorProjection targetQuotientProjection targetCellClass
        targetComparison hAttachingDegree) :
    ∀ c : cellularChainGroup X ((n : ℕ) + 1),
      targetComparison
          (cellularDifferentialFromDegrees X (n : ℕ) attachingDegree c) =
        suspensionComparison.symm
          (provisionalReducedGroupPositiveMap n
            boundaryComparison (sourceComparison c)) := sorry

/-- In source degree `1`, the displayed Chapter 13 data are source-faithful when the degree-`1`
coefficient family is the actual endpoint-difference differential of a chosen
`CellularLowDegreeBoundary X`, the source comparison is induced from a chosen wedge-of-circles
model for `X¹ / X⁰`, the target comparison is tied to the actual `0`-cells on
`cellularDegreeZeroQuotientPointed X`, the suspension equivalence has forward map equal to the
actual suspension map, and the generator formula is the actual low-degree boundary-composite
formula for those same data. -/
def IsCellularBoundaryCompositeInSourceDegreeOne
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (x_zero : cellularSkeleton X 0)
    (lowDegreeBoundary : CellularLowDegreeBoundary X)
    (sourceWedge :
      cellularDegreeOneSourceQuotientPointed X x_zero ≅
        wedgeOfNSpheres 1 (cellularCell X 1))
    (sourceWedgeCellClass :
      cellularCell X 1 →
        provisionalReducedGroup 1 (wedgeOfNSpheres 1 (cellularCell X 1)))
    (sourceCellClass :
      cellularCell X 1 →
        provisionalReducedGroup 1 (cellularDegreeOneSourceQuotientPointed X x_zero))
    (sourceComparison :
      cellularChainGroup X 1 ≃
        provisionalReducedGroup 1 (cellularDegreeOneSourceQuotientPointed X x_zero))
    (targetCellClass :
      cellularCell X 0 →
        provisionalReducedGroup 0 (cellularDegreeZeroQuotientPointed X))
    (boundaryComparison :
      cellularDegreeOneSourceQuotientPointed X x_zero ⟶
        Σ (cellularDegreeZeroQuotientPointed X))
    (suspensionComparison : CellularDegreeZeroSuspensionComparison X)
    (targetComparison : CellularDegreeZeroComparisonIso X) : Prop :=
  (∀ j : cellularCell X 1,
    sourceCellClass j =
      provisionalReducedGroupPointedMap 1 sourceWedge.inv (sourceWedgeCellClass j)) ∧
    (∀ j : cellularCell X 1,
      sourceComparison (FreeAbelianGroup.of j) = sourceCellClass j) ∧
    (∀ i : cellularCell X 0,
      targetComparison (FreeAbelianGroup.of i) = targetCellClass i) ∧
    suspensionComparison.toFun =
      provisionalReducedGroupSuspensionMap 0 (cellularDegreeZeroQuotientPointed X) ∧
    ∀ j : cellularCell X 1,
      targetComparison
          (cellularDifferentialFromDegrees X 0 lowDegreeBoundary.attachingDegree
            (FreeAbelianGroup.of j)) =
        suspensionComparison.symm
          (provisionalReducedGroupPointedMap 1
            boundaryComparison (sourceComparison (FreeAbelianGroup.of j)))

/-- The actual degree-`1` Chapter 13 comparison data compute the cellular differential on
generators by the boundary-composite formula. -/
theorem cellularDifferentialFromDegrees_agreesWithBoundaryComposite_one_actual
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (x_zero : cellularSkeleton X 0)
    (lowDegreeBoundary : CellularLowDegreeBoundary X)
    (sourceWedge :
      cellularDegreeOneSourceQuotientPointed X x_zero ≅
        wedgeOfNSpheres 1 (cellularCell X 1))
    (sourceWedgeCellClass :
      cellularCell X 1 →
        provisionalReducedGroup 1 (wedgeOfNSpheres 1 (cellularCell X 1)))
    (sourceCellClass :
      cellularCell X 1 →
        provisionalReducedGroup 1 (cellularDegreeOneSourceQuotientPointed X x_zero))
    (sourceComparison :
      cellularChainGroup X 1 ≃
        provisionalReducedGroup 1 (cellularDegreeOneSourceQuotientPointed X x_zero))
    (targetCellClass :
      cellularCell X 0 →
        provisionalReducedGroup 0 (cellularDegreeZeroQuotientPointed X))
    (boundaryComparison :
      cellularDegreeOneSourceQuotientPointed X x_zero ⟶
        Σ (cellularDegreeZeroQuotientPointed X))
    (suspensionComparison : CellularDegreeZeroSuspensionComparison X)
    (targetComparison : CellularDegreeZeroComparisonIso X)
    (hcomp :
      IsCellularBoundaryCompositeInSourceDegreeOne X x_zero
        lowDegreeBoundary
        sourceWedge sourceWedgeCellClass sourceCellClass sourceComparison
        targetCellClass boundaryComparison suspensionComparison targetComparison) :
    ∀ j : cellularCell X 1,
      targetComparison
          (cellularDifferentialFromDegrees X 0 lowDegreeBoundary.attachingDegree
            (FreeAbelianGroup.of j)) =
        suspensionComparison.symm
          (provisionalReducedGroupPointedMap 1
            boundaryComparison (sourceComparison (FreeAbelianGroup.of j))) := by
  rcases hcomp with ⟨_, _, _, _, hBoundaryComposite⟩
  exact hBoundaryComposite

/-- In source degree `1`, under the Chapter 13 identifications
`C₁(X) ≃ H'_1(X¹ / X⁰)` and `C₀(X) ≃ H'_0(X^0 / X^(-1))`, the cellular differential
`d₁ : C₁(X) → C₀(X)` agrees with the composite
`H'_1(X¹ / X⁰) → H'_1(Σ(X^0 / X^(-1))) → H'_0(X^0 / X^(-1))`.

The degree-`1` cellular differential is represented here by the actual endpoint-difference
family `lowDegreeBoundary.attachingDegree` carried by a chosen `CellularLowDegreeBoundary X`.
The compatibility predicate requires that the displayed source comparison come from a chosen
wedge-of-circles model for `X¹ / X⁰`, and that the displayed boundary comparison, suspension
equivalence, and target comparison satisfy the actual low-degree boundary-composite generator
formula on the chosen owners `X¹ / X⁰` and `cellularDegreeZeroQuotientPointed X` for
`X^0 / X^(-1)`. -/
theorem cellularDifferential_agreesWithBoundaryComposite_one
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (x_zero : cellularSkeleton X 0)
    (lowDegreeBoundary : CellularLowDegreeBoundary X)
    (sourceWedge :
      cellularDegreeOneSourceQuotientPointed X x_zero ≅
        wedgeOfNSpheres 1 (cellularCell X 1))
    (sourceWedgeCellClass :
      cellularCell X 1 →
        provisionalReducedGroup 1 (wedgeOfNSpheres 1 (cellularCell X 1)))
    (sourceCellClass :
      cellularCell X 1 →
        provisionalReducedGroup 1 (cellularDegreeOneSourceQuotientPointed X x_zero))
    (sourceComparison :
      cellularChainGroup X 1 ≃
        provisionalReducedGroup 1 (cellularDegreeOneSourceQuotientPointed X x_zero))
    (targetCellClass :
      cellularCell X 0 →
        provisionalReducedGroup 0 (cellularDegreeZeroQuotientPointed X))
    (boundaryComparison :
      cellularDegreeOneSourceQuotientPointed X x_zero ⟶
        Σ (cellularDegreeZeroQuotientPointed X))
    (suspensionComparison : CellularDegreeZeroSuspensionComparison X)
    (targetComparison : CellularDegreeZeroComparisonIso X)
    (hcomp :
      IsCellularBoundaryCompositeInSourceDegreeOne X x_zero
        lowDegreeBoundary
        sourceWedge sourceWedgeCellClass sourceCellClass sourceComparison
        targetCellClass boundaryComparison suspensionComparison targetComparison) :
    ∀ c : cellularChainGroup X 1,
      targetComparison
          (cellularDifferentialFromDegrees X 0 lowDegreeBoundary.attachingDegree c) =
        suspensionComparison.symm
          (provisionalReducedGroupPointedMap 1
            boundaryComparison (sourceComparison c)) := sorry

/-- Lemma 13.2.9. For positive target degree `n`, equivalently for source degree `n + 1`,
under the Chapter 13 identifications
`C_(n + 1)(X) ≃ H'_(n + 1)(X^(n + 1) / X^n)` and
`C_n(X) ≃ H'_n(X^n / X^(n - 1))`, the cellular differential
`d_(n + 1) : C_(n + 1)(X) → C_n(X)` agrees with the composite
`H'_(n + 1)(X^(n + 1) / X^n) → H'_(n + 1)(Σ(X^n / X^(n - 1))) →
  H'_n(X^n / X^(n - 1))`.

This is the canonical Chapter 13 compatibility statement itself: the public inputs are the actual
Construction 13.2.4 boundary comparison on `X^(n + 1) / X^n`, the actual Construction 13.2.3
attaching-degree family on the `n`-cells determined by that boundary comparison, and a chosen
suspension equivalence on `H'_n(X^n / X^(n - 1))` whose forward map is the actual suspension map
and which in the intended application arises from Lemma 13.2.8 after identifying the target
quotient with a wedge of `n`-spheres. The compatibility between the Construction 13.2.3 quotient
projections and the chosen target wedge projections is stated directly through
`IsCellularBoundaryCompositeInSourceDegree`, rather than through an extra wrapper package. -/
theorem cellularDifferential_agreesWithBoundaryComposite_succ
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (boundaryComparison :
      cellularSourceQuotientPointed X n x_prev ⟶
        cellularTargetQuotientSuspension X n x_prev)
    (mapComposite :
      cellularCell X ((n : ℕ) + 1) →
        cellularCell X (n : ℕ) → SphereSelfMap n)
    (attachingDegree :
      cellularCell X ((n : ℕ) + 1) → cellularCell X (n : ℕ) →₀ ℤ)
    (sourceWedge :
      cellularSourceQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1)))
    (sourceWedgeCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X ((n : ℕ) + 1))))
    (sourceCellClass :
      cellularCell X ((n : ℕ) + 1) →
        provisionalReducedGroup ((n : ℕ) + 1) (cellularSourceQuotientPointed X n x_prev))
    (sourceComparison : CellularSourceComparisonIso X n x_prev)
    (suspensionComparison : CellularTargetSuspensionComparison X n x_prev)
    (targetWedge :
      cellularTargetQuotientPointed X n x_prev ≅
        wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ)))
    (targetWedgeCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ)
          (wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))))
    (targetSphereFactorProjection :
      cellularCell X (n : ℕ) →
        C((wedgeOfNSpheres (n : ℕ) (cellularCell X (n : ℕ))).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetQuotientProjection :
      cellularCell X (n : ℕ) →
        C((cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (targetCellClass :
      cellularCell X (n : ℕ) →
        provisionalReducedGroup (n : ℕ) (cellularTargetQuotientPointed X n x_prev))
    (targetComparison : CellularTargetComparisonIso X n x_prev)
    (hAttachingDegree :
      CellularActualAttachingDegreeSpec X n x_prev boundaryComparison
        mapComposite attachingDegree)
    (hcomp :
      IsCellularBoundaryCompositeInSourceDegree X n x_prev
        boundaryComparison mapComposite attachingDegree
        sourceWedge sourceWedgeCellClass sourceCellClass sourceComparison
        suspensionComparison targetWedge targetWedgeCellClass
        targetSphereFactorProjection targetQuotientProjection targetCellClass
        targetComparison hAttachingDegree) :
    ∀ c : cellularChainGroup X ((n : ℕ) + 1),
      targetComparison
          (cellularDifferentialFromDegrees X (n : ℕ) attachingDegree c) =
        suspensionComparison.symm
          (provisionalReducedGroupPositiveMap n
            boundaryComparison (sourceComparison c)) := sorry
