import Mathlib.Data.Finsupp.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_2

noncomputable section

universe u

open CategoryTheory
open Topology
open scoped TopCat Topology
open scoped CellularChainGroup

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex.cell` is the canonical cell owner,
-- `Topology.CWComplex.skeleton` is the canonical skeleton owner, `FreeAbelianGroup.lift` is the
-- canonical way to extend generator data to the cellular chain groups, and the current
-- Chapter 13 degree predicate is `SphereSelfMap.HasDegree`. The fuller boundary-comparison owner
-- appears later in
-- Chapter 13 and imports this file, so this item records the explicit coefficient data together
-- with a local source-faithful attaching-data specification.

/-- A CW complex structure on `X` provides the Hausdorffness needed by the classical skeleton
API. -/
instance instT2SpaceOfCWComplexUniv (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] : T2Space X := sorry

/-- The chosen `n`-skeleton `X^n` of the CW complex `X`. -/
abbrev cellularSkeleton (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) : Set X :=
  Topology.CWComplex.skeleton (Set.univ : Set X) n

/-- The chosen skeleta of a CW complex are monotone in the degree parameter. -/
theorem cellularSkeleton_mono {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {m n : ℕ} (hmn : m ≤ n) :
    cellularSkeleton X m ⊆ cellularSkeleton X n := sorry

/-- The pointed quotient model `X^(n + 1) / X^n`, based at the collapsed image of `x0 ∈ X^n`. -/
def cellularSkeletonQuotientPointed (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] (n : ℕ) (x0 : cellularSkeleton X n) :
    PointedCompactlyGenerated.{u, u} :=
  let h : cellularSkeleton X n ⊆ cellularSkeleton X (n + 1) :=
    cellularSkeleton_mono (Nat.le_succ n)
  previousSkeletonQuotientPointed h x0

/-- The predecessor basepoint `x_prev ∈ X^(n - 1)` viewed inside the chosen `n`-skeleton `X^n`. -/
def predecessorSkeletonPoint
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :
    cellularSkeleton X (n : ℕ) :=
  ⟨x_prev.1, cellularSkeleton_mono (Nat.sub_le (n : ℕ) 1) x_prev.2⟩

/-- The pointed quotient `X^(n + 1) / X^n` used on the source side of the positive-degree
cellular boundary comparison. -/
abbrev cellularSourceQuotientPointed
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :
    PointedCompactlyGenerated.{u, u} :=
  cellularSkeletonQuotientPointed X (n : ℕ) (predecessorSkeletonPoint X n x_prev)

/-- The pointed quotient `X^n / X^(n - 1)` used as the target of the attaching-map composite in
Construction 13.2.3. -/
abbrev cellularTargetQuotientPointed
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :
    PointedCompactlyGenerated.{u, u} :=
  cellularSkeletonQuotientPointed X ((n : ℕ) - 1) x_prev

/-- The reduced suspension `Σ(X^n / X^(n - 1))` on the target side of the positive-degree
cellular boundary comparison. -/
abbrev cellularTargetQuotientSuspension
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :
    PointedCompactlyGenerated.{u, u} :=
  suspensionSpace (cellularTargetQuotientPointed X n x_prev)

/-- The copy of `X^(n - 1)` sitting inside `X^(n + 1)`, used to specialize Construction 13.2.4
to the cellular boundary in degree `n + 1`. -/
def secondPredecessorSkeleton
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) : Set (cellularSkeleton X ((n : ℕ) + 1)) :=
  { x | x.1 ∈ cellularSkeleton X ((n : ℕ) - 1) }

/-- Inside `X^(n + 1)`, the copy of `X^(n - 1)` lies in the copy of `X^n`. -/
theorem secondPredecessorSkeleton_subset_predecessor
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ+) :
    secondPredecessorSkeleton X n ⊆
      previousSkeletonLowerSubset
        (cellularSkeleton X (n : ℕ))
        (cellularSkeleton X ((n : ℕ) + 1)) := sorry

/-- The chosen predecessor point `x_prev ∈ X^(n - 1)` viewed inside the copy of `X^(n - 1)`
contained in the chosen `(n + 1)`-skeleton. -/
def secondPredecessorSkeletonPoint
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :
    secondPredecessorSkeleton X n :=
  ⟨⟨x_prev.1,
      cellularSkeleton_mono
        (Nat.le_trans (Nat.sub_le (n : ℕ) 1) (Nat.le_succ (n : ℕ)))
        x_prev.2⟩,
    x_prev.2⟩

/-- The copied quotient `X^n / X^(n - 1)` sitting inside the chosen `(n + 1)`-skeleton. -/
abbrev copiedTargetQuotientPointed
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :
    PointedCompactlyGenerated.{u, u} :=
  previousSkeletonQuotientPointed
    (secondPredecessorSkeleton_subset_predecessor X n)
    (secondPredecessorSkeletonPoint X n x_prev)

/-- The reduced suspension of the copied quotient `X^n / X^(n - 1)` inside `X^(n + 1)`. -/
abbrev copiedTargetQuotientSuspension
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1)) :
    PointedCompactlyGenerated.{u, u} :=
  suspensionSpace (copiedTargetQuotientPointed X n x_prev)

/-- A finitely supported integral linear combination of the degree-`n` cellular generators of
`X`, viewed as an element of `C[n](X)`. -/
def cellularChainCombination (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) (coeff : cellularCell X n →₀ ℤ) : C[n](X) :=
  coeff.support.sum fun i ↦ coeff i • FreeAbelianGroup.of i

/-- The boundary of the generator corresponding to an `(n + 1)`-cell, determined by the displayed
finitely supported coefficient family on the `n`-cells. -/
def cellularBoundaryOnGenerator (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) (attachingDegree : cellularCell X (n + 1) → cellularCell X n →₀ ℤ)
    (j : cellularCell X (n + 1)) : C[n](X) :=
  cellularChainCombination X n (attachingDegree j)

/-- The degree-`n` cellular differential determined by explicit attaching-degree coefficients on
the generators of `C[n + 1](X)`. -/
def cellularDifferentialFromDegrees (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] (n : ℕ)
    (attachingDegree : cellularCell X (n + 1) → cellularCell X n →₀ ℤ) :
    C[n + 1](X) →+ C[n](X) :=
  FreeAbelianGroup.lift (cellularBoundaryOnGenerator X n attachingDegree)

/-- Applying `cellularDifferentialFromDegrees` to the generator of an `(n + 1)`-cell returns the
prescribed formal sum of `n`-cells with the chosen attaching-degree coefficients. -/
theorem cellularDifferentialFromDegrees_apply_of (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] (n : ℕ)
    (attachingDegree : cellularCell X (n + 1) → cellularCell X n →₀ ℤ)
    (j : cellularCell X (n + 1)) :
    cellularDifferentialFromDegrees X n attachingDegree (FreeAbelianGroup.of j) =
      cellularBoundaryOnGenerator X n attachingDegree j := sorry

/-- The coefficient of the generator `i` in an element of `C[n](X)`, extracted via
the universal property of the free Abelian group on the `n`-cells of `X`. -/
def cellularGeneratorCoefficient (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) (i : cellularCell X n) : C[n](X) →+ ℤ :=
  let _ : DecidableEq (cellularCell X n) := Classical.decEq _
  FreeAbelianGroup.lift fun k ↦ if i = k then 1 else 0

/-- The formal sum `cellularBoundaryOnGenerator X n attachingDegree j` has coefficient
`(attachingDegree j) i` on the generator `i`. -/
theorem cellularBoundaryOnGenerator_coefficient (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] (n : ℕ)
    (attachingDegree : cellularCell X (n + 1) → cellularCell X n →₀ ℤ)
    (j : cellularCell X (n + 1)) (i : cellularCell X n) :
    cellularGeneratorCoefficient X n i (cellularBoundaryOnGenerator X n attachingDegree j) =
      (attachingDegree j) i := sorry

/-- Applying `cellularDifferentialFromDegrees` to a cellular generator produces an element whose
`i`-coefficient is the prescribed attaching-degree coefficient. -/
theorem cellularDifferentialFromDegrees_coefficient (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] (n : ℕ)
    (attachingDegree : cellularCell X (n + 1) → cellularCell X n →₀ ℤ)
    (j : cellularCell X (n + 1)) (i : cellularCell X n) :
    cellularGeneratorCoefficient X n i
      (cellularDifferentialFromDegrees X n attachingDegree (FreeAbelianGroup.of j)) =
        (attachingDegree j) i := sorry

/-- The concrete `S^n ⟶ S^n` composite used for the coefficient of the `n`-cell `i` in the
boundary of the `(n + 1)`-cell `j`: first map into the quotient `X^n / X^(n - 1)` using the
actual attaching map of `j`, then project to the `i`-sphere factor. -/
def cellularActualAttachingComposite
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (attachingMapToQuotient :
      cellularCell X ((n : ℕ) + 1) →
        C((suspensionSphere (n : ℕ)).toCompactlyGenerated,
          (cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated))
    (quotientProjection :
      cellularCell X (n : ℕ) →
        C((cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated,
          (suspensionSphere (n : ℕ)).toCompactlyGenerated))
    (j : cellularCell X ((n : ℕ) + 1)) (i : cellularCell X (n : ℕ)) :
    SphereSelfMap n :=
  (quotientProjection i).comp (attachingMapToQuotient j)

/-- Source-faithful Construction 13.2.3 data for a chosen Construction 13.2.4 boundary
comparison: `topologicalBoundaryComparison` is the actual cellular boundary comparison on
`X^(n + 1) / X^n`, transported to the Chapter 13 pointed owners, and `mapComposite` together
with `attachingDegree` records the actual composites `S^n ⟶ X^n ⟶ X^n / X^(n - 1) ⟶ S^n` and
their degree coefficients for that chosen comparison data. The spec keeps the Construction 13.2.4
comparison witnesses explicit and identifies `mapComposite j i` with the concrete composite built
from the actual attaching map of `j` and the projection to the `i`-sphere factor. -/
structure CellularActualAttachingDegreeSpec
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+)
    (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (topologicalBoundaryComparison :
      cellularSourceQuotientPointed X n x_prev ⟶
        cellularTargetQuotientSuspension X n x_prev)
    (mapComposite :
      cellularCell X ((n : ℕ) + 1) →
        cellularCell X (n : ℕ) → SphereSelfMap n)
    (attachingDegree :
      cellularCell X ((n : ℕ) + 1) → cellularCell X (n : ℕ) →₀ ℤ) where
  /-- The canonical Construction 13.2.4 boundary map from `X^(n + 1) / X^n` to the reduced
  suspension of the copied quotient `X^n / X^(n - 1)` inside `X^(n + 1)`. -/
  topologicalBoundaryMapComparison :
    C((cellularSourceQuotientPointed X n x_prev).toCompactlyGenerated,
      (copiedTargetQuotientSuspension X n x_prev).toCompactlyGenerated)
  /-- The explicit comparison from the reduced suspension of the copied quotient
  `X^n / X^(n - 1)` inside `X^(n + 1)` to the Chapter 13 suspension owner on the chosen quotient
  `X^n / X^(n - 1)`. -/
  suspensionComparison :
    C((copiedTargetQuotientSuspension X n x_prev).toCompactlyGenerated,
      (cellularTargetQuotientSuspension X n x_prev).toCompactlyGenerated)
  /-- The chosen boundary comparison comes from Construction 13.2.4 on
  `X^(n - 1) ⊆ X^n ⊆ X^(n + 1)` via the canonical boundary map into the reduced suspension of
  the copied quotient and the displayed comparison to the Chapter 13 target owner. -/
  boundaryComparison :
    CategoryTheory.ConcreteCategory.hom
        (PointedCompactlyGenerated.Hom.hom topologicalBoundaryComparison) =
      suspensionComparison.comp topologicalBoundaryMapComparison
  /-- The actual attaching map of an `(n + 1)`-cell `j`, followed by the quotient
  `X^n ⟶ X^n / X^(n - 1)`. -/
  attachingMapToQuotient :
    cellularCell X ((n : ℕ) + 1) →
      C((suspensionSphere (n : ℕ)).toCompactlyGenerated,
        (cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated)
  /-- The projection from the quotient `X^n / X^(n - 1)` to the `i`-th sphere factor in the
  chosen wedge decomposition. -/
  quotientProjection :
    cellularCell X (n : ℕ) →
      C((cellularTargetQuotientPointed X n x_prev).toCompactlyGenerated,
        (suspensionSphere (n : ℕ)).toCompactlyGenerated)
  /-- For each `(n + 1)`-cell `j` and `n`-cell `i`, `mapComposite j i` is the actual composite
  determined by the chosen attaching map and quotient projection. -/
  mapComposite_eq :
    ∀ j : cellularCell X ((n : ℕ) + 1), ∀ i : cellularCell X (n : ℕ),
      mapComposite j i =
        cellularActualAttachingComposite X n x_prev
          attachingMapToQuotient quotientProjection j i
  /-- For each `(n + 1)`-cell `j` and `n`-cell `i`, the coefficient function records the degree of
  the actual composite `S^n ⟶ X^n ⟶ X^n / X^(n - 1) ⟶ S^n`. -/
  hasDegree :
    ∀ j : cellularCell X ((n : ℕ) + 1), ∀ i : cellularCell X (n : ℕ),
      SphereSelfMap.HasDegree n (mapComposite j i) ((attachingDegree j) i)

/-- Construction 13.2.3: let `mapComposite j i` be the actual composite
`S^n ⟶ X^n ⟶ X^n / X^(n - 1) ⟶ S^n` for the `(n + 1)`-cell `j` and the `n`-cell `i`, and let
`attachingDegree` be the corresponding finitely supported coefficient function on the actual
`n`-cells for a chosen Construction 13.2.4 boundary comparison on
`X^(n - 1) ⊆ X^n ⊆ X^(n + 1)`. For the canonical degree-`(n + 1)` cellular differential
`cellularDifferentialFromDegrees X n attachingDegree` determined by these actual coefficients, the
coefficient of `i` in the boundary of the generator `j` is the degree of that concrete
composite. This is the index-shifted form of the textbook statement. -/
theorem cellularDifferential_coefficient_hasDegree (X : Type u)
    [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ+)
    (x_prev : cellularSkeleton X ((n : ℕ) - 1))
    (topologicalBoundaryComparison :
      cellularSourceQuotientPointed X n x_prev ⟶
        cellularTargetQuotientSuspension X n x_prev)
    (mapComposite :
      cellularCell X ((n : ℕ) + 1) →
        cellularCell X (n : ℕ) → SphereSelfMap n)
    (attachingDegree :
      cellularCell X ((n : ℕ) + 1) → cellularCell X (n : ℕ) →₀ ℤ)
    (hActual :
      CellularActualAttachingDegreeSpec X n x_prev topologicalBoundaryComparison
        mapComposite attachingDegree)
    (j : cellularCell X ((n : ℕ) + 1)) (i : cellularCell X (n : ℕ)) :
    SphereSelfMap.HasDegree n (mapComposite j i)
      (cellularGeneratorCoefficient X (n : ℕ) i
        (cellularDifferentialFromDegrees X (n : ℕ) attachingDegree (FreeAbelianGroup.of j))) :=
  sorry
