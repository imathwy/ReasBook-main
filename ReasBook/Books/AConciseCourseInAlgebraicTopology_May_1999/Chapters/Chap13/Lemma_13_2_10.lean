import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Lemma_13_2_9

noncomputable section

universe u

open Topology
open scoped CellularChainGroup

-- Semantic recall via `lean_leansearch`: `HomologicalComplex.d_comp_d'` is the canonical
-- square-zero theorem after packaging differentials into a chain complex. This item stays at the
-- explicit Chapter 13 cellular-differential owner `cellularDifferentialFromDegrees`.

namespace CellularLowDegreeBoundary

/-- The degree-`1` cellular differential determined by the actual endpoint data of the `1`-cells.
-/
def differential
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularLowDegreeBoundary X) :
    C[1](X) →+ C[0](X) :=
  cellularDifferentialFromDegrees X 0 data.attachingDegree

end CellularLowDegreeBoundary

/-- Chosen Chapter 13 data defining the positive-degree cellular differential
`d_(n + 1) : C[n + 1](X) → C[n](X)`. -/
structure PositiveCellularDifferentialChoice
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+) where
  x_prev : cellularSkeleton X n.natPred
  boundaryComparison :
    cellularSourceQuotientPointed X n x_prev ⟶
      cellularTargetQuotientSuspension X n x_prev
  mapComposite :
    cellularCell X ((n : ℕ) + 1) →
      cellularCell X (n : ℕ) → SphereSelfMap n
  attachingDegree :
    cellularCell X ((n : ℕ) + 1) → cellularCell X (n : ℕ) →₀ ℤ
  attachingDegreeSpec :
    CellularActualAttachingDegreeSpec X n x_prev boundaryComparison
      mapComposite attachingDegree

namespace PositiveCellularDifferentialChoice

/-- The chosen Chapter 13 cellular differential in target degree `n`. -/
def differential
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ+} (data : PositiveCellularDifferentialChoice X n) :
    C[((n : ℕ) + 1)](X) →+ C[(n : ℕ)](X) :=
  cellularDifferentialFromDegrees X (n : ℕ) data.attachingDegree

@[simp] theorem differential_eq
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ+} (data : PositiveCellularDifferentialChoice X n) :
    data.differential = cellularDifferentialFromDegrees X (n : ℕ) data.attachingDegree :=
  rfl

end PositiveCellularDifferentialChoice

/-- A chosen family of cellular differentials on `X`, consisting of explicit endpoint data in
degree `1` and chosen Chapter 13 attaching-degree data in every positive target degree. -/
structure CellularDifferentialFamily
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] where
  lowDegree : CellularLowDegreeBoundary X
  positiveDegree : ∀ n : ℕ+, PositiveCellularDifferentialChoice X n

namespace CellularDifferentialFamily

/-- The degree-`n` cellular differential `C[n + 1](X) → C[n](X)` determined by a chosen family of
cellular differential data. -/
  def differential
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) :
    ∀ n : ℕ, C[n + 1](X) →+ C[n](X)
  | 0 => data.lowDegree.differential
  | Nat.succ n => (data.positiveDegree ⟨Nat.succ n, Nat.succ_pos n⟩).differential

/-- In degree `0`, `data.differential` is the endpoint differential determined by the chosen
degree-`1` boundary data. -/
@[simp] theorem differential_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) :
    data.differential 0 = data.lowDegree.differential :=
  rfl

/-- In positive target degree `n + 1`, `data.differential` is the cellular differential determined
by the chosen Chapter 13 attaching-degree data in degree `n + 1`. -/
@[simp] theorem differential_succ
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) (n : ℕ) :
    data.differential (n + 1) =
      (data.positiveDegree ⟨n + 1, Nat.succ_pos n⟩).differential :=
  rfl

end CellularDifferentialFamily

/-- Low-degree square-zero case `d₁ ∘ d₂ = 0` for chosen cellular differential data. -/
private theorem cellularDifferential_squareZero_one_two
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (lowDegree : CellularLowDegreeBoundary X)
    (x_zero : cellularSkeleton X 0)
    (boundaryComparisonOne :
      cellularSourceQuotientPointed X 1 x_zero ⟶
        cellularTargetQuotientSuspension X 1 x_zero)
    (mapCompositeOne :
      cellularCell X 2 → cellularCell X 1 → SphereSelfMap 1)
    (attachingDegreeOne : cellularCell X 2 → cellularCell X 1 →₀ ℤ)
    (hAttachingDegreeOne :
      CellularActualAttachingDegreeSpec X 1 x_zero boundaryComparisonOne
        mapCompositeOne attachingDegreeOne) :
    (cellularDifferentialFromDegrees X 0 lowDegree.attachingDegree).comp
      (cellularDifferentialFromDegrees X 1 attachingDegreeOne) = 0 := sorry

/-- Positive-degree square-zero case `d_(n + 1) ∘ d_(n + 2) = 0` for chosen Chapter 13
attaching-degree data in consecutive positive target degrees. -/
private theorem cellularDifferential_squareZero_succ
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ+)
    (x_prev : cellularSkeleton X n.natPred)
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
    (x_curr : cellularSkeleton X (n : ℕ))
    (boundaryComparisonSucc :
      cellularSourceQuotientPointed X (n + 1) x_curr ⟶
        cellularTargetQuotientSuspension X (n + 1) x_curr)
    (mapCompositeSucc :
      cellularCell X ((n : ℕ) + 2) →
        cellularCell X ((n : ℕ) + 1) → SphereSelfMap (n + 1))
    (attachingDegreeSucc :
      cellularCell X ((n : ℕ) + 2) → cellularCell X ((n : ℕ) + 1) →₀ ℤ)
    (hAttachingDegreeSucc :
      CellularActualAttachingDegreeSpec X (n + 1) x_curr boundaryComparisonSucc
        mapCompositeSucc attachingDegreeSucc) :
    (cellularDifferentialFromDegrees X (n : ℕ) attachingDegree).comp
      (cellularDifferentialFromDegrees X ((n : ℕ) + 1) attachingDegreeSucc) = 0 := sorry

namespace PositiveCellularDifferentialChoice

/-- The chosen degree-`2` differential composes trivially with the chosen low-degree boundary. -/
theorem lowDegree_comp_differential_eq_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (lowDegree : CellularLowDegreeBoundary X)
    (data : PositiveCellularDifferentialChoice X 1) :
    lowDegree.differential.comp data.differential = 0 := by
  simpa [CellularLowDegreeBoundary.differential, PositiveCellularDifferentialChoice.differential]
    using
      cellularDifferential_squareZero_one_two X lowDegree
        data.x_prev
        data.boundaryComparison
        data.mapComposite
        data.attachingDegree
        data.attachingDegreeSpec

/-- Consecutive positive-degree differentials in the chosen Chapter 13 data compose to zero. -/
theorem differential_comp_succ_eq_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ+} (data : PositiveCellularDifferentialChoice X n)
    (succData : PositiveCellularDifferentialChoice X (n + 1)) :
    data.differential.comp succData.differential = 0 := by
  simpa [PositiveCellularDifferentialChoice.differential] using
    cellularDifferential_squareZero_succ X n
      data.x_prev
      data.boundaryComparison
      data.mapComposite
      data.attachingDegree
      data.attachingDegreeSpec
      succData.x_prev
      succData.boundaryComparison
      succData.mapComposite
      succData.attachingDegree
      succData.attachingDegreeSpec

end PositiveCellularDifferentialChoice

namespace CellularDifferentialFamily

/-- Consecutive differentials in a chosen cellular differential family compose to zero. -/
theorem differential_comp_differential
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) (n : ℕ) :
    (data.differential n).comp (data.differential (n + 1)) = 0 := by
  cases n with
  | zero =>
      simpa using
        (data.positiveDegree 1).lowDegree_comp_differential_eq_zero data.lowDegree
  | succ n =>
      let m : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
      simpa using
        (data.positiveDegree m).differential_comp_succ_eq_zero
          (data.positiveDegree (m + 1))

end CellularDifferentialFamily

/-- Lemma 13.2.10: for the chosen cellular differentials on `X`, the square-zero law
`d (n + 1) ≫ d n = 0` holds uniformly in every degree `n`. -/
theorem cellularDifferential_squareZero
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) (n : ℕ) :
    (data.differential n).comp (data.differential (n + 1)) = 0 :=
  data.differential_comp_differential n
