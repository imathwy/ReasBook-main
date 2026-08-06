import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4.Quotient

open scoped Topology.Homotopy unitInterval

noncomputable section

/-- The boundary sphere `S^(n - 1)` viewed as a subset of the standard closed disk `D^n =
unitDisk ((n : ℕ) - 1)`. -/
def diskBoundarySubset (n : ℕ+) : Set (unitDisk ((n : ℕ) - 1)) :=
  { x | x.1 ∈ sphereBoundary ((n : ℕ) - 1) }

/-- The quotient model `D^n / S^(n - 1)` obtained by collapsing the boundary sphere inside the
standard closed disk `D^n = unitDisk ((n : ℕ) - 1)`. -/
abbrev diskBoundaryQuotient (n : ℕ+) :=
  collapseSubsetType (unitDisk ((n : ℕ) - 1)) (diskBoundarySubset n)

/-- The standard sphere `S^(n - 1)` is compactly generated because it is a closed subspace of the
ambient Euclidean space. -/
instance boundarySphere_uCompactlyGeneratedSpace (n : ℕ+) :
    UCompactlyGeneratedSpace.{0} (sphereBoundary ((n : ℕ) - 1)) := sorry

/-- The standard sphere `S^(n - 1)` with the chosen basepoint `diskBoundaryBasepoint n`, regarded
as a pointed compactly generated space so that its reduced suspension realizes `Σ S^(n - 1)`. -/
def boundarySpherePointed (n : ℕ+) : PointedCompactlyGenerated.{0, 0} :=
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of.{0, 0} (sphereBoundary ((n : ℕ) - 1)))
    (diskBoundaryBasepoint n)

/-- The quotient-to-sphere comparison sends the disk model of `D^n / S^(n - 1)` to `S^n` by the
standard disk-fold formula that collapses the boundary sphere to the north pole. -/
def diskBoundaryQuotientToSpherePoint (n : ℕ+) (x : unitDisk n.natPred) :
    sphereBoundary (n.natPred + 1) :=
  ⟨EuclideanSpace.single (Fin.last (n.natPred + 1))
        (2 * ‖x.1‖ ^ 2 - 1) +
      ∑ i : Fin (n.natPred + 1),
        EuclideanSpace.single (Fin.castSucc i)
          (2 * Real.sqrt (1 - ‖x.1‖ ^ 2) * x.1 i), by
    sorry⟩

/-- The chosen comparison map `D^n / S^(n - 1) → S^n`, obtained by descending
`diskBoundaryQuotientToSpherePoint n` to the quotient collapsing the boundary sphere. -/
def diskBoundaryQuotientToSphere (n : ℕ+) :
    C(diskBoundaryQuotient n, sphereBoundary (n.natPred + 1)) where
  toFun :=
    Quotient.lift
      (fun x : unitDisk n.natPred ↦ diskBoundaryQuotientToSpherePoint n x)
      (by
        intro x y hxy
        sorry)
  continuous_toFun := by
    sorry

/-- The chosen comparison map `S^n → Σ S^(n - 1)` is the explicit reduced-suspension model map
obtained from the last coordinate on `S^n` and the normalized equatorial projection away from the
two poles; at the poles it uses the chosen basepoint of `S^(n - 1)`. -/
def sphereToBoundarySphereSuspension (n : ℕ+) :
    C(sphereBoundary (n.natPred + 1), (Σ (boundarySpherePointed n)).toCompactlyGenerated) where
  toFun x :=
    let last := x.1 (Fin.last (n.natPred + 1))
    let boundaryPoint : sphereBoundary n.natPred :=
      if hPole : last = 1 ∨ last = (-1 : ℝ) then
        diskBoundaryBasepoint n
      else
        ⟨∑ i : Fin (n.natPred + 1),
            EuclideanSpace.single i
              (x.1 (Fin.castSucc i) / Real.sqrt (1 - last ^ 2)), by
          sorry⟩
    let height : I := ⟨(last + 1) / 2, by
      sorry⟩
    reducedSuspensionMk (boundarySpherePointed n) (boundaryPoint, height)
  continuous_toFun := by
    sorry

/-- The norm of a point of `D^n` gives a valid suspension height in `I`. -/
theorem diskBoundaryQuotientToBoundarySphereSuspensionHeight_mem
    (n : ℕ+) (x : unitDisk n.natPred) :
    (0 : ℝ) ≤ ‖x.1‖ ∧ ‖x.1‖ ≤ 1 := sorry

/-- Normalizing a nonzero point of `D^n` lands on the boundary sphere `S^(n - 1)`. -/
theorem diskBoundaryQuotientToBoundarySphereSuspensionNormalize_mem
    (n : ℕ+) (x : unitDisk n.natPred) (hx : x.1 ≠ 0) :
    (‖x.1‖)⁻¹ • x.1 ∈ sphereBoundary n.natPred := sorry

/-- The representative-level direct comparison formula from `D^n` to `Σ S^(n - 1)`: the origin
uses the chosen basepoint, every nonzero point uses its normalized direction, and the suspension
height is `‖x‖`, so boundary points land at the north pole. -/
def diskBoundaryQuotientToBoundarySphereSuspensionPoint
    (n : ℕ+) (x : unitDisk n.natPred) :
    (Σ (boundarySpherePointed n)).toCompactlyGenerated :=
  let boundaryPoint : sphereBoundary n.natPred :=
    if hx : x.1 = 0 then
      diskBoundaryBasepoint n
    else
      ⟨(‖x.1‖)⁻¹ • x.1,
        diskBoundaryQuotientToBoundarySphereSuspensionNormalize_mem n x hx⟩
  let height : I :=
    ⟨‖x.1‖, diskBoundaryQuotientToBoundarySphereSuspensionHeight_mem n x⟩
  reducedSuspensionMk (boundarySpherePointed n) (boundaryPoint, height)

/-- The representative-level direct comparison formula respects the quotient relation collapsing
`S^(n - 1) ⊆ D^n`. -/
theorem diskBoundaryQuotientToBoundarySphereSuspensionPoint_respects
    (n : ℕ+) {x y : unitDisk n.natPred}
    (hxy : collapseSubsetSetoid (diskBoundarySubset n) x y) :
    diskBoundaryQuotientToBoundarySphereSuspensionPoint n x =
      diskBoundaryQuotientToBoundarySphereSuspensionPoint n y := sorry

/-- The quotient-lifted direct comparison formula is continuous. -/
theorem diskBoundaryQuotientToBoundarySphereSuspension_continuous
    (n : ℕ+) :
    Continuous
      (Quotient.lift
        (fun x : unitDisk n.natPred ↦
          diskBoundaryQuotientToBoundarySphereSuspensionPoint n x)
        (fun _ _ hxy ↦
          diskBoundaryQuotientToBoundarySphereSuspensionPoint_respects n hxy)) := sorry

/-- The direct comparison map `D^n / S^(n - 1) → Σ S^(n - 1)` is the quotient/suspension formula
that sends a class in `D^n / S^(n - 1)` to the suspension class determined by its normalized
direction and radius. -/
def diskBoundaryQuotientToBoundarySphereSuspension (n : ℕ+) :
    C(diskBoundaryQuotient n, (Σ (boundarySpherePointed n)).toCompactlyGenerated) :=
  ⟨Quotient.lift
      (fun x : unitDisk n.natPred ↦
        diskBoundaryQuotientToBoundarySphereSuspensionPoint n x)
      (fun _ _ hxy ↦
        diskBoundaryQuotientToBoundarySphereSuspensionPoint_respects n hxy),
    diskBoundaryQuotientToBoundarySphereSuspension_continuous n⟩

/-- Lemma 13.2.5. The comparison diagram relating `D^n / S^{n-1}`, `S^n`, and `Σ S^{n-1}` is
homotopy commutative: the composite
`(sphereToBoundarySphereSuspension n).comp (diskBoundaryQuotientToSphere n)` is homotopic to the
independently defined direct map `diskBoundaryQuotientToBoundarySphereSuspension n`. -/
theorem diskBoundaryQuotientSphereSuspension_homotopyCommutes (n : ℕ+) :
    ContinuousMap.Homotopic
      ((sphereToBoundarySphereSuspension n).comp (diskBoundaryQuotientToSphere n))
      (diskBoundaryQuotientToBoundarySphereSuspension n) := sorry
