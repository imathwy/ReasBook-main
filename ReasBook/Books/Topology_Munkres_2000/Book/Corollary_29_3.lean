module

public import Mathlib.Topology.Separation.Hausdorff

public section

universe u

/-- A locally closed subspace of a weakly locally compact `R1Space` is weakly locally
compact. -/
protected theorem IsLocallyClosed.weaklyLocallyCompactSpace
    {X : Type u} [TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X]
    {A : Set X} (hA : IsLocallyClosed A) : WeaklyLocallyCompactSpace A := by
  -- Transfer ambient local compactness to the locally closed subtype.
  letI : LocallyCompactSpace A := hA.locallyCompactSpace
  -- Local compactness supplies the required weak local compactness instance.
  infer_instance

/-- Corollary 29.3. A closed or open subspace of a locally compact Hausdorff
space is locally compact in the sense of `WeaklyLocallyCompactSpace`. -/
theorem weaklyLocallyCompactSpace_of_isClosed_or_isOpen
    {X : Type u} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    (A : Set X) (hA : IsClosed A ∨ IsOpen A) : WeaklyLocallyCompactSpace A := by
  -- Closed and open subsets are both locally closed, so the helper applies in either case.
  rcases hA with hA | hA
  · exact hA.isLocallyClosed.weaklyLocallyCompactSpace
  · exact hA.isLocallyClosed.weaklyLocallyCompactSpace
