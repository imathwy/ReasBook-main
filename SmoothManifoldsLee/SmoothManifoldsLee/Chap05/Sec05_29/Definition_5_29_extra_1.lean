import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.

open Set ChartedSpace
open scoped Manifold

universe u

namespace Set

private def tailCoordinate {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) : Fin n :=
  Fin.cast (Nat.add_sub_of_le hk) (i.natAdd k)

/-- The standard Euclidean `k`-slice of `U ⊆ ℝ^n` obtained by fixing the last `n - k`
coordinates to the values `c`. -/
def euclideanSlice {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k ≤ n)
    (c : Fin (n - k) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  { x ∈ U | ∀ i : Fin (n - k), x (tailCoordinate hk i) = c i }

/-- A subset `S` of an open set `U ⊆ ℝ^n` is a `k`-slice if it is obtained by fixing the last
`n - k` coordinates to constants. -/
def IsEuclideanSlice {n : ℕ} (S U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ hk : k ≤ n, ∃ c : Fin (n - k) → ℝ, S = euclideanSlice U k hk c

/-- A subset `S ⊆ M` is a `k`-slice in the chart `e` when its image in Euclidean coordinates is
a Euclidean `k`-slice of the chart image `e.target`. -/
def IsSliceInChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (S : Set M) (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  (e '' (S ∩ e.source)).IsEuclideanSlice e.target k

end Set

namespace OpenPartialHomeomorph

/-- A slice chart for `S` is a smooth chart in the maximal atlas whose local image of `S`
is a Euclidean `k`-slice. -/
def IsSliceChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (S : Set M)
    (k : ℕ) : Prop :=
  e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M ∧
    S.IsSliceInChart e k

/-- Every slice chart lies in the smooth maximal atlas. -/
theorem IsSliceChart.mem_maximalAtlas
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {S : Set M} {k : ℕ}
    (he : e.IsSliceChart S k) :
    e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
  he.1

end OpenPartialHomeomorph

namespace Set

section

variable (n : ℕ) {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Definition 5.29-extra-1: a subset `S` of an `n`-manifold satisfies the local `k`-slice
condition if each point of `S` lies in the source of some smooth slice chart for `S`; any such
chart gives slice coordinates for `S`. -/
class SatisfiesLocalSliceCondition (S : Set M) (k : ℕ) : Prop where
  /-- Every point of `S` lies in the source of some slice chart for `S`. -/
  exists_sliceChart (x : M) (hx : x ∈ S) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source ∧ e.IsSliceChart S k

/-- The empty subset satisfies the local `k`-slice condition vacuously. -/
instance satisfiesLocalSliceCondition_empty (k : ℕ) :
    Set.SatisfiesLocalSliceCondition n (∅ : Set M) k := by
  refine ⟨?_⟩
  intro x hx
  cases hx

end

end Set
