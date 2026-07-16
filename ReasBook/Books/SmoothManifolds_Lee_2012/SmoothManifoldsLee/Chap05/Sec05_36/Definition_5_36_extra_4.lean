import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_29.Definition_5_29_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Manifold

universe uM

section

variable {n k : ℕ}
variable {M : Type uM}
variable [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The last free coordinate of a `k`-dimensional half-slice, viewed as a coordinate of the
ambient space `ℝ^n`. -/
private def lastFreeCoordinate (hk : 0 < k) (hkn : k ≤ n) : Fin n :=
  ⟨k - 1, lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hk)) hkn⟩

namespace Set

/-- The standard Euclidean `k`-dimensional half-slice of `U ⊆ ℝ^n` obtained by fixing the last
`n - k` coordinates to the values `c` and requiring the last free coordinate to be nonnegative.
This is the boundary analogue of `euclideanSlice`, with the same primitive tail-coordinate data;
the free coordinates carry the standard `k`-dimensional boundary-model geometry. -/
def euclideanHalfSlice (U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (c : Fin (n - k) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  { x ∈ euclideanSlice U k hkn c | 0 ≤ x (lastFreeCoordinate hk hkn) }

/-- A subset `S` of an open set `U ⊆ ℝ^n` is a `k`-dimensional half-slice if it is obtained by
fixing the last `n - k` coordinates to constants and requiring the last free coordinate to be
nonnegative. -/
def IsEuclideanHalfSlice (S U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ hk : 0 < k, ∃ hkn : k ≤ n, ∃ c : Fin (n - k) → ℝ, S = euclideanHalfSlice U k hk hkn c

/-- A subset `S ⊆ M` is a `k`-dimensional half-slice in the chart `e` when its image in Euclidean
coordinates is a Euclidean `k`-dimensional half-slice of the chart image `e.target`. -/
def IsHalfSliceInChart (S : Set M) (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ℕ) : Prop :=
  (e '' (S ∩ e.source)).IsEuclideanHalfSlice e.target k

end Set

namespace OpenPartialHomeomorph

/-- A boundary slice chart for `S` is a smooth chart in the maximal atlas whose local image of `S`
is a Euclidean `k`-dimensional half-slice. -/
def IsBoundarySliceChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (S : Set M)
    (k : ℕ) : Prop :=
  e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M ∧ S.IsHalfSliceInChart e k

/-- Every boundary slice chart lies in the smooth maximal atlas. -/
theorem IsBoundarySliceChart.mem_maximalAtlas
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {S : Set M} {k : ℕ}
    (he : e.IsBoundarySliceChart S k) :
    e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
  he.1

end OpenPartialHomeomorph

namespace Set

section

variable (n : ℕ) {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Definition 5.36-extra-4: A subset `S ⊆ M` satisfies the local `k`-slice condition for
submanifolds with boundary if each point of `S` lies in a smooth chart whose local image of `S`
is either a Euclidean `k`-slice or a Euclidean `k`-dimensional half-slice. -/
class SatisfiesLocalSliceConditionWithBoundary (S : Set M) (k : ℕ) : Prop where
  /-- Every point of `S` lies in the source of some interior or boundary slice chart for `S`. -/
  exists_sliceChart (x : M) (hx : x ∈ S) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source ∧ (e.IsSliceChart S k ∨ e.IsBoundarySliceChart S k)

/-- The empty subset satisfies the local slice condition with boundary vacuously. -/
instance satisfiesLocalSliceConditionWithBoundary_empty (k : ℕ) :
    Set.SatisfiesLocalSliceConditionWithBoundary n (∅ : Set M) k := by
  refine ⟨?_⟩
  intro x hx
  cases hx

end

end Set

end
