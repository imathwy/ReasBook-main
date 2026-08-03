module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.MetricSpace.Thickening

public section

open Set Filter

namespace Schoenflies

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Theorem 63.6: a finite polygonal chain records successive
closed line segments contained in a prescribed set. -/
inductive PolygonalChain (U : Set E) : E → E → Type u
  | point (x : E) (hx : x ∈ U) : PolygonalChain U x x
  | snoc {x y z : E} (initial : PolygonalChain U x y)
      (lastEdge : segment ℝ y z ⊆ U) : PolygonalChain U x z

namespace PolygonalChain

/-- Helper for Theorem 63.6: containment of a segment is symmetric in its endpoints. -/
private lemma segment_subset_symm {U : Set E} {x y : E}
    (hxy : segment ℝ x y ⊆ U) : segment ℝ y x ⊆ U := by
  -- Rewrite the reversed segment to the original carrier.
  simpa only [segment_symm] using hxy

/-- Helper for Theorem 63.6: a single contained segment gives a one-edge chain. -/
def single {U : Set E} {x y : E} (hxy : segment ℝ x y ⊆ U) :
    PolygonalChain U x y :=
  .snoc (.point x (hxy (left_mem_segment ℝ x y))) hxy

/-- Helper for Theorem 63.6: concatenate two finite polygonal chains. -/
def append {U : Set E} {x y : E} (first : PolygonalChain U x y) :
    {z : E} → PolygonalChain U y z → PolygonalChain U x z
  | _, .point _ _ => first
  | _, .snoc initial lastEdge => .snoc (append first initial) lastEdge

/-- Helper for Theorem 63.6: reverse the order and direction of every edge in a chain. -/
def reverse {U : Set E} : {x y : E} → PolygonalChain U x y → PolygonalChain U y x
  | _, _, .point x hx => .point x hx
  | _, _, .snoc initial lastEdge =>
      (single (segment_subset_symm lastEdge)).append initial.reverse

/-- Helper for Theorem 63.6: the initial endpoint of a polygonal chain belongs to its set. -/
lemma start_mem {U : Set E} {x y : E} (chain : PolygonalChain U x y) : x ∈ U := by
  -- Follow initial subchains until reaching the first point constructor.
  induction chain with
  | point hx => exact hx
  | snoc _ _ ih => exact ih

/-- Helper for Theorem 63.6: the terminal endpoint of a polygonal chain belongs to its set. -/
lemma end_mem {U : Set E} {x y : E} (chain : PolygonalChain U x y) : y ∈ U := by
  -- The last segment contains its right endpoint; a point chain stores membership directly.
  induction chain with
  | point hx => exact hx
  | snoc _ lastEdge _ => exact lastEdge (right_mem_segment ℝ _ _)

end PolygonalChain

/-- Helper for Theorem 63.6: two points are polygonally joined in `U` when a
finite chain of closed line segments contained in `U` connects them. -/
def IsPolygonallyJoinedIn (U : Set E) (x y : E) : Prop :=
  Nonempty (PolygonalChain U x y)

/-- Helper for Theorem 63.6: a polygonal joining exposes a finite chain witness. -/
lemma IsPolygonallyJoinedIn.nonempty_chain {U : Set E} {x y : E}
    (hxy : IsPolygonallyJoinedIn U x y) : Nonempty (PolygonalChain U x y) := by
  -- Unpack the predicate in its owner module so clients need no definitional unfolding.
  exact hxy

/-- Helper for Theorem 63.6: one segment contained in `U` is a polygonal chain. -/
lemma IsPolygonallyJoinedIn.of_segment_subset {U : Set E} {x y : E}
    (hxy : segment ℝ x y ⊆ U) : IsPolygonallyJoinedIn U x y := by
  -- Package the one-edge data as a nonempty chain type.
  exact ⟨PolygonalChain.single hxy⟩

/-- Helper for Theorem 63.6: polygonal chains concatenate at a common endpoint. -/
lemma IsPolygonallyJoinedIn.trans {U : Set E} {x y z : E}
    (hxy : IsPolygonallyJoinedIn U x y) (hyz : IsPolygonallyJoinedIn U y z) :
    IsPolygonallyJoinedIn U x z := by
  -- Concatenate representatives of the two nonempty chain types.
  obtain ⟨first⟩ := hxy
  obtain ⟨second⟩ := hyz
  exact ⟨first.append second⟩

/-- Helper for Theorem 63.6: reversing every segment reverses a polygonal chain. -/
lemma IsPolygonallyJoinedIn.symm {U : Set E} {x y : E}
    (hxy : IsPolygonallyJoinedIn U x y) : IsPolygonallyJoinedIn U y x := by
  -- Reverse a representative finite chain.
  obtain ⟨chain⟩ := hxy
  exact ⟨chain.reverse⟩

/-- Helper for Theorem 63.6: sufficiently near points of an open set are joined
to the center by their straight segment inside the set. -/
private lemma eventually_segment_subset_of_isOpen {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) :
    ∀ᶠ y in nhdsWithin x U, segment ℝ x y ⊆ U := by
  -- Choose a convex metric ball around `x` contained in the open set.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε)] with y hy
  exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) hy).trans hball

/-- Helper for Theorem 63.6: any two points of an open connected subset of a
real normed vector space are connected by a finite polygonal chain in that set. -/
theorem existsPolygonalChainInOpenConnected {U : Set E}
    (hUopen : IsOpen U) (hUconnected : IsConnected U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    IsPolygonallyJoinedIn U x y := by
  -- Local convex balls supply the one-edge relation used by preconnected induction.
  apply hUconnected.isPreconnected.induction₂ (IsPolygonallyJoinedIn U)
      (fun z hz ↦ (eventually_segment_subset_of_isOpen hUopen hz).mono
        (fun _ hsegment ↦ IsPolygonallyJoinedIn.of_segment_subset hsegment))
  · -- Concatenate the two chains produced at an intermediate point.
    exact fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂
  · -- Reverse a chain when the induction crosses a local class backwards.
    exact fun _ _ _ _ h ↦ h.symm
  · exact hx
  · exact hy

/-- Helper for Theorem 63.6: components of open subsets of a real normed
vector space are open, without requiring a global local-connectedness instance. -/
lemma isOpen_connectedComponentIn_of_isOpen {U : Set E} (hUopen : IsOpen U) (x : E) :
    IsOpen (connectedComponentIn U x) := by
  -- A small convex ball around any component point remains in the same component.
  rw [Metric.isOpen_iff]
  intro y hy
  have hyU : y ∈ U := connectedComponentIn_subset U x hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen y hyU
  refine ⟨ε, hε, ?_⟩
  have hballComponent : Metric.ball y ε ⊆ connectedComponentIn U y :=
    (convex_ball y ε).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self hε) hball
  rwa [← connectedComponentIn_eq hy] at hballComponent

/-- Helper for Theorem 63.6: two points in the same component of an open set
are joined by a finite polygonal chain contained in that component. -/
theorem existsPolygonalChainInOpenComponent {U : Set E} (hUopen : IsOpen U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ connectedComponentIn U x) :
    IsPolygonallyJoinedIn (connectedComponentIn U x) x y := by
  -- Components of open subsets of a normed space are themselves open and connected.
  apply existsPolygonalChainInOpenConnected (isOpen_connectedComponentIn_of_isOpen hUopen x)
      (isConnected_connectedComponentIn_iff.mpr hx)
  · exact mem_connectedComponentIn hx
  · exact hy

/-- Helper for Theorem 63.6: two points of a preconnected set are joined by a
polygonal chain inside one component of every positive metric thickening. -/
theorem existsPolygonalChainInThickeningComponent {K : Set E}
    (hK : IsPreconnected K) {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    {r : ℝ} (hr : 0 < r) :
    IsPolygonallyJoinedIn (connectedComponentIn (Metric.thickening r K) x) x y := by
  -- The whole preconnected core lies in the thickening component containing `x`.
  have hKthickening : K ⊆ Metric.thickening r K := Metric.self_subset_thickening hr K
  have hyComponent : y ∈ connectedComponentIn (Metric.thickening r K) x :=
    hK.subset_connectedComponentIn hx hKthickening hy
  -- The thickening is open, so its selected component admits a polygonal chain.
  exact existsPolygonalChainInOpenComponent Metric.isOpen_thickening
    (hKthickening hx) hyComponent

end Schoenflies
