import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe uG

noncomputable section

-- `lean_leansearch` was unavailable in this session; local inspection identified the
-- source-facing specialization to the chapter owner `open_submanifold_isEmbeddedSubmanifold`,
-- while the topological subgroup facts are owned canonically by `OpenSubgroup.isClosed`,
-- `OpenSubgroup.isClopen`, and `IsClopen.biUnion_connectedComponent_eq`.

section OpenSubgroupsAsSubmanifolds

variable {n : ℕ}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) G]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) G]

-- Bridge the canonical open-subset manifold structure from `Opens G` to an `OpenSubgroup` carrier.
instance (K : OpenSubgroup G) : ChartedSpace (EuclideanSpace ℝ (Fin n)) (K : Set G) :=
  show ChartedSpace (EuclideanSpace ℝ (Fin n)) (((K : TopologicalSpace.Opens G) : Set G)) from
    inferInstance

instance (K : OpenSubgroup G) : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (K : Set G) :=
  show IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (((K : TopologicalSpace.Opens G) : Set G)) from
    inferInstance

/-- Lemma 7.12 (1): if `H` is an open subgroup of a Lie group `G`, then its carrier is an embedded
submanifold of `G`, hence `H` is an embedded Lie subgroup with its induced smooth structure. -/
theorem open_subgroup_isEmbeddedSubmanifold (K : OpenSubgroup G) :
    IsEmbeddedSubmanifold (𝓡 n) (𝓡 n) (K : Set G) := by
  simpa using open_submanifold_isEmbeddedSubmanifold (K : TopologicalSpace.Opens G)

end OpenSubgroupsAsSubmanifolds

section OpenSubgroupsAsClopen

variable {G : Type uG} [Group G] [TopologicalSpace G]

/- Lemma 7.12 (2): an open subgroup is closed by the canonical mathlib owner
`OpenSubgroup.isClosed`. -/
#check OpenSubgroup.isClosed

section

variable [SeparatelyContinuousMul G]

/-- Lemma 7.12 (3): an open subgroup of a Lie group is the union of the connected components of
its points. -/
theorem open_subgroup_eq_iUnion_connectedComponent (K : OpenSubgroup G) :
    (K : Set G) = ⋃ x ∈ (K : Set G), connectedComponent x := by
  simpa [eq_comm] using K.isClopen.biUnion_connectedComponent_eq

end

end OpenSubgroupsAsClopen
