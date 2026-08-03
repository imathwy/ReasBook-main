module

public import Topology_Munkres_2000.Book.Exercise_24_12.LongLine
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.T5
import Topology_Munkres_2000.Book.Exercise_24_12
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Clopen

public section

open Set

namespace LongLine

/-- Companion for Exercise 8.99.5 (1): every point of the long line has an open neighborhood
homeomorphic to an open subset of `EuclideanSpace ℝ (Fin 1)`. -/
theorem locallyEuclideanOneDimensional (x : LongLine) :
    ∃ U : Set LongLine, IsOpen U ∧ x ∈ U ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin 1)), IsOpen V ∧ Nonempty (U ≃ₜ V) := by
  obtain ⟨U, a, b, hU, hxU, hab, ⟨e⟩⟩ := existsIntervalNeighborhood x
  let φ : ℝ ≃ₜ EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toHomeomorph
  exact ⟨U, hU, hxU, φ '' Ioo a b, φ.isOpen_image.mpr isOpen_Ioo,
    ⟨e.trans (φ.image (Ioo a b))⟩⟩

end LongLine

/- Exercise 8.99.5 (2). The long line satisfies the normality condition (iv). -/
#check (inferInstance : NormalSpace LongLine)

universe u v

namespace Set

/-- Helper for Exercise 8.99.5: a locally finite family has only countably many members meeting a
σ-compact subspace. -/
lemma countable_indices_inter_of_locallyFinite_of_sigmaCompact {X : Type u} {ι : Type v}
    [TopologicalSpace X] {w : ι → Set X} {U : Set X} [SigmaCompactSpace U]
    (hw : LocallyFinite w) : {i | (w i ∩ U).Nonempty}.Countable := by
  let I := {i | (w i ∩ U).Nonempty}
  have hlocal : LocallyFinite (fun i : I ↦ ((↑) : U → X) ⁻¹' w i) := by
    -- Restrict the family to the σ-compact subspace and then to the relevant indices.
    exact (hw.preimage_continuous continuous_subtype_val).comp_injective Subtype.val_injective
  have hnonempty : ∀ i : I, (((↑) : U → X) ⁻¹' w i).Nonempty := by
    intro i
    obtain ⟨x, hxw, hxU⟩ := i.2
    exact ⟨⟨x, hxU⟩, hxw⟩
  have hcountable : Countable I := by
    exact Set.countable_univ_iff.mp (hlocal.countable_univ hnonempty)
  exact hcountable.to_set

end Set

namespace Relation

/-- Helper for Exercise 8.99.5: `reachableIn r x n` is the set of vertices reached from `x` by
exactly `n` relation steps. -/
def reachableIn {ι : Type u} (r : ι → ι → Prop) (x : ι) : ℕ → Set ι
  | 0 => {x}
  | n + 1 => ⋃ y ∈ reachableIn r x n, {z | r y z}

/-- Helper for Exercise 8.99.5: reflexive-transitive reachability is countable when every vertex
has countably many immediate successors. -/
lemma countable_reflTransGen_of_countable_successors {ι : Type u} {r : ι → ι → Prop}
    (hr : ∀ x, {y | r x y}.Countable) (x : ι) :
    {y | ReflTransGen r x y}.Countable := by
  have hreachable : ∀ n, (reachableIn r x n).Countable := by
    intro n
    induction n with
    | zero => exact countable_singleton x
    | succ n ih =>
        -- A new layer is a countable union of countable successor sets.
        exact ih.biUnion fun y _ ↦ hr y
  have hsubset : {y | ReflTransGen r x y} ⊆ ⋃ n, reachableIn r x n := by
    intro y hy
    induction hy with
    | refl => exact mem_iUnion.2 ⟨0, mem_singleton x⟩
    | tail hy hyz ih =>
        rcases mem_iUnion.1 ih with ⟨n, hyn⟩
        exact mem_iUnion.2 ⟨n + 1, mem_iUnion.2 ⟨_, mem_iUnion.2 ⟨hyn, hyz⟩⟩⟩
  exact (countable_iUnion hreachable).mono hsubset

end Relation

/-- Helper for Exercise 8.99.5: a connected metrizable space covered pointwise by open,
second-countable, locally compact subspaces is second countable. -/
lemma secondCountable_of_connected_metrizable_open_cover {X : Type u} [TopologicalSpace X]
    [ConnectedSpace X] [TopologicalSpace.MetrizableSpace X] (U : X → Set X)
    (hUopen : ∀ x, IsOpen (U x)) (hUmem : ∀ x, x ∈ U x)
    (hUsc : ∀ x, SecondCountableTopology (U x))
    (hUlc : ∀ x, LocallyCompactSpace (U x)) : SecondCountableTopology X := by
  classical
  letI : ∀ x, SecondCountableTopology (U x) := hUsc
  letI : ∀ x, LocallyCompactSpace (U x) := hUlc
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have hUcover : ⋃ x, U x = univ := iUnion_eq_univ_iff.2 fun x ↦ ⟨x, hUmem x⟩
  obtain ⟨w, hwopen, hwcover, hwlocal, hwsub⟩ :=
    precise_refinement U hUopen hUcover
  let r : X → X → Prop := fun i j ↦ (w i ∩ w j).Nonempty
  have hsuccessors : ∀ i, {j | r i j}.Countable := by
    intro i
    letI : SigmaCompactSpace (U i) :=
      sigmaCompactSpace_of_locallyCompact_secondCountable
    -- Every neighbor of `i` meets the chart containing the refinement member `w i`.
    exact (Set.countable_indices_inter_of_locallyFinite_of_sigmaCompact hwlocal).mono fun j hj ↦ by
      obtain ⟨x, hxi, hxj⟩ := hj
      exact ⟨x, hxj, hwsub i hxi⟩
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨i₀, hxi₀⟩ := mem_iUnion.1 (Set.ext_iff.mp hwcover x₀ |>.mpr (mem_univ x₀))
  let reachable : Set X := {i | Relation.ReflTransGen r i₀ i}
  have hreachable : reachable.Countable :=
    Relation.countable_reflTransGen_of_countable_successors hsuccessors i₀
  let W : Set X := ⋃ i : reachable, w i
  have hWopen : IsOpen W := isOpen_iUnion fun i ↦ hwopen i
  have hWnonempty : W.Nonempty := by
    -- The chosen refinement member belongs to the reachable component.
    exact ⟨x₀, mem_iUnion.2 ⟨⟨i₀, Relation.ReflTransGen.refl⟩, hxi₀⟩⟩
  have hWcompl : Wᶜ = ⋃ i : {i | i ∉ reachable}, w i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.1 (Set.ext_iff.mp hwcover x |>.mpr (mem_univ x))
      have hir : i ∉ reachable := by
        intro hir
        exact hx (mem_iUnion.2 ⟨⟨i, hir⟩, hxi⟩)
      exact mem_iUnion.2 ⟨⟨i, hir⟩, hxi⟩
    · intro hx hxr
      rcases mem_iUnion.1 hx with ⟨i, hxi⟩
      rcases mem_iUnion.1 hxr with ⟨j, hxj⟩
      exact i.2 (Relation.ReflTransGen.tail j.2 ⟨x, hxj, hxi⟩)
  have hWclosed : IsClosed W := by
    rw [← isOpen_compl_iff, hWcompl]
    exact isOpen_iUnion fun i ↦ hwopen i
  have hWuniv : W = univ := IsClopen.eq_univ ⟨hWclosed, hWopen⟩ hWnonempty
  letI : Countable reachable := hreachable.to_subtype
  haveI : ∀ i : reachable, SecondCountableTopology (w i) := fun i ↦
    (Topology.IsEmbedding.inclusion (hwsub i)).secondCountableTopology
  -- The reachable refinement is countable and still covers the connected space.
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun i : reachable ↦ hwopen i) hWuniv

namespace LongLine

/-- Helper for Exercise 8.99.5: every point of the long line lies in an open,
second-countable, locally compact subspace. -/
lemma existsOpenSecondCountableLocallyCompactNeighborhood (x : LongLine) :
    ∃ U : Set LongLine, IsOpen U ∧ x ∈ U ∧
      SecondCountableTopology U ∧ LocallyCompactSpace U := by
  -- Transfer both countability and local compactness through a Euclidean chart.
  obtain ⟨U, hU, hxU, V, hV, ⟨e⟩⟩ := locallyEuclideanOneDimensional x
  haveI : SecondCountableTopology V :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hUsc : SecondCountableTopology U := e.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace V := hV.locallyCompactSpace
  have hUlc : LocallyCompactSpace U := e.locallyCompactSpace_iff.mpr inferInstance
  exact ⟨U, hU, hxU, hUsc, hUlc⟩

/-- Exercise 8.99.5 (3). The long line does not satisfy the metrizability condition (iii). -/
theorem notMetrizable : ¬ TopologicalSpace.MetrizableSpace LongLine := by
  intro hmetrizable
  letI : TopologicalSpace.MetrizableSpace LongLine := hmetrizable
  choose U hUopen hUmem hUsc hUlc using existsOpenSecondCountableLocallyCompactNeighborhood
  -- Connectedness turns the locally countable chart cover into a global countable basis.
  haveI : SecondCountableTopology LongLine :=
    secondCountable_of_connected_metrizable_open_cover U hUopen hUmem hUsc hUlc
  exact LongLine.notSecondCountable inferInstance

end LongLine
