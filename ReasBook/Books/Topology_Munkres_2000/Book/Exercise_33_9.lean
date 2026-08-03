module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Topology_Munkres_2000.Book.Proposition_19_3.Comparison
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Topology.WithTopology

public section

universe u v

namespace Pi

/-- Helper for Exercise 33.9: coordinatewise continuous maps are continuous between box
products. -/
private lemma continuous_boxMap {ι : Type u} {X Y : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)]
    (f : (i : ι) → X i → Y i) (hf : ∀ i, Continuous (f i)) :
    @Continuous ((i : ι) → X i) ((i : ι) → Y i)
      (boxTopologicalSpace X) (boxTopologicalSpace Y)
      (fun x i ↦ f i (x i)) := by
  -- Pull a generating target box back coordinatewise.
  rw [continuous_generateFrom_iff]
  intro s hs
  obtain ⟨U, hU, rfl⟩ := (mem_boxBasis s).mp hs
  rw [Set.preimage_pi]
  exact isOpen_box _ fun i ↦ (hU i).preimage (hf i)

/-- Helper for Exercise 33.9: coordinatewise continuous binary maps are jointly continuous on
box products. -/
private lemma continuous_boxMap₂ {ι : Type u} {X Y Z : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → TopologicalSpace (Y i)]
    [(i : ι) → TopologicalSpace (Z i)]
    (f : (i : ι) → X i → Y i → Z i)
    (hf : ∀ i, Continuous (Function.uncurry (f i))) :
    @Continuous (((i : ι) → X i) × ((i : ι) → Y i)) ((i : ι) → Z i)
      (@instTopologicalSpaceProd _ _ (boxTopologicalSpace X) (boxTopologicalSpace Y))
      (boxTopologicalSpace Z)
      (fun p i ↦ f i (p.1 i) (p.2 i)) := by
  classical
  letI : TopologicalSpace ((i : ι) → X i) := boxTopologicalSpace X
  letI : TopologicalSpace ((i : ι) → Y i) := boxTopologicalSpace Y
  -- Reduce continuity to openness of preimages of generating target boxes.
  rw [continuous_generateFrom_iff]
  intro s hs
  obtain ⟨W, hW, rfl⟩ := (mem_boxBasis s).mp hs
  rw [isOpen_prod_iff]
  intro x y hxy
  -- Choose an open coordinate rectangle inside every coordinate preimage.
  choose A B hA hB hxA hyB hAB using fun i ↦
    (isOpen_prod_iff.mp ((hW i).preimage (hf i))) (x i) (y i)
      (hxy i (Set.mem_univ i))
  refine ⟨Set.pi Set.univ A, Set.pi Set.univ B, isOpen_box A hA, isOpen_box B hB,
    ?_, ?_, ?_⟩
  · exact fun i _ ↦ hxA i
  · exact fun i _ ↦ hyB i
  · intro p hp i _
    have hxi : p.1 i ∈ A i := hp.1 i (Set.mem_univ i)
    have hyi : p.2 i ∈ B i := hp.2 i (Set.mem_univ i)
    have hpCoordinate : (p.1 i, p.2 i) ∈ A i ×ˢ B i := ⟨hxi, hyi⟩
    exact hAB i hpCoordinate

/-- Helper for Exercise 33.9: a dependent box product of topological additive groups is a
topological additive group. -/
private lemma boxIsTopologicalAddGroup {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → AddGroup (X i)]
    [(i : ι) → IsTopologicalAddGroup (X i)] :
    @IsTopologicalAddGroup ((i : ι) → X i) (boxTopologicalSpace X) inferInstance := by
  letI : TopologicalSpace ((i : ι) → X i) := boxTopologicalSpace X
  -- Joint continuity of addition is the binary coordinatewise case.
  refine { toContinuousAdd := ?_, toContinuousNeg := ?_ }
  · refine { continuous_add := ?_ }
    exact continuous_boxMap₂ (fun i (x y : X i) ↦ x + y) fun _ ↦ continuous_add
  -- Continuity of negation is the unary coordinatewise case.
  · refine { continuous_neg := ?_ }
    exact continuous_boxMap (fun i (x : X i) ↦ -x) fun _ ↦ continuous_neg

/-- Helper for Exercise 33.9: the raw real box topology is a T₃.₅ topology. -/
private lemma realBoxT35SpaceRaw (J : Type u) :
    @T35Space (J → ℝ) (boxTopologicalSpace fun _ : J ↦ ℝ) := by
  have productT1Space : @T1Space (J → ℝ) Pi.topologicalSpace := inferInstance
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace fun _ : J ↦ ℝ
  letI : IsTopologicalAddGroup (J → ℝ) := boxIsTopologicalAddGroup
  -- The finer box topology inherits T₁ separation from the product topology.
  letI : T1Space (J → ℝ) := t1Space_antitone box_le_product productT1Space
  -- The canonical group uniformity induces the box topology and hence complete regularity.
  letI : UniformSpace (J → ℝ) := IsTopologicalAddGroup.rightUniformSpace (J → ℝ)
  refine { toT0Space := ?_, toCompletelyRegularSpace := ?_ }
  · infer_instance
  · exact UniformSpace.toCompletelyRegularSpace

/-- Exercise 33.9: The box topology on `J → ℝ` is completely regular. -/
instance realBoxT35Space (J : Type u) :
    T35Space (WithTopology (J → ℝ) (boxTopologicalSpace fun _ : J ↦ ℝ)) := by
  -- Transport the raw result across the canonical topology wrapper.
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace fun _ : J ↦ ℝ
  letI : T35Space (J → ℝ) := realBoxT35SpaceRaw J
  have hEmbedding : Topology.IsEmbedding
      (WithTopology.ofTopology (t := boxTopologicalSpace fun _ : J ↦ ℝ)) := by
    refine ⟨⟨?_⟩, WithTopology.ofTopology_injective _⟩
    rw [WithTopology.topology_eq_induced]
  exact hEmbedding.t35Space

end Pi
