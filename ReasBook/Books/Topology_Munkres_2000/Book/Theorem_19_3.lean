module

public import Topology_Munkres_2000.Book.Theorem_19_3.BoxTopology

universe u v

public section

namespace Pi

/-- Helper for Theorem 19.3: coordinatewise continuous maps pull ambient box
generators back to domain box generators. -/
private lemma preimage_boxBasis_piMap_subset {ι : Type u} {A : ι → Type v} {B : ι → Type w}
    [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)]
    (f : (i : ι) → A i → B i) (hf : ∀ i, Continuous (f i)) :
    Set.preimage (Pi.map f) '' boxBasis B ⊆ boxBasis A := by
  -- Expose an ambient box and pull each coordinate set back separately.
  rintro _ ⟨S, hS, rfl⟩
  obtain ⟨U, hU, rfl⟩ := (mem_boxBasis S).mp hS
  refine (mem_boxBasis _).mpr
    ⟨fun i ↦ f i ⁻¹' U i, fun i ↦ Continuous.isOpen_preimage (hf i) (U i) (hU i), ?_⟩
  exact Set.preimage_pi Set.univ U f

/-- Helper for Theorem 19.3: coordinatewise inducing maps lift every domain box
generator to an ambient box generator. -/
private lemma boxBasis_subset_preimage_piMap {ι : Type u} {A : ι → Type v} {B : ι → Type w}
    [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)]
    (f : (i : ι) → A i → B i) (hf : ∀ i, Topology.IsInducing (f i)) :
    boxBasis A ⊆ Set.preimage (Pi.map f) '' boxBasis B := by
  classical
  -- Lift all coordinate-open sets through the inducing maps at once.
  rintro S hS
  obtain ⟨U, hU, rfl⟩ := (mem_boxBasis S).mp hS
  choose V hVopen hVpre using fun i ↦ (hf i).isOpen_iff.mp (hU i)
  refine ⟨Set.pi Set.univ V, (mem_boxBasis _).mpr ⟨V, hVopen, rfl⟩, ?_⟩
  -- The lifted ambient box has exactly the original coordinatewise preimage.
  calc
    Pi.map f ⁻¹' Set.pi Set.univ V = Set.pi Set.univ (fun i ↦ f i ⁻¹' V i) :=
      Set.preimage_pi Set.univ V f
    _ = Set.pi Set.univ U := congrArg (Set.pi Set.univ) (funext hVpre)

/-- Helper for Theorem 19.3: coordinatewise inducing maps identify the pulled-back
ambient box generators with the domain box generators. -/
private lemma preimage_boxBasis_piMap {ι : Type u} {A : ι → Type v} {B : ι → Type w}
    [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)]
    (f : (i : ι) → A i → B i) (hf : ∀ i, Topology.IsInducing (f i)) :
    Set.preimage (Pi.map f) '' boxBasis B = boxBasis A := by
  -- Combine continuity for one inclusion with openness lifting for the other.
  apply Set.Subset.antisymm
  · exact preimage_boxBasis_piMap_subset f fun i ↦ (hf i).continuous
  · exact boxBasis_subset_preimage_piMap f hf

/-- Theorem 19.3 (1): the product of coordinate subspaces has the topology induced
by its coordinatewise inclusion when both products carry the box topology. -/
theorem subtypeVal_box {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (A : (i : ι) → Set (X i)) :
    TopologicalSpace.induced
        (Pi.map fun i ↦ (Subtype.val : A i → X i))
        (boxTopologicalSpace X) =
      boxTopologicalSpace (fun i ↦ A i) := by
  -- Pull induction through the generated box topology, then identify its generators.
  rw [induced_generateFrom_eq]
  rw [preimage_boxBasis_piMap (fun i ↦ (Subtype.val : A i → X i)) fun _ ↦ .subtypeVal]

/-- Theorem 19.3 (2): the coordinatewise inclusion of the product of subspaces
is inducing when both products carry the product topology. -/
theorem subtypeVal_product {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (A : (i : ι) → Set (X i)) :
    Topology.IsInducing (Pi.map fun i ↦ (Subtype.val : A i → X i)) :=
  .piMap fun _ ↦ .subtypeVal

end Pi
