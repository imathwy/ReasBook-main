module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup

public section

open Set

/-- Helper for Example 63.2: a compact set disjoint from a decreasing intersection of closed
sets is already disjoint from one member of the sequence. -/
lemma IsCompact.subset_compl_iInter_of_antitone {X : Type*} [TopologicalSpace X]
    {L : Set X} (hL : IsCompact L) (K : ℕ → Set X) (hKclosed : ∀ n, IsClosed (K n))
    (hK : Antitone K) (hLdisjoint : L ⊆ (⋂ n, K n)ᶜ) :
    ∃ n, L ⊆ (K n)ᶜ := by
  -- The complements form an increasing open cover of the compact set.
  refine hL.elim_directed_cover (fun n ↦ (K n)ᶜ) (fun n ↦ (hKclosed n).isOpen_compl) ?_ ?_
  · simpa only [compl_iInter] using hLdisjoint
  · -- A maximum index contains either of the two earlier complements.
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact compl_subset_compl.mpr (hK (Nat.le_max_left i j))
    · exact compl_subset_compl.mpr (hK (Nat.le_max_right i j))

namespace Path.Homotopy

/-- Helper for Example 63.2: an ambient path homotopy whose image lies in a subset restricts
to a homotopy of chosen subtype-valued boundary paths. -/
lemma codRestrictHomotopic {X : Type*} [TopologicalSpace X] {V : Set X}
    {x₀ x₁ : V} {p₀ p₁ : Path (x₀ : X) (x₁ : X)} {q₀ q₁ : Path x₀ x₁}
    (F : Path.Homotopy p₀ p₁) (hF : ∀ z, F z ∈ V)
    (hq₀ : ∀ t, (q₀ t : X) = p₀ t) (hq₁ : ∀ t, (q₁ t : X) = p₁ t) :
    Path.Homotopic q₀ q₁ := by
  -- Restrict the entire square-valued map to the subset before assembling its boundary laws.
  let G : C(unitInterval × unitInterval, V) :=
    ⟨fun z ↦ ⟨F z, hF z⟩, F.continuous.codRestrict hF⟩
  have hzero (t : unitInterval) : G (0, t) = q₀ t := by
    apply Subtype.ext
    exact (F.apply_zero t).trans (hq₀ t).symm
  have hone (t : unitInterval) : G (1, t) = q₁ t := by
    apply Subtype.ext
    exact (F.apply_one t).trans (hq₁ t).symm
  have hfixed (t s : unitInterval) (hs : s ∈ ({0, 1} : Set unitInterval)) :
      G (t, s) = q₀ s := by
    -- At either endpoint, the ambient homotopy and every subtype path have the fixed endpoint.
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · apply Subtype.ext
      exact (F.source t).trans (congrArg Subtype.val q₀.source).symm
    · apply Subtype.ext
      exact (F.target t).trans (congrArg Subtype.val q₀.target).symm
  -- The restricted continuous map now satisfies the two time faces and the fixed path endpoints.
  refine ⟨{
    toFun := G
    continuous_toFun := G.continuous
    map_zero_left := hzero
    map_one_left := hone
    prop' := hfixed
  }⟩

end Path.Homotopy

namespace AlexanderHornGeometry

/-- Helper for Example 63.2: the connected component of a subset includes continuously into
the subset itself. -/
def connectedComponentInInclusion {X : Type*} [TopologicalSpace X] (F : Set X) (x : X) :
    C({y // y ∈ connectedComponentIn F x}, F) :=
  ⟨fun y ↦ ⟨y, connectedComponentIn_subset F x y.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Helper for Example 63.2: a linked-horn approximation records the uniformly convergent
finite stages and the finite-stage meridian detectors needed by the compactness argument. -/
structure LinkedHornApproximation where
  stageMap : ℕ → StandardSphere 2 → StandardSphere 3
  limitMap : StandardSphere 2 → StandardSphere 3
  stageMap_continuous : ∀ n, Continuous (stageMap n)
  stageMap_tendsto : TendstoUniformly stageMap limitMap Filter.atTop
  limitMap_injective : Function.Injective limitMap
  obstacle : ℕ → Set (StandardSphere 3)
  obstacle_closed : ∀ n, IsClosed (obstacle n)
  obstacle_antitone : Antitone obstacle
  stageBase : ∀ n, {p // p ∈ (obstacle n)ᶜ}
  stageMeridian : ∀ n, Path (stageBase n) (stageBase n)
  stageDetector : ∀ n, C({p // p ∈ (obstacle n)ᶜ}, Circle)
  stageDetector_base : ∀ n, stageDetector n (stageBase n) = 1
  stageMeridian_degree : ∀ n,
    Circle.fundamentalGroupEquivInt
        (FundamentalGroup.mapOfEq (stageDetector n) (stageDetector_base n)
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (stageMeridian n)))) =
      Multiplicative.ofAdd 1
  limitBase : StandardSphere 3
  limitBase_mem : limitBase ∈ (Set.range limitMap)ᶜ
  limitMeridian : Path
    (⟨limitBase, mem_connectedComponentIn limitBase_mem⟩ :
      {p // p ∈ connectedComponentIn (Set.range limitMap)ᶜ limitBase})
    ⟨limitBase, mem_connectedComponentIn limitBase_mem⟩
  nullhomotopy_factors :
    Path.Homotopic limitMeridian
        (Path.refl
          (⟨limitBase, mem_connectedComponentIn limitBase_mem⟩ :
            {p // p ∈ connectedComponentIn (Set.range limitMap)ᶜ limitBase})) →
      ∃ n, Path.Homotopic (stageMeridian n) (Path.refl (stageBase n))

/-- Helper for Example 63.2: a degree-one detector on a complementary component gives a
constant-stage linked-horn approximation. -/
lemma LinkedHornApproximation.nonempty_of_detector
    (f : StandardSphere 2 → StandardSphere 3) (hf : Continuous f)
    (hfinjective : Function.Injective f) (x : StandardSphere 3)
    (hx : x ∈ (Set.range f)ᶜ)
    (μ : Path
      (⟨x, mem_connectedComponentIn hx⟩ :
        {y // y ∈ connectedComponentIn (Set.range f)ᶜ x})
      ⟨x, mem_connectedComponentIn hx⟩)
    (q : C({y // y ∈ (Set.range f)ᶜ}, Circle))
    (hq : q (connectedComponentInInclusion (Set.range f)ᶜ x
      ⟨x, mem_connectedComponentIn hx⟩) = 1)
    (hdegree :
      Circle.fundamentalGroupEquivInt
          (FundamentalGroup.mapOfEq q hq
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk
                (μ.map (connectedComponentInInclusion
                  (Set.range f)ᶜ x).continuous)))) =
        Multiplicative.ofAdd 1) :
    Nonempty LinkedHornApproximation := by
  -- Reuse the same embedded sphere and detected meridian at every finite stage.
  let i := connectedComponentInInclusion (Set.range f)ᶜ x
  let μ' := μ.map i.continuous
  refine ⟨{
    stageMap := fun _ ↦ f
    limitMap := f
    stageMap_continuous := fun _ ↦ hf
    stageMap_tendsto := ?_
    limitMap_injective := hfinjective
    obstacle := fun _ ↦ Set.range f
    obstacle_closed := fun _ ↦ (isCompact_range hf).isClosed
    obstacle_antitone := fun _ _ _ _ h ↦ h
    stageBase := fun _ ↦ i ⟨x, mem_connectedComponentIn hx⟩
    stageMeridian := fun _ ↦ μ'
    stageDetector := fun _ ↦ q
    stageDetector_base := fun _ ↦ hq
    stageMeridian_degree := fun _ ↦ hdegree
    limitBase := x
    limitBase_mem := hx
    limitMeridian := μ
    nullhomotopy_factors := ?_
  }⟩
  · -- A constant sequence of maps converges uniformly to the same map.
    intro u hu
    exact Filter.Eventually.of_forall (fun _ _ ↦ refl_mem_uniformity hu)
  · -- Mapping a hypothetical component nullhomotopy into the full complement supplies stage zero.
    intro hnull
    refine ⟨0, ?_⟩
    have hrefl :
        (Path.refl
          (⟨x, mem_connectedComponentIn hx⟩ :
            {y // y ∈ connectedComponentIn (Set.range f)ᶜ x})).map i.continuous =
          Path.refl (i ⟨x, mem_connectedComponentIn hx⟩) := by
      -- Mapping a constant path is propositionally the constant path at the mapped point.
      ext t
      rfl
    have hmapped := hnull.map i
    rw [hrefl] at hmapped
    exact hmapped

end AlexanderHornGeometry
