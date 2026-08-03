module

public import Topology_Munkres_2000.Book.Definition_80_1.Covering
public import Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
import all Topology_Munkres_2000.Book.Definition_80_1.Covering
import Topology_Munkres_2000.Book.Definition_9_0_2
import Topology_Munkres_2000.Book.Lemma_80_4
import Topology_Munkres_2000.Book.Theorem_82_1

public section

universe u

/-- Helper for Corollary 82.2: an injective group homomorphism with trivial range has a
subsingleton domain. -/
private lemma MonoidHom.subsingleton_of_injective_range_eq_bot
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hinjective : Function.Injective f) (hrange : f.range = ⊥) : Subsingleton G := by
  -- Rewrite the trivial-range hypothesis as triviality of the homomorphism itself.
  rw [MonoidHom.range_eq_bot_iff] at hrange
  constructor
  intro x y
  -- Injectivity reduces equality in the domain to equality of two values of the trivial map.
  apply hinjective
  rw [hrange]
  simp only [MonoidHom.one_apply]

/-- Helper for Corollary 82.2: a covering whose induced fundamental-group subgroup is
trivial has a subsingleton fundamental group upstairs. -/
private lemma IsCoveringMap.fundamentalGroup_subsingleton_of_fundamentalGroupMapRange_eq_bot
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsCoveringMap p) {e₀ : E} {b₀ : B} (h₀ : p e₀ = b₀)
    (hrange : hp.fundamentalGroupMapRange h₀ = ⊥) :
    Subsingleton (FundamentalGroup E e₀) := by
  -- Expose the range definition once to connect the covering API to the algebraic helper.
  have hmapRange :
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ h₀).range = ⊥ := by
    simpa only [IsCoveringMap.fundamentalGroupMapRange] using hrange
  -- The induced homomorphism is injective for every covering map.
  exact MonoidHom.subsingleton_of_injective_range_eq_bot
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ h₀)
    (hp.fundamentalGroupMap_injective h₀) hmapRange

/-- Helper for Corollary 82.2: a connected covering inducing the trivial subgroup is a
universal covering map. -/
private lemma ConnectedCovering.isUniversalCoveringMap_of_fundamentalGroupMapRange_eq_bot
    {B : Type u} [TopologicalSpace B] (C : ConnectedCovering.{u} B)
    {b₀ : B} (e₀ : C.Total) (h₀ : C.proj e₀ = b₀)
    (hrange : C.isCoveringMap.fundamentalGroupMapRange h₀ = ⊥) :
    IsUniversalCoveringMap C.proj := by
  -- Triviality of the induced subgroup and injectivity make the upstairs fundamental group
  -- subsingleton.
  have hfundamentalGroup : Subsingleton (FundamentalGroup C.Total e₀) :=
    C.isCoveringMap.fundamentalGroup_subsingleton_of_fundamentalGroupMapRange_eq_bot
      h₀ hrange
  letI : PathConnectedSpace C.Total := C.pathConnectedSpace
  -- For a path-connected total space, this algebraic condition is simple connectedness.
  have hsimplyConnected : SimplyConnectedSpace C.Total :=
    (simplyConnectedSpace_iff_subsingleton_fundamentalGroup C.Total e₀).mpr
      hfundamentalGroup
  -- Reassemble the three fields of a universal covering map.
  unfold IsUniversalCoveringMap
  exact ⟨C.isCoveringMap, C.surjective, hsimplyConnected⟩

/-- A space has a universal covering space in the Chapter 13 convention when the total
and base spaces are path connected and locally path connected. -/
def HasUniversalCover (B : Type u) [TopologicalSpace B] : Prop :=
  ∃ C : UniversalCovering.{u} B,
    PathConnectedSpace C.Total ∧ LocallyPathConnectedSpace C.Total ∧
      PathConnectedSpace B ∧ LocallyPathConnectedSpace B

/-- Corollary 82.2: A space has a universal covering space if and only if it is path
connected, locally path connected, and semilocally simply connected. -/
theorem hasUniversalCover_iff {B : Type u} [TopologicalSpace B] :
    HasUniversalCover B ↔ PathConnectedSpace B ∧ LocallyPathConnectedSpace B ∧
      SemilocallySimplyConnectedSpace B := by
  constructor
  · rintro ⟨C, htotalPathConnected, htotalLocallyPathConnected,
      hbasePathConnected, hbaseLocallyPathConnected⟩
    -- The bundled universal cover supplies the simply connected, surjective covering needed
    -- by Lemma 80.4; the remaining two conclusions are part of `HasUniversalCover`.
    refine ⟨hbasePathConnected, hbaseLocallyPathConnected, ?_⟩
    letI : SimplyConnectedSpace C.Total := C.simplyConnectedSpace
    exact C.isCoveringMap.semilocallySimplyConnectedSpace_of_surjective C.surjective
  · rintro ⟨hbasePathConnected, hbaseLocallyPathConnected,
      hbaseSemilocallySimplyConnected⟩
    -- Install the three base-space hypotheses required by the classification theorem.
    letI : PathConnectedSpace B := hbasePathConnected
    letI : LocallyPathConnectedSpace B := hbaseLocallyPathConnected
    letI : SemilocallySimplyConnectedSpace B := hbaseSemilocallySimplyConnected
    let b₀ : B := Classical.choice hbasePathConnected.nonempty
    -- Realize the bottom subgroup as the subgroup induced by a connected covering.
    obtain ⟨C, e₀, h₀, hrange⟩ :=
      ConnectedCovering.exists_fundamentalGroupMapRange_eq b₀ ⊥
    have huniversal : IsUniversalCoveringMap C.proj :=
      C.isUniversalCoveringMap_of_fundamentalGroupMapRange_eq_bot e₀ h₀ hrange
    -- Package this map and retain the connectedness data demanded by the chapter convention.
    refine ⟨UniversalCovering.of C.Total C.proj huniversal, ?_⟩
    exact ⟨C.pathConnectedSpace, C.locallyPathConnectedSpace,
      hbasePathConnected, hbaseLocallyPathConnected⟩
