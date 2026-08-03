module

public import Topology_Munkres_2000.Book.Theorem_82_1
import Topology_Munkres_2000.Book.Definition_9_0_2
import Topology_Munkres_2000.Book.Lemma_80_4

public section

universe u

open scoped Pointwise

namespace Subgroup

/-- Helper for Remark 82.2: a subgroup represents the bottom conjugacy class exactly when it
is the bottom subgroup. -/
private lemma mkConjClass_eq_bot_iff {G : Type*} [Group G] (H : Subgroup G) :
    mkConjClass H = mkConjClass (⊥ : Subgroup G) ↔ H = ⊥ := by
  constructor
  · intro hclass
    -- A conjugating automorphism preserves the bottom subgroup, so cancellation recovers `H`.
    obtain ⟨g, hg⟩ := Subgroup.isConj_iff_exists.mp
      (Subgroup.mkConjClass_eq_iff.mp hclass)
    exact smul_left_cancel (MulAut.conj g)
      (hg.trans (Subgroup.smul_bot (MulAut.conj g)).symm)
  · intro hH
    -- Equal subgroups determine the same quotient representative.
    subst H
    rfl

end Subgroup

namespace MonoidHom

/-- Helper for Remark 82.2: an injective group homomorphism with bottom range has a
subsingleton domain. -/
private lemma subsingleton_of_injective_range_eq_bot
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hinjective : Function.Injective f) (hrange : f.range = ⊥) : Subsingleton G := by
  -- Bottom range identifies the homomorphism with the constant-one homomorphism.
  rw [MonoidHom.range_eq_bot_iff] at hrange
  constructor
  intro x y
  -- Injectivity reduces equality in the domain to equality of constant images.
  apply hinjective
  rw [hrange]
  simp only [MonoidHom.one_apply]

end MonoidHom

namespace IsCoveringMap

/-- Helper for Remark 82.2: a covering with bottom induced subgroup has a subsingleton
fundamental group upstairs. -/
private lemma fundamentalGroup_subsingleton_of_fundamentalGroupMapRange_eq_bot
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsCoveringMap p) {e₀ : E} {b₀ : B} (h₀ : p e₀ = b₀)
    (hrange : hp.fundamentalGroupMapRange h₀ = ⊥) :
    Subsingleton (FundamentalGroup E e₀) := by
  -- Expose the canonical range once, then combine bottom range with covering-map injectivity.
  have hmapRange :
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ h₀).range = ⊥ := by
    simpa only [IsCoveringMap.fundamentalGroupMapRange] using hrange
  exact MonoidHom.subsingleton_of_injective_range_eq_bot
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ h₀)
    (hp.fundamentalGroupMap_injective h₀) hmapRange

end IsCoveringMap

namespace ConnectedCovering

/-- Helper for Remark 82.2: a bottom connected-covering subgroup class gives bottom induced
fundamental-group range at every chosen point over the base point. -/
private lemma fundamentalGroupMapRange_eq_bot_of_subgroupClass_eq_bot
    {B : Type u} [TopologicalSpace B] (C : ConnectedCovering.{u} B)
    {b₀ : B} (e₀ : C.Total) (h₀ : C.proj e₀ = b₀)
    (hclass : C.subgroupClass b₀ =
      Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀))) :
    C.isCoveringMap.fundamentalGroupMapRange h₀ = ⊥ := by
  -- Compute the public subgroup class using the selected point in the fiber.
  have hrangeClass :
      Subgroup.mkConjClass
          (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ h₀).range =
        Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀)) :=
    (C.subgroupClassAt_eq_mkConjClass b₀ e₀ h₀).symm.trans
      ((C.subgroupClass_mk b₀ e₀ h₀).symm.trans hclass)
  -- The bottom conjugacy class has only the bottom subgroup as a representative.
  have hmapRange :
      (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ h₀).range = ⊥ :=
    (Subgroup.mkConjClass_eq_bot_iff
      (FundamentalGroup.mapOfEq
        ⟨C.proj, C.isCoveringMap.continuous⟩ h₀).range).mp hrangeClass
  simpa only [IsCoveringMap.fundamentalGroupMapRange] using hmapRange

/-- Helper for Remark 82.2: a connected covering classified by the bottom subgroup has simply
connected total space. -/
private lemma simplyConnectedSpace_of_subgroupClass_eq_bot
    {B : Type u} [TopologicalSpace B] (C : ConnectedCovering.{u} B) (b₀ : B)
    (hclass : C.subgroupClass b₀ =
      Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀))) :
    SimplyConnectedSpace C.Total := by
  -- Choose a point in the fiber and turn the bottom class into a bottom induced range.
  obtain ⟨e₀, h₀⟩ := C.surjective b₀
  have hrange : C.isCoveringMap.fundamentalGroupMapRange h₀ = ⊥ :=
    C.fundamentalGroupMapRange_eq_bot_of_subgroupClass_eq_bot e₀ h₀ hclass
  have hfundamentalGroup : Subsingleton (FundamentalGroup C.Total e₀) :=
    C.isCoveringMap.fundamentalGroup_subsingleton_of_fundamentalGroupMapRange_eq_bot
      h₀ hrange
  letI : PathConnectedSpace C.Total := C.pathConnectedSpace
  -- On the connected total space, triviality of one fundamental group is simple connectedness.
  exact (simplyConnectedSpace_iff_subsingleton_fundamentalGroup C.Total e₀).mpr
    hfundamentalGroup

/-- Remark 82.2. For a path-connected, locally path-connected based space `B`, semilocal
simple connectedness is equivalent to surjectivity of the classification of connected
coverings by conjugacy classes of subgroups of `π₁(B, b₀)`. -/
theorem semilocallySimplyConnected_iff_classificationSurjective {B : Type u}
    [TopologicalSpace B] [PathConnectedSpace B] [LocallyPathConnectedSpace B] (b₀ : B) :
    SemilocallySimplyConnectedSpace B ↔ IsClassificationSurjective.{u} b₀ := by
  constructor
  · intro hsemilocallySimplyConnected
    -- Theorem 82.1 realizes every subgroup once semilocal simple connectedness is installed.
    letI : SemilocallySimplyConnectedSpace B := hsemilocallySimplyConnected
    exact ConnectedCovering.isClassificationSurjective b₀
  · intro hsurjective
    -- Realize the bottom conjugacy class and choose a concrete connected-covering representative.
    have hrealizesEveryClass :=
      (ConnectedCovering.isClassificationSurjective_iff b₀).mp hsurjective
    obtain ⟨coveringClass, hclassification⟩ :=
      hrealizesEveryClass
        (Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀)))
    obtain ⟨C, hrepresentative⟩ := Quotient.exists_rep coveringClass
    have hclassificationRepresentative :
        ConnectedCovering.classification B b₀
            (Quotient.mk (ConnectedCovering.equivalentSetoid B) C) =
          Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀)) :=
      (congrArg (ConnectedCovering.classification B b₀) hrepresentative).trans
        hclassification
    have hsubgroupClass :
        C.subgroupClass b₀ =
          Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀)) :=
      (ConnectedCovering.classification_mk C b₀).symm.trans
        hclassificationRepresentative
    -- The bottom-class representative is simply connected, so Lemma 80.4 applies to its map.
    letI : SimplyConnectedSpace C.Total :=
      C.simplyConnectedSpace_of_subgroupClass_eq_bot b₀ hsubgroupClass
    exact C.isCoveringMap.semilocallySimplyConnectedSpace_of_surjective C.surjective

end ConnectedCovering
