module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Order.T5
public import Mathlib.Order.Zorn
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Powerset

public section

open scoped CoveringDimension
open scoped Interval

namespace Set

/-- Helper for Example 50.1: an order-connected component of an open set in a real
subspace is open. -/
lemma isOpen_ordConnectedComponent_of_isOpen {X : Set ℝ} {U : Set X} {x : X}
    (hU : IsOpen U) : IsOpen (ordConnectedComponent U x) := by
  -- A small metric ball around a point of the component stays in the same component.
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y (ordConnectedComponent_subset hy)
  refine ⟨ε, hε, fun z hz ↦ mem_ordConnectedComponent_trans hy ?_⟩
  rw [mem_ordConnectedComponent]
  intro w hw
  apply hball
  rw [Metric.mem_ball] at hz ⊢
  have hdist : dist (y : ℝ) z < ε := by
    simpa only [Subtype.dist_eq, dist_comm] using hz
  simpa only [Subtype.dist_eq, dist_comm] using
    (Real.dist_le_of_mem_uIcc left_mem_uIcc hw).trans_lt hdist

/-- Helper for Example 50.1: every open cover of a real subspace has a point-finite
open refinement by order-connected sets. -/
lemma existsPointFiniteOrdConnectedOpenRefinement (X : Set ℝ) (𝒜 : Set (Set X))
    (hopen : ∀ U ∈ 𝒜, IsOpen U) (hcover : ⋃₀ 𝒜 = univ) :
    ∃ 𝒱 : Set (Set X), IsOpenRefinement 𝒱 𝒜 ∧ ⋃₀ 𝒱 = univ ∧
      (∀ V ∈ 𝒱, V.OrdConnected) ∧
      ∀ x : X, {V ∈ 𝒱 | x ∈ V}.Finite := by
  classical
  -- First take a locally finite open refinement indexed by an auxiliary type.
  let U : 𝒜 → Set X := fun A ↦ A
  have hUopen : ∀ A, IsOpen (U A) := fun A ↦ hopen A A.property
  have hUcover : ⋃ A, U A = univ := by
    rw [← sUnion_range, Subtype.range_coe, hcover]
  obtain ⟨β, V, hVopen, hVcover, hVfinite, hVrefines⟩ :=
    ParacompactSpace.locallyFinite_refinement 𝒜 U hUopen hUcover
  -- Split each refining set into its order-connected components.
  let 𝒱 : Set (Set X) :=
    {C | ∃ b x, x ∈ V b ∧ C = ordConnectedComponent (V b) x}
  refine ⟨𝒱, ?_, ?_, ?_, ?_⟩
  · rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      rintro C ⟨b, x, hx, rfl⟩
      obtain ⟨A, hsub⟩ := hVrefines b
      exact ⟨U A, A.property, ordConnectedComponent_subset.trans hsub⟩
    · rintro C ⟨b, x, hx, rfl⟩
      exact isOpen_ordConnectedComponent_of_isOpen (hVopen b)
  · apply Subset.antisymm (subset_univ _)
    intro x _
    rw [mem_sUnion]
    have hxunion : x ∈ ⋃ b, V b := by rw [hVcover]; trivial
    obtain ⟨b, hxb⟩ := mem_iUnion.mp hxunion
    exact ⟨ordConnectedComponent (V b) x, ⟨b, x, hxb, rfl⟩,
      self_mem_ordConnectedComponent.2 hxb⟩
  · rintro C ⟨b, x, hx, rfl⟩
    infer_instance
  · intro x
    -- At a point there is at most one component from each original refining set.
    apply (hVfinite.point_finite x).image (fun b ↦ ordConnectedComponent (V b) x) |>.subset
    rintro C ⟨hC, hxC⟩
    obtain ⟨b, y, hy, rfl⟩ := hC
    have hxb : x ∈ V b := ordConnectedComponent_subset hxC
    refine ⟨b, hxb, ?_⟩
    exact (ordConnectedComponent_eq hxC).symm

/-- Helper for Example 50.1: a chain of nonempty subsets of a fixed finite
nonempty set has nonempty intersection. -/
lemma sInter_nonempty_of_isChain_of_finite {α : Type*} {S : Set α}
    (hS : S.Finite) (hSnonempty : S.Nonempty) {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) (hcS : ∀ T ∈ c, T ⊆ S)
    (hne : ∀ T ∈ c, T.Nonempty) : (⋂₀ c).Nonempty := by
  classical
  by_cases hc_empty : c.Nonempty
  · -- A finite chain has a minimal member, which equals its total intersection.
    let d : Set (Set α) := {T | T ∈ c ∧ T ⊆ S}
    have hd_finite : d.Finite := (hS.powerset).subset fun T hT ↦ hT.2
    have hd_nonempty : d.Nonempty := by
      obtain ⟨T, hT⟩ := hc_empty
      exact ⟨T, hT, hcS T hT⟩
    obtain ⟨M, hM⟩ := hd_finite.exists_minimal hd_nonempty
    obtain ⟨hMc, hMS⟩ := hM.1
    obtain ⟨x, hxM⟩ := hne M hMc
    refine ⟨x, ?_⟩
    rw [mem_sInter]
    intro T hTc
    have hTd : T ∈ d := ⟨hTc, hcS T hTc⟩
    rcases hc.total hMc hTc with hMT | hTM
    · exact hMT hxM
    · have hEq : M = T := le_antisymm (hM.2 hTd hTM) hTM
      exact hEq ▸ hxM
  · -- The intersection of an empty family is universal.
    rw [not_nonempty_iff_eq_empty.mp hc_empty, sInter_empty]
    exact ⟨hSnonempty.choose, mem_univ _⟩

/-- Helper for Example 50.1: a point-finite cover has an inclusion-minimal
subcover. -/
lemma existsIrredundantSubcover_of_pointFinite {Y : Type*} (𝒱 : Set (Set Y))
    (hcover : ⋃₀ 𝒱 = univ)
    (hfinite : ∀ y : Y, {V ∈ 𝒱 | y ∈ V}.Finite) :
    ∃ 𝒲 ⊆ 𝒱, ⋃₀ 𝒲 = univ ∧ ∀ W ∈ 𝒲, ⋃₀ (𝒲 \ {W}) ≠ univ := by
  classical
  let Covers : Set (Set (Set Y)) := {𝒲 | 𝒲 ⊆ 𝒱 ∧ ⋃₀ 𝒲 = univ}
  obtain ⟨𝒲, h𝒲min⟩ := zorn_superset Covers (fun c hcovers hchain ↦ by
    by_cases hc : c.Nonempty
    · refine ⟨⋂₀ c, ?_, ?_⟩
      · constructor
        · obtain ⟨𝒞, h𝒞⟩ := hc
          exact (sInter_subset_of_mem h𝒞).trans (hcovers h𝒞).1
        · apply Subset.antisymm (subset_univ _)
          intro y _
          let I : Set (Set Y) := {V ∈ 𝒱 | y ∈ V}
          have hI_finite : I.Finite := hfinite y
          have hI_nonempty : I.Nonempty := by
            have hy : y ∈ ⋃₀ 𝒱 := by rw [hcover]; trivial
            obtain ⟨V, hV, hyV⟩ := mem_sUnion.mp hy
            exact ⟨V, hV, hyV⟩
          let d : Set (Set (Set Y)) := (fun 𝒞 ↦ 𝒞 ∩ I) '' c
          have hd_chain : IsChain (· ⊆ ·) d := by
            rintro _ ⟨𝒞, h𝒞, rfl⟩ _ ⟨𝒟, h𝒟, rfl⟩ hne
            rcases hchain.total h𝒞 h𝒟 with hCD | hDC
            · exact Or.inl (inter_subset_inter_left I hCD)
            · exact Or.inr (inter_subset_inter_left I hDC)
          have hd_sub : ∀ T ∈ d, T ⊆ I := by
            rintro _ ⟨𝒞, h𝒞, rfl⟩
            exact inter_subset_right
          have hd_nonempty : ∀ T ∈ d, T.Nonempty := by
            rintro _ ⟨𝒞, h𝒞, rfl⟩
            have hycover : y ∈ ⋃₀ 𝒞 := by rw [(hcovers h𝒞).2]; trivial
            obtain ⟨V, hV𝒞, hyV⟩ := mem_sUnion.mp hycover
            exact ⟨V, hV𝒞, (hcovers h𝒞).1 hV𝒞, hyV⟩
          obtain ⟨V, hV⟩ :=
            sInter_nonempty_of_isChain_of_finite hI_finite hI_nonempty hd_chain hd_sub hd_nonempty
          rw [mem_sInter] at hV
          have hVI : V ∈ I := by
            obtain ⟨𝒞, h𝒞⟩ := hc
            exact (hV (𝒞 ∩ I) ⟨𝒞, h𝒞, rfl⟩).2
          rw [mem_sUnion]
          refine ⟨V, ?_, hVI.2⟩
          rw [mem_sInter]
          intro 𝒞 h𝒞
          exact (hV (𝒞 ∩ I) ⟨𝒞, h𝒞, rfl⟩).1
      · intro 𝒞 h𝒞
        exact sInter_subset_of_mem h𝒞
    · refine ⟨𝒱, ⟨Subset.rfl, hcover⟩, ?_⟩
      intro 𝒞 h𝒞
      exact (hc ⟨𝒞, h𝒞⟩).elim)
  -- Minimality says that deleting any member destroys coverage.
  refine ⟨𝒲, h𝒲min.1.1, h𝒲min.1.2, ?_⟩
  intro W hW hremove
  have hsmaller : 𝒲 \ {W} ∈ Covers :=
    ⟨sdiff_subset.trans h𝒲min.1.1, hremove⟩
  have hback : 𝒲 ⊆ 𝒲 \ {W} := h𝒲min.2 hsmaller sdiff_subset
  exact (hback hW).2 rfl

/-- Helper for Example 50.1: among three points in a linear order, one lies between
a fourth point and one of the other two. -/
lemma one_mem_uIcc_of_three (x a b c : Y) [LinearOrder Y] :
    a ∈ [[x, b]] ∨ b ∈ [[x, a]] ∨ a ∈ [[x, c]] ∨
      c ∈ [[x, a]] ∨ b ∈ [[x, c]] ∨ c ∈ [[x, b]] := by
  -- Split according to which side of `x` contains two of the three points.
  simp only [mem_uIcc]
  rcases le_total x a with hxa | hax
  · rcases le_total x b with hxb | hbx
    · rcases le_total a b with hab | hba
      · exact Or.inl (Or.inl ⟨hxa, hab⟩)
      · exact Or.inr (Or.inl (Or.inl ⟨hxb, hba⟩))
    · rcases le_total x c with hxc | hcx
      · rcases le_total a c with hac | hca
        · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨hxa, hac⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨hxc, hca⟩))))
      · rcases le_total b c with hbc | hcb
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hbc, hcx⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨hcb, hbx⟩)))))
  · rcases le_total x b with hxb | hbx
    · rcases le_total x c with hxc | hcx
      · rcases le_total b c with hbc | hcb
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨hxb, hbc⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hxc, hcb⟩)))))
      · rcases le_total a c with hac | hca
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨hac, hcx⟩))))
        · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hca, hax⟩)))
    · rcases le_total a b with hab | hba
      · exact Or.inr (Or.inl (Or.inr ⟨hab, hbx⟩))
      · exact Or.inl (Or.inr ⟨hba, hax⟩)

/-- Helper for Example 50.1: an irredundant cover of a linear order by
order-connected sets has point multiplicity at most two. -/
lemma hasOrderLE_two_of_irredundant_ordConnected_cover {Y : Type*} [LinearOrder Y]
    (𝒲 : Set (Set Y)) (hcover : ⋃₀ 𝒲 = univ)
    (hord : ∀ W ∈ 𝒲, W.OrdConnected)
    (hirr : ∀ W ∈ 𝒲, ⋃₀ (𝒲 \ {W}) ≠ univ) : 𝒲.HasOrderLE 2 := by
  classical
  -- If three members meet at `x`, irredundance supplies a private point for each.
  rw [hasOrderLE_iff]
  intro x
  by_contra hnot
  have hthree : (3 : ℕ∞) ≤ {W ∈ 𝒲 | x ∈ W}.encard := by
    calc
      (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ {W ∈ 𝒲 | x ∈ W}.encard :=
        (ENat.add_one_le_iff (by simp : (2 : ℕ∞) ≠ ⊤)).mpr (lt_of_not_ge hnot)
  obtain ⟨𝒯, h𝒯sub, h𝒯card⟩ := exists_subset_encard_eq hthree
  obtain ⟨A, B, C, hAB, hAC, hBC, rfl⟩ := encard_eq_three.mp h𝒯card
  have hA : A ∈ 𝒲 ∧ x ∈ A := h𝒯sub (by simp)
  have hB : B ∈ 𝒲 ∧ x ∈ B := h𝒯sub (by simp)
  have hC : C ∈ 𝒲 ∧ x ∈ C := h𝒯sub (by simp)
  obtain ⟨a, ha⟩ := (ne_univ_iff_exists_notMem _).mp (hirr A hA.1)
  obtain ⟨b, hb⟩ := (ne_univ_iff_exists_notMem _).mp (hirr B hB.1)
  obtain ⟨c, hc⟩ := (ne_univ_iff_exists_notMem _).mp (hirr C hC.1)
  have haA : a ∈ A := by
    have haCover : a ∈ ⋃₀ 𝒲 := by rw [hcover]; trivial
    obtain ⟨W, hW, haW⟩ := mem_sUnion.mp haCover
    have hWA : W = A := by
      by_contra hne
      exact ha ⟨W, ⟨hW, by simpa using hne⟩, haW⟩
    simpa [hWA] using haW
  have hbB : b ∈ B := by
    have hbCover : b ∈ ⋃₀ 𝒲 := by rw [hcover]; trivial
    obtain ⟨W, hW, hbW⟩ := mem_sUnion.mp hbCover
    have hWB : W = B := by
      by_contra hne
      exact hb ⟨W, ⟨hW, by simpa using hne⟩, hbW⟩
    simpa [hWB] using hbW
  have hcC : c ∈ C := by
    have hcCover : c ∈ ⋃₀ 𝒲 := by rw [hcover]; trivial
    obtain ⟨W, hW, hcW⟩ := mem_sUnion.mp hcCover
    have hWC : W = C := by
      by_contra hne
      exact hc ⟨W, ⟨hW, by simpa using hne⟩, hcW⟩
    simpa [hWC] using hcW
  -- One private point lies in an interval contained in a different cover member.
  rcases one_mem_uIcc_of_three x a b c with hab | hba | hac | hca | hbc | hcb
  · exact ha ⟨B, ⟨hB.1, hAB.symm⟩, (hord B hB.1).uIcc_subset hB.2 hbB hab⟩
  · exact hb ⟨A, ⟨hA.1, hAB⟩, (hord A hA.1).uIcc_subset hA.2 haA hba⟩
  · exact ha ⟨C, ⟨hC.1, hAC.symm⟩, (hord C hC.1).uIcc_subset hC.2 hcC hac⟩
  · exact hc ⟨A, ⟨hA.1, hAC⟩, (hord A hA.1).uIcc_subset hA.2 haA hca⟩
  · exact hb ⟨C, ⟨hC.1, hBC.symm⟩, (hord C hC.1).uIcc_subset hC.2 hcC hbc⟩
  · exact hc ⟨B, ⟨hB.1, hBC⟩, (hord B hB.1).uIcc_subset hB.2 hbB hcb⟩

end Set
