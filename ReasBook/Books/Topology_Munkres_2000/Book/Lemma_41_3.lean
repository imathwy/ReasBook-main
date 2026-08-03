module

public import Mathlib.Topology.Compactness.Paracompact
public import Topology_Munkres_2000.Book.Definition_39_4.Refinement
public import Topology_Munkres_2000.Book.Definition_6_0_3.CountablyLocallyFinite
public import Topology_Munkres_2000.Book.Lemma_39_1.LocallyFinite

public section

universe u

open scoped Topology

/-- Helper for Lemma 41.3: every locally finite collection is countably locally finite. -/
private lemma locallyFiniteCollection_countablyLocallyFinite
    {X : Type u} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.LocallyFinite) : 𝒜.CountablyLocallyFinite := by
  -- Put the whole collection in the zeroth layer and leave all later layers empty.
  rw [Set.countablyLocallyFinite_iff]
  refine ⟨fun n ↦ if n = 0 then 𝒜 else ∅, ?_, ?_⟩
  · ext U
    simp
  · intro n
    by_cases hn : n = 0
    · simpa [hn] using h𝒜
    · simp [hn, locallyFinite_of_finite]

/-- Helper for Lemma 41.3: regular shrinking and pointwise closure turn locally finite
refinements into locally finite closed refinements. -/
private lemma exists_closedLocallyFiniteRefinement_of_locallyFiniteRefinement
    {X : Type u} [TopologicalSpace X] [RegularSpace X]
    (h : ∀ 𝒜 : Set (Set X),
      (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.LocallyFinite) :
    ∀ 𝒜 : Set (Set X),
      (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsClosedRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.LocallyFinite := by
  intro 𝒜 h𝒜_open h𝒜_cover
  classical
  let 𝒰 : Set (Set X) :=
    {U | IsOpen U ∧ ∃ A ∈ 𝒜, closure U ⊆ A}
  have h𝒰_open : ∀ U ∈ 𝒰, IsOpen U := by
    intro U hU
    exact hU.1
  have h𝒰_cover : ⋃₀ 𝒰 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx_union : x ∈ ⋃₀ 𝒜 := by
      rw [h𝒜_cover]
      exact Set.mem_univ x
    obtain ⟨A, hA𝒜, hxA⟩ := Set.mem_sUnion.mp hx_union
    have hA_nhds : A ∈ 𝓝 x := (h𝒜_open A hA𝒜).mem_nhds hxA
    obtain ⟨U, ⟨hxU, hU_open⟩, hU_closure⟩ :=
      (hasBasis_opens_closure x).mem_iff.mp hA_nhds
    exact Set.mem_sUnion_of_mem hxU ⟨hU_open, A, hA𝒜, hU_closure⟩
  obtain ⟨𝒞, h𝒞_refines, h𝒞_cover, h𝒞_finite⟩ := h 𝒰 h𝒰_open h𝒰_cover
  refine ⟨closure '' 𝒞, ?_, ?_, h𝒞_finite.closure_image⟩
  · -- Each closure stays inside the original cover member selected by the shrinking cover.
    rw [isClosedRefinement_iff, isRefinement_iff]
    constructor
    · rintro D ⟨C, hC𝒞, rfl⟩
      obtain ⟨U, hU𝒰, hCU⟩ := h𝒞_refines.subset_of_mem hC𝒞
      obtain ⟨_, A, hA𝒜, hUA⟩ := hU𝒰
      exact ⟨A, hA𝒜, (closure_mono hCU).trans hUA⟩
    · rintro D ⟨C, hC𝒞, rfl⟩
      exact isClosed_closure
  · -- The closure family still covers because every original member lies in its closure.
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx_union : x ∈ ⋃₀ 𝒞 := by
      rw [h𝒞_cover]
      exact Set.mem_univ x
    obtain ⟨C, hC𝒞, hxC⟩ := Set.mem_sUnion.mp hx_union
    exact Set.mem_sUnion_of_mem (subset_closure hxC) ⟨C, hC𝒞, rfl⟩

/-- Helper for Lemma 41.3: trim a member of a numbered layer by all earlier layers. -/
private def trimmedMember {X : Type u} (pieces : ℕ → Set (Set X))
    (i : Σ n, pieces n) : Set X :=
  i.2 \ ⋃₀ (⋃ k, ⋃ (_ : k < i.1), pieces k)

/-- Helper for Lemma 41.3: the least-layer trimming of a covering family still covers. -/
private lemma trimmedMembers_cover
    {X : Type u} (pieces : ℕ → Set (Set X))
    (hcover : ⋃₀ (⋃ n, pieces n) = Set.univ) :
    ⋃₀ (Set.range (trimmedMember pieces)) = Set.univ := by
  -- For each point, choose the least layer containing it.
  classical
  rw [Set.eq_univ_iff_forall]
  intro x
  have hexists : ∃ n, ∃ U ∈ pieces n, x ∈ U := by
    have hx : x ∈ ⋃₀ (⋃ n, pieces n) := by
      rw [hcover]
      exact Set.mem_univ x
    obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hx
    obtain ⟨n, hUn⟩ := Set.mem_iUnion.mp hU
    exact ⟨n, U, hUn, hxU⟩
  let N := Nat.find hexists
  obtain ⟨U, hUpieces, hxU⟩ := Nat.find_spec hexists
  let i : Σ n, pieces n := ⟨N, U, hUpieces⟩
  have hxTrimmed : x ∈ trimmedMember pieces i := by
    refine ⟨hxU, ?_⟩
    intro hxEarlier
    obtain ⟨V, hV, hxV⟩ := Set.mem_sUnion.mp hxEarlier
    obtain ⟨k, hV⟩ := Set.mem_iUnion.mp hV
    obtain ⟨hkN, hVk⟩ := Set.mem_iUnion.mp hV
    exact (Nat.not_lt_of_ge (Nat.find_min' hexists ⟨V, hVk, hxV⟩)) hkN
  exact Set.mem_sUnion_of_mem hxTrimmed ⟨i, rfl⟩

/-- Helper for Lemma 41.3: least-layer trimming turns locally finite open layers
into one locally finite indexed family. -/
private lemma locallyFinite_trimmedMembers
    {X : Type u} [TopologicalSpace X] (pieces : ℕ → Set (Set X))
    (hfinite : ∀ n, (pieces n).LocallyFinite)
    (hopen : ∀ U ∈ ⋃ n, pieces n, IsOpen U)
    (hcover : ⋃₀ (⋃ n, pieces n) = Set.univ) :
    _root_.LocallyFinite (trimmedMember pieces) := by
  -- Use the least occupied layer as the cutoff between finitely controlled layers
  -- and a disjoint tail.
  classical
  intro x
  have hexists : ∃ n, ∃ U ∈ pieces n, x ∈ U := by
    have hx : x ∈ ⋃₀ (⋃ n, pieces n) := by
      rw [hcover]
      exact Set.mem_univ x
    obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hx
    obtain ⟨n, hUn⟩ := Set.mem_iUnion.mp hU
    exact ⟨n, U, hUn, hxU⟩
  let N := Nat.find hexists
  obtain ⟨U, hUpieces, hxU⟩ := Nat.find_spec hexists
  have hUopen : IsOpen U := hopen U (Set.mem_iUnion_of_mem N hUpieces)
  choose W hW_nhds hW_finite using fun n ↦ hfinite n x
  let T := U ∩ ⋂ n : Fin (N + 1), W n
  have hT_nhds : T ∈ 𝓝 x := by
    apply Filter.inter_mem (hUopen.mem_nhds hxU)
    rw [Filter.iInter_mem]
    intro n
    exact hW_nhds n
  refine ⟨T, hT_nhds, ?_⟩
  let controlled : Set (Σ n, pieces n) :=
    ⋃ n ∈ (↑(Finset.range (N + 1)) : Set ℕ),
      Sigma.mk n '' {V : pieces n | (V.1 ∩ W n).Nonempty}
  have hcontrolled : controlled.Finite := by
    apply Set.Finite.biUnion (Finset.finite_toSet (Finset.range (N + 1)))
    intro n hn
    exact (hW_finite n).image (Sigma.mk n)
  apply hcontrolled.subset
  intro i hi
  have hi_le : i.1 ≤ N := by
    by_contra hnot
    have hNi : N < i.1 := Nat.lt_of_not_ge hnot
    obtain ⟨y, hytrimmed, hyT⟩ := hi
    exact hytrimmed.2 (Set.mem_sUnion_of_mem hyT.1
      (Set.mem_iUnion_of_mem N (Set.mem_iUnion_of_mem hNi hUpieces)))
  refine Set.mem_iUnion_of_mem i.1 (Set.mem_iUnion_of_mem ?_ ?_)
  · simpa only [Finset.mem_coe, Finset.mem_range] using Nat.lt_succ_of_le hi_le
  · refine ⟨i.2, ?_, rfl⟩
    obtain ⟨y, hytrimmed, hyT⟩ := hi
    exact ⟨y, hytrimmed.1, Set.mem_iInter.mp hyT.2 ⟨i.1, Nat.lt_succ_of_le hi_le⟩⟩

/-- Helper for Lemma 41.3: a locally finite union of closed sets is closed. -/
private lemma isClosed_sUnion_of_locallyFinite
    {X : Type u} [TopologicalSpace X] {𝒞 : Set (Set X)}
    (hfinite : 𝒞.LocallyFinite) (hclosed : ∀ C ∈ 𝒞, IsClosed C) :
    IsClosed (⋃₀ 𝒞) := by
  -- Rewrite the closure of the union as the union of the pointwise closures.
  rw [← closure_eq_iff_isClosed, hfinite.closure_sUnion]
  congr 1
  ext C
  constructor
  · rintro ⟨D, hD, rfl⟩
    simpa only [(hclosed D hD).closure_eq] using hD
  · intro hC
    exact ⟨C, hC, (hclosed C hC).closure_eq⟩

/-- Helper for Lemma 41.3: swell a set by deleting auxiliary closed members
that lie in its complement. -/
private def openSwelling {X : Type u} (𝒞 : Set (Set X)) (B : Set X) : Set X :=
  (⋃₀ {C | C ∈ 𝒞 ∧ C ⊆ Bᶜ})ᶜ

/-- Helper for Lemma 41.3: each swelling is open and contains the original set. -/
private lemma openSwelling_isOpen_subset
    {X : Type u} [TopologicalSpace X] {𝒞 : Set (Set X)}
    (hfinite : 𝒞.LocallyFinite) (hclosed : ∀ C ∈ 𝒞, IsClosed C)
    (B : Set X) : IsOpen (openSwelling 𝒞 B) ∧ B ⊆ openSwelling 𝒞 B := by
  -- The deleted subcollection is locally finite and closed, while no point of `B` belongs to it.
  have hsubfinite : {C | C ∈ 𝒞 ∧ C ⊆ Bᶜ}.LocallyFinite :=
    hfinite.mono fun _ hC ↦ hC.1
  constructor
  · exact (isClosed_sUnion_of_locallyFinite hsubfinite fun C hC ↦ hclosed C hC.1).isOpen_compl
  · intro x hxB hxUnion
    obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hxUnion
    exact hC.2 hxC hxB

/-- Helper for Lemma 41.3: swellings are locally finite when every auxiliary
cover member meets only finitely many original members. -/
private lemma locallyFinite_openSwelling
    {X : Type u} [TopologicalSpace X] (ℬ 𝒞 : Set (Set X))
    (hcover : ⋃₀ 𝒞 = Set.univ) (hfinite : 𝒞.LocallyFinite)
    (hincidence : ∀ C ∈ 𝒞, {B | B ∈ ℬ ∧ (C ∩ B).Nonempty}.Finite) :
    _root_.LocallyFinite (fun B : ℬ ↦ openSwelling 𝒞 B) := by
  -- A neighborhood meeting finitely many auxiliary members can meet only their
  -- finite incidence union.
  classical
  intro x
  obtain ⟨W, hW_nhds, hW_finite⟩ := hfinite x
  refine ⟨W, hW_nhds, ?_⟩
  let meeting : Set 𝒞 := {C | (C.1 ∩ W).Nonempty}
  have hmeeting : meeting.Finite := hW_finite
  let bounded : Set ℬ := ⋃ C ∈ meeting, {B | (C.1 ∩ B.1).Nonempty}
  have hbounded : bounded.Finite := by
    apply Set.Finite.biUnion hmeeting
    intro C hC
    have hbase := hincidence C C.property
    have hpreimage :
        (Subtype.val ⁻¹' {B | B ∈ ℬ ∧ (C.1 ∩ B).Nonempty} : Set ℬ).Finite :=
      hbase.preimage Subtype.val_injective.injOn
    apply hpreimage.subset
    intro B hB
    exact ⟨B.property, hB⟩
  apply hbounded.subset
  intro B hB
  obtain ⟨y, hySwelling, hyW⟩ := hB
  have hyUnion : y ∈ ⋃₀ 𝒞 := by
    rw [hcover]
    exact Set.mem_univ y
  obtain ⟨C, hC𝒞, hyC⟩ := Set.mem_sUnion.mp hyUnion
  let C' : 𝒞 := ⟨C, hC𝒞⟩
  refine Set.mem_iUnion_of_mem C' (Set.mem_iUnion_of_mem ?_ ?_)
  · exact ⟨y, hyC, hyW⟩
  · by_contra hCB
    have hCsubset : C ⊆ B.1ᶜ := by
      intro z hzC hzB
      exact hCB ⟨z, hzC, hzB⟩
    exact hySwelling (Set.mem_sUnion_of_mem hyC ⟨hC𝒞, hCsubset⟩)

/-- Helper for Lemma 41.3: an open countably locally finite cover admits a covering
locally finite refinement. -/
private lemma exists_locallyFiniteRefinement_of_countablyLocallyFiniteOpenCover
    {X : Type u} [TopologicalSpace X] (ℬ : Set (Set X))
    (hℬ_open : ∀ U ∈ ℬ, IsOpen U) (hℬ_cover : ⋃₀ ℬ = Set.univ)
    (hℬ_countable : ℬ.CountablyLocallyFinite) :
    ∃ 𝒞 : Set (Set X),
      IsRefinement 𝒞 ℬ ∧ ⋃₀ 𝒞 = Set.univ ∧ 𝒞.LocallyFinite := by
  -- Decompose the cover into locally finite layers and retain each member's layer as an index.
  rw [Set.countablyLocallyFinite_iff] at hℬ_countable
  obtain ⟨pieces, hpieces, hfinite⟩ := hℬ_countable
  have hopen : ∀ U ∈ ⋃ n, pieces n, IsOpen U := by
    rwa [← hpieces]
  have hcover : ⋃₀ (⋃ n, pieces n) = Set.univ := by
    rwa [← hpieces]
  let 𝒞 := Set.range (trimmedMember pieces)
  refine ⟨𝒞, ?_, ?_, (locallyFinite_trimmedMembers pieces hfinite hopen hcover).on_range⟩
  · -- Every trimmed member remains inside its source member and hence inside `ℬ`.
    rw [isRefinement_iff]
    rintro C ⟨i, rfl⟩
    refine ⟨i.2, ?_, Set.sdiff_subset⟩
    rw [hpieces]
    exact Set.mem_iUnion_of_mem i.1 i.2.property
  · -- The least occupied layer guarantees that the trimmed range still covers.
    exact trimmedMembers_cover pieces hcover

/-- Helper for Lemma 41.3: locally finite closed refinements of all open covers imply
paracompactness. -/
private lemma paracompactSpace_of_exists_locallyFinite_closedRefinement
    {X : Type u} [TopologicalSpace X] [T1Space X] [RegularSpace X]
    (h : ∀ 𝒜 : Set (Set X),
      (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsClosedRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.LocallyFinite) :
    ParacompactSpace X := by
  -- Build an indexed locally finite open refinement, as required by `ParacompactSpace`.
  constructor
  intro α A hA_open hA_cover
  classical
  let 𝒜 : Set (Set X) := Set.range A
  have h𝒜_open : ∀ U ∈ 𝒜, IsOpen U := by
    rintro U ⟨i, rfl⟩
    exact hA_open i
  have h𝒜_cover : ⋃₀ 𝒜 = Set.univ := by
    unfold 𝒜
    simpa only [Set.sUnion_range] using hA_cover
  obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_finite⟩ := h 𝒜 h𝒜_open h𝒜_cover
  let 𝒰 : Set (Set X) :=
    {U | IsOpen U ∧ {B | B ∈ ℬ ∧ (B ∩ U).Nonempty}.Finite}
  have h𝒰_open : ∀ U ∈ 𝒰, IsOpen U := by
    intro U hU
    exact hU.1
  have h𝒰_cover : ⋃₀ 𝒰 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.locallyFinite_iff] at hℬ_finite
    obtain ⟨W, hW_nhds, hW_finite⟩ := hℬ_finite x
    obtain ⟨V, hVW, hVopen, hxV⟩ := mem_nhds_iff.mp hW_nhds
    apply Set.mem_sUnion_of_mem hxV
    refine ⟨hVopen, hW_finite.subset ?_⟩
    intro B hB
    exact ⟨hB.1, hB.2.mono (Set.inter_subset_inter_right B hVW)⟩
  obtain ⟨𝒞, h𝒞_refines, h𝒞_cover, h𝒞_finite⟩ := h 𝒰 h𝒰_open h𝒰_cover
  have h𝒞_closed : ∀ C ∈ 𝒞, IsClosed C := by
    intro C hC
    exact h𝒞_refines.isClosed_of_mem hC
  have h𝒞_incidence : ∀ C ∈ 𝒞, {B | B ∈ ℬ ∧ (C ∩ B).Nonempty}.Finite := by
    intro C hC
    obtain ⟨U, hU𝒰, hCU⟩ := h𝒞_refines.subset_of_mem hC
    apply hU𝒰.2.subset
    intro B hB
    refine ⟨hB.1, ?_⟩
    obtain ⟨x, hxC, hxB⟩ := hB.2
    exact ⟨x, hxB, hCU hxC⟩
  choose F hF𝒜 hBF using fun B : ℬ ↦ hℬ_refines.subset_of_mem B.property
  choose index hFindex using fun B : ℬ ↦ hF𝒜 B
  let swelling : ℬ → Set X := fun B ↦ openSwelling 𝒞 B
  let refinement : ℬ → Set X := fun B ↦ swelling B ∩ F B
  have hswelling_open : ∀ B, IsOpen (swelling B) := by
    intro B
    exact (openSwelling_isOpen_subset h𝒞_finite h𝒞_closed B).1
  have hswelling_contains : ∀ B, B.1 ⊆ swelling B := by
    intro B
    exact (openSwelling_isOpen_subset h𝒞_finite h𝒞_closed B).2
  have hswelling_finite : _root_.LocallyFinite swelling :=
    locallyFinite_openSwelling ℬ 𝒞 h𝒞_cover h𝒞_finite h𝒞_incidence
  refine ⟨ℬ, refinement, ?_, ?_, ?_, ?_⟩
  · -- Intersections with chosen original members are open.
    intro B
    exact (hswelling_open B).inter (h𝒜_open (F B) (hF𝒜 B))
  · -- Each closed refinement member remains inside its swelling and chosen cover member.
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ ⋃₀ ℬ := by
      rw [hℬ_cover]
      exact Set.mem_univ x
    obtain ⟨B, hBℬ, hxB⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_iUnion_of_mem ⟨B, hBℬ⟩ ⟨hswelling_contains ⟨B, hBℬ⟩ hxB,
      hBF ⟨B, hBℬ⟩ hxB⟩
  · -- Local finiteness is preserved by taking pointwise subsets.
    exact hswelling_finite.subset fun B ↦ Set.inter_subset_left
  · intro B
    refine ⟨index B, ?_⟩
    unfold refinement
    rw [hFindex B]
    exact Set.inter_subset_right

/-- Paracompactness in the collection-of-subsets formulation used in Chapter 7. -/
theorem paracompactSpace_iff_exists_locallyFinite_openRefinement
    (X : Type u) [TopologicalSpace X] :
    ParacompactSpace X ↔
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
          ∃ ℬ : Set (Set X),
            IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
              ℬ.LocallyFinite := by
  constructor
  · rintro ⟨h⟩ 𝒜 h𝒜 h_cover
    rcases h 𝒜 Subtype.val (fun U ↦ h𝒜 U U.property)
        (by simpa only [Set.sUnion_eq_iUnion] using h_cover) with
      ⟨β, B, hB_open, hB_cover, hB_finite, hB_refines⟩
    refine ⟨Set.range B, ?_, ?_, hB_finite.on_range⟩
    · refine { subset_of_mem := ?_, isOpen_of_mem := ?_ }
      · rintro C ⟨i, rfl⟩
        obtain ⟨A, hBA⟩ := hB_refines i
        exact ⟨A, A.property, hBA⟩
      · rintro C ⟨i, rfl⟩
        exact hB_open i
    · simpa only [Set.sUnion_range] using hB_cover
  · intro h
    constructor
    intro α A hA_open hA_cover
    rcases h (Set.range A) (by rintro U ⟨i, rfl⟩; exact hA_open i)
        (by simpa only [Set.sUnion_range] using hA_cover) with
      ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_finite⟩
    exact ⟨ℬ, Subtype.val, fun B ↦ hℬ_refines.isOpen_of_mem B.property,
      by simpa only [Set.sUnion_eq_iUnion] using hℬ_cover, hℬ_finite,
      fun B ↦ by
        obtain ⟨_, ⟨i, rfl⟩, hBA⟩ := hℬ_refines.subset_of_mem B.property
        exact ⟨i, hBA⟩⟩

/-- Lemma 41.3. In a regular `T1Space`, the existence of sigma-locally-finite
open refinements, locally finite refinements, locally finite closed refinements,
and paracompactness are equivalent. -/
theorem openCoverRefinement_tfae
    (X : Type u) [TopologicalSpace X] [T1Space X] [RegularSpace X] :
    List.TFAE [
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
          ∃ ℬ : Set (Set X),
            IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.CountablyLocallyFinite,
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
          ∃ ℬ : Set (Set X),
            IsRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
              ℬ.LocallyFinite,
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
          ∃ ℬ : Set (Set X),
            IsClosedRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
              ℬ.LocallyFinite,
      ParacompactSpace X] := by
  tfae_have 1 → 2 := by
    intro h
    intro 𝒜 h𝒜_open h𝒜_cover
    obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_countable⟩ := h 𝒜 h𝒜_open h𝒜_cover
    -- Trim the countably many locally finite layers, then compose refinements.
    obtain ⟨𝒞, h𝒞_refines, h𝒞_cover, h𝒞_finite⟩ :=
      exists_locallyFiniteRefinement_of_countablyLocallyFiniteOpenCover ℬ
        (fun U hU ↦ hℬ_refines.isOpen_of_mem hU) hℬ_cover hℬ_countable
    exact ⟨𝒞, h𝒞_refines.trans hℬ_refines.toIsRefinement, h𝒞_cover, h𝒞_finite⟩
  tfae_have 2 → 3 := by
    intro h
    -- Regular shrinking followed by closure supplies the closed refinement.
    exact exists_closedLocallyFiniteRefinement_of_locallyFiniteRefinement h
  tfae_have 3 → 4 := by
    intro h
    -- The swelling construction converts closed refinements into open ones.
    exact paracompactSpace_of_exists_locallyFinite_closedRefinement h
  tfae_have 4 → 1 := by
    intro h
    rw [paracompactSpace_iff_exists_locallyFinite_openRefinement] at h
    intro 𝒜 h𝒜_open h𝒜_cover
    obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_finite⟩ := h 𝒜 h𝒜_open h𝒜_cover
    -- A locally finite refinement is countably locally finite in one layer.
    exact ⟨ℬ, hℬ_refines, hℬ_cover,
      locallyFiniteCollection_countablyLocallyFinite hℬ_finite⟩
  tfae_finish
