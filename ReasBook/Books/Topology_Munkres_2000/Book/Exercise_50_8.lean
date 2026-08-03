module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Definition_50_10.CompactExhaustible
public import Mathlib.Topology.SeparatedMap

public section

open scoped CoveringDimension

universe u

/-- Helper for Exercise 50.8: a dimension-bounded compact subtype admits an ambient open
refinement with the same multiplicity bound at points of the compact set. -/
private lemma existsOpenRefinementWithOrderOnCompact {m : ℕ} {X : Type u}
    [TopologicalSpace X] [T2Space X] (S : Set X) (hS_compact : IsCompact S)
    (hS_dim : HasCoveringDimensionLE S m) (ℬ : Set (Set X))
    (hℬ_open : ∀ B ∈ ℬ, IsOpen B) (hℬ_cover : ⋃₀ ℬ = Set.univ) :
    ∃ 𝒞 : Set (Set X), IsOpenRefinement 𝒞 ℬ ∧ ⋃₀ 𝒞 = Set.univ ∧
      ∀ x ∈ S, Set.encard {C ∈ 𝒞 | x ∈ C} ≤ (m + 1 : ℕ) := by
  classical
  let restrictedCover : Set (Set S) :=
    {U | ∃ B ∈ ℬ, U = Subtype.val ⁻¹' B}
  have hrestricted_open : ∀ U ∈ restrictedCover, IsOpen U := by
    rintro U ⟨B, hB, rfl⟩
    exact (hℬ_open B hB).preimage continuous_subtype_val
  have hrestricted_cover : ⋃₀ restrictedCover = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.1 ∈ ⋃₀ ℬ := by
      rw [hℬ_cover]
      exact Set.mem_univ x.1
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨B, hB, hxB⟩ := hx
    exact ⟨Subtype.val ⁻¹' B, ⟨B, hB, rfl⟩, hxB⟩
  obtain ⟨𝒟, h𝒟_refines, h𝒟_cover, h𝒟_order⟩ :=
    hS_dim restrictedCover hrestricted_open hrestricted_cover
  rw [Set.hasOrderLE_iff] at h𝒟_order
  have h_parent_exists (D : 𝒟) :
      ∃ B ∈ ℬ, D.1 ⊆ Subtype.val ⁻¹' B := by
    obtain ⟨U, ⟨B, hB, rfl⟩, hDU⟩ := h𝒟_refines.subset_of_mem D.2
    exact ⟨B, hB, hDU⟩
  choose parent hparent_mem hD_parent using h_parent_exists
  have h_ambient_exists (D : 𝒟) :
      ∃ O : Set X, IsOpen O ∧ Subtype.val ⁻¹' O = D.1 := by
    exact isOpen_induced_iff.mp (h𝒟_refines.isOpen_of_mem D.2)
  choose ambient hambient_open hambient_preimage using h_ambient_exists
  let lift : 𝒟 → Set X := fun D ↦ ambient D ∩ parent D
  let outside : Set (Set X) := {C | ∃ B ∈ ℬ, C = B ∩ Sᶜ}
  let 𝒞 : Set (Set X) := Set.range lift ∪ outside
  refine ⟨𝒞, ?_, ?_, ?_⟩
  · -- Both lifted and exterior members are open subsets of members of `ℬ`.
    rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      intro C hC
      rcases hC with ⟨D, rfl⟩ | ⟨B, hB, rfl⟩
      · exact ⟨parent D, hparent_mem D, fun _ hz ↦ hz.2⟩
      · exact ⟨B, hB, Set.inter_subset_left⟩
    · intro C hC
      rcases hC with ⟨D, rfl⟩ | ⟨B, hB, rfl⟩
      · exact (hambient_open D).inter (hℬ_open (parent D) (hparent_mem D))
      · exact (hℬ_open B hB).inter hS_compact.isClosed.isOpen_compl
  · -- Lifted members cover `S`, while exterior intersections cover its complement.
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxS : x ∈ S
    · have hxD : (⟨x, hxS⟩ : S) ∈ ⋃₀ 𝒟 := by
        rw [h𝒟_cover]
        exact Set.mem_univ _
      rw [Set.mem_sUnion] at hxD ⊢
      obtain ⟨D, hD, hxD⟩ := hxD
      let D' : 𝒟 := ⟨D, hD⟩
      refine ⟨lift D', Or.inl ⟨D', rfl⟩, ?_⟩
      constructor
      · exact (Set.ext_iff.mp (hambient_preimage D') ⟨x, hxS⟩).mpr hxD
      · exact hD_parent D' hxD
    · have hxB : x ∈ ⋃₀ ℬ := by
        rw [hℬ_cover]
        exact Set.mem_univ x
      rw [Set.mem_sUnion] at hxB ⊢
      obtain ⟨B, hB, hxB⟩ := hxB
      exact ⟨B ∩ Sᶜ, Or.inr ⟨B, hB, rfl⟩, ⟨hxB, hxS⟩⟩
  · -- At a point of `S`, exterior members disappear and lifted membership comes from `𝒟`.
    intro x hxS
    let source : Set 𝒟 := {D | (⟨x, hxS⟩ : S) ∈ D.1}
    have hmembers_subset : {C ∈ 𝒞 | x ∈ C} ⊆ lift '' source := by
      intro C hC
      rcases hC.1 with ⟨D, rfl⟩ | ⟨B, hB, rfl⟩
      · refine ⟨D, ?_, rfl⟩
        simpa only [source, Set.mem_setOf_eq] using
          (Set.ext_iff.mp (hambient_preimage D) ⟨x, hxS⟩).mp hC.2.1
      · exact (hC.2.2 hxS).elim
    have hsource_image : Subtype.val '' source =
        {D ∈ 𝒟 | (⟨x, hxS⟩ : S) ∈ D} := by
      ext D
      constructor
      · rintro ⟨D', hD', rfl⟩
        exact ⟨D'.2, hD'⟩
      · rintro ⟨hD, hxD⟩
        exact ⟨⟨D, hD⟩, hxD, rfl⟩
    calc
      Set.encard {C ∈ 𝒞 | x ∈ C} ≤ Set.encard (lift '' source) :=
        Set.encard_le_encard hmembers_subset
      _ ≤ Set.encard source := Set.encard_image_le lift source
      _ = Set.encard (Subtype.val '' source) :=
        (Subtype.val_injective.encard_image source).symm
      _ = Set.encard {D ∈ 𝒟 | (⟨x, hxS⟩ : S) ∈ D} := congrArg Set.encard hsource_image
      _ ≤ (m + 1 : ℕ) := h𝒟_order (⟨x, hxS⟩ : S)


/-- Helper for Exercise 50.8: a shifted compact exhaustion supports an open refinement whose
members meeting one compact stage lie in the next stage. -/
private lemma existsControlledOpenRefinement {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) (hK_zero : K 0 = ∅) (𝒜 : Set (Set X))
    (h𝒜_open : ∀ U ∈ 𝒜, IsOpen U) (h𝒜_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℬ : Set (Set X), IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
      ∀ n B, B ∈ ℬ → (B ∩ K n).Nonempty → B ⊆ K (n + 1) := by
  classical
  -- Choose one member of the original cover through each point.
  have h_parent_exists (x : X) : ∃ U ∈ 𝒜, x ∈ U := by
    have hx : x ∈ ⋃₀ 𝒜 := by
      rw [h𝒜_cover]
      exact Set.mem_univ x
    simpa only [Set.mem_sUnion] using hx
  choose parent hparent_mem hx_parent using h_parent_exists
  let neighborhood : X → Set X := fun x ↦
    parent x ∩ interior (K (K.find x + 1)) ∩ (K (K.find x - 1))ᶜ
  refine ⟨Set.range neighborhood, ?_, ?_, ?_⟩
  · -- Each chosen neighborhood is open and remains inside its selected parent.
    rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      rintro B ⟨x, rfl⟩
      exact ⟨parent x, hparent_mem x, fun _ hz ↦ hz.1.1⟩
    · rintro B ⟨x, rfl⟩
      exact ((h𝒜_open (parent x) (hparent_mem x)).inter isOpen_interior).inter
        (K.isCompact (K.find x - 1)).isClosed.isOpen_compl
  · -- Every point belongs to its own chosen neighborhood.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    refine ⟨neighborhood x, ⟨x, rfl⟩, ⟨⟨hx_parent x, ?_⟩, ?_⟩⟩
    · exact K.subset_interior_succ (K.find x) (K.mem_find x)
    · intro hx_lower
      have hfind_pos : 0 < K.find x := by
        by_contra h
        have hfind_zero : K.find x = 0 := Nat.eq_zero_of_not_pos h
        have : x ∈ (∅ : Set X) := by
          rw [← hK_zero, ← hfind_zero]
          exact K.mem_find x
        exact this
      have hfind_le_pred : K.find x ≤ K.find x - 1 :=
        K.mem_iff_find_le.mp hx_lower
      omega
  · -- Meeting `K n` forces the center rank below `n + 1`, hence controls the whole set.
    rintro n B ⟨x, rfl⟩ ⟨y, hyB, hyK⟩ z hz
    have hfind_pos : 0 < K.find x := by
      by_contra h
      have hfind_zero : K.find x = 0 := Nat.eq_zero_of_not_pos h
      have : x ∈ (∅ : Set X) := by
        rw [← hK_zero, ← hfind_zero]
        exact K.mem_find x
      exact this
    have hnot_le : ¬ n ≤ K.find x - 1 := by
      intro hn
      exact hyB.2 (K.subset hn hyK)
    have hfind_le : K.find x ≤ n := by omega
    exact K.subset (Nat.add_le_add_right hfind_le 1) (interior_subset hz.1.2)

/-- Helper for Exercise 50.8: `CoverStage K m ℬ₀ n ℬ` records refinement, coverage, and
the order bound on the `n`th compact stage. -/
private def CoverStage {X : Type u} [TopologicalSpace X] (K : CompactExhaustion X) (m : ℕ)
    (ℬ₀ : Set (Set X)) (n : ℕ) (ℬ : Set (Set X)) : Prop :=
  IsOpenRefinement ℬ ℬ₀ ∧ ⋃₀ ℬ = Set.univ ∧
    ∀ x ∈ K n, Set.encard {B ∈ ℬ | x ∈ B} ≤ (m + 1 : ℕ)

/-- Helper for Exercise 50.8: a member of a refining cover that meets the preceding compact
stage is contained in the current compact stage. -/
private lemma subset_compactStage_of_meets_previous {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) (hK_zero : K 0 = ∅) (ℬ₀ ℬ : Set (Set X))
    (hℬ_refines : IsRefinement ℬ ℬ₀)
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (n : ℕ) (B : Set X) (hB : B ∈ ℬ) (hB_meets : (B ∩ K (n - 1)).Nonempty) :
    B ⊆ K n := by
  -- Pass to an initial-cover parent and apply its support control.
  cases n with
  | zero =>
      obtain ⟨x, _, hxK⟩ := hB_meets
      rw [hK_zero] at hxK
      exact hxK.elim
  | succ n =>
      obtain ⟨B₀, hB₀, hBB₀⟩ := hℬ_refines.subset_of_mem hB
      have hB₀_meets : (B₀ ∩ K (Nat.succ n - 1)).Nonempty := by
        obtain ⟨x, hxB, hxK⟩ := hB_meets
        exact ⟨x, hBB₀ hxB, hxK⟩
      have hB₀_subset : B₀ ⊆ K ((Nat.succ n - 1) + 1) :=
        hℬ₀_control (Nat.succ n - 1) B₀ hB₀ hB₀_meets
      simpa using hBB₀.trans hB₀_subset

/-- Helper for Exercise 50.8: membership of a set meeting a fixed compact core persists
forward through a core-stable sequence of covers. -/
private lemma coverMembership_persists {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) (ℬ : ℕ → Set (Set X))
    (hstable : ∀ n B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ (n + 1) ↔ B ∈ ℬ n))
    {q start : ℕ} {B : Set X} (hB_meets : (B ∩ K q).Nonempty)
    (hstart : q + 2 ≤ start) (hB_start : B ∈ ℬ start) :
    ∀ n ≥ start, B ∈ ℬ n := by
  -- At every later transition, `K q` lies in the stability core `K (n - 1)`.
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hB_start
  | succ n hn hBn =>
      have hq_pred : q ≤ n - 1 := by omega
      have hB_meets_pred : (B ∩ K (n - 1)).Nonempty := by
        obtain ⟨x, hxB, hxK⟩ := hB_meets
        exact ⟨x, hxB, K.subset hq_pred hxK⟩
      exact (hstable n B hB_meets_pred).2 hBn

/-- Helper for Exercise 50.8: the sets belonging to every sufficiently late cover in a
sequence. -/
private def EventuallyStableCover {X : Type u} (ℬ : ℕ → Set (Set X)) : Set (Set X) :=
  {B | ∃ N, ∀ n ≥ N, B ∈ ℬ n}

/-- Helper for Exercise 50.8: eventual membership in a core-stable sequence defines an open
refinement covering the space with the global stagewise order bound. -/
private lemma eventuallyStableCover_spec {m : ℕ} {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) (ℬ₀ : Set (Set X)) (ℬ : ℕ → Set (Set X))
    (hstage : ∀ n, CoverStage K m ℬ₀ n (ℬ n))
    (hstable : ∀ n B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ (n + 1) ↔ B ∈ ℬ n)) :
    IsOpenRefinement (EventuallyStableCover ℬ) ℬ₀ ∧
      ⋃₀ EventuallyStableCover ℬ = Set.univ ∧
      (EventuallyStableCover ℬ).HasOrderLE (m + 1) := by
  classical
  let eventual : Set (Set X) := EventuallyStableCover ℬ
  refine ⟨?_, ?_, ?_⟩
  · -- An eventual member belongs to one stage, so stage refinement supplies openness and a parent.
    rw [isOpenRefinement_iff]
    constructor
    · rw [isRefinement_iff]
      intro B hB
      obtain ⟨N, hN⟩ := hB
      exact (hstage N).1.1.subset_of_mem (hN N le_rfl)
    · intro B hB
      obtain ⟨N, hN⟩ := hB
      exact (hstage N).1.isOpen_of_mem (hN N le_rfl)
  · -- Start two stages beyond a compact core containing the point, then persist forward.
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨q, hxq⟩ := K.exists_mem x
    have hxcover : x ∈ ⋃₀ ℬ (q + 2) := by
      rw [(hstage (q + 2)).2.1]
      exact Set.mem_univ x
    rw [Set.mem_sUnion] at hxcover ⊢
    obtain ⟨B, hB_stage, hxB⟩ := hxcover
    have hB_meets : (B ∩ K q).Nonempty := ⟨x, hxB, hxq⟩
    refine ⟨B, ?_, hxB⟩
    exact ⟨q + 2, coverMembership_persists K ℬ hstable hB_meets le_rfl hB_stage⟩
  · -- Every eventual member through `x` already belongs to the fixed stage two beyond its core.
    rw [Set.hasOrderLE_iff]
    intro x
    obtain ⟨q, hxq⟩ := K.exists_mem x
    have hmembers_subset : {B ∈ eventual | x ∈ B} ⊆ {B ∈ ℬ (q + 2) | x ∈ B} := by
      intro B hB
      obtain ⟨N, hN⟩ := hB.1
      have hB_meets : (B ∩ K q).Nonempty := ⟨x, hB.2, hxq⟩
      by_cases hN_le : N ≤ q + 2
      · exact ⟨hN (q + 2) hN_le, hB.2⟩
      · have hstart : q + 2 ≤ N := by omega
        have hbackward : B ∈ ℬ (q + 2) := by
          refine Nat.decreasingInduction' (m := q + 2) (n := N) ?_ hstart (hN N le_rfl)
          intro k _ hk_lower hBk
          have hq_pred : q ≤ k - 1 := by omega
          have hB_meets_pred : (B ∩ K (k - 1)).Nonempty := by
            obtain ⟨y, hyB, hyK⟩ := hB_meets
            exact ⟨y, hyB, K.subset hq_pred hyK⟩
          exact (hstable k B hB_meets_pred).1 hBk
        exact ⟨hbackward, hB.2⟩
    exact (Set.encard_le_encard hmembers_subset).trans ((hstage (q + 2)).2.2 x
      (K.subset (by omega) hxq))

/-- Helper for Exercise 50.8: retain a parent meeting the core, and otherwise replace it by
the union of its selected children. -/
private def coreReplacement {X : Type u} (core : Set X) (𝒞 : Set (Set X))
    (parent : Set X → Set X) (B : Set X) : Set X :=
  @ite (Set X) (B ∩ core).Nonempty (Classical.propDecidable _)
    B (⋃₀ {C ∈ 𝒞 | parent C = B})

/-- Helper for Exercise 50.8: every core replacement is contained in its parent when each
selected child is contained in its parent. -/
private lemma coreReplacement_subset_parent {X : Type u} (core : Set X)
    (𝒞 : Set (Set X)) (parent : Set X → Set X)
    (hchild : ∀ C ∈ 𝒞, C ⊆ parent C) (B : Set X) :
    coreReplacement core 𝒞 parent B ⊆ B := by
  -- The retained branch is immediate; union membership supplies a child in the other branch.
  by_cases hB_core : (B ∩ core).Nonempty
  · simpa only [coreReplacement, if_pos hB_core] using (Set.Subset.rfl : B ⊆ B)
  · rw [coreReplacement, if_neg hB_core]
    intro x hx
    rw [Set.mem_sUnion] at hx
    obtain ⟨C, ⟨hC, hparent⟩, hxC⟩ := hx
    exact hparent ▸ hchild C hC hxC

/-- Helper for Exercise 50.8: members through a point in an image-indexed replacement family
come from replacements of old members through that point. -/
private lemma coreReplacementMembers_subset_parentImage {X : Type u}
    (replacement : Set X → Set X) (ℬ : Set (Set X)) (x : X)
    (hsubset : ∀ B ∈ ℬ, replacement B ⊆ B) :
    {R ∈ replacement '' ℬ | x ∈ R} ⊆ replacement '' {B ∈ ℬ | x ∈ B} := by
  -- Unpack the replacement witness and transport point membership to its old parent.
  rintro R ⟨⟨B, hB, rfl⟩, hx⟩
  exact ⟨B, ⟨hB, hsubset B hB hx⟩, rfl⟩

/-- Helper for Exercise 50.8: outside a controlled set, every replacement member through a
point is indexed by the parent of a child through that point. -/
private lemma coreReplacementMembersOutside_subset_childParentImage {X : Type u}
    (core controlled : Set X) (𝒞 ℬ : Set (Set X)) (parent : Set X → Set X) (x : X)
    (hcore_control : ∀ B ∈ ℬ, (B ∩ core).Nonempty → B ⊆ controlled)
    (hx_controlled : x ∉ controlled) :
    {R ∈ coreReplacement core 𝒞 parent '' ℬ | x ∈ R} ⊆
      coreReplacement core 𝒞 parent '' (parent '' {C ∈ 𝒞 | x ∈ C}) := by
  -- A retained parent would put `x` in the controlled set, so only the child-union branch remains.
  rintro R ⟨⟨B, hB, rfl⟩, hxR⟩
  have hB_core : ¬(B ∩ core).Nonempty := by
    intro hB_core
    have hxB : x ∈ B := by
      simpa only [coreReplacement, if_pos hB_core] using hxR
    exact hx_controlled (hcore_control B hB hB_core hxB)
  rw [coreReplacement, if_neg hB_core, Set.mem_sUnion] at hxR
  obtain ⟨C, ⟨hC, hparent⟩, hxC⟩ := hxR
  refine ⟨B, ?_, rfl⟩
  exact ⟨C, ⟨hC, hxC⟩, hparent⟩

/-- Helper for Exercise 50.8: one cover stage can be refined while preserving exactly the
members meeting the preceding compact core. -/
private lemma existsCoreStableCoverStage {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) (hK_zero : K 0 = ∅) (ℬ₀ ℬ : Set (Set X))
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (hstage : CoverStage K m ℬ₀ n ℬ)
    (h_dim : ∀ S : Set X, IsCompact S → HasCoveringDimensionLE S m) :
    ∃ ℬ' : Set (Set X), CoverStage K m ℬ₀ (n + 1) ℬ' ∧ IsRefinement ℬ' ℬ ∧
      ∀ B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ' ↔ B ∈ ℬ) := by
  classical
  -- Route correction: use raw-set images rather than a subtype-indexed range, so both
  -- multiplicity bounds reduce directly to image-cardinality inequalities.
  obtain ⟨𝒞, h𝒞_refines, h𝒞_cover, h𝒞_order⟩ :=
    existsOpenRefinementWithOrderOnCompact (K (n + 1)) (K.isCompact (n + 1))
      (h_dim (K (n + 1)) (K.isCompact (n + 1))) ℬ
      (fun _ hB ↦ hstage.1.isOpen_of_mem hB) hstage.2.1
  have hparent_exists (C : Set X) : ∃ B : Set X, C ∈ 𝒞 → B ∈ ℬ ∧ C ⊆ B := by
    by_cases hC : C ∈ 𝒞
    · obtain ⟨B, hB, hCB⟩ := h𝒞_refines.subset_of_mem hC
      exact ⟨B, fun _ ↦ ⟨hB, hCB⟩⟩
    · exact ⟨∅, fun hC' ↦ (hC hC').elim⟩
  choose parent hparent_spec using hparent_exists
  let core : Set X := K (n - 1)
  let replacement : Set X → Set X := coreReplacement core 𝒞 parent
  let ℬ' : Set (Set X) := replacement '' ℬ
  have hparent_mem (C : Set X) (hC : C ∈ 𝒞) : parent C ∈ ℬ :=
    (hparent_spec C hC).1
  have hchild_subset (C : Set X) (hC : C ∈ 𝒞) : C ⊆ parent C :=
    (hparent_spec C hC).2
  have hreplacement_subset (B : Set X) (hB : B ∈ ℬ) : replacement B ⊆ B := by
    exact coreReplacement_subset_parent core 𝒞 parent hchild_subset B
  have hcore_control (B : Set X) (hB : B ∈ ℬ)
      (hB_core : (B ∩ core).Nonempty) : B ⊆ K n := by
    exact subset_compactStage_of_meets_previous K hK_zero ℬ₀ ℬ hstage.1.1
      hℬ₀_control n B hB hB_core
  have hreplacement_open (B : Set X) (hB : B ∈ ℬ) : IsOpen (replacement B) := by
    -- Retained parents are already open; otherwise openness follows from the child union.
    by_cases hB_core : (B ∩ core).Nonempty
    · simpa only [replacement, coreReplacement, if_pos hB_core] using
        hstage.1.isOpen_of_mem hB
    · simp only [replacement, coreReplacement, if_neg hB_core]
      exact isOpen_sUnion fun C hC ↦ h𝒞_refines.isOpen_of_mem hC.1
  have hℬ'_refines : IsRefinement ℬ' ℬ := by
    rw [isRefinement_iff]
    rintro R ⟨B, hB, rfl⟩
    exact ⟨B, hB, hreplacement_subset B hB⟩
  have hℬ'_open : ∀ R ∈ ℬ', IsOpen R := by
    rintro R ⟨B, hB, rfl⟩
    exact hreplacement_open B hB
  have hℬ'_cover : ⋃₀ ℬ' = Set.univ := by
    -- A child through `x` either lies in its retained parent or in that parent's replacement union.
    apply Set.eq_univ_of_forall
    intro x
    have hx𝒞 : x ∈ ⋃₀ 𝒞 := by
      rw [h𝒞_cover]
      exact Set.mem_univ x
    rw [Set.mem_sUnion] at hx𝒞 ⊢
    obtain ⟨C, hC, hxC⟩ := hx𝒞
    refine ⟨replacement (parent C), ⟨parent C, hparent_mem C hC, rfl⟩, ?_⟩
    by_cases hparent_core : (parent C ∩ core).Nonempty
    · simp only [replacement, coreReplacement, if_pos hparent_core]
      exact hchild_subset C hC hxC
    · simp only [replacement, coreReplacement, if_neg hparent_core, Set.mem_sUnion]
      exact ⟨C, ⟨hC, rfl⟩, hxC⟩
  have hℬ'_order : ∀ x ∈ K (n + 1),
      Set.encard {R ∈ ℬ' | x ∈ R} ≤ (m + 1 : ℕ) := by
    intro x hx_stage
    by_cases hx_controlled : x ∈ K n
    · -- On the old stage, replacement membership maps to old-parent membership.
      have hmembers_subset : {R ∈ ℬ' | x ∈ R} ⊆
          replacement '' {B ∈ ℬ | x ∈ B} :=
        coreReplacementMembers_subset_parentImage replacement ℬ x hreplacement_subset
      calc
        Set.encard {R ∈ ℬ' | x ∈ R} ≤
            Set.encard (replacement '' {B ∈ ℬ | x ∈ B}) :=
          Set.encard_le_encard hmembers_subset
        _ ≤ Set.encard {B ∈ ℬ | x ∈ B} :=
          Set.encard_image_le replacement {B ∈ ℬ | x ∈ B}
        _ ≤ (m + 1 : ℕ) := hstage.2.2 x hx_controlled
    · -- Outside the old stage, every member is indexed by a child through `x` and its parent.
      have hmembers_subset : {R ∈ ℬ' | x ∈ R} ⊆
          replacement '' (parent '' {C ∈ 𝒞 | x ∈ C}) := by
        exact coreReplacementMembersOutside_subset_childParentImage core (K n) 𝒞 ℬ parent x
          hcore_control hx_controlled
      calc
        Set.encard {R ∈ ℬ' | x ∈ R} ≤
            Set.encard (replacement '' (parent '' {C ∈ 𝒞 | x ∈ C})) :=
          Set.encard_le_encard hmembers_subset
        _ ≤ Set.encard (parent '' {C ∈ 𝒞 | x ∈ C}) :=
          Set.encard_image_le replacement (parent '' {C ∈ 𝒞 | x ∈ C})
        _ ≤ Set.encard {C ∈ 𝒞 | x ∈ C} :=
          Set.encard_image_le parent {C ∈ 𝒞 | x ∈ C}
        _ ≤ (m + 1 : ℕ) := h𝒞_order x hx_stage
  refine ⟨ℬ', ?_, hℬ'_refines, ?_⟩
  · -- Assemble openness, refinement to the initial cover, coverage, and the stage order bound.
    refine ⟨?_, hℬ'_cover, hℬ'_order⟩
    rw [isOpenRefinement_iff]
    exact ⟨hℬ'_refines.trans hstage.1.1, hℬ'_open⟩
  · -- A core-meeting parent is retained, and containment forces every equal replacement witness
    -- to meet the core and hence to be retained as well.
    intro B hB_core
    constructor
    · rintro ⟨A, hA, hreplacement⟩
      have hBA : B ⊆ A := by
        intro x hxB
        exact hreplacement_subset A hA (hreplacement ▸ hxB)
      have hA_core : (A ∩ core).Nonempty := by
        obtain ⟨x, hxB, hxcore⟩ := hB_core
        exact ⟨x, hBA hxB, hxcore⟩
      have hreplacement_A : replacement A = A := by
        simp only [replacement, coreReplacement, if_pos hA_core]
      have hAB : A = B := hreplacement_A.symm.trans hreplacement
      exact hAB ▸ hA
    · intro hB
      refine ⟨B, hB, ?_⟩
      have hB_core' : (B ∩ core).Nonempty := by
        simpa only [core] using hB_core
      simp only [replacement, coreReplacement, if_pos hB_core']

/-- Helper for Exercise 50.8: iterating the core-stable successor construction yields a sequence
of stagewise bounded covers with exact consecutive stability. -/
private lemma existsCoreStableCoverSequence {m : ℕ} {X : Type u}
    [TopologicalSpace X] [T2Space X] (K : CompactExhaustion X) (hK_zero : K 0 = ∅)
    (ℬ₀ : Set (Set X)) (hℬ₀_open : ∀ B ∈ ℬ₀, IsOpen B) (hℬ₀_cover : ⋃₀ ℬ₀ = Set.univ)
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (h_dim : ∀ S : Set X, IsCompact S → HasCoveringDimensionLE S m) :
    ∃ ℬ : ℕ → Set (Set X), ℬ 0 = ℬ₀ ∧ (∀ n, CoverStage K m ℬ₀ n (ℬ n)) ∧
      ∀ n B, (B ∩ K (n - 1)).Nonempty → (B ∈ ℬ (n + 1) ↔ B ∈ ℬ n) := by
  classical
  -- The initial order condition is vacuous because the zeroth compact stage is empty.
  have hinitial : CoverStage K m ℬ₀ 0 ℬ₀ := by
    refine ⟨?_, hℬ₀_cover, ?_⟩
    · rw [isOpenRefinement_iff]
      exact ⟨IsRefinement.refl ℬ₀, hℬ₀_open⟩
    · intro x hx
      rw [hK_zero] at hx
      exact hx.elim
  let StageData (n : ℕ) := {𝒞 : Set (Set X) // CoverStage K m ℬ₀ n 𝒞}
  let initial : StageData 0 := ⟨ℬ₀, hinitial⟩
  have hsuccessor (n : ℕ) (stage : StageData n) :
      ∃ next : StageData (n + 1), IsRefinement next.1 stage.1 ∧
        ∀ B, (B ∩ K (n - 1)).Nonempty → (B ∈ next.1 ↔ B ∈ stage.1) := by
    obtain ⟨next, hnext, hrefines, hstable⟩ :=
      existsCoreStableCoverStage K hK_zero ℬ₀ stage.1 hℬ₀_control stage.2 h_dim
    exact ⟨⟨next, hnext⟩, hrefines, hstable⟩
  let next (n : ℕ) (stage : StageData n) : StageData (n + 1) :=
    Classical.choose (hsuccessor n stage)
  have hnext_stable (n : ℕ) (stage : StageData n) :
      ∀ B, (B ∩ K (n - 1)).Nonempty → (B ∈ (next n stage).1 ↔ B ∈ stage.1) :=
    (Classical.choose_spec (hsuccessor n stage)).2
  let stages : (n : ℕ) → StageData n :=
    fun n ↦ Nat.rec initial (fun n stage ↦ next n stage) n
  refine ⟨fun n ↦ (stages n).1, ?_, ?_, ?_⟩
  · rfl
  · intro n
    exact (stages n).2
  · intro n B hB_meets
    exact hnext_stable n (stages n) B hB_meets

/-- Helper for Exercise 50.8: a controlled cover can be recursively stabilized to a global
bounded-order refinement along a compact exhaustion. -/
private lemma existsGloballyBoundedRefinementOfControlledCover {m : ℕ} {X : Type u}
    [TopologicalSpace X] [T2Space X] (K : CompactExhaustion X) (hK_zero : K 0 = ∅)
    (ℬ₀ : Set (Set X)) (hℬ₀_open : ∀ B ∈ ℬ₀, IsOpen B) (hℬ₀_cover : ⋃₀ ℬ₀ = Set.univ)
    (hℬ₀_control : ∀ n B, B ∈ ℬ₀ → (B ∩ K n).Nonempty → B ⊆ K (n + 1))
    (h_dim : ∀ S : Set X, IsCompact S → HasCoveringDimensionLE S m) :
    ∃ ℬ : Set (Set X), IsOpenRefinement ℬ ℬ₀ ∧ ⋃₀ ℬ = Set.univ ∧
      ℬ.HasOrderLE (m + 1) := by
  -- Assemble the recursive stages, then pass to their eventually stable members.
  obtain ⟨stages, _, hstage, hstable⟩ :=
    existsCoreStableCoverSequence K hK_zero ℬ₀ hℬ₀_open hℬ₀_cover hℬ₀_control h_dim
  exact ⟨EventuallyStableCover stages, eventuallyStableCover_spec K ℬ₀ stages hstage hstable⟩

/-- Exercise 50.8. If every compact subspace of the compactly exhaustible Hausdorff space `X`
has covering dimension at most `m`, then so does `X`. -/
theorem hasCoveringDimensionLE_of_compact_subspaces {m : ℕ} {X : Type u}
    [TopologicalSpace X] [CompactlyExhaustibleSpace X] [T2Space X]
    (h_dim : ∀ K : Set X, IsCompact K → HasCoveringDimensionLE K m) :
    HasCoveringDimensionLE X m := by
  classical
  intro 𝒜 h𝒜_open h𝒜_cover
  -- Use the canonical exhaustion with an empty initial stage.
  let K : CompactExhaustion X := (CompactExhaustion.choice X).shiftr
  have hK_zero : K 0 = ∅ := rfl
  -- First arrange the support control required by the recursive replacement construction.
  obtain ⟨ℬ₀, hℬ₀_refines, hℬ₀_cover, hℬ₀_control⟩ :=
    existsControlledOpenRefinement K hK_zero 𝒜 h𝒜_open h𝒜_cover
  have hℬ₀_open : ∀ B ∈ ℬ₀, IsOpen B := fun _ hB ↦ hℬ₀_refines.isOpen_of_mem hB
  -- The remaining source construction stabilizes successive compact-order improvements.
  obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_order⟩ :=
    existsGloballyBoundedRefinementOfControlledCover K hK_zero ℬ₀ hℬ₀_open hℬ₀_cover
      hℬ₀_control h_dim
  refine ⟨ℬ, ?_, hℬ_cover, hℬ_order⟩
  rw [isOpenRefinement_iff] at hℬ_refines hℬ₀_refines ⊢
  exact ⟨hℬ_refines.1.trans hℬ₀_refines.1, hℬ_refines.2⟩

/-- The numerical covering-dimension form of Exercise 50.8. -/
theorem coveringDimension_le_of_compact_subspaces {m : ℕ} {X : Type u}
    [TopologicalSpace X] [CompactlyExhaustibleSpace X] [T2Space X]
    (h_dim : ∀ K : Set X, IsCompact K → dim K ≤ (m : WithBot ℕ∞)) :
    dim X ≤ (m : WithBot ℕ∞) :=
  (coveringDimension_le_iff X m).2 <|
    hasCoveringDimensionLE_of_compact_subspaces fun K hK ↦
      (coveringDimension_le_iff K m).1 (h_dim K hK)
