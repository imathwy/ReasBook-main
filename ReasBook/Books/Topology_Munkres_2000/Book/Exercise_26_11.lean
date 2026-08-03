module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Basic

public section

open Set

universe u

/-- Helper for Exercise 26.11: a preconnected set meeting two disjoint open sets has a point
outside their union. -/
private lemma IsPreconnected.nonempty_sdiff_union_of_disjoint {X : Type u}
    [TopologicalSpace X] {s u v : Set X} (hs : IsPreconnected s) (hu : IsOpen u)
    (hv : IsOpen v) (huv : Disjoint u v) (hsu : (s ∩ u).Nonempty)
    (hsv : (s ∩ v).Nonempty) : (s \ (u ∪ v)).Nonempty := by
  -- If no point escapes, the two open sets cover the preconnected set.
  by_contra houtside
  rw [not_nonempty_iff_eq_empty] at houtside
  have hcover : s ⊆ u ∪ v := by
    intro x hx
    by_contra hxuv
    have hxoutside : x ∈ s \ (u ∪ v) := ⟨hx, hxuv⟩
    rw [houtside] at hxoutside
    exact hxoutside
  -- Preconnectedness then forces a point in the disjoint overlap.
  have hoverlap := hs u v hu hv hcover hsu hsv
  rw [disjoint_iff_inter_eq_empty.mp huv, inter_empty] at hoverlap
  obtain ⟨x, hx⟩ := hoverlap
  exact hx

/-- Exercise 26.11: In the repository's preconnectedness representation of Munkres
connectedness, the intersection of a nonempty chain of closed preconnected sets in a compact
Hausdorff space is preconnected. -/
theorem isPreconnected_sInter_of_chain {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (𝒜 : Set (Set X)) (h𝒜 : 𝒜.Nonempty)
    (hchain : IsChain (· ⊆ ·) 𝒜)
    (hclosed : ∀ A ∈ 𝒜, IsClosed A) (hconnected : ∀ A ∈ 𝒜, IsPreconnected A) :
    IsPreconnected (⋂₀ 𝒜) := by
  intro u v hu hv hcover hmeetU hmeetV
  -- Assume the relative overlap is empty and turn the two pieces into closed compact sets.
  by_contra hoverlap
  have hYclosed : IsClosed (⋂₀ 𝒜) := isClosed_sInter hclosed
  have hleft_eq : ⋂₀ 𝒜 ∩ u = ⋂₀ 𝒜 \ v := by
    ext x
    constructor
    · rintro ⟨hxY, hxu⟩
      refine ⟨hxY, ?_⟩
      intro hxv
      exact hoverlap ⟨x, hxY, hxu, hxv⟩
    · rintro ⟨hxY, hxv⟩
      rcases hcover hxY with hxu | hxv'
      · exact ⟨hxY, hxu⟩
      · exact False.elim (hxv hxv')
  have hright_eq : ⋂₀ 𝒜 ∩ v = ⋂₀ 𝒜 \ u := by
    ext x
    constructor
    · rintro ⟨hxY, hxv⟩
      refine ⟨hxY, ?_⟩
      intro hxu
      exact hoverlap ⟨x, hxY, hxu, hxv⟩
    · rintro ⟨hxY, hxu⟩
      rcases hcover hxY with hxu' | hxv
      · exact False.elim (hxu hxu')
      · exact ⟨hxY, hxv⟩
  have hleftClosed : IsClosed (⋂₀ 𝒜 ∩ u) := by
    rw [hleft_eq]
    exact hYclosed.sdiff hv
  have hrightClosed : IsClosed (⋂₀ 𝒜 ∩ v) := by
    rw [hright_eq]
    exact hYclosed.sdiff hu
  have hpiecesDisjoint : Disjoint (⋂₀ 𝒜 ∩ u) (⋂₀ 𝒜 ∩ v) := by
    rw [disjoint_left]
    intro x hxleft hxright
    exact hoverlap ⟨x, hxleft.1, hxleft.2, hxright.2⟩
  obtain ⟨U, V, hU, hV, hleftU, hrightV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed hleftClosed.isCompact
      hrightClosed.isCompact hrightClosed hpiecesDisjoint
  -- Every member of the chain meets both neighborhoods and therefore escapes their union.
  have hescape : ∀ A ∈ 𝒜, (A \ (U ∪ V)).Nonempty := by
    intro A hA
    have hAU : (A ∩ U).Nonempty := by
      obtain ⟨x, hxY, hxu⟩ := hmeetU
      exact ⟨x, sInter_subset_of_mem hA hxY, hleftU ⟨hxY, hxu⟩⟩
    have hAV : (A ∩ V).Nonempty := by
      obtain ⟨x, hxY, hxv⟩ := hmeetV
      exact ⟨x, sInter_subset_of_mem hA hxY, hrightV ⟨hxY, hxv⟩⟩
    exact (hconnected A hA).nonempty_sdiff_union_of_disjoint hU hV hUV hAU hAV
  let 𝒝 : Set (Set X) := (fun A : Set X ↦ A \ (U ∪ V)) '' 𝒜
  have h𝒝nonempty : 𝒝.Nonempty := by
    obtain ⟨A, hA⟩ := h𝒜
    exact ⟨A \ (U ∪ V), A, hA, rfl⟩
  letI : Nonempty 𝒝 := h𝒝nonempty.to_subtype
  have h𝒝chain : IsChain (· ⊆ ·) 𝒝 := by
    exact hchain.image_of_map_rel (· ⊆ ·) (· ⊆ ·) (fun A : Set X ↦ A \ (U ∪ V))
      (fun _ _ hAB _ hx ↦ ⟨hAB hx.1, hx.2⟩)
  have h𝒝closed : ∀ B ∈ 𝒝, IsClosed B := by
    rintro B ⟨A, hA, rfl⟩
    exact (hclosed A hA).sdiff (hU.union hV)
  -- Compactness gives a point in every escaped closed set of the directed chain.
  have h𝒝directed : DirectedOn (· ⊇ ·) 𝒝 := by
    intro B hB C hC
    rcases h𝒝chain.total hB hC with hBC | hCB
    · exact ⟨B, hB, Subset.rfl, hBC⟩
    · exact ⟨C, hC, hCB, Subset.rfl⟩
  have h𝒝escape : ∀ B ∈ 𝒝, B.Nonempty := by
    rintro B ⟨A, hA, rfl⟩
    exact hescape A hA
  obtain ⟨x, hx𝒝⟩ :=
    IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
      h𝒝directed h𝒝escape (fun B hB ↦ (h𝒝closed B hB).isCompact) h𝒝closed
  have hxY : x ∈ ⋂₀ 𝒜 := by
    intro A hA
    exact (hx𝒝 (A \ (U ∪ V)) ⟨A, hA, rfl⟩).1
  obtain ⟨A, hA⟩ := h𝒜
  have hxoutside : x ∉ U ∪ V := (hx𝒝 (A \ (U ∪ V)) ⟨A, hA, rfl⟩).2
  -- The original cover places this point in one closed piece and hence in its neighborhood.
  rcases hcover hxY with hxu | hxv
  · exact hxoutside (Or.inl (hleftU ⟨hxY, hxu⟩))
  · exact hxoutside (Or.inr (hrightV ⟨hxY, hxv⟩))
