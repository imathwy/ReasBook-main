module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Mathlib.Topology.Constructions
import Topology_Munkres_2000.Book.Theorem_50_1

public section

open scoped CoveringDimension

universe u

/-- Helper for Theorem 50.2: an open cover can be refined with controlled order at
the points of a closed subspace whose covering dimension is bounded. -/
private lemma existsOpenRefinementWithOrderOnClosedSet
    {X : Type u} [TopologicalSpace X] {S : Set X} {n : ℕ}
    (hSclosed : IsClosed S) (hSdim : HasCoveringDimensionLE S n)
    (𝒜 : Set (Set X)) (h𝒜open : ∀ A ∈ 𝒜, IsOpen A)
    (h𝒜cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℬ : Set (Set X),
      IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
        ∀ s : S, Set.encard {B ∈ ℬ | s.1 ∈ B} ≤ (n + 1 : ℕ) := by
  classical
  -- Restrict the ambient cover to `S` and use its covering-dimension bound there.
  let traceCover : Set (Set S) :=
    (fun A : Set X ↦ ((↑) : S → X) ⁻¹' A) '' 𝒜
  have htraceOpen : ∀ A ∈ traceCover, IsOpen A := by
    rintro A ⟨U, hU, rfl⟩
    exact (h𝒜open U hU).preimage continuous_subtype_val
  have htraceCover : ⋃₀ traceCover = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    have hs : s.1 ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ s.1
    rw [Set.mem_sUnion] at hs ⊢
    obtain ⟨A, hA, hsA⟩ := hs
    exact ⟨((↑) : S → X) ⁻¹' A, ⟨A, hA, rfl⟩, hsA⟩
  obtain ⟨traceRefinement, hrefines, hrefinementCover, hrefinementOrder⟩ :=
    hSdim traceCover htraceOpen htraceCover
  -- Choose an original parent and an ambient open representative for each trace member.
  have hparentExists (B : traceRefinement) :
      ∃ A : 𝒜, (B.1 : Set S) ⊆ ((↑) : S → X) ⁻¹' (A.1 : Set X) := by
    obtain ⟨T, hT, hBT⟩ := hrefines.subset_of_mem B.2
    obtain ⟨A, hA, rfl⟩ := hT
    exact ⟨⟨A, hA⟩, hBT⟩
  choose parent hparent using hparentExists
  have hambientExists (B : traceRefinement) :
      ∃ U : Set X, IsOpen U ∧ ((↑) : S → X) ⁻¹' U = (B.1 : Set S) := by
    exact isOpen_induced_iff.mp (hrefines.isOpen_of_mem B.2)
  choose ambient hambientOpen hambientTrace using hambientExists
  let extended : traceRefinement → Set X :=
    fun B ↦ ambient B ∩ (parent B : Set X)
  let outside : 𝒜 → Set X := fun A ↦ (A : Set X) \ S
  let ℬ : Set (Set X) := Set.range (Sum.elim extended outside)
  refine ⟨ℬ, ?_, ?_, ?_⟩
  · -- Intersecting with the chosen parent preserves openness and refinement.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨j, rfl⟩
      cases j with
      | inl B =>
          exact ⟨parent B, (parent B).2, Set.inter_subset_right⟩
      | inr A =>
          exact ⟨A, A.2, Set.sdiff_subset⟩
    · rintro V ⟨j, rfl⟩
      cases j with
      | inl B =>
          exact (hambientOpen B).inter (h𝒜open (parent B) (parent B).2)
      | inr A =>
          exact (h𝒜open A A.2).sdiff hSclosed
  · -- Trace members cover `S`, while the original members minus `S` cover its complement.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    by_cases hxS : x ∈ S
    · let s : S := ⟨x, hxS⟩
      have hs : s ∈ ⋃₀ traceRefinement :=
        hrefinementCover.symm ▸ Set.mem_univ s
      rw [Set.mem_sUnion] at hs
      obtain ⟨B, hB, hsB⟩ := hs
      let j : traceRefinement := ⟨B, hB⟩
      have hsAmbient : x ∈ ambient j := by
        have hsPreimage : s ∈ ((↑) : S → X) ⁻¹' ambient j := by
          rw [hambientTrace j]
          exact hsB
        exact hsPreimage
      have hsParent : x ∈ (parent j : Set X) := hparent j hsB
      exact ⟨extended j, ⟨Sum.inl j, rfl⟩, hsAmbient, hsParent⟩
    · have hx : x ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ x
      rw [Set.mem_sUnion] at hx
      obtain ⟨A, hA, hxA⟩ := hx
      let j : 𝒜 := ⟨A, hA⟩
      exact ⟨outside j, ⟨Sum.inr j, rfl⟩, hxA, hxS⟩
  · -- At a point of `S`, outside members disappear and each remaining member has one trace.
    intro s
    let source : Set traceRefinement := {B | s ∈ (B.1 : Set S)}
    have hsub : {V ∈ ℬ | s.1 ∈ V} ⊆ extended '' source := by
      intro V hV
      obtain ⟨j, rfl⟩ := hV.1
      cases j with
      | inl B =>
          have hsTrace : s ∈ (B.1 : Set S) := by
            rw [← hambientTrace B]
            exact hV.2.1
          exact ⟨B, hsTrace, rfl⟩
      | inr A =>
          exact (hV.2.2 s.2).elim
    have hsourceImage :
        ((fun B : traceRefinement ↦ (B.1 : Set S)) '' source) =
          {B ∈ traceRefinement | s ∈ B} := by
      ext B
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j.2, hj⟩
      · intro hB
        exact ⟨⟨B, hB.1⟩, hB.2, rfl⟩
    calc
      Set.encard {V ∈ ℬ | s.1 ∈ V}
          ≤ Set.encard (extended '' source) := Set.encard_le_encard hsub
      _ ≤ Set.encard source := Set.encard_image_le extended source
      _ = Set.encard {B ∈ traceRefinement | s ∈ B} := by
        rw [← hsourceImage, Subtype.val_injective.encard_image]
      _ ≤ n + 1 := (Set.hasOrderLE_iff.mp hrefinementOrder) s

namespace HasCoveringDimensionLE

/-- Helper for Theorem 50.2: a common covering-dimension bound on two closed
subspaces covering `X` is also a bound on `X`. -/
theorem unionClosed
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} {n : ℕ}
    (hYclosed : IsClosed Y) (hZclosed : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    (hYdim : HasCoveringDimensionLE Y n)
    (hZdim : HasCoveringDimensionLE Z n) :
    HasCoveringDimensionLE X n := by
  classical
  intro 𝒜 h𝒜open h𝒜cover
  -- First control multiplicity on `Y`, then refine once more to control it on `Z`.
  obtain ⟨ℬ, hℬrefines, hℬcover, hℬorderY⟩ :=
    existsOpenRefinementWithOrderOnClosedSet hYclosed hYdim 𝒜 h𝒜open h𝒜cover
  obtain ⟨𝒞, h𝒞refines, h𝒞cover, h𝒞orderZ⟩ :=
    existsOpenRefinementWithOrderOnClosedSet hZclosed hZdim ℬ
      (fun B hB ↦ hℬrefines.isOpen_of_mem hB) hℬcover
  have hparentExists (C : 𝒞) :
      ∃ B : ℬ, (C.1 : Set X) ⊆ (B.1 : Set X) := by
    obtain ⟨B, hB, hCB⟩ := h𝒞refines.subset_of_mem C.2
    exact ⟨⟨B, hB⟩, hCB⟩
  choose parent hparent using hparentExists
  -- Group all second-stage members having the same first-stage parent.
  let grouped : ℬ → Set X := fun B ↦
    ⋃ C : {C : 𝒞 // parent C = B}, (C.1.1 : Set X)
  let 𝒟 : Set (Set X) := Set.range grouped
  have h𝒟refinesℬ : IsRefinement 𝒟 ℬ := by
    rw [isRefinement_iff]
    rintro D ⟨B, rfl⟩
    refine ⟨B, B.2, ?_⟩
    intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    rw [← C.2]
    exact hparent C.1 hxC
  have h𝒟open : ∀ D ∈ 𝒟, IsOpen D := by
    rintro D ⟨B, rfl⟩
    apply isOpen_iUnion
    intro C
    exact h𝒞refines.isOpen_of_mem C.1.2
  refine ⟨𝒟, ?_, ?_, ?_⟩
  · -- The grouped family remains an open refinement of the original cover.
    rw [isOpenRefinement_iff]
    exact ⟨h𝒟refinesℬ.trans hℬrefines.toIsRefinement, h𝒟open⟩
  · -- Each second-stage member lies in the group indexed by its chosen parent.
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃₀ 𝒞 := h𝒞cover.symm ▸ Set.mem_univ x
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨C, hC, hxC⟩ := hx
    let j : 𝒞 := ⟨C, hC⟩
    have hxGrouped : x ∈ grouped (parent j) := by
      rw [Set.mem_iUnion]
      exact ⟨⟨j, rfl⟩, hxC⟩
    exact ⟨grouped (parent j), ⟨parent j, rfl⟩, hxGrouped⟩
  · -- Over `Y` count parents; over `Z` count chosen second-stage witnesses.
    rw [Set.hasOrderLE_iff]
    intro x
    have hxYZ : x ∈ Y ∪ Z := hcover.symm ▸ Set.mem_univ x
    rcases hxYZ with hxY | hxZ
    · let y : Y := ⟨x, hxY⟩
      let source : Set ℬ := {B | x ∈ (B.1 : Set X)}
      have hsub : {D ∈ 𝒟 | x ∈ D} ⊆ grouped '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        have hxB : x ∈ (B.1 : Set X) := by
          rw [← C.2]
          exact hparent C.1 hxC
        exact ⟨B, hxB, rfl⟩
      have hsourceImage :
          ((fun B : ℬ ↦ (B.1 : Set X)) '' source) =
            {B ∈ ℬ | x ∈ B} := by
        ext B
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.2, hj⟩
        · intro hB
          exact ⟨⟨B, hB.1⟩, hB.2, rfl⟩
      calc
        Set.encard {D ∈ 𝒟 | x ∈ D}
            ≤ Set.encard (grouped '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le grouped source
        _ = Set.encard {B ∈ ℬ | x ∈ B} := by
          rw [← hsourceImage, Subtype.val_injective.encard_image]
        _ ≤ n + 1 := hℬorderY y
    · let z : Z := ⟨x, hxZ⟩
      let source : Set 𝒞 := {C | x ∈ (C.1 : Set X)}
      let groupOf : 𝒞 → Set X := fun C ↦ grouped (parent C)
      have hsub : {D ∈ 𝒟 | x ∈ D} ⊆ groupOf '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        refine ⟨C.1, hxC, ?_⟩
        exact congrArg grouped C.2
      have hsourceImage :
          ((fun C : 𝒞 ↦ (C.1 : Set X)) '' source) =
            {C ∈ 𝒞 | x ∈ C} := by
        ext C
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.2, hj⟩
        · intro hC
          exact ⟨⟨C, hC.1⟩, hC.2, rfl⟩
      calc
        Set.encard {D ∈ 𝒟 | x ∈ D}
            ≤ Set.encard (groupOf '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le groupOf source
        _ = Set.encard {C ∈ 𝒞 | x ∈ C} := by
          rw [← hsourceImage, Subtype.val_injective.encard_image]
        _ ≤ n + 1 := h𝒞orderZ z

end HasCoveringDimensionLE

/-- Theorem 50.2. If two closed subspaces cover `X`, then the covering dimension
of `X` is the maximum of their covering dimensions. -/
theorem coveringDimension_union_closed
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hY : IsClosed Y) (hZ : IsClosed Z) (hcover : Y ∪ Z = Set.univ) :
    dim X = max (dim Y) (dim Z) := by
  apply le_antisymm
  · -- Reduce the upper bound to the natural-valued companion, treating totalized endpoints.
    let d : WithBot ℕ∞ := max (dim Y) (dim Z)
    have hd : d = max (dim Y) (dim Z) := rfl
    rw [← hd]
    by_cases hdTop : d = ⊤
    · rw [hdTop]
      exact le_top
    by_cases hdBot : d = ⊥
    · have hYBot : dim Y = ⊥ := (max_eq_bot.mp hdBot).1
      have hZBot : dim Z = ⊥ := (max_eq_bot.mp hdBot).2
      have hYempty : IsEmpty Y := (coveringDimension_eq_bot_iff Y).mp hYBot
      have hZempty : IsEmpty Z := (coveringDimension_eq_bot_iff Z).mp hZBot
      have hXempty : IsEmpty X := by
        constructor
        intro x
        have hxYZ : x ∈ Y ∪ Z := hcover.symm ▸ Set.mem_univ x
        rcases hxYZ with hxY | hxZ
        · exact hYempty.false ⟨x, hxY⟩
        · exact hZempty.false ⟨x, hxZ⟩
      rw [(coveringDimension_eq_bot_iff X).mpr hXempty, hdBot]
    · let e : ℕ∞ := d.unbot hdBot
      have heNeTop : e ≠ ⊤ := by
        intro heTop
        apply hdTop
        calc
          d = (e : WithBot ℕ∞) := (WithBot.coe_unbot d hdBot).symm
          _ = ⊤ := by rw [heTop, WithBot.coe_top]
      have heLtTop : e < ⊤ := WithTop.lt_top_iff_ne_top.mpr heNeTop
      let n : ℕ := ENat.lift e heLtTop
      have hdNat : d = (n : WithBot ℕ∞) := by
        calc
          d = (e : WithBot ℕ∞) := (WithBot.coe_unbot d hdBot).symm
          _ = (n : WithBot ℕ∞) := by
            exact congrArg (fun a : ℕ∞ ↦ (a : WithBot ℕ∞))
              (ENat.coe_lift e heLtTop).symm
      have hYle : dim Y ≤ (n : WithBot ℕ∞) := by
        rw [← hdNat]
        exact le_max_left (dim Y) (dim Z)
      have hZle : dim Z ≤ (n : WithBot ℕ∞) := by
        rw [← hdNat]
        exact le_max_right (dim Y) (dim Z)
      have hYdim : HasCoveringDimensionLE Y n :=
        (coveringDimension_le_iff Y n).mp hYle
      have hZdim : HasCoveringDimensionLE Z n :=
        (coveringDimension_le_iff Z n).mp hZle
      rw [hdNat]
      exact (coveringDimension_le_iff X n).mpr
        (HasCoveringDimensionLE.unionClosed hY hZ hcover hYdim hZdim)
  · -- Closed-subspace monotonicity gives the reverse inequality componentwise.
    exact max_le hY.coveringDimension_le hZ.coveringDimension_le
