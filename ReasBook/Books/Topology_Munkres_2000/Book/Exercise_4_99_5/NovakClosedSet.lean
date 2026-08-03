module

public import Topology_Munkres_2000.Book.Exercise_4_99_5.DisjointNeighborhoods
public import Mathlib.SetTheory.Cardinal.Continuum

public section

open Function Filter Set Topology

/-- Helper for Exercise 4.99.5: compute extension membership by pulling back a basic clopen. -/
lemma mem_ultrafilterExtend_iff {a : ℕ → Ultrafilter ℕ} (F : Ultrafilter ℕ) (B : Set ℕ) :
    B ∈ Ultrafilter.extend a F ↔ {n | B ∈ a n} ∈ F := by
  have heq : Ultrafilter.extend a F = joinM (F.map a) := by
    apply ultrafilter_extend_eq_iff.mpr
    exact ultrafilter_converges_iff.mpr rfl
  rw [heq]
  rfl

/-- Helper for Exercise 4.99.5: every infinite closed subset of `Ultrafilter ℕ` has full
ambient cardinality. -/
lemma ultrafilterNat_closedSet_cardinalMk (C : Set (Ultrafilter ℕ))
    (hC : IsClosed C) (hCinfinite : C.Infinite) :
    Cardinal.mk C = Cardinal.mk (Ultrafilter ℕ) := by
  classical
  -- An accumulation point yields disjoint ambient open sets, each meeting `C`.
  obtain ⟨x, hxC, hx⟩ :=
    hCinfinite.exists_accPt_of_subset_isCompact hC.isCompact Subset.rfl
  obtain ⟨U, hUopen, hUmeet, hUdisjoint⟩ :=
    hx.existsPairwiseDisjointOpen_meets
  choose a haU haC using hUmeet
  have hBasic (n : ℕ) :
      ∃ B : Set ℕ, B ∈ a n ∧ {F : Ultrafilter ℕ | B ∈ F} ⊆ U n := by
    obtain ⟨V, hVBasis, haV, hVU⟩ :=
      ultrafilterBasis_is_basis.exists_subset_of_mem_open (haU n) (hUopen n)
    obtain ⟨B, rfl⟩ := hVBasis
    exact ⟨B, haV, hVU⟩
  choose B haB hBU using hBasic
  have hBdisjoint : Pairwise (Disjoint on B) := by
    intro i j hij
    refine Set.disjoint_left.mpr (fun n hni hnj ↦ ?_)
    exact Set.disjoint_left.mp (hUdisjoint hij)
      (hBU i (show (pure n : Ultrafilter ℕ) ∈ {F | B i ∈ F} from
        Ultrafilter.mem_pure.mpr hni))
      (hBU j (show (pure n : Ultrafilter ℕ) ∈ {F | B j ∈ F} from
        Ultrafilter.mem_pure.mpr hnj))
  -- The Stone–Čech extension of the selected sequence is injective.
  have hExtendInjective : Function.Injective (Ultrafilter.extend a) := by
    intro F G hFG
    apply Ultrafilter.ext
    intro S
    let T : Set ℕ := ⋃ n ∈ S, B n
    have hpreimage : {n | T ∈ a n} = S := by
      ext n
      constructor
      · intro hT
        by_contra hnS
        have hcompl : Tᶜ ∈ a n := by
          apply Filter.mem_of_superset (haB n)
          intro z hzB hzT
          obtain ⟨m, hmS, hzm⟩ := Set.mem_iUnion₂.mp hzT
          have hnm : n ≠ m := fun hnm ↦ hnS (hnm ▸ hmS)
          exact Set.disjoint_left.mp (hBdisjoint hnm) hzB hzm
        exact (Ultrafilter.compl_mem_iff_notMem.mp hcompl) hT
      · intro hnS
        apply Filter.mem_of_superset (haB n)
        exact fun z hz ↦ Set.mem_iUnion₂.mpr ⟨n, hnS, hz⟩
    have hMem : S ∈ F ↔ S ∈ G := by
      rw [← hpreimage, ← mem_ultrafilterExtend_iff,
        hFG, mem_ultrafilterExtend_iff]
    exact hMem
  -- Continuity and density keep the whole extension inside the closed set.
  have hRange : Set.range (Ultrafilter.extend a) ⊆ C := by
    refine (continuous_ultrafilter_extend a).range_subset_closure_image_dense
      (denseRange_pure : DenseRange (pure : ℕ → Ultrafilter ℕ)) |>.trans ?_
    apply closure_minimal
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨n, rfl⟩ := hz
      simpa only [ultrafilter_extend_pure] using haC n
    · exact hC
  apply le_antisymm (Cardinal.mk_set_le C)
  exact Cardinal.mk_le_of_injective
    (f := fun F ↦ ⟨Ultrafilter.extend a F, hRange ⟨F, rfl⟩⟩)
    (fun F G h ↦ hExtendInjective (congrArg Subtype.val h))
