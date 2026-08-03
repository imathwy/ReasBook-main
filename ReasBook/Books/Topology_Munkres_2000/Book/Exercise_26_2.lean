module

public import Topology_Munkres_2000.Book.Example_12_4.CocountableTopology
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.NoetherianSpace

public section

/- Exercise 26.2 (1). In the finite complement topology on `ℝ`, every subspace is
compact. -/
#check (TopologicalSpace.NoetherianSpace.isCompact :
  ∀ s : Set (CofiniteTopology ℝ), IsCompact s)

open Set

universe u

namespace CocountableTopology

/-- Helper for Exercise 26.2: the complement of the cocountable image of a countable set is
open. -/
private lemma isOpen_compl_image_of_countable {X : Type u} {s : Set X} (hs : s.Countable) :
    IsOpen ((CocountableTopology.of '' s)ᶜ) := by
  -- Reduce openness to countability of the excluded image.
  rw [CocountableTopology.isOpen_iff']
  right
  simpa only [compl_compl] using hs.image CocountableTopology.of

/-- Helper for Exercise 26.2: a sequence point avoids the image of the tail starting at `n`
exactly when its index is less than `n`. -/
private lemma mem_compl_image_tail_iff {X : Type u} {f : ℕ → X}
    (hf : Function.Injective f) (m n : ℕ) :
    CocountableTopology.of (f m) ∈
        (CocountableTopology.of '' (f '' Set.Ici n))ᶜ ↔ m < n := by
  -- Expand complement membership while retaining the nested images as explicit witnesses.
  rw [Set.mem_compl_iff]
  constructor
  · intro hnotMem
    by_contra hmn
    apply hnotMem
    refine ⟨f m, ?_, rfl⟩
    refine ⟨m, Nat.le_of_not_gt hmn, rfl⟩
  · intro hmn hmem
    obtain ⟨x, ⟨k, hnk, hkx⟩, hx⟩ := hmem
    -- Injectivity of both maps identifies the tail index with `m`.
    have hfx : f k = f m := hkx.trans (CocountableTopology.of.injective hx)
    have hkm : k = m := hf hfx
    subst k
    exact (Nat.not_lt_of_ge hnk) hmn

/-- Helper for Exercise 26.2: the cocountable image of every infinite set is not compact. -/
private lemma not_isCompact_image_of_infinite {X : Type} {s : Set X} (hs : s.Infinite) :
    ¬ IsCompact (CocountableTopology.of '' s) := by
  classical
  let e : ℕ ↪ s := hs.natEmbedding s
  let f : ℕ → X := fun n ↦ e n
  have hf : Function.Injective f := by
    intro m n hmn
    exact e.injective (Subtype.ext hmn)
  have hfs (n : ℕ) : f n ∈ s := (e n).property
  let U : ℕ → Set (CocountableTopology X) := fun n ↦
    (CocountableTopology.of '' (f '' Set.Ici n))ᶜ
  have hUopen (n : ℕ) : IsOpen (U n) := by
    -- Every excluded tail is contained in the countable range of the sequence.
    have htail : (f '' Set.Ici n).Countable :=
      (Set.countable_range f).mono (Set.image_subset_range f (Set.Ici n))
    exact isOpen_compl_image_of_countable htail
  have hUcover : CocountableTopology.of '' s ⊆ ⋃ n, U n := by
    intro y hy
    obtain ⟨x, hxs, rfl⟩ := hy
    by_cases hx : x ∈ Set.range f
    · obtain ⟨m, rfl⟩ := hx
      -- The point with index `m` lies in the complement of the next tail.
      refine Set.mem_iUnion.2 ⟨m + 1, ?_⟩
      exact (mem_compl_image_tail_iff hf m (m + 1)).2 (Nat.lt_succ_self m)
    · -- A point outside the whole sequence range already avoids the zeroth tail.
      refine Set.mem_iUnion.2 ⟨0, ?_⟩
      rw [Set.mem_compl_iff]
      intro hmem
      obtain ⟨z, ⟨k, _, hkz⟩, hz⟩ := hmem
      apply hx
      refine ⟨k, ?_⟩
      exact hkz.trans (CocountableTopology.of.injective hz)
  intro hCompact
  rw [isCompact_iff_finite_subcover] at hCompact
  obtain ⟨t, ht⟩ := hCompact U hUopen hUcover
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range t
  have hpoint : CocountableTopology.of (f N) ∈ CocountableTopology.of '' s := by
    refine ⟨f N, hfs N, rfl⟩
  have hcovered := ht hpoint
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hcovered
  obtain ⟨hnt, hmem⟩ := Set.mem_iUnion.1 hn
  -- A selected index is below `N`, while membership in its tail complement forces the reverse.
  have hnN : n < N := Finset.mem_range.1 (hN hnt)
  have hNn : N < n := (mem_compl_image_tail_iff hf N n).1 hmem
  omega

end CocountableTopology

/-- Exercise 26.2 (2). In the cocountable topology on `ℝ`, the interval `[0, 1]`
is not compact. -/
theorem cocountableUnitInterval_not_isCompact :
    ¬ IsCompact (CocountableTopology.of '' Set.Icc (0 : ℝ) 1) := by
  -- The interval is infinite, so the generic tail-cover obstruction applies.
  have h01 : (0 : ℝ) < 1 := by
    norm_num
  exact CocountableTopology.not_isCompact_image_of_infinite (Set.Icc_infinite h01)
