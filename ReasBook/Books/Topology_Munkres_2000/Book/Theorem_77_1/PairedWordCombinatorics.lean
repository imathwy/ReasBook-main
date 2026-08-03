module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme
public import Mathlib.Data.Set.Card

public section

namespace SurfaceWord

/-- Helper for Theorem 77.1: a raw signed word is paired when every unsigned
label fiber consists of exactly two positions. -/
def IsPaired (letters : List (α × Bool)) : Prop :=
  ∀ i : Fin letters.length,
    {j : Fin letters.length | (letters.get j).1 = (letters.get i).1}.ncard = 2

/-- Helper for Theorem 77.1: a two-element fiber has a unique member other
than any specified member of that fiber. -/
theorem ncardFiber_eq_two_iff_uniqueOther (f : ι → α) (i : ι) :
    {j : ι | f j = f i}.ncard = 2 ↔
      ∃! j : ι, j ≠ i ∧ f j = f i := by
  constructor
  · intro hcard
    obtain ⟨x, y, hxy, hfiber⟩ := Set.ncard_eq_two.mp hcard
    have hi : i = x ∨ i = y := by
      have hiFiber : i ∈ {j : ι | f j = f i} := by
        exact rfl
      rw [hfiber] at hiFiber
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hiFiber
    rcases hi with rfl | rfl
    · refine ⟨y, ⟨hxy.symm, ?_⟩, ?_⟩
      · -- Membership of the second fiber point gives the required value equality.
        have hyFiber : y ∈ {j : ι | f j = f i} := by
          rw [hfiber]
          exact Set.mem_insert_iff.mpr (Or.inr rfl)
        exact hyFiber
      · intro z hz
        have hzFiber : z ∈ {j : ι | f j = f i} := hz.2
        rw [hfiber] at hzFiber
        rcases hzFiber with hzx | hzy
        · exact (hz.1 hzx).elim
        · exact hzy
    · refine ⟨x, ⟨hxy, ?_⟩, ?_⟩
      · -- Membership of the first fiber point gives the required value equality.
        have hxFiber : x ∈ {j : ι | f j = f i} := by
          rw [hfiber]
          exact Set.mem_insert_iff.mpr (Or.inl rfl)
        exact hxFiber
      · intro z hz
        have hzFiber : z ∈ {j : ι | f j = f i} := hz.2
        rw [hfiber] at hzFiber
        rcases hzFiber with hzx | hzy
        · exact hzx
        · exact (hz.1 hzy).elim
  · rintro ⟨j, hj, hj_unique⟩
    apply Set.ncard_eq_two.mpr
    refine ⟨i, j, hj.1.symm, ?_⟩
    ext k
    constructor
    · intro hk
      by_cases hki : k = i
      · exact Set.mem_insert_iff.mpr (Or.inl hki)
      · exact Set.mem_insert_iff.mpr (Or.inr (hj_unique k ⟨hki, hk⟩))
    · intro hk
      rcases hk with hki | hkj
      · change f k = f i
        simp only [hki]
      · change f k = f i
        simp only [Set.mem_singleton_iff] at hkj
        simpa only [hkj] using hj.2

/-- Helper for Theorem 77.1: unsigned multiplicity two is equivalent to the
unique-distinct-mate formulation used by the edge-pasting API. -/
theorem isPaired_iff_uniqueMate (letters : List (α × Bool)) :
    IsPaired letters ↔
      ∀ i : Fin letters.length, ∃! j : Fin letters.length,
        j ≠ i ∧ (letters.get j).1 = (letters.get i).1 := by
  constructor
  · intro hpaired i
    -- Read the two-element unsigned-label fiber at the selected position.
    exact (ncardFiber_eq_two_iff_uniqueOther
      (fun j : Fin letters.length ↦ (letters.get j).1) i).mp (hpaired i)
  · intro hmates i
    -- Repackage the unique mate as the cardinality statement defining pairing.
    exact (ncardFiber_eq_two_iff_uniqueOther
      (fun j : Fin letters.length ↦ (letters.get j).1) i).mpr (hmates i)

/-- Helper for Theorem 77.1: a paired word has either opposite signs at every
unsigned-label pair or a pair whose two signs agree. -/
theorem IsPaired.signDichotomy {letters : List (α × Bool)}
    (hpaired : IsPaired letters) :
    (∀ i : Fin letters.length,
      ∃! j : Fin letters.length,
        j ≠ i ∧ (letters.get j).1 = (letters.get i).1 ∧
          (letters.get j).2 ≠ (letters.get i).2) ∨
      ∃ i j : Fin letters.length,
        i ≠ j ∧ (letters.get i).1 = (letters.get j).1 ∧
          (letters.get i).2 = (letters.get j).2 := by
  classical
  by_cases hsame : ∃ i j : Fin letters.length,
      i ≠ j ∧ (letters.get i).1 = (letters.get j).1 ∧
        (letters.get i).2 = (letters.get j).2
  · exact Or.inr hsame
  · left
    have hmates := (isPaired_iff_uniqueMate letters).mp hpaired
    intro i
    obtain ⟨j, hj, hj_unique⟩ := hmates i
    refine ⟨j, ⟨hj.1, hj.2, ?_⟩, ?_⟩
    · -- Equal mate signs would put this pair in the excluded projective branch.
      intro hsign
      exact hsame ⟨i, j, hj.1.symm, hj.2.symm, hsign.symm⟩
    · intro k hk
      -- Unsigned-label uniqueness already determines the signed mate position.
      exact hj_unique k ⟨hk.1, hk.2.1⟩

end SurfaceWord
