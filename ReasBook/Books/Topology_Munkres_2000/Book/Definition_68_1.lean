module

public import Topology_Munkres_2000.Book.Definition_68_1.Word

public section

/- Definition 68.1 (1): A word in an indexed family of subgroups is a finite ordered list
whose letters each belong to one of the specified subgroups. -/
#check Subgroup.Word

/- Definition 68.1 (2): A word represents the group element equal to its ordered product. -/
#check Subgroup.Word.Represents

namespace Subgroup

universe u v

variable {G : Type u} {ι : Type v} [Group G]

/-- Definition 68.1 (3): An indexed family of subgroups has supremum `⊤` exactly when every
group element is represented by a finite word in the family. -/
theorem iSup_eq_top_iff_exists_word (H : ι → Subgroup G) :
    (⨆ i, H i) = ⊤ ↔ ∀ x : G, ∃ w : Word H, w.Represents x := by
  constructor
  · intro htop x
    -- Convert generation into membership, then build a representing word by supremum induction.
    have hx : x ∈ ⨆ i, H i := by
      rw [htop]
      exact Subgroup.mem_top x
    refine Subgroup.iSup_induction H (C := fun y ↦ ∃ w : Word H, w.Represents y) hx ?_ ?_ ?_
    · intro i y hy
      -- A generator is represented by its singleton word.
      have hrep : (Word.singleton H i y hy).Represents y := by
        rw [Word.represents_iff, Word.prod_singleton]
      exact Exists.intro (Word.singleton H i y hy) hrep
    · -- The identity is represented by the empty word.
      have hrep : (Word.empty H).Represents 1 := by
        rw [Word.represents_iff, Word.prod_empty]
      exact Exists.intro (Word.empty H) hrep
    · intro y z hy hz
      -- Concatenation multiplies elements represented by the two induction words.
      obtain ⟨wy, hwy⟩ := hy
      obtain ⟨wz, hwz⟩ := hz
      have hyprod : wy.prod = y := (Word.represents_iff wy y).mp hwy
      have hzprod : wz.prod = z := (Word.represents_iff wz z).mp hwz
      have hrep : (Word.append H wy wz).Represents (y * z) := by
        rw [Word.represents_iff, Word.prod_append, hyprod, hzprod]
      exact Exists.intro (Word.append H wy wz) hrep
  · intro hwords
    -- Products of representing words lie in the supremum, so every element does.
    apply (Subgroup.eq_top_iff' (⨆ i, H i)).mpr
    intro x
    obtain ⟨w, hw⟩ := hwords x
    have hprod : w.prod ∈ ⨆ i, H i := Word.prod_mem_iSup H w
    have heq : w.prod = x := (Word.represents_iff w x).mp hw
    rw [← heq]
    exact hprod

end Subgroup
