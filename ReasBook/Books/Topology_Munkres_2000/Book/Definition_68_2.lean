module

public import Topology_Munkres_2000.Book.Definition_68_2.ReducedWord

public section

/- Definition 68.2 (1): A reduced word has nonidentity letters from the specified subgroups,
with no specified subgroup containing two adjacent letters; the empty word is included. -/
#check Subgroup.ReducedWord

/- Definition 68.2 (2): If the specified subgroups generate the ambient group, every element is
represented by a reduced word. -/
namespace Subgroup.ReducedWord

universe u v

variable {G : Type u} {ι : Type v} [Group G]

/-- Definition 68.2 (2): If the specified subgroups generate the ambient group, every element is
represented by a reduced word. -/
theorem exists_prod_eq_of_iSup_eq_top (H : ι → Subgroup G)
    (h_generate : ⨆ i, H i = ⊤) (x : G) :
    ∃ w : ReducedWord H, w.prod = x := by
  -- Start from an arbitrary subgroup word, then replace it by its reduced normal form.
  obtain ⟨w, hw⟩ := (Subgroup.iSup_eq_top_iff_exists_word H).mp h_generate x
  obtain ⟨r, hr_prod, _⟩ := exists_prod_eq_listProd_length_le H w.toList w.mem_subgroup
  refine ⟨r, ?_⟩
  rw [hr_prod, ← Word.prod_def w]
  exact (Word.represents_iff w x).mp hw

end Subgroup.ReducedWord
