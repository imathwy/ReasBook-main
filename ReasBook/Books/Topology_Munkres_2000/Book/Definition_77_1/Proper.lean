module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme
import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Count

public section

universe u

namespace LabellingScheme

/-- The multiset of unsigned label occurrences in a labelling scheme. -/
def labels {α : Type u} (scheme : LabellingScheme α) : Multiset α :=
  scheme.bind (fun word ↦ word.1.map Prod.fst)

/-- A label occurs in `scheme.labels` exactly when it occurs with some sign in a polygon word. -/
theorem mem_labels_iff {α : Type u} {scheme : LabellingScheme α} {c : α} :
    c ∈ scheme.labels ↔ ∃ word ∈ scheme, ∃ b : Bool, (c, b) ∈ word.1 := by
  constructor
  · intro hc
    -- Select a polygon word containing an unsigned occurrence of `c`.
    rw [labels, Multiset.mem_bind] at hc
    obtain ⟨word, hword, hcword⟩ := hc
    -- Recover the signed letter whose first coordinate is that occurrence.
    rw [Multiset.mem_coe] at hcword
    obtain ⟨letter, hletter, hlabel⟩ := List.mem_map.mp hcword
    obtain ⟨label, sign⟩ := letter
    simp only at hlabel
    subst label
    exact ⟨word, hword, sign, hletter⟩
  · rintro ⟨word, hword, sign, hletter⟩
    -- Map the signed occurrence to its unsigned label, then insert its word into the bind.
    rw [labels, Multiset.mem_bind]
    refine ⟨word, hword, ?_⟩
    rw [Multiset.mem_coe]
    exact List.mem_map.mpr ⟨(c, sign), hletter, rfl⟩

/-- A labelling scheme is proper when every occurring unsigned label occurs exactly twice. -/
def Proper {α : Type u} (scheme : LabellingScheme α) : Prop :=
  ∀ c ∈ scheme.labels,
    ∃ rest : Multiset α, scheme.labels = c ::ₘ c ::ₘ rest ∧ c ∉ rest

/-- The multiplicity characterization of a proper labelling scheme. -/
theorem proper_iff {α : Type u} [DecidableEq α] {scheme : LabellingScheme α} :
    scheme.Proper ↔ ∀ c ∈ scheme.labels, Multiset.count c scheme.labels = 2 := by
  constructor
  · intro h c hc
    obtain ⟨rest, hrs, hnot⟩ := h c hc
    rw [hrs, Multiset.count_cons_self, Multiset.count_cons_self,
      Multiset.count_eq_zero.mpr hnot]
  · intro h c hc
    let rest := (scheme.labels.erase c).erase c
    refine ⟨rest, ?_, ?_⟩
    · rw [← Multiset.cons_erase hc]
      have hc' : c ∈ scheme.labels.erase c := by
        rw [← Multiset.count_pos, Multiset.count_erase_self, h c hc]
        decide
      rw [← Multiset.cons_erase hc']
    · rw [← Multiset.count_eq_zero, Multiset.count_erase_self,
        Multiset.count_erase_self, h c hc]


end LabellingScheme
