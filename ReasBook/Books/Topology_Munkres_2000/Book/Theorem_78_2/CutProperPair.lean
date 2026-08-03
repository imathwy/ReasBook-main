module

public import Topology_Munkres_2000.Book.Algorithm_76_2.Cut
public import Topology_Munkres_2000.Book.Definition_77_1.Proper

import all Topology_Munkres_2000.Book.Definition_77_1.Proper

public section

universe u

namespace LabellingScheme.Cut

/-- Helper for Theorem 78.2: in a proper split scheme, the displayed opposite-sign
pair exhausts its label and therefore determines the canonical preceding cut. -/
theorem ofProperPair {alpha : Type u}
    (y₀ y₁ : List (alpha × Bool)) (c : alpha) (b : Bool)
    (rest : LabellingScheme alpha) (hy₀Length : 2 ≤ y₀.length)
    (hy₁Length : 2 ≤ y₁.length)
    (hproper : LabellingScheme.Proper
      (⟨y₀ ++ [(c, !b)],
          PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁,
          PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest)) :
    LabellingScheme.Cut
      (⟨y₀ ++ y₁,
          PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)
      (⟨y₀ ++ [(c, !b)],
          PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁,
          PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest) := by
  classical
  -- Route correction: isolate the combinatorial cut argument from the currently
  -- broken geometric realization imports of the main theorem.
  have hcMem : c ∈ LabellingScheme.labels
      (⟨y₀ ++ [(c, !b)],
          PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁,
          PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest) := by
    rw [LabellingScheme.mem_labels_iff]
    refine ⟨⟨y₀ ++ [(c, !b)],
      PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩, by simp, !b, ?_⟩
    simp
  have hcCount := LabellingScheme.proper_iff.mp hproper c hcMem
  simp only [LabellingScheme.labels, Multiset.cons_bind, List.map_append,
    List.map_cons, List.map_nil, Multiset.count_add, Multiset.coe_count,
    List.count_append, List.count_cons, List.count_nil, beq_self_eq_true,
    ite_true] at hcCount
  have hy₀Count : (y₀.map Prod.fst).count c = 0 := by omega
  have hy₁Count : (y₁.map Prod.fst).count c = 0 := by omega
  have hrestCount : Multiset.count c rest.labels = 0 := by
    simpa only [LabellingScheme.labels] using (show
      Multiset.count c (rest.bind fun word ↦ (word.1.map Prod.fst : Multiset alpha)) = 0
      by omega)
  -- Zero residual counts give precisely the three freshness fields of `Cut.of`.
  apply LabellingScheme.Cut.of y₀ y₁ c b rest hy₀Length hy₁Length
  · intro letter hletter heq
    apply List.not_mem_of_count_eq_zero hy₀Count
    exact List.mem_map.mpr ⟨letter, hletter, heq⟩
  · intro letter hletter heq
    apply List.not_mem_of_count_eq_zero hy₁Count
    exact List.mem_map.mpr ⟨letter, hletter, heq⟩
  · rw [LabellingScheme.avoidsLabel_iff]
    intro word hword letter hletter heq
    have hcNotMem : c ∉ rest.labels := Multiset.count_eq_zero.mp hrestCount
    apply hcNotMem
    rw [LabellingScheme.mem_labels_iff]
    obtain ⟨label, sign⟩ := letter
    simp only at heq hletter ⊢
    subst label
    exact ⟨word, hword, sign, hletter⟩

end LabellingScheme.Cut
