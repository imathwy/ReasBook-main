module

public import Topology_Munkres_2000.Book.Definition_77_2.OrientationType
import all Topology_Munkres_2000.Book.Definition_77_2.OrientationType
import Mathlib.Data.List.Duplicate

public section

universe u

namespace PolygonWord.ProjectiveType

/-- Helper for Assumption 77.1: forgetting Boolean signs decomposes the multiplicity of a
label into the multiplicities of its two signed lifts. -/
private lemma count_map_fst {α : Type u} [DecidableEq α]
    (letters : Multiset (α × Bool)) (c : α) :
    Multiset.count c (letters.map Prod.fst) =
      Multiset.count (c, false) letters + Multiset.count (c, true) letters := by
  induction letters using Multiset.induction_on with
  | empty =>
      -- The identity is immediate when there are no signed letters.
      simp
  | @cons letter letters ih =>
      obtain ⟨label, sign⟩ := letter
      -- Separate whether the new letter lies over `c`, then inspect its Boolean sign.
      by_cases hlabel : label = c
      · subst label
        cases sign
        · simp [ih]
          omega
        · simp [ih]
          omega
      · have hcLabel : c ≠ label := Ne.symm hlabel
        cases sign
        · simp [hcLabel, ih]
        · simp [hcLabel, ih]

/-- Helper for Assumption 77.1: if a Boolean fiber has total multiplicity two and one
specified signed lift does not occur once, then some signed lift occurs twice. -/
private lemma existsSignCountEqTwo {α : Type u} [DecidableEq α]
    (letters : Multiset (α × Bool)) (c : α) (sign : Bool)
    (htotal : Multiset.count c (letters.map Prod.fst) = 2)
    (hne : Multiset.count (c, sign) letters ≠ 1) :
    ∃ repeatedSign : Bool, Multiset.count (c, repeatedSign) letters = 2 := by
  have hsum : Multiset.count (c, false) letters +
      Multiset.count (c, true) letters = 2 := by
    -- Rewrite the unsigned count as the sum of the two signed counts.
    rw [← count_map_fst]
    exact htotal
  by_cases hfalse : Multiset.count (c, false) letters = 2
  · exact ⟨false, hfalse⟩
  · refine ⟨true, ?_⟩
    -- The remaining signed count must carry the full multiplicity two.
    cases sign <;> omega

/-- Helper for Assumption 77.1: a duplicated list element determines two ordered
occurrences and the three fragments surrounding them. -/
private lemma existsRepeatedLetterDecomposition {β : Type*} {letter : β}
    {letters : List β} (hduplicate : List.Duplicate letter letters) :
    ∃ y₀ y₁ y₂ : List β,
      letters = y₀ ++ [letter] ++ y₁ ++ [letter] ++ y₂ := by
  induction hduplicate with
  | @cons_mem tail hmem =>
      -- Split the tail at the second occurrence of `letter`.
      rw [List.mem_iff_append] at hmem
      obtain ⟨y₁, y₂, hy⟩ := hmem
      refine ⟨[], y₁, y₂, ?_⟩
      simp [hy]
  | @cons_duplicate head tail htail ih =>
      -- Extend the fragment preceding both occurrences by the new head.
      obtain ⟨y₀, y₁, y₂, hy⟩ := ih
      refine ⟨head :: y₀, y₁, y₂, ?_⟩
      simp only [hy, List.cons_append]

/-- Assumption 77.1: A projective-type polygon word contains two occurrences of the
same label with the same exponent, with possibly empty intervening fragments. -/
theorem exists_sameExponent {α : Type u} {word : PolygonWord α}
    (hword : word.ProjectiveType) :
    ∃ y₀ y₁ y₂ : List (α × Bool), ∃ letter : α × Bool,
      word.1 = y₀ ++ [letter] ++ y₁ ++ [letter] ++ y₂ := by
  classical
  -- Properness fixes unsigned multiplicities, while non-torus type selects a bad sign.
  obtain ⟨hproper, hnottorus⟩ := projectiveType_iff.mp hword
  rw [torusType_iff_count] at hnottorus
  push Not at hnottorus
  obtain ⟨label, hlabel, sign, hsignedNe⟩ := hnottorus
  have hschemeCount :
      Multiset.count label ({word} : LabellingScheme α).labels = 2 :=
    (LabellingScheme.proper_iff.mp hproper) label hlabel
  have hunsignedCount :
      Multiset.count label ((word.1 : Multiset (α × Bool)).map Prod.fst) = 2 := by
    -- A singleton scheme's unsigned labels are the projection of its unique word.
    simpa only [LabellingScheme.labels, Multiset.singleton_bind, Multiset.map_coe]
      using hschemeCount
  obtain ⟨repeatedSign, hrepeatedCount⟩ :=
    existsSignCountEqTwo (word.1 : Multiset (α × Bool)) label sign
      hunsignedCount hsignedNe
  have hduplicate : List.Duplicate (label, repeatedSign) word.1 := by
    -- Transport the multiset count to the list and invoke the canonical duplicate criterion.
    rw [List.duplicate_iff_two_le_count, ← Multiset.coe_count, hrepeatedCount]
  obtain ⟨y₀, y₁, y₂, hdecomposition⟩ :=
    existsRepeatedLetterDecomposition hduplicate
  -- Package the repeated signed letter and its three surrounding fragments.
  exact ⟨y₀, y₁, y₂, (label, repeatedSign), hdecomposition⟩

end PolygonWord.ProjectiveType
