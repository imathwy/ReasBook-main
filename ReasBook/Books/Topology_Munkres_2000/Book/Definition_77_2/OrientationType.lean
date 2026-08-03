module

public import Topology_Munkres_2000.Book.Definition_77_2
import all Topology_Munkres_2000.Book.Definition_77_2

public section

universe u

namespace PolygonWord

/-- Helper for Definition 77.2: a signed label has one occurrence of each sign exactly when
it can be split off with a residual multiset avoiding that label. -/
private lemma signedPairDecomposition_iff_count {α : Type u} [DecidableEq α]
    {letters : Multiset (α × Bool)} {c : α} :
    (∃ rest : Multiset (α × Bool),
        letters = (c, true) ::ₘ (c, false) ::ₘ rest ∧ ∀ b : Bool, (c, b) ∉ rest) ↔
      ∀ b : Bool, Multiset.count (c, b) letters = 1 := by
  constructor
  · rintro ⟨rest, hletters, hrest⟩ b
    -- Count the two displayed signed occurrences; the residual count is zero.
    cases b <;> simp [hletters, hrest]
  · intro hcount
    -- Positive counts locate both signed occurrences in the multiset.
    have hpositive : (c, true) ∈ letters := by
      rw [← Multiset.count_pos, hcount true]
      decide
    have hnegative : (c, false) ∈ letters := by
      rw [← Multiset.count_pos, hcount false]
      decide
    have hfalseTrue : (c, false) ≠ (c, true) := by
      simp
    have htrueFalse : (c, true) ≠ (c, false) := by
      simp
    have hnegativeAfter : (c, false) ∈ letters.erase (c, true) :=
      (Multiset.mem_erase_of_ne hfalseTrue).mpr hnegative
    refine ⟨(letters.erase (c, true)).erase (c, false), ?_, ?_⟩
    · -- Erase the positive and negative occurrences in their displayed order.
      calc
        letters = (c, true) ::ₘ letters.erase (c, true) :=
          (Multiset.cons_erase hpositive).symm
        _ = (c, true) ::ₘ (c, false) ::ₘ (letters.erase (c, true)).erase (c, false) :=
          congrArg (Multiset.cons (c, true)) (Multiset.cons_erase hnegativeAfter).symm
    · intro b
      -- Both residual signed counts vanish after erasing their unique occurrence.
      rw [← Multiset.count_eq_zero]
      cases b
      · rw [Multiset.count_erase_self, Multiset.count_erase_of_ne hfalseTrue,
          hcount false]
      · rw [Multiset.count_erase_of_ne htrueFalse, Multiset.count_erase_self,
          hcount true]

/-- The signed-count characterization of a polygon word of torus type. -/
theorem torusType_iff_count {α : Type u} [DecidableEq α] {word : PolygonWord α} :
    word.TorusType ↔
      ∀ c ∈ ({word} : LabellingScheme α).labels,
        ∀ b : Bool, Multiset.count (c, b) (word.1 : Multiset (α × Bool)) = 1 := by
  -- Apply the signed-pair characterization independently to every occurring label.
  unfold TorusType
  constructor
  · intro hword c hc
    exact signedPairDecomposition_iff_count.mp (hword c hc)
  · intro hword c hc
    exact signedPairDecomposition_iff_count.mpr (hword c hc)

/-- The proper-word complement characterization of projective type. -/
theorem projectiveType_iff {α : Type u} {word : PolygonWord α} :
    word.ProjectiveType ↔
      ({word} : LabellingScheme α).Proper ∧ ¬ word.TorusType := by
  rfl

/-- Helper for Definition 77.2: forgetting signs maps a signed-pair decomposition to two
unsigned copies while preserving avoidance by the residual multiset. -/
private lemma signedPairDecomposition_map_fst {α : Type u} {letters rest : Multiset (α × Bool)}
    {c : α} (hletters : letters = (c, true) ::ₘ (c, false) ::ₘ rest)
    (hrest : ∀ b : Bool, (c, b) ∉ rest) :
    letters.map Prod.fst = c ::ₘ c ::ₘ rest.map Prod.fst ∧ c ∉ rest.map Prod.fst := by
  constructor
  · -- Mapping the displayed signed pair forgets both signs.
    rw [hletters, Multiset.map_cons, Multiset.map_cons]
  · intro hc
    -- Any unsigned residual occurrence would lift to a forbidden signed occurrence.
    rw [Multiset.mem_map] at hc
    obtain ⟨⟨label, sign⟩, hletter, hlabel⟩ := hc
    simp only at hlabel
    subst label
    exact hrest sign hletter

/-- A polygon word of torus type is a proper single-region labelling scheme. -/
theorem TorusType.proper {α : Type u} {word : PolygonWord α} (hword : word.TorusType) :
    ({word} : LabellingScheme α).Proper := by
  -- Route correction: the implementation import exposes the intrinsic `Proper` constructor shape.
  unfold LabellingScheme.Proper
  intro c hc
  -- Forget signs in the intrinsic torus-type decomposition for this label.
  obtain ⟨rest, hletters, hrest⟩ := hword c hc
  obtain ⟨hmapped, havoids⟩ := signedPairDecomposition_map_fst hletters hrest
  refine ⟨rest.map Prod.fst, ?_, havoids⟩
  -- A singleton scheme's label multiset is precisely the mapped word.
  simpa only [LabellingScheme.labels, Multiset.singleton_bind, Multiset.map_coe] using hmapped


end PolygonWord
