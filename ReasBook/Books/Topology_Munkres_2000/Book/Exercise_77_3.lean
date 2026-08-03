module

public import Topology_Munkres_2000.Book.Lemma_77_4
public import Mathlib.Data.Fintype.EquivFin
import all Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Definition_76_6.Relabel

public section

universe u

namespace PolygonWord

/-- Removing an adjacent inverse pair leaves enough letters for a polygon word. -/
theorem cancelPair_length {α : Type u} (y₀ y₁ : List (α × Bool))
    (h_length : 4 ≤ (y₀ ++ y₁).length) :
    3 ≤ (y₀ ++ y₁).length :=
  Nat.le_trans (by decide) h_length

/-- The commutator-front rearrangement has enough letters for a polygon word. -/
theorem commutatorFront_length {α : Type u} (word : PolygonWord α)
    (w₀ y₁ y₂ y₃ y₄ y₅ : List (α × Bool)) (a b : α)
    (h_decomp : word.1 =
      w₀ ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
        [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅) :
    3 ≤ (w₀ ++ [(a, true), (b, true), (a, false), (b, false)] ++
      y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅).length := by
  have h_length := word.property
  rw [h_decomp] at h_length
  simp only [List.length_append, List.length_cons, List.length_nil] at h_length ⊢
  omega

end PolygonWord

namespace SurfaceClassificationWord

/-- The polygon word `abacb⁻¹c⁻¹`. -/
def abacBInvCInv : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (0, true), (2, true), (1, false), (2, false)], by decide⟩

/-- The polygon word `abca⁻¹cb`. -/
def abcAInvCb : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (2, true), (0, false), (2, true), (1, true)], by decide⟩

/-- The polygon word `abbca⁻¹ddc⁻¹`. -/
def abbcAInvDdCInv : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (1, true), (2, true), (0, false),
    (3, true), (3, true), (2, false)], by decide⟩

/-- The polygon word `abcda⁻¹b⁻¹c⁻¹d⁻¹`. -/
def abcdAInvBInvCInvDInv : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (2, true), (3, true), (0, false),
    (1, false), (2, false), (3, false)], by decide⟩

/-- The polygon word `abcda⁻¹c⁻¹b⁻¹d⁻¹`. -/
def abcdAInvCInvBInvDInv : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (2, true), (3, true), (0, false),
    (2, false), (1, false), (3, false)], by decide⟩

/-- The polygon word `aabcdc⁻¹b⁻¹d⁻¹`. -/
def aabcdCInvBInvDInv : PolygonWord ℕ :=
  ⟨[(0, true), (0, true), (1, true), (2, true), (3, true),
    (2, false), (1, false), (3, false)], by decide⟩

/-- The polygon word `abcdabdc`. -/
def abcdAbdc : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (2, true), (3, true), (0, true),
    (1, true), (3, true), (2, true)], by decide⟩

/-- The polygon word `abcdabcd`. -/
def abcdAbcd : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (2, true), (3, true), (0, true),
    (1, true), (2, true), (3, true)], by decide⟩

/-- The standard word `abab`. -/
def projectivePlane : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (0, true), (1, true)], by decide⟩

/-- The standard two-crosscap word `aabb`. -/
def twoCrosscap : PolygonWord ℕ :=
  ⟨[(0, true), (0, true), (1, true), (1, true)], by decide⟩

/-- The standard three-crosscap word `aabbcc`. -/
def threeCrosscap : PolygonWord ℕ :=
  ⟨[(0, true), (0, true), (1, true), (1, true), (2, true), (2, true)], by decide⟩

/-- The standard four-crosscap word `aabbccdd`. -/
def fourCrosscap : PolygonWord ℕ :=
  ⟨[(0, true), (0, true), (1, true), (1, true), (2, true),
    (2, true), (3, true), (3, true)], by decide⟩

/-- The standard one-handle word `aba⁻¹b⁻¹`. -/
def oneHandle : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (0, false), (1, false)], by decide⟩

/-- The standard two-handle word `aba⁻¹b⁻¹cdc⁻¹d⁻¹`. -/
def twoHandle : PolygonWord ℕ :=
  ⟨[(0, true), (1, true), (0, false), (1, false), (2, true),
    (3, true), (2, false), (3, false)], by decide⟩


end SurfaceClassificationWord

namespace LabellingScheme

/-- Helper for Exercise 77.3: a singleton scheme is proper exactly when every
unsigned label in its word occurs twice. -/
theorem proper_singleton_iff {α : Type u} [DecidableEq α]
    (word : PolygonWord α) :
    ({word} : LabellingScheme α).Proper ↔
      ∀ c ∈ word.1.map Prod.fst, (word.1.map Prod.fst).count c = 2 := by
  -- Normalize the singleton bind in `labels`, leaving only the word's label list.
  rw [LabellingScheme.proper_iff]
  simp [LabellingScheme.labels]

/-- Helper for Exercise 77.3: every letter of a polygon word contributes its
unsigned label to the associated singleton scheme. -/
theorem mem_labels_singleton_of_mem {α : Type u} (word : PolygonWord α)
    (letter : α × Bool) (hletter : letter ∈ word.1) :
    letter.1 ∈ ({word} : LabellingScheme α).labels := by
  -- Use the public membership characterization without unfolding the opaque projection.
  rw [LabellingScheme.mem_labels_iff]
  have hword : word ∈ ({word} : LabellingScheme α) := by simp
  exact ⟨word, hword, letter.2, hletter⟩

/-- Helper for Exercise 77.3: a singleton scheme avoids a label exactly when
every signed letter of its word has a different unsigned label. -/
theorem singleton_avoidsLabel_iff {α : Type u} (word : PolygonWord α) (a : α) :
    ({word} : LabellingScheme α).AvoidsLabel a ↔
      ∀ letter ∈ word.1, letter.1 ≠ a := by
  -- The singleton membership condition selects the unique polygon word.
  rw [LabellingScheme.avoidsLabel_iff]
  simp

end LabellingScheme

/-- Helper for Exercise 77.3: two displayed copies exhaust multiplicity two
exactly when neither surrounding fragment contains another copy. -/
private theorem count_append_two_self_eq_two_iff {α : Type u} [DecidableEq α]
    (left right : List α) (a : α) :
    (left ++ [a, a] ++ right).count a = 2 ↔
      left.count a = 0 ∧ right.count a = 0 := by
  -- Expand list counts so the claim reduces to arithmetic on natural numbers.
  simp only [List.count_append, List.count_cons, List.count_nil, beq_self_eq_true, ite_true]
  omega

namespace LabellingScheme.Proper

/-- Helper for Exercise 77.3: two displayed occurrences of a label exhaust all
occurrences of that label in the three residual fragments of a proper word. -/
theorem not_mem_fragments_of_twoOccurrences {α : Type u}
    (word : PolygonWord α) (z₀ z₁ z₂ : List (α × Bool)) (a : α)
    (s₀ s₁ : Bool) (h_proper : ({word} : LabellingScheme α).Proper)
    (h_decomp : word.1 = z₀ ++ [(a, s₀)] ++ z₁ ++ [(a, s₁)] ++ z₂) :
    (∀ letter ∈ z₀, letter.1 ≠ a) ∧
      (∀ letter ∈ z₁, letter.1 ≠ a) ∧
      (∀ letter ∈ z₂, letter.1 ≠ a) := by
  classical
  -- Properness fixes the total unsigned multiplicity of the displayed label at two.
  rw [LabellingScheme.proper_singleton_iff] at h_proper
  have ha_mem : a ∈ word.1.map Prod.fst := by
    rw [h_decomp]
    simp
  have ha_count := h_proper a ha_mem
  rw [h_decomp] at ha_count
  simp only [List.map_append, List.map_cons, List.map_nil,
    List.count_append, List.count_cons, List.count_nil, beq_self_eq_true,
    ite_true] at ha_count
  have hz₀ : (z₀.map Prod.fst).count a = 0 := by omega
  have hz₁ : (z₁.map Prod.fst).count a = 0 := by omega
  have hz₂ : (z₂.map Prod.fst).count a = 0 := by omega
  -- A positive list count would contradict each of the three zero-count equations.
  constructor
  · intro letter hletter hlabel
    have ha_not_mem := List.not_mem_of_count_eq_zero hz₀
    apply ha_not_mem
    rw [← hlabel]
    exact List.mem_map.mpr ⟨letter, hletter, rfl⟩
  constructor
  · intro letter hletter hlabel
    have ha_not_mem := List.not_mem_of_count_eq_zero hz₁
    apply ha_not_mem
    rw [← hlabel]
    exact List.mem_map.mpr ⟨letter, hletter, rfl⟩
  · intro letter hletter hlabel
    have ha_not_mem := List.not_mem_of_count_eq_zero hz₂
    apply ha_not_mem
    rw [← hlabel]
    exact List.mem_map.mpr ⟨letter, hletter, rfl⟩

/-- Helper for Exercise 77.3: in a proper interlaced pair, the two labels are
distinct and all six residual fragments avoid both labels. -/
theorem fresh_interlacedPair {α : Type u} (word : PolygonWord α)
    (w₀ y₁ y₂ y₃ y₄ y₅ : List (α × Bool)) (a b : α)
    (h_proper : ({word} : LabellingScheme α).Proper)
    (h_decomp : word.1 =
      w₀ ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
        [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅) :
    a ≠ b ∧
      (∀ letter ∈ w₀ ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ a) ∧
        (∀ letter ∈ w₀ ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ b) := by
  classical
  -- Apply the two-occurrence lemma separately to `a` and `b`.
  have hdecompA : word.1 =
      (w₀ ++ y₁) ++ [(a, true)] ++
        (y₂ ++ [(b, true)] ++ y₃) ++ [(a, false)] ++
          (y₄ ++ [(b, false)] ++ y₅) := by
    simpa only [List.append_assoc] using h_decomp
  have hA := not_mem_fragments_of_twoOccurrences word
    (w₀ ++ y₁) (y₂ ++ [(b, true)] ++ y₃)
      (y₄ ++ [(b, false)] ++ y₅) a true false h_proper hdecompA
  have hdecompB : word.1 =
      (w₀ ++ y₁ ++ [(a, true)] ++ y₂) ++ [(b, true)] ++
        (y₃ ++ [(a, false)] ++ y₄) ++ [(b, false)] ++ y₅ := by
    simpa only [List.append_assoc] using h_decomp
  have hB := not_mem_fragments_of_twoOccurrences word
    (w₀ ++ y₁ ++ [(a, true)] ++ y₂)
      (y₃ ++ [(a, false)] ++ y₄) y₅ b true false h_proper hdecompB
  have hbMem : (b, true) ∈ y₂ ++ [(b, true)] ++ y₃ := by simp
  have ha_ne_b : a ≠ b := Ne.symm (hA.2.1 (b, true) hbMem)
  refine ⟨ha_ne_b, ?_, ?_⟩
  · intro letter hletter
    simp only [List.mem_append] at hletter
    rcases hletter with ((((hw | hy₁) | hy₂) | hy₃) | hy₄) | hy₅
    · exact hA.1 letter (List.mem_append_left y₁ hw)
    · exact hA.1 letter (List.mem_append_right w₀ hy₁)
    · apply hA.2.1 letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl hy₂)
    · apply hA.2.1 letter
      simp only [List.mem_append]
      exact Or.inr hy₃
    · apply hA.2.2 letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl hy₄)
    · apply hA.2.2 letter
      simp only [List.mem_append]
      exact Or.inr hy₅
  · intro letter hletter
    simp only [List.mem_append] at hletter
    rcases hletter with ((((hw | hy₁) | hy₂) | hy₃) | hy₄) | hy₅
    · apply hB.1 letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hw))
    · apply hB.1 letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr hy₁))
    · apply hB.1 letter
      simp only [List.mem_append]
      exact Or.inr hy₂
    · apply hB.2.1 letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl hy₃)
    · apply hB.2.1 letter
      simp only [List.mem_append]
      exact Or.inr hy₄
    · exact hB.2.2 letter hy₅

/-- Helper for Exercise 77.3: the displayed inverse pair exhausts its label's two
occurrences in a proper singleton scheme. -/
theorem not_mem_fragments_of_inversePair {α : Type u} (word : PolygonWord α)
    (y₀ y₁ : List (α × Bool)) (a : α)
    (h_proper : ({word} : LabellingScheme α).Proper)
    (h_decomp : word.1 = y₀ ++ [(a, true), (a, false)] ++ y₁) :
    (∀ letter ∈ y₀, letter.1 ≠ a) ∧ (∀ letter ∈ y₁, letter.1 ≠ a) := by
  classical
  -- Specialize the two-occurrence exclusion lemma with an empty middle fragment.
  have hfragments := not_mem_fragments_of_twoOccurrences word y₀ [] y₁ a
    true false h_proper
  have h_decomp' : word.1 = y₀ ++ [(a, true)] ++ [] ++ [(a, false)] ++ y₁ := by
    rw [h_decomp]
    simp
  have h := hfragments h_decomp'
  exact ⟨h.1, h.2.2⟩

end LabellingScheme.Proper

namespace LabellingScheme

/-- Helper for Exercise 77.3: an infinite label type supplies a label avoided by a
scheme and outside any prescribed finite set. -/
theorem exists_avoidedLabel_not_mem {α : Type u} [Infinite α]
    (scheme : LabellingScheme α) (forbidden : Finset α) :
    ∃ c, scheme.AvoidsLabel c ∧ c ∉ forbidden := by
  classical
  -- Avoid both the finite support of the scheme and the extra forbidden labels.
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (scheme.labels.toFinset ∪ forbidden)
  refine ⟨c, ?_, ?_⟩
  · rw [LabellingScheme.avoidsLabel_iff]
    intro word hword letter hletter heq
    subst heq
    apply hc
    simp only [Finset.mem_union, Multiset.mem_toFinset, LabellingScheme.mem_labels_iff]
    exact Or.inl ⟨word, hword, letter.2, hletter⟩
  · intro hforbidden
    apply hc
    exact Finset.mem_union_right scheme.labels.toFinset hforbidden

end LabellingScheme

namespace PolygonWord

/-- Helper for Exercise 77.3: concatenating two fragments that avoid a label
again gives a fragment that avoids that label. -/
theorem forall_fst_ne_append {α : Type u} (left right : List (α × Bool)) (a : α)
    (hleft : ∀ letter ∈ left, letter.1 ≠ a)
    (hright : ∀ letter ∈ right, letter.1 ≠ a) :
    ∀ letter ∈ left ++ right, letter.1 ≠ a := by
  -- Split membership in the concatenation and use the corresponding hypothesis.
  intro letter hletter
  rw [List.mem_append] at hletter
  exact hletter.elim (hleft letter) (hright letter)

/-- Helper for Exercise 77.3: a singleton signed letter avoids every distinct
unsigned label. -/
theorem forall_fst_ne_singleton {α : Type u} (a c : α) (sign : Bool)
    (h : a ≠ c) : ∀ letter ∈ [(a, sign)], letter.1 ≠ c := by
  -- Membership identifies the unique signed letter in the singleton.
  intro letter hletter
  simp only [List.mem_singleton] at hletter
  simpa only [hletter, Prod.fst] using h

/-- Helper for Exercise 77.3: swapping two labels fixes a list whose unsigned
labels avoid both endpoints of the swap. -/
theorem map_swapLabels_eq_self {α : Type u} (letters : List (α × Bool))
    (a c : α) (ha : ∀ letter ∈ letters, letter.1 ≠ a)
    (hc : ∀ letter ∈ letters, letter.1 ≠ c) :
    letters.map (fun letter ↦ (PolygonWord.swapLabels a c letter.1, letter.2)) =
      letters := by
  classical
  -- Induct pointwise; each head is fixed by `Equiv.swap` away from its endpoints.
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have hheadMem : head ∈ head :: tail := List.mem_cons_self
      have hheadA := ha head hheadMem
      have hheadC := hc head hheadMem
      have htailA : ∀ letter ∈ tail, letter.1 ≠ a := by
        intro letter hletter
        have htailMem : letter ∈ head :: tail := List.mem_cons_of_mem head hletter
        exact ha letter htailMem
      have htailC : ∀ letter ∈ tail, letter.1 ≠ c := by
        intro letter hletter
        have htailMem : letter ∈ head :: tail := List.mem_cons_of_mem head hletter
        exact hc letter htailMem
      rw [List.map_cons, ih htailA htailC]
      have hswap : PolygonWord.swapLabels a c head.1 = head.1 := by
        exact Equiv.swap_apply_of_ne_of_ne hheadA hheadC
      rw [hswap]

/-- Helper for Exercise 77.3: equality of the mapped signed-label lists
determines equality of relabelled polygon words. -/
theorem relabel_eq_of_val {α : Type u} (e : α ≃ α)
    (word target : PolygonWord α)
    (hval : word.1.map (fun letter ↦ (e letter.1, letter.2)) = target.1) :
    word.relabel e = target := by
  -- Polygon words are subtypes, so equality is determined by their list values.
  apply Subtype.ext
  simpa only [PolygonWord.relabel_val] using hval

/-- Helper for Exercise 77.3: cyclic rotation of one polygon word gives an
elementary equivalence of the associated singleton schemes. -/
theorem equivalent_of_isRotated {α : Type u} (word rotated : PolygonWord α)
    (h : List.IsRotated word.1 rotated.1) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({rotated} : LabellingScheme α) := by
  -- Package the list rotation as the singleton permutation constructor.
  exact LabellingScheme.Equivalent.ofElementary (.permute (.of word rotated 0 h))

/-- Helper for Exercise 77.3: a computed word-level sign reversal yields an
elementary equivalence of singleton schemes. -/
theorem equivalent_reverseLabel_eq {α : Type u} (word target : PolygonWord α)
    (a : α) (h : word.reverseLabel a = target) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({target} : LabellingScheme α) := by
  -- Map the word equality through the singleton scheme after the reversal step.
  have hscheme : ({word} : LabellingScheme α).reverseLabel a =
      ({target} : LabellingScheme α) := by
    unfold LabellingScheme.reverseLabel
    simp only [Multiset.map_singleton, h]
  have hstep := LabellingScheme.Equivalent.ofElementary
    (.reverse ({word} : LabellingScheme α) a)
  rwa [hscheme] at hstep

/-- Helper for Exercise 77.3: a computed fresh renaming yields an elementary
equivalence of singleton schemes. -/
theorem equivalent_renameLabel_eq {α : Type u} (word target : PolygonWord α)
    (a c : α) (h_ne : a ≠ c)
    (h_fresh : ({word} : LabellingScheme α).AvoidsLabel c)
    (h : word.relabel (PolygonWord.swapLabels a c) = target) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({target} : LabellingScheme α) := by
  -- Rewrite the target of the elementary rename by the supplied word computation.
  have hscheme : ({word} : LabellingScheme α).renameLabel a c =
      ({target} : LabellingScheme α) := by
    unfold LabellingScheme.renameLabel LabellingScheme.relabel
    simp only [Multiset.map_singleton, h]
  have hstep := LabellingScheme.Equivalent.ofElementary
    (.rename ({word} : LabellingScheme α) a c h_ne h_fresh)
  rwa [hscheme] at hstep

/-- Helper for Exercise 77.3: the cut-and-paste fragment rearrangement preserves
the minimum polygon-word length. -/
theorem cutPasteReorder_length {α : Type u} (word : PolygonWord α)
    (w x y z t : List (α × Bool)) (p c : α)
    (h_decomp : word.1 =
      w ++ x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t) :
    3 ≤ (w ++ [(c, true)] ++ z ++ y ++ [(c, false)] ++ x ++ t).length := by
  -- The rearrangement changes neither the residual letters nor the two displayed edges.
  have h_length := word.property
  rw [h_decomp] at h_length
  simp only [List.length_append, List.length_cons, List.length_nil] at h_length ⊢
  omega

/-- Helper for Exercise 77.3: cutting at a fresh label and pasting along an
oppositely signed pair cyclically exchanges the two intervening fragments. -/
theorem equivalentCutPasteReorder {α : Type u} (word : PolygonWord α)
    (w x y z t : List (α × Bool)) (p c : α)
    (h_decomp : word.1 =
      w ++ x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t)
    (hc : ({word} : LabellingScheme α).AvoidsLabel c)
    (hp : ∀ letter ∈ w ++ x ++ y ++ z ++ t, letter.1 ≠ p)
    (hleft : 2 ≤ (x ++ [(p, true)] ++ y).length)
    (hright : 2 ≤ (z ++ [(p, false)] ++ t ++ w).length) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({⟨w ++ [(c, true)] ++ z ++ y ++ [(c, false)] ++ x ++ t,
        cutPasteReorder_length word w x y z t p c h_decomp⟩} :
        LabellingScheme α) := by
  classical
  let left := x ++ [(p, true)] ++ y
  let right := z ++ [(p, false)] ++ t ++ w
  have hword_mem : word ∈ ({word} : LabellingScheme α) := by simp
  have hcWord : ∀ letter ∈ word.1, letter.1 ≠ c := by
    rw [LabellingScheme.avoidsLabel_iff] at hc
    exact hc word hword_mem
  have hp_ne_c : p ≠ c := by
    apply hcWord (p, true)
    rw [h_decomp]
    simp
  have hc_ne_p : c ≠ p := Ne.symm hp_ne_c
  have hleftFreshC : ∀ letter ∈ left, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_decomp]
    simp only [left, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hletter ⊢
    aesop
  have hrightFreshC : ∀ letter ∈ right, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_decomp]
    simp only [right, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hletter ⊢
    aesop
  have hzeroC : (0 : LabellingScheme α).AvoidsLabel c := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro remaining hremaining
    simp at hremaining
  have hzeroP : (0 : LabellingScheme α).AvoidsLabel p := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro remaining hremaining
    simp at hremaining
  have hleftLength : 2 ≤ left.length := by simpa only [left] using hleft
  have hrightLength : 2 ≤ right.length := by simpa only [right] using hright
  have hfirstPasteLength : 2 ≤ (y ++ [(c, false)] ++ x).length := by
    simp only [left, List.length_append, List.length_cons, List.length_nil] at hleftLength ⊢
    omega
  have hsecondPasteLength : 2 ≤ (t ++ w ++ [(c, true)] ++ z).length := by
    simp only [right, List.length_append, List.length_cons, List.length_nil] at hrightLength ⊢
    omega
  have hfirstPastedWordLength :
      3 ≤ (y ++ [(c, false)] ++ x ++ [(p, true)]).length := by
    simpa only [List.append_assoc] using
      PolygonWord.appendLetter_length (y ++ [(c, false)] ++ x) (p, true)
        hfirstPasteLength
  have hpastedLength :
      3 ≤ (y ++ [(c, false)] ++ x ++ t ++ w ++ [(c, true)] ++ z).length := by
    simpa only [List.append_assoc] using
      PolygonWord.append_length (y ++ [(c, false)] ++ x)
        (t ++ w ++ [(c, true)] ++ z) hfirstPasteLength hsecondPasteLength
  have hfirstPasteFresh :
      ∀ letter ∈ y ++ [(c, false)] ++ x, letter.1 ≠ p := by
    intro letter hletter
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with (hy | hcLetter) | hx
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · simpa only [hcLetter, Prod.fst] using hc_ne_p
    · apply hp letter
      simp only [List.mem_append]
      aesop
  have hsecondPasteFresh :
      ∀ letter ∈ t ++ w ++ [(c, true)] ++ z, letter.1 ≠ p := by
    intro letter hletter
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with ((ht | hw) | hcLetter) | hz
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · simpa only [hcLetter, Prod.fst] using hc_ne_p
    · apply hp letter
      simp only [List.mem_append]
      aesop
  let rotated : PolygonWord α :=
    ⟨left ++ right, PolygonWord.append_length left right hleftLength hrightLength⟩
  let firstCut : PolygonWord α :=
    ⟨left ++ [(c, false)],
      PolygonWord.appendLetter_length left (c, false) hleftLength⟩
  let secondCut : PolygonWord α :=
    ⟨(c, true) :: right,
      PolygonWord.consLetter_length (c, true) right hrightLength⟩
  let firstPasted : PolygonWord α :=
    ⟨y ++ [(c, false)] ++ x ++ [(p, true)], hfirstPastedWordLength⟩
  let secondPasted : PolygonWord α :=
    ⟨(p, false) :: (t ++ w ++ [(c, true)] ++ z),
      PolygonWord.consLetter_length (p, false)
        (t ++ w ++ [(c, true)] ++ z) hsecondPasteLength⟩
  let pasted : PolygonWord α :=
    ⟨y ++ [(c, false)] ++ x ++ t ++ w ++ [(c, true)] ++ z,
      hpastedLength⟩
  let target : PolygonWord α :=
    ⟨w ++ [(c, true)] ++ z ++ y ++ [(c, false)] ++ x ++ t,
      cutPasteReorder_length word w x y z t p c h_decomp⟩
  have hsourceRotation : List.IsRotated word.val rotated.val := by
    have hrotation := List.isRotated_append
      (l := w) (l' := x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t)
    simpa only [rotated, left, right, h_decomp, List.append_assoc] using hrotation
  have hfirstRotation : List.IsRotated firstCut.val firstPasted.val := by
    have hrotation := List.isRotated_append
      (l := x ++ [(p, true)]) (l' := y ++ [(c, false)])
    simpa only [firstCut, firstPasted, left, List.append_assoc] using hrotation
  have hsecondRotation : List.IsRotated secondCut.val secondPasted.val := by
    have hrotation := List.isRotated_append
      (l := (c, true) :: z) (l' := [(p, false)] ++ t ++ w)
    simpa [secondCut, secondPasted, right, List.append_assoc] using hrotation
  have htargetRotation : List.IsRotated pasted.val target.val := by
    have hrotation := List.isRotated_append
      (l := y ++ [(c, false)] ++ x ++ t)
      (l' := w ++ [(c, true)] ++ z)
    simpa only [pasted, target, List.append_assoc] using hrotation
  have hrotateSource :
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {rotated} := by
    exact LabellingScheme.Equivalent.ofElementary (.permute
      (.of word rotated 0 hsourceRotation))
  have hcut :
      LabellingScheme.Equivalent ({rotated} : LabellingScheme α)
        (firstCut ::ₘ secondCut ::ₘ 0) := by
    exact LabellingScheme.Equivalent.ofElementary (.cut
      (.of left right c true 0 hleftLength hrightLength
        hleftFreshC hrightFreshC hzeroC))
  have hrotateCut :
      LabellingScheme.Equivalent (firstCut ::ₘ secondCut ::ₘ 0)
        (firstPasted ::ₘ secondPasted ::ₘ 0) := by
    have hfirstStep := LabellingScheme.Equivalent.ofElementary (.permute
      (.of firstCut firstPasted (secondCut ::ₘ 0) hfirstRotation))
    have hsecondStepRaw := LabellingScheme.Equivalent.ofElementary (.permute
      (.of secondCut secondPasted (firstPasted ::ₘ 0) hsecondRotation))
    have hsecondStep :
        LabellingScheme.Equivalent (firstPasted ::ₘ secondCut ::ₘ 0)
          (firstPasted ::ₘ secondPasted ::ₘ 0) := by
      rw [Multiset.cons_swap firstPasted secondCut 0,
        Multiset.cons_swap firstPasted secondPasted 0]
      exact hsecondStepRaw
    exact hfirstStep.trans hsecondStep
  have hpaste :
      LabellingScheme.Equivalent (firstPasted ::ₘ secondPasted ::ₘ 0)
        ({pasted} : LabellingScheme α) := by
    have hpasteConstruction := LabellingScheme.Paste.of
      (y ++ [(c, false)] ++ x) (t ++ w ++ [(c, true)] ++ z)
      p false 0 hfirstPasteLength hsecondPasteLength
      hfirstPasteFresh hsecondPasteFresh hzeroP
    have hpasteStep : LabellingScheme.Paste
        (firstPasted ::ₘ secondPasted ::ₘ 0) ({pasted} : LabellingScheme α) := by
      simpa [firstPasted, secondPasted, pasted, List.append_assoc] using hpasteConstruction
    exact LabellingScheme.Equivalent.ofElementary (.paste hpasteStep)
  have hrotateTarget :
      LabellingScheme.Equivalent ({pasted} : LabellingScheme α) {target} := by
    exact LabellingScheme.Equivalent.ofElementary (.permute
      (.of pasted target 0 htargetRotation))
  exact hrotateSource.trans (hcut.trans
    (hrotateCut.trans (hpaste.trans hrotateTarget)))

/-- Helper for Exercise 77.3: after the cut-and-paste rearrangement, the fresh
cut label may be renamed back to the removed inverse-pair label. -/
theorem equivalentCutPasteReorderRelabel {α : Type u} (word : PolygonWord α)
    (w x y z t : List (α × Bool)) (p c : α)
    (h_decomp : word.1 =
      w ++ x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t)
    (hc : ({word} : LabellingScheme α).AvoidsLabel c)
    (hp : ∀ letter ∈ w ++ x ++ y ++ z ++ t, letter.1 ≠ p)
    (hleft : 2 ≤ (x ++ [(p, true)] ++ y).length)
    (hright : 2 ≤ (z ++ [(p, false)] ++ t ++ w).length) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({⟨w ++ [(p, true)] ++ z ++ y ++ [(p, false)] ++ x ++ t,
        cutPasteReorder_length word w x y z t p p h_decomp⟩} :
        LabellingScheme α) := by
  classical
  let freshTarget : PolygonWord α :=
    ⟨w ++ [(c, true)] ++ z ++ y ++ [(c, false)] ++ x ++ t,
      cutPasteReorder_length word w x y z t p c h_decomp⟩
  let target : PolygonWord α :=
    ⟨w ++ [(p, true)] ++ z ++ y ++ [(p, false)] ++ x ++ t,
      cutPasteReorder_length word w x y z t p p h_decomp⟩
  have hcutPaste :
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {freshTarget} := by
    simpa only [freshTarget] using
      equivalentCutPasteReorder word w x y z t p c h_decomp hc hp hleft hright
  have hwordMem : word ∈ ({word} : LabellingScheme α) := by simp
  have hcWord : ∀ letter ∈ word.1, letter.1 ≠ c := by
    rw [LabellingScheme.avoidsLabel_iff] at hc
    exact hc word hwordMem
  have hp_ne_c : p ≠ c := by
    apply hcWord (p, true)
    rw [h_decomp]
    simp
  have hc_ne_p : c ≠ p := Ne.symm hp_ne_c
  have hcResidual : ∀ letter ∈ w ++ x ++ y ++ z ++ t, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_decomp]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hletter ⊢
    aesop
  have hfreshAvoidsP : ({freshTarget} : LabellingScheme α).AvoidsLabel p := by
    rw [LabellingScheme.singleton_avoidsLabel_iff]
    intro letter hletter
    simp only [freshTarget, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hletter
    rcases hletter with (((((hw | hcFirst) | hz) | hy) | hcSecond) | hx) | ht
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · simpa only [hcFirst, Prod.fst] using hc_ne_p
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · simpa only [hcSecond, Prod.fst] using hc_ne_p
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · apply hp letter
      simp only [List.mem_append]
      aesop
  have hfixW :
      w.map (fun letter ↦ (PolygonWord.swapLabels c p letter.1, letter.2)) = w := by
    apply PolygonWord.map_swapLabels_eq_self w c p
    · intro letter hletter
      apply hcResidual letter
      simp only [List.mem_append]
      aesop
    · intro letter hletter
      apply hp letter
      simp only [List.mem_append]
      aesop
  have hfixX :
      x.map (fun letter ↦ (PolygonWord.swapLabels c p letter.1, letter.2)) = x := by
    apply PolygonWord.map_swapLabels_eq_self x c p
    · intro letter hletter
      apply hcResidual letter
      simp only [List.mem_append]
      aesop
    · intro letter hletter
      apply hp letter
      simp only [List.mem_append]
      aesop
  have hfixY :
      y.map (fun letter ↦ (PolygonWord.swapLabels c p letter.1, letter.2)) = y := by
    apply PolygonWord.map_swapLabels_eq_self y c p
    · intro letter hletter
      apply hcResidual letter
      simp only [List.mem_append]
      aesop
    · intro letter hletter
      apply hp letter
      simp only [List.mem_append]
      aesop
  have hfixZ :
      z.map (fun letter ↦ (PolygonWord.swapLabels c p letter.1, letter.2)) = z := by
    apply PolygonWord.map_swapLabels_eq_self z c p
    · intro letter hletter
      apply hcResidual letter
      simp only [List.mem_append]
      aesop
    · intro letter hletter
      apply hp letter
      simp only [List.mem_append]
      aesop
  have hfixT :
      t.map (fun letter ↦ (PolygonWord.swapLabels c p letter.1, letter.2)) = t := by
    apply PolygonWord.map_swapLabels_eq_self t c p
    · intro letter hletter
      apply hcResidual letter
      simp only [List.mem_append]
      aesop
    · intro letter hletter
      apply hp letter
      simp only [List.mem_append]
      aesop
  have hrenameVal :
      freshTarget.1.map
          (fun letter ↦ (PolygonWord.swapLabels c p letter.1, letter.2)) = target.1 := by
    simp only [freshTarget, target, List.map_append, List.map_cons, List.map_nil]
    rw [hfixW, hfixX, hfixY, hfixZ, hfixT]
    simp only [PolygonWord.swapLabels,
      Equiv.swap_apply_left]
  have hrenameWord : freshTarget.relabel (PolygonWord.swapLabels c p) = target :=
    PolygonWord.relabel_eq_of_val (PolygonWord.swapLabels c p)
      freshTarget target hrenameVal
  have hrenameScheme :
      ({freshTarget} : LabellingScheme α).renameLabel c p =
        ({target} : LabellingScheme α) := by
    unfold LabellingScheme.renameLabel LabellingScheme.relabel
    simp only [Multiset.map_singleton, hrenameWord]
  have hrename :
      LabellingScheme.Equivalent ({freshTarget} : LabellingScheme α) {target} := by
    have hstep := LabellingScheme.Equivalent.ofElementary
      (.rename ({freshTarget} : LabellingScheme α) c p hc_ne_p hfreshAvoidsP)
    rwa [hrenameScheme] at hstep
  exact hcutPaste.trans hrename

/-- Helper for Exercise 77.3: the relabelled cut-and-paste interface may target
any polygon word with the prescribed rearranged signed-label list. -/
theorem equivalentCutPasteReorderRelabelTo {α : Type u}
    (word target : PolygonWord α) (w x y z t : List (α × Bool)) (p c : α)
    (h_decomp : word.1 =
      w ++ x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t)
    (h_target : target.1 =
      w ++ [(p, true)] ++ z ++ y ++ [(p, false)] ++ x ++ t)
    (hc : ({word} : LabellingScheme α).AvoidsLabel c)
    (hp : ∀ letter ∈ w ++ x ++ y ++ z ++ t, letter.1 ≠ p)
    (hleft : 2 ≤ (x ++ [(p, true)] ++ y).length)
    (hright : 2 ≤ (z ++ [(p, false)] ++ t ++ w).length) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({target} : LabellingScheme α) := by
  -- First use the canonical constructed target, then identify it by subtype extensionality.
  let normalized : PolygonWord α :=
    ⟨w ++ [(p, true)] ++ z ++ y ++ [(p, false)] ++ x ++ t,
      cutPasteReorder_length word w x y z t p p h_decomp⟩
  have hnormalized :
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} := by
    simpa only [normalized] using
      equivalentCutPasteReorderRelabel word w x y z t p c
        h_decomp hc hp hleft hright
  have htargetEq : normalized = target := by
    apply Subtype.ext
    simpa only [normalized] using h_target.symm
  rwa [htargetEq] at hnormalized

/-- Helper for Exercise 77.3: rotating an adjacent inverse pair past a prefix also
rotates the cancelled remainder back to its original concatenation order. -/
theorem cancelPair_prefixRotation {α : Type u} (y₀ y₁ : List (α × Bool)) (a : α) :
    (y₀ ++ [(a, true), (a, false)] ++ y₁) ~r
        ([(a, true), (a, false)] ++ y₁ ++ y₀) ∧
      (y₁ ++ y₀) ~r (y₀ ++ y₁) := by
  -- Regard the original word as the prefix followed by the inverse-pair block.
  constructor
  · simpa only [List.append_assoc] using
      (List.isRotated_append (l := y₀)
        (l' := [(a, true), (a, false)] ++ y₁))
  -- After cancellation, the same cyclic cut restores the displayed remainder.
  · exact List.isRotated_append

/-- Helper for Exercise 77.3: cyclically repartition the surviving letters into two
fragments of length at least two while keeping the inverse pair adjacent. -/
theorem existsCancelRepartition {α : Type u} (y₀ y₁ : List (α × Bool)) (a : α)
    (h_length : 4 ≤ (y₀ ++ y₁).length) :
    ∃ p q : List (α × Bool),
      2 ≤ p.length ∧ 2 ≤ q.length ∧
        (y₀ ++ [(a, true), (a, false)] ++ y₁) ~r
          (p ++ [(a, true), (a, false)] ++ q) ∧
        (p ++ q) ~r (y₀ ++ y₁) := by
  let surviving := y₁ ++ y₀
  let q := surviving.take 2
  let p := surviving.drop 2
  -- The total bound leaves at least two letters on each side of the chosen split.
  have hsurviving : 4 ≤ surviving.length := by
    simp only [surviving, List.length_append] at h_length ⊢
    omega
  have hq : 2 ≤ q.length := by
    simp only [q, List.length_take]
    omega
  have hp : 2 ≤ p.length := by
    simp only [p, List.length_drop]
    omega
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · -- Rotate the inverse pair to the front, split the survivor, then rotate the suffix forward.
    have hfront := (cancelPair_prefixRotation y₀ y₁ a).1
    have hfront' :
        (y₀ ++ [(a, true), (a, false)] ++ y₁) ~r
          ([(a, true), (a, false)] ++ surviving) := by
      simpa only [surviving, List.append_assoc] using hfront
    have hsplit : surviving = q ++ p := by
      simp only [surviving, q, p, List.take_append_drop]
    have hrotate := List.isRotated_append
      (l := [(a, true), (a, false)] ++ q) (l' := p)
    rw [hsplit] at hfront'
    have hrotate' :
        ([(a, true), (a, false)] ++ q ++ p) ~r
          (p ++ [(a, true), (a, false)] ++ q) := by
      simpa only [List.append_assoc] using hrotate
    exact hfront'.trans hrotate'
  · -- The cancelled survivor differs from the requested order by two cyclic cuts.
    have hrotate : p ++ q ~r q ++ p := List.isRotated_append
    have hsplit : surviving = q ++ p := by
      simp only [surviving, q, p, List.take_append_drop]
    rw [← hsplit] at hrotate
    exact hrotate.trans (cancelPair_prefixRotation y₀ y₁ a).2

end PolygonWord

/- Exercise 77.3 (1): Moving equal signed letters to the front and inverting the
intervening fragment is an elementary equivalence. -/
#check PolygonWord.equivalent_pairFront

/-- Helper for Exercise 77.3 (2): an adjacent oppositely signed pair may be cancelled when the
remaining word has length at least four. -/
theorem PolygonWord.equivalentCancelPair {α : Type u} (word : PolygonWord α)
    (y₀ y₁ : List (α × Bool)) (a : α)
    (h_proper : ({word} : LabellingScheme α).Proper)
    (h_decomp : word.1 = y₀ ++ [(a, true), (a, false)] ++ y₁)
    (h_length : 4 ≤ (y₀ ++ y₁).length) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({⟨y₀ ++ y₁, PolygonWord.cancelPair_length y₀ y₁ h_length⟩} :
        LabellingScheme α) := by
  classical
  obtain ⟨p, q, hp, hq, hsourceRotation, hremainderRotation⟩ :=
    PolygonWord.existsCancelRepartition y₀ y₁ a h_length
  have hfragments :=
    LabellingScheme.Proper.not_mem_fragments_of_inversePair
      word y₀ y₁ a h_proper h_decomp
  have hsurvivor : ∀ letter ∈ y₀ ++ y₁, letter.1 ≠ a := by
    intro letter hletter
    rw [List.mem_append] at hletter
    exact hletter.elim (hfragments.1 letter) (hfragments.2 letter)
  -- Transport freshness through the cyclic repartition used by cancellation.
  have hpFresh : ∀ letter ∈ p, letter.1 ≠ a := by
    intro letter hletter
    apply hsurvivor letter
    exact hremainderRotation.mem_iff.mp (List.mem_append_left q hletter)
  have hqFresh : ∀ letter ∈ q, letter.1 ≠ a := by
    intro letter hletter
    apply hsurvivor letter
    exact hremainderRotation.mem_iff.mp (List.mem_append_right p hletter)
  have hzero : (0 : LabellingScheme α).AvoidsLabel a := by
    -- The empty remainder contains no polygon word using the cancelled label.
    rw [LabellingScheme.avoidsLabel_iff]
    intro remaining hremaining
    simp at hremaining
  let rotated : PolygonWord α :=
    ⟨p ++ [(a, true), (a, false)] ++ q,
      PolygonWord.insertCancelPair_length p q a true hp⟩
  let cancelled : PolygonWord α :=
    ⟨p ++ q, PolygonWord.append_length p q hp hq⟩
  let target : PolygonWord α :=
    ⟨y₀ ++ y₁, PolygonWord.cancelPair_length y₀ y₁ h_length⟩
  have hsourceRotated : List.IsRotated word.val rotated.val := by
    simpa only [rotated, h_decomp] using hsourceRotation
  have hremainderRotated : List.IsRotated cancelled.val target.val := by
    simpa only [cancelled, target] using hremainderRotation
  have hfirst :
      LabellingScheme.Equivalent ({word} : LabellingScheme α)
        ({rotated} : LabellingScheme α) := by
    -- First rotate the displayed inverse pair to the balanced repartition.
    exact LabellingScheme.Equivalent.ofElementary (.permute
      (.of word rotated 0 hsourceRotated))
  have hcancel :
      LabellingScheme.Equivalent ({rotated} : LabellingScheme α)
        ({cancelled} : LabellingScheme α) := by
    -- The balanced fragments now satisfy the cancellation constructor directly.
    exact LabellingScheme.Equivalent.ofElementary (.cancel
      (LabellingScheme.Cancel.ofPositiveNegative p q a 0 hp hq hpFresh hqFresh hzero))
  have hlast :
      LabellingScheme.Equivalent ({cancelled} : LabellingScheme α)
        ({target} : LabellingScheme α) := by
    -- Rotate the surviving letters back to the order requested by the theorem.
    exact LabellingScheme.Equivalent.ofElementary (.permute
      (.of cancelled target 0 hremainderRotated))
  exact hfirst.trans (hcancel.trans hlast)

/-- Exercise 77.3 (3): A proper interlaced pair can be moved to a commutator block at
the front, with the remaining fragments ordered as `y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅`. -/
theorem PolygonWord.equivalentCommutatorFront {α : Type u}
    [Infinite α] (word : PolygonWord α)
    (w₀ y₁ y₂ y₃ y₄ y₅ : List (α × Bool)) (a b : α)
    (h_proper : ({word} : LabellingScheme α).Proper)
    (h_decomp : word.1 =
      w₀ ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
        [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({⟨w₀ ++ [(a, true), (b, true), (a, false), (b, false)] ++
          y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅,
        PolygonWord.commutatorFront_length word w₀ y₁ y₂ y₃ y₄ y₅ a b h_decomp⟩} :
        LabellingScheme α) := by
  classical
  -- Properness supplies the global freshness invariant for both displayed labels.
  obtain ⟨ha_ne_b, hA, hB⟩ :=
    LabellingScheme.Proper.fresh_interlacedPair word w₀ y₁ y₂ y₃ y₄ y₅
      a b h_proper h_decomp
  have hb_ne_a : b ≠ a := Ne.symm ha_ne_b
  have haW : ∀ letter ∈ w₀, letter.1 ≠ a := by
    intro letter hletter
    apply hA letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hletter))))
  have haY₁ : ∀ letter ∈ y₁, letter.1 ≠ a := by
    intro letter hletter
    apply hA letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hletter))))
  have haY₂ : ∀ letter ∈ y₂, letter.1 ≠ a := by
    intro letter hletter
    apply hA letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hletter)))
  have haY₃ : ∀ letter ∈ y₃, letter.1 ≠ a := by
    intro letter hletter
    apply hA letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr hletter))
  have haY₄ : ∀ letter ∈ y₄, letter.1 ≠ a := by
    intro letter hletter
    apply hA letter
    simp only [List.mem_append]
    exact Or.inl (Or.inr hletter)
  have haY₅ : ∀ letter ∈ y₅, letter.1 ≠ a := by
    intro letter hletter
    apply hA letter
    simp only [List.mem_append]
    exact Or.inr hletter
  have hbW : ∀ letter ∈ w₀, letter.1 ≠ b := by
    intro letter hletter
    apply hB letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hletter))))
  have hbY₁ : ∀ letter ∈ y₁, letter.1 ≠ b := by
    intro letter hletter
    apply hB letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hletter))))
  have hbY₂ : ∀ letter ∈ y₂, letter.1 ≠ b := by
    intro letter hletter
    apply hB letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hletter)))
  have hbY₃ : ∀ letter ∈ y₃, letter.1 ≠ b := by
    intro letter hletter
    apply hB letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr hletter))
  have hbY₄ : ∀ letter ∈ y₄, letter.1 ≠ b := by
    intro letter hletter
    apply hB letter
    simp only [List.mem_append]
    exact Or.inl (Or.inr hletter)
  have hbY₅ : ∀ letter ∈ y₅, letter.1 ≠ b := by
    intro letter hletter
    apply hB letter
    simp only [List.mem_append]
    exact Or.inr hletter
  have haBPos := PolygonWord.forall_fst_ne_singleton b a true hb_ne_a
  have haBNeg := PolygonWord.forall_fst_ne_singleton b a false hb_ne_a
  have hbAPos := PolygonWord.forall_fst_ne_singleton a b true ha_ne_b
  have hbANeg := PolygonWord.forall_fst_ne_singleton a b false ha_ne_b
  have hnilA : ∀ letter ∈ ([] : List (α × Bool)), letter.1 ≠ a := by simp
  have hnilB : ∀ letter ∈ ([] : List (α × Bool)), letter.1 ≠ b := by simp
  -- Assemble exactly the residual freshness shapes consumed by the four exchanges.
  have haMiddle := PolygonWord.forall_fst_ne_append
    (y₂ ++ [(b, true)]) y₃ a
      (PolygonWord.forall_fst_ne_append y₂ [(b, true)] a haY₂ haBPos) haY₃
  have haTail := PolygonWord.forall_fst_ne_append
    (y₄ ++ [(b, false)]) y₅ a
      (PolygonWord.forall_fst_ne_append y₄ [(b, false)] a haY₄ haBNeg) haY₅
  have hresOne := PolygonWord.forall_fst_ne_append
    (w₀ ++ y₁ ++ (y₂ ++ [(b, true)] ++ y₃) ++ [])
      (y₄ ++ [(b, false)] ++ y₅) a
      (PolygonWord.forall_fst_ne_append
        (w₀ ++ y₁ ++ (y₂ ++ [(b, true)] ++ y₃)) [] a
          (PolygonWord.forall_fst_ne_append (w₀ ++ y₁)
            (y₂ ++ [(b, true)] ++ y₃) a
              (PolygonWord.forall_fst_ne_append w₀ y₁ a haW haY₁) haMiddle) hnilA)
      haTail
  have hbPrefix := PolygonWord.forall_fst_ne_append w₀ [(a, true)] b hbW hbAPos
  have hbSignedY₃ := PolygonWord.forall_fst_ne_append
    y₃ [(a, false)] b hbY₃ hbANeg
  have hbY₁Y₄ := PolygonWord.forall_fst_ne_append y₁ y₄ b hbY₁ hbY₄
  have hresTwo := PolygonWord.forall_fst_ne_append
    ((w₀ ++ [(a, true)]) ++ y₂ ++ (y₃ ++ [(a, false)]) ++ (y₁ ++ y₄)) y₅ b
      (PolygonWord.forall_fst_ne_append
        ((w₀ ++ [(a, true)]) ++ y₂ ++ (y₃ ++ [(a, false)]))
          (y₁ ++ y₄) b
          (PolygonWord.forall_fst_ne_append ((w₀ ++ [(a, true)]) ++ y₂)
            (y₃ ++ [(a, false)]) b
              (PolygonWord.forall_fst_ne_append (w₀ ++ [(a, true)]) y₂ b
                hbPrefix hbY₂) hbSignedY₃) hbY₁Y₄) hbY₅
  have haBlock := PolygonWord.forall_fst_ne_append
    (y₁ ++ y₄) y₃ a
      (PolygonWord.forall_fst_ne_append y₁ y₄ a haY₁ haY₄) haY₃
  have haLast := PolygonWord.forall_fst_ne_append
    ([(b, false)] ++ y₂) y₅ a
      (PolygonWord.forall_fst_ne_append [(b, false)] y₂ a haBNeg haY₂) haY₅
  have hresThree := PolygonWord.forall_fst_ne_append
    (w₀ ++ [] ++ [(b, true)] ++ (y₁ ++ y₄ ++ y₃))
      ([(b, false)] ++ y₂ ++ y₅) a
      (PolygonWord.forall_fst_ne_append
        (w₀ ++ [] ++ [(b, true)]) (y₁ ++ y₄ ++ y₃) a
          (PolygonWord.forall_fst_ne_append (w₀ ++ []) [(b, true)] a
            (PolygonWord.forall_fst_ne_append w₀ [] a haW hnilA) haBPos) haBlock)
      haLast
  have hbBlock := PolygonWord.forall_fst_ne_append
    (y₁ ++ y₄) y₃ b
      (PolygonWord.forall_fst_ne_append y₁ y₄ b hbY₁ hbY₄) hbY₃
  have hbLast := PolygonWord.forall_fst_ne_append y₂ y₅ b hbY₂ hbY₅
  have hresFour := PolygonWord.forall_fst_ne_append
    ((w₀ ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃) ++ [] ++ [(a, false)])
      (y₂ ++ y₅) b
      (PolygonWord.forall_fst_ne_append
        ((w₀ ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃) ++ []) [(a, false)] b
          (PolygonWord.forall_fst_ne_append
            ((w₀ ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃)) [] b
              (PolygonWord.forall_fst_ne_append (w₀ ++ [(a, true)])
                (y₁ ++ y₄ ++ y₃) b hbPrefix hbBlock) hnilB) hbANeg) hbLast
  -- Name the three intermediate polygon words so each cut-and-paste call sees a stable target.
  have hstageOneLength : 3 ≤
      (w₀ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++ [(a, false)] ++
        y₁ ++ y₄ ++ [(b, false)] ++ y₅).length := by
    have hlength := word.property
    rw [h_decomp] at hlength
    simp only [List.length_append, List.length_cons, List.length_nil] at hlength ⊢
    omega
  let stageOne : PolygonWord α :=
    ⟨w₀ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++ [(a, false)] ++
      y₁ ++ y₄ ++ [(b, false)] ++ y₅, hstageOneLength⟩
  have hstageTwoLength : 3 ≤
      (w₀ ++ [(a, true), (b, true)] ++ y₁ ++ y₄ ++ y₃ ++
        [(a, false), (b, false)] ++ y₂ ++ y₅).length := by
    have hlength := stageOne.property
    simp only [stageOne, List.length_append, List.length_cons,
      List.length_nil] at hlength ⊢
    omega
  let stageTwo : PolygonWord α :=
    ⟨w₀ ++ [(a, true), (b, true)] ++ y₁ ++ y₄ ++ y₃ ++
      [(a, false), (b, false)] ++ y₂ ++ y₅, hstageTwoLength⟩
  have hstageThreeLength : 3 ≤
      (w₀ ++ [(a, true)] ++ y₁ ++ y₄ ++ y₃ ++
        [(b, true), (a, false), (b, false)] ++ y₂ ++ y₅).length := by
    have hlength := stageTwo.property
    simp only [stageTwo, List.length_append, List.length_cons,
      List.length_nil] at hlength ⊢
    omega
  let stageThree : PolygonWord α :=
    ⟨w₀ ++ [(a, true)] ++ y₁ ++ y₄ ++ y₃ ++
      [(b, true), (a, false), (b, false)] ++ y₂ ++ y₅, hstageThreeLength⟩
  let target : PolygonWord α :=
    ⟨w₀ ++ [(a, true), (b, true), (a, false), (b, false)] ++
      y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅,
        PolygonWord.commutatorFront_length word w₀ y₁ y₂ y₃ y₄ y₅ a b h_decomp⟩
  -- Each exchange chooses its own fresh cut label, refreshing elaboration interfaces.
  obtain ⟨c₁, hc₁, -⟩ := LabellingScheme.exists_avoidedLabel_not_mem
    ({word} : LabellingScheme α) (∅ : Finset α)
  have hdecompOne : word.1 = w₀ ++ y₁ ++ [(a, true)] ++
      (y₂ ++ [(b, true)] ++ y₃) ++ [] ++ [(a, false)] ++
        (y₄ ++ [(b, false)] ++ y₅) := by
    simpa [List.append_assoc] using h_decomp
  have htargetOne : stageOne.1 = w₀ ++ [(a, true)] ++ [] ++
      (y₂ ++ [(b, true)] ++ y₃) ++ [(a, false)] ++ y₁ ++
        (y₄ ++ [(b, false)] ++ y₅) := by
    simp [stageOne, List.append_assoc]
  have hleftOne : 2 ≤
      (y₁ ++ [(a, true)] ++ (y₂ ++ [(b, true)] ++ y₃)).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hrightOne : 2 ≤
      ([] ++ [(a, false)] ++ (y₄ ++ [(b, false)] ++ y₅) ++ w₀).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hfirst := PolygonWord.equivalentCutPasteReorderRelabelTo word stageOne
    w₀ y₁ (y₂ ++ [(b, true)] ++ y₃) [] (y₄ ++ [(b, false)] ++ y₅)
      a c₁ hdecompOne htargetOne hc₁ hresOne hleftOne hrightOne
  obtain ⟨c₂, hc₂, -⟩ := LabellingScheme.exists_avoidedLabel_not_mem
    ({stageOne} : LabellingScheme α) (∅ : Finset α)
  have hdecompTwo : stageOne.1 = (w₀ ++ [(a, true)]) ++ y₂ ++ [(b, true)] ++
      (y₃ ++ [(a, false)]) ++ (y₁ ++ y₄) ++ [(b, false)] ++ y₅ := by
    simp [stageOne, List.append_assoc]
  have htargetTwo : stageTwo.1 = (w₀ ++ [(a, true)]) ++ [(b, true)] ++
      (y₁ ++ y₄) ++ (y₃ ++ [(a, false)]) ++ [(b, false)] ++ y₂ ++ y₅ := by
    simp [stageTwo, List.append_assoc]
  have hleftTwo : 2 ≤
      (y₂ ++ [(b, true)] ++ (y₃ ++ [(a, false)])).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hrightTwo : 2 ≤
      ((y₁ ++ y₄) ++ [(b, false)] ++ y₅ ++ (w₀ ++ [(a, true)])).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hsecond := PolygonWord.equivalentCutPasteReorderRelabelTo stageOne stageTwo
    (w₀ ++ [(a, true)]) y₂ (y₃ ++ [(a, false)]) (y₁ ++ y₄) y₅
      b c₂ hdecompTwo htargetTwo hc₂ hresTwo hleftTwo hrightTwo
  obtain ⟨c₃, hc₃, -⟩ := LabellingScheme.exists_avoidedLabel_not_mem
    ({stageTwo} : LabellingScheme α) (∅ : Finset α)
  have hdecompThree : stageTwo.1 = w₀ ++ [] ++ [(a, true)] ++ [(b, true)] ++
      (y₁ ++ y₄ ++ y₃) ++ [(a, false)] ++ ([(b, false)] ++ y₂ ++ y₅) := by
    simp [stageTwo, List.append_assoc]
  have htargetThree : stageThree.1 = w₀ ++ [(a, true)] ++
      (y₁ ++ y₄ ++ y₃) ++ [(b, true)] ++ [(a, false)] ++ [] ++
        ([(b, false)] ++ y₂ ++ y₅) := by
    simp [stageThree, List.append_assoc]
  have hleftThree : 2 ≤ ([] ++ [(a, true)] ++ [(b, true)]).length := by simp
  have hrightThree : 2 ≤
      ((y₁ ++ y₄ ++ y₃) ++ [(a, false)] ++
        ([(b, false)] ++ y₂ ++ y₅) ++ w₀).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hthird := PolygonWord.equivalentCutPasteReorderRelabelTo stageTwo stageThree
    w₀ [] [(b, true)] (y₁ ++ y₄ ++ y₃) ([(b, false)] ++ y₂ ++ y₅)
      a c₃ hdecompThree htargetThree hc₃ hresThree hleftThree hrightThree
  obtain ⟨c₄, hc₄, -⟩ := LabellingScheme.exists_avoidedLabel_not_mem
    ({stageThree} : LabellingScheme α) (∅ : Finset α)
  have hdecompFour : stageThree.1 = (w₀ ++ [(a, true)]) ++
      (y₁ ++ y₄ ++ y₃) ++ [(b, true)] ++ [(a, false)] ++ [] ++
        [(b, false)] ++ (y₂ ++ y₅) := by
    simp [stageThree, List.append_assoc]
  have htargetFour : target.1 = (w₀ ++ [(a, true)]) ++ [(b, true)] ++
      [] ++ [(a, false)] ++ [(b, false)] ++ (y₁ ++ y₄ ++ y₃) ++
        (y₂ ++ y₅) := by
    simp [target, List.append_assoc]
  have hleftFour : 2 ≤
      ((y₁ ++ y₄ ++ y₃) ++ [(b, true)] ++ [(a, false)]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hrightFour : 2 ≤
      ([] ++ [(b, false)] ++ (y₂ ++ y₅) ++
        (w₀ ++ [(a, true)])).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hresFour' : ∀ letter ∈
      (w₀ ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃) ++ [(a, false)] ++ [] ++
        (y₂ ++ y₅), letter.1 ≠ b := by
    simpa only [List.append_nil, List.append_assoc] using hresFour
  have hfourth := PolygonWord.equivalentCutPasteReorderRelabelTo stageThree target
    (w₀ ++ [(a, true)]) (y₁ ++ y₄ ++ y₃) [(a, false)] [] (y₂ ++ y₅)
      b c₄ hdecompFour htargetFour hc₄ hresFour' hleftFour hrightFour
  -- The main theorem now consumes only the four stable interfaces.
  exact hfirst.trans (hsecond.trans (hthird.trans hfourth))
/- Exercise 77.3 (4): A crosscap followed by a handle is equivalent to three
consecutive crosscap pairs. -/
#check PolygonWord.equivalent_pairCommutator

/-- Exercise 77.3 (5): The scheme `abacb⁻¹c⁻¹` reduces to `aabbcc`. -/
theorem reduceAbacBInvCInv :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.abacBInvCInv} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.threeCrosscap} :
        LabellingScheme ℕ) := by
  -- First expose the interlaced `b,c,b⁻¹,c⁻¹` block behind the initial `a`.
  have hproperSource :
      ({SurfaceClassificationWord.abacBInvCInv} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    decide
  have hdecompSource : SurfaceClassificationWord.abacBInvCInv.1 =
      [(0, true)] ++ [] ++ [(1, true)] ++ [(0, true)] ++
        [(2, true)] ++ [] ++ [(1, false)] ++ [] ++ [(2, false)] ++ [] := by
    rfl
  have hwOneLength :
      3 ≤ ([(0, true), (1, true), (2, true), (1, false),
        (2, false), (0, true)] : List (ℕ × Bool)).length := by decide
  let wOne : PolygonWord ℕ :=
    ⟨[(0, true), (1, true), (2, true), (1, false),
      (2, false), (0, true)], hwOneLength⟩
  have hfirst :
      LabellingScheme.Equivalent ({SurfaceClassificationWord.abacBInvCInv} :
        LabellingScheme ℕ) {wOne} := by
    simpa [SurfaceClassificationWord.abacBInvCInv, wOne,
      List.append_assoc] using
        PolygonWord.equivalentCommutatorFront
          SurfaceClassificationWord.abacBInvCInv [(0, true)] [] [(0, true)]
            [] [] [] 1 2 hproperSource hdecompSource
  have hwTwoLength :
      3 ≤ ([(0, true), (0, true), (1, true), (2, true),
        (1, false), (2, false)] : List (ℕ × Bool)).length := by decide
  let wTwo : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (1, true), (2, true),
      (1, false), (2, false)], hwTwoLength⟩
  have hrotationOne : List.IsRotated wOne.1 wTwo.1 := by
    have hrotation := List.isRotated_append
      (l := [(0, true), (1, true), (2, true), (1, false), (2, false)])
      (l' := [(0, true)])
    simpa [wOne, wTwo] using hrotation
  have hrotateOne :
      LabellingScheme.Equivalent ({wOne} : LabellingScheme ℕ) {wTwo} :=
    PolygonWord.equivalent_of_isRotated wOne wTwo hrotationOne
  have hproperTwo : ({wTwo} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wTwo]
    decide
  have hdecompTwo : wTwo.1 = [] ++
      [(0, true), (0, true), (1, true), (2, true), (1, false), (2, false)] ++
        [] := by
    rfl
  have hwThreeLength :
      3 ≤ ([(1, true), (1, true), (2, true), (2, true),
        (0, true), (0, true)] : List (ℕ × Bool)).length := by decide
  let wThree : PolygonWord ℕ :=
    ⟨[(1, true), (1, true), (2, true), (2, true),
      (0, true), (0, true)], hwThreeLength⟩
  have hpair :
      LabellingScheme.Equivalent ({wTwo} : LabellingScheme ℕ) {wThree} := by
    simpa [wTwo, wThree, PolygonWord.pairCommutator] using
        PolygonWord.equivalent_pairCommutator wTwo [] [] 1 2 0
          hproperTwo hdecompTwo
  have hrotationTwo :
      List.IsRotated wThree.1 SurfaceClassificationWord.threeCrosscap.1 := by
    have hrotation := List.isRotated_append
      (l := [(1, true), (1, true), (2, true), (2, true)])
      (l' := [(0, true), (0, true)])
    simpa [wThree, SurfaceClassificationWord.threeCrosscap] using hrotation
  have hrotateTwo := PolygonWord.equivalent_of_isRotated wThree
    SurfaceClassificationWord.threeCrosscap hrotationTwo
  exact hfirst.trans (hrotateOne.trans (hpair.trans hrotateTwo))

/-- Exercise 77.3 (6): The scheme `abca⁻¹cb` reduces to `aabb`. -/
theorem reduceAbcAInvCb :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.abcAInvCb} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.twoCrosscap} :
        LabellingScheme ℕ) := by
  -- Move the two positive `b` edges forward; the intervening word is inverted.
  have hproperSource :
      ({SurfaceClassificationWord.abcAInvCb} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    decide
  have hdecompSource : SurfaceClassificationWord.abcAInvCb.1 =
      [(0, true)] ++ [(1, true)] ++
        [(2, true), (0, false), (2, true)] ++ [(1, true)] ++ [] := by
    rfl
  have hwOneLength :
      3 ≤ ([(1, true), (1, true), (0, true), (2, false),
        (0, true), (2, false)] : List (ℕ × Bool)).length := by decide
  let wOne : PolygonWord ℕ :=
    ⟨[(1, true), (1, true), (0, true), (2, false),
      (0, true), (2, false)], hwOneLength⟩
  have hfirst :
      LabellingScheme.Equivalent ({SurfaceClassificationWord.abcAInvCb} :
        LabellingScheme ℕ) {wOne} := by
    simpa [SurfaceClassificationWord.abcAInvCb, wOne,
      PolygonWord.pairFront, FreeGroup.invRev] using
        PolygonWord.equivalent_pairFront SurfaceClassificationWord.abcAInvCb
          [(0, true)] [(2, true), (0, false), (2, true)] []
            (1, true) hproperSource hdecompSource
  have hproperOne : ({wOne} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wOne]
    decide
  have hdecompOne : wOne.1 =
      [(1, true), (1, true)] ++ [(0, true)] ++ [(2, false)] ++
        [(0, true)] ++ [(2, false)] := by
    rfl
  have hwTwoLength :
      3 ≤ ([(0, true), (0, true), (1, true), (1, true),
        (2, true), (2, false)] : List (ℕ × Bool)).length := by decide
  let wTwo : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (1, true), (1, true),
      (2, true), (2, false)], hwTwoLength⟩
  have hsecond :
      LabellingScheme.Equivalent ({wOne} : LabellingScheme ℕ) {wTwo} := by
    simpa [wOne, wTwo, PolygonWord.pairFront, FreeGroup.invRev] using
      PolygonWord.equivalent_pairFront wOne [(1, true), (1, true)]
        [(2, false)] [(2, false)] (0, true) hproperOne hdecompOne
  have hproperTwo : ({wTwo} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wTwo]
    decide
  have hdecompTwo : wTwo.1 =
      [(0, true), (0, true), (1, true), (1, true)] ++
        [(2, true), (2, false)] ++ [] := by
    rfl
  have hremainingLength :
      4 ≤ ([(0, true), (0, true), (1, true), (1, true)] ++ []).length := by
    decide
  have hcancel := PolygonWord.equivalentCancelPair wTwo
    [(0, true), (0, true), (1, true), (1, true)] [] 2
      hproperTwo hdecompTwo hremainingLength
  -- Cancelling the final `cc⁻¹` pair leaves the standard two-crosscap word.
  simpa [wTwo, SurfaceClassificationWord.twoCrosscap] using
    hfirst.trans (hsecond.trans hcancel)

/-- Exercise 77.3 (7): The scheme `abbca⁻¹ddc⁻¹` reduces to `aabbccdd`. -/
theorem reduceAbbcAInvDdCInv :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.abbcAInvDdCInv} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.fourCrosscap} :
        LabellingScheme ℕ) := by
  -- Extract the `a,c,a⁻¹,c⁻¹` handle, leaving the two positive pairs behind it.
  have hproperSource :
      ({SurfaceClassificationWord.abbcAInvDdCInv} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    decide
  have hdecompSource : SurfaceClassificationWord.abbcAInvDdCInv.1 =
      [] ++ [] ++ [(0, true)] ++ [(1, true), (1, true)] ++
        [(2, true)] ++ [] ++ [(0, false)] ++ [(3, true), (3, true)] ++
          [(2, false)] ++ [] := by
    rfl
  have hwOneLength :
      3 ≤ ([(0, true), (2, true), (0, false), (2, false),
        (3, true), (3, true), (1, true), (1, true)] :
          List (ℕ × Bool)).length := by decide
  let wOne : PolygonWord ℕ :=
    ⟨[(0, true), (2, true), (0, false), (2, false),
      (3, true), (3, true), (1, true), (1, true)], hwOneLength⟩
  have hfirst :
      LabellingScheme.Equivalent ({SurfaceClassificationWord.abbcAInvDdCInv} :
        LabellingScheme ℕ) {wOne} := by
    simpa [SurfaceClassificationWord.abbcAInvDdCInv, wOne, List.append_assoc] using
      PolygonWord.equivalentCommutatorFront
        SurfaceClassificationWord.abbcAInvDdCInv [] []
          [(1, true), (1, true)] [] [(3, true), (3, true)] []
            0 2 hproperSource hdecompSource
  have hwTwoLength :
      3 ≤ ([(3, true), (3, true), (1, true), (1, true),
        (0, true), (2, true), (0, false), (2, false)] :
          List (ℕ × Bool)).length := by decide
  let wTwo : PolygonWord ℕ :=
    ⟨[(3, true), (3, true), (1, true), (1, true),
      (0, true), (2, true), (0, false), (2, false)], hwTwoLength⟩
  have hrotationOne : List.IsRotated wOne.1 wTwo.1 := by
    have hrotation := List.isRotated_append
      (l := [(0, true), (2, true), (0, false), (2, false)])
      (l' := [(3, true), (3, true), (1, true), (1, true)])
    simpa [wOne, wTwo] using hrotation
  have hrotateOne := PolygonWord.equivalent_of_isRotated wOne wTwo hrotationOne
  have hproperTwo : ({wTwo} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wTwo]
    decide
  have hdecompTwo : wTwo.1 = [(3, true), (3, true)] ++
      [(1, true), (1, true), (0, true), (2, true), (0, false), (2, false)] ++
        [] := by
    rfl
  have hwThreeLength :
      3 ≤ ([(3, true), (3, true), (0, true), (0, true),
        (2, true), (2, true), (1, true), (1, true)] :
          List (ℕ × Bool)).length := by decide
  let wThree : PolygonWord ℕ :=
    ⟨[(3, true), (3, true), (0, true), (0, true),
      (2, true), (2, true), (1, true), (1, true)], hwThreeLength⟩
  have hpair :
      LabellingScheme.Equivalent ({wTwo} : LabellingScheme ℕ) {wThree} := by
    simpa [wTwo, wThree, PolygonWord.pairCommutator] using
      PolygonWord.equivalent_pairCommutator wTwo [(3, true), (3, true)] []
        0 2 1 hproperTwo hdecompTwo
  have hproperThree : ({wThree} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wThree]
    decide
  have hdecompThree : wThree.1 =
      [(3, true), (3, true), (0, true), (0, true)] ++ [(2, true)] ++ [] ++
        [(2, true)] ++ [(1, true), (1, true)] := by
    rfl
  have hwFourLength :
      3 ≤ ([(2, true), (2, true), (3, true), (3, true),
        (0, true), (0, true), (1, true), (1, true)] :
          List (ℕ × Bool)).length := by decide
  let wFour : PolygonWord ℕ :=
    ⟨[(2, true), (2, true), (3, true), (3, true),
      (0, true), (0, true), (1, true), (1, true)], hwFourLength⟩
  have hfront :
      LabellingScheme.Equivalent ({wThree} : LabellingScheme ℕ) {wFour} := by
    simpa [wThree, wFour, PolygonWord.pairFront, FreeGroup.invRev] using
      PolygonWord.equivalent_pairFront wThree
        [(3, true), (3, true), (0, true), (0, true)] []
          [(1, true), (1, true)] (2, true) hproperThree hdecompThree
  have hrotationTwo :
      List.IsRotated wFour.1 SurfaceClassificationWord.fourCrosscap.1 := by
    have hrotation := List.isRotated_append
      (l := [(2, true), (2, true), (3, true), (3, true)])
      (l' := [(0, true), (0, true), (1, true), (1, true)])
    simpa [wFour, SurfaceClassificationWord.fourCrosscap] using hrotation
  have hrotateTwo := PolygonWord.equivalent_of_isRotated wFour
    SurfaceClassificationWord.fourCrosscap hrotationTwo
  exact hfirst.trans (hrotateOne.trans (hpair.trans (hfront.trans hrotateTwo)))

/-- Exercise 77.3 (8): The scheme `abcda⁻¹b⁻¹c⁻¹d⁻¹` reduces to the two-handle word. -/
theorem reduceAbcdAInvBInvCInvDInv :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.abcdAInvBInvCInvDInv} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.twoHandle} :
        LabellingScheme ℕ) := by
  -- Extract the interlaced `a,b,a⁻¹,b⁻¹` block; the residual is the second handle.
  have hproper :
      ({SurfaceClassificationWord.abcdAInvBInvCInvDInv} :
        LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    decide
  have hdecomp : SurfaceClassificationWord.abcdAInvBInvCInvDInv.1 =
      [] ++ [] ++ [(0, true)] ++ [] ++ [(1, true)] ++
        [(2, true), (3, true)] ++ [(0, false)] ++ [] ++
          [(1, false)] ++ [(2, false), (3, false)] := by
    rfl
  simpa [SurfaceClassificationWord.abcdAInvBInvCInvDInv,
    SurfaceClassificationWord.twoHandle, List.append_assoc] using
      PolygonWord.equivalentCommutatorFront
        SurfaceClassificationWord.abcdAInvBInvCInvDInv [] [] []
          [(2, true), (3, true)] [] [(2, false), (3, false)]
            0 1 hproper hdecomp

/-- Exercise 77.3 (9): The scheme `abcda⁻¹c⁻¹b⁻¹d⁻¹` reduces to the one-handle word. -/
theorem reduceAbcdAInvCInvBInvDInv :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.abcdAInvCInvBInvDInv} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.oneHandle} :
        LabellingScheme ℕ) := by
  -- Rotate the final `d⁻¹` edge forward so the `a,b` handle is interlaced.
  have hproperSource :
      ({SurfaceClassificationWord.abcdAInvCInvBInvDInv} :
        LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    decide
  have hwOneLength :
      3 ≤ ([(3, false), (0, true), (1, true), (2, true),
        (3, true), (0, false), (2, false), (1, false)] :
          List (ℕ × Bool)).length := by decide
  let wOne : PolygonWord ℕ :=
    ⟨[(3, false), (0, true), (1, true), (2, true),
      (3, true), (0, false), (2, false), (1, false)], hwOneLength⟩
  have hrotation :
      List.IsRotated SurfaceClassificationWord.abcdAInvCInvBInvDInv.1 wOne.1 := by
    have hrot := List.isRotated_append
      (l := [(0, true), (1, true), (2, true), (3, true),
        (0, false), (2, false), (1, false)]) (l' := [(3, false)])
    simpa [SurfaceClassificationWord.abcdAInvCInvBInvDInv, wOne] using hrot
  have hrotate := PolygonWord.equivalent_of_isRotated
    SurfaceClassificationWord.abcdAInvCInvBInvDInv wOne hrotation
  have hproperOne : ({wOne} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wOne]
    decide
  have hdecompOne : wOne.1 = [] ++ [(3, false)] ++ [(0, true)] ++ [] ++
      [(1, true)] ++ [(2, true), (3, true)] ++ [(0, false)] ++ [(2, false)] ++
        [(1, false)] ++ [] := by
    rfl
  have hwTwoLength :
      3 ≤ ([(0, true), (1, true), (0, false), (1, false),
        (3, false), (2, false), (2, true), (3, true)] :
          List (ℕ × Bool)).length := by decide
  let wTwo : PolygonWord ℕ :=
    ⟨[(0, true), (1, true), (0, false), (1, false),
      (3, false), (2, false), (2, true), (3, true)], hwTwoLength⟩
  have hcomm :
      LabellingScheme.Equivalent ({wOne} : LabellingScheme ℕ) {wTwo} := by
    simpa [wOne, wTwo, List.append_assoc] using
      PolygonWord.equivalentCommutatorFront wOne [] [(3, false)] []
        [(2, true), (3, true)] [(2, false)] [] 0 1 hproperOne hdecompOne
  have hwThreeLength :
      3 ≤ ([(0, true), (1, true), (0, false), (1, false),
        (3, false), (2, true), (2, false), (3, true)] :
          List (ℕ × Bool)).length := by decide
  let wThree : PolygonWord ℕ :=
    ⟨[(0, true), (1, true), (0, false), (1, false),
      (3, false), (2, true), (2, false), (3, true)], hwThreeLength⟩
  have hreverseCWord : wTwo.reverseLabel 2 = wThree := by
    apply Subtype.ext
    rw [PolygonWord.reverseLabel_val]
    simp [wTwo, wThree, PolygonWord.reverseSignAt]
  have hreverseC := PolygonWord.equivalent_reverseLabel_eq
    wTwo wThree 2 hreverseCWord
  have hproperThree : ({wThree} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wThree]
    decide
  have hdecompThree : wThree.1 =
      [(0, true), (1, true), (0, false), (1, false), (3, false)] ++
        [(2, true), (2, false)] ++ [(3, true)] := by
    rfl
  have hremainC :
      4 ≤ ([(0, true), (1, true), (0, false), (1, false), (3, false)] ++
        [(3, true)]).length := by decide
  have hwFourLength :
      3 ≤ ([(0, true), (1, true), (0, false), (1, false),
        (3, false), (3, true)] : List (ℕ × Bool)).length := by decide
  let wFour : PolygonWord ℕ :=
    ⟨[(0, true), (1, true), (0, false), (1, false),
      (3, false), (3, true)], hwFourLength⟩
  have hcancelC :
      LabellingScheme.Equivalent ({wThree} : LabellingScheme ℕ) {wFour} := by
    simpa [wThree, wFour] using
      PolygonWord.equivalentCancelPair wThree
        [(0, true), (1, true), (0, false), (1, false), (3, false)]
          [(3, true)] 2 hproperThree hdecompThree hremainC
  have hwFiveLength :
      3 ≤ ([(0, true), (1, true), (0, false), (1, false),
        (3, true), (3, false)] : List (ℕ × Bool)).length := by decide
  let wFive : PolygonWord ℕ :=
    ⟨[(0, true), (1, true), (0, false), (1, false),
      (3, true), (3, false)], hwFiveLength⟩
  have hreverseDWord : wFour.reverseLabel 3 = wFive := by
    apply Subtype.ext
    rw [PolygonWord.reverseLabel_val]
    simp [wFour, wFive, PolygonWord.reverseSignAt]
  have hreverseD := PolygonWord.equivalent_reverseLabel_eq
    wFour wFive 3 hreverseDWord
  have hproperFive : ({wFive} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wFive]
    decide
  have hdecompFive : wFive.1 =
      [(0, true), (1, true), (0, false), (1, false)] ++
        [(3, true), (3, false)] ++ [] := by
    rfl
  have hremainD :
      4 ≤ ([(0, true), (1, true), (0, false), (1, false)] ++ []).length := by
    decide
  have hcancelD := PolygonWord.equivalentCancelPair wFive
    [(0, true), (1, true), (0, false), (1, false)] [] 3
      hproperFive hdecompFive hremainD
  simpa [wFive, SurfaceClassificationWord.oneHandle] using
    hrotate.trans (hcomm.trans
      (hreverseC.trans (hcancelC.trans (hreverseD.trans hcancelD))))

/-- Exercise 77.3 (10): The scheme `aabcdc⁻¹b⁻¹d⁻¹` reduces to `aabbcc`. -/
theorem reduceAabcdCInvBInvDInv :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.aabcdCInvBInvDInv} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.threeCrosscap} :
        LabellingScheme ℕ) := by
  -- Extract the `b,d,b⁻¹,d⁻¹` handle and retain the leading `aa` pair.
  have hproperSource :
      ({SurfaceClassificationWord.aabcdCInvBInvDInv} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    decide
  have hdecompSource : SurfaceClassificationWord.aabcdCInvBInvDInv.1 =
      [] ++ [(0, true), (0, true)] ++ [(1, true)] ++ [(2, true)] ++
        [(3, true)] ++ [(2, false)] ++ [(1, false)] ++ [] ++
          [(3, false)] ++ [] := by
    rfl
  have hwOneLength :
      3 ≤ ([(1, true), (3, true), (1, false), (3, false),
        (0, true), (0, true), (2, false), (2, true)] :
          List (ℕ × Bool)).length := by decide
  let wOne : PolygonWord ℕ :=
    ⟨[(1, true), (3, true), (1, false), (3, false),
      (0, true), (0, true), (2, false), (2, true)], hwOneLength⟩
  have hcomm :
      LabellingScheme.Equivalent ({SurfaceClassificationWord.aabcdCInvBInvDInv} :
        LabellingScheme ℕ) {wOne} := by
    simpa [SurfaceClassificationWord.aabcdCInvBInvDInv, wOne,
      List.append_assoc] using
        PolygonWord.equivalentCommutatorFront
          SurfaceClassificationWord.aabcdCInvBInvDInv []
            [(0, true), (0, true)] [(2, true)] [(2, false)] [] []
              1 3 hproperSource hdecompSource
  have hwTwoLength :
      3 ≤ ([(1, true), (3, true), (1, false), (3, false),
        (0, true), (0, true), (2, true), (2, false)] :
          List (ℕ × Bool)).length := by decide
  let wTwo : PolygonWord ℕ :=
    ⟨[(1, true), (3, true), (1, false), (3, false),
      (0, true), (0, true), (2, true), (2, false)], hwTwoLength⟩
  have hreverseWord : wOne.reverseLabel 2 = wTwo := by
    apply Subtype.ext
    rw [PolygonWord.reverseLabel_val]
    simp [wOne, wTwo, PolygonWord.reverseSignAt]
  have hreverse := PolygonWord.equivalent_reverseLabel_eq
    wOne wTwo 2 hreverseWord
  have hproperTwo : ({wTwo} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wTwo]
    decide
  have hdecompTwo : wTwo.1 =
      [(1, true), (3, true), (1, false), (3, false), (0, true), (0, true)] ++
        [(2, true), (2, false)] ++ [] := by
    rfl
  have hremain :
      4 ≤ ([(1, true), (3, true), (1, false), (3, false),
        (0, true), (0, true)] ++ []).length := by decide
  have hwThreeLength :
      3 ≤ ([(1, true), (3, true), (1, false), (3, false),
        (0, true), (0, true)] : List (ℕ × Bool)).length := by decide
  let wThree : PolygonWord ℕ :=
    ⟨[(1, true), (3, true), (1, false), (3, false),
      (0, true), (0, true)], hwThreeLength⟩
  have hcancel :
      LabellingScheme.Equivalent ({wTwo} : LabellingScheme ℕ) {wThree} := by
    simpa [wTwo, wThree] using
      PolygonWord.equivalentCancelPair wTwo
        [(1, true), (3, true), (1, false), (3, false), (0, true), (0, true)]
          [] 2 hproperTwo hdecompTwo hremain
  have hwFourLength :
      3 ≤ ([(1, true), (2, true), (1, false), (2, false),
        (0, true), (0, true)] : List (ℕ × Bool)).length := by decide
  let wFour : PolygonWord ℕ :=
    ⟨[(1, true), (2, true), (1, false), (2, false),
      (0, true), (0, true)], hwFourLength⟩
  have hfresh : ({wThree} : LabellingScheme ℕ).AvoidsLabel 2 := by
    rw [LabellingScheme.singleton_avoidsLabel_iff]
    simp [wThree]
  have hthree_ne_two : (3 : ℕ) ≠ 2 := by decide
  have hrenameWord : wThree.relabel (PolygonWord.swapLabels 3 2) = wFour := by
    apply Subtype.ext
    rw [PolygonWord.relabel_val]
    simp [wThree, wFour, PolygonWord.swapLabels, Equiv.swap_apply_def]
  have hrename := PolygonWord.equivalent_renameLabel_eq
    wThree wFour 3 2 hthree_ne_two hfresh hrenameWord
  have hwFiveLength :
      3 ≤ ([(0, true), (0, true), (1, true), (2, true),
        (1, false), (2, false)] : List (ℕ × Bool)).length := by decide
  let wFive : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (1, true), (2, true),
      (1, false), (2, false)], hwFiveLength⟩
  have hrotationOne : List.IsRotated wFour.1 wFive.1 := by
    have hrot := List.isRotated_append
      (l := [(1, true), (2, true), (1, false), (2, false)])
      (l' := [(0, true), (0, true)])
    simpa [wFour, wFive] using hrot
  have hrotateOne := PolygonWord.equivalent_of_isRotated wFour wFive hrotationOne
  have hproperFive : ({wFive} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wFive]
    decide
  have hdecompFive : wFive.1 = [] ++
      [(0, true), (0, true), (1, true), (2, true), (1, false), (2, false)] ++
        [] := by
    rfl
  have hwSixLength :
      3 ≤ ([(1, true), (1, true), (2, true), (2, true),
        (0, true), (0, true)] : List (ℕ × Bool)).length := by decide
  let wSix : PolygonWord ℕ :=
    ⟨[(1, true), (1, true), (2, true), (2, true),
      (0, true), (0, true)], hwSixLength⟩
  have hpair :
      LabellingScheme.Equivalent ({wFive} : LabellingScheme ℕ) {wSix} := by
    simpa [wFive, wSix, PolygonWord.pairCommutator] using
      PolygonWord.equivalent_pairCommutator wFive [] [] 1 2 0
        hproperFive hdecompFive
  have hrotationTwo :
      List.IsRotated wSix.1 SurfaceClassificationWord.threeCrosscap.1 := by
    have hrot := List.isRotated_append
      (l := [(1, true), (1, true), (2, true), (2, true)])
      (l' := [(0, true), (0, true)])
    simpa [wSix, SurfaceClassificationWord.threeCrosscap] using hrot
  have hrotateTwo := PolygonWord.equivalent_of_isRotated wSix
    SurfaceClassificationWord.threeCrosscap hrotationTwo
  exact hcomm.trans (hreverse.trans (hcancel.trans
    (hrename.trans (hrotateOne.trans (hpair.trans hrotateTwo)))))

/-- Exercise 77.3 (11): The scheme `abcdabdc` reduces to `aabbcc`. -/
theorem reduceAbcdAbdc :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.abcdAbdc} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.threeCrosscap} :
        LabellingScheme ℕ) := by
  -- Rotate to place the two `b` edges around the fragment to be inverted.
  have hwOneLength :
      3 ≤ ([(2, true), (3, true), (0, true), (1, true),
        (3, true), (2, true), (0, true), (1, true)] :
          List (ℕ × Bool)).length := by decide
  let wOne : PolygonWord ℕ :=
    ⟨[(2, true), (3, true), (0, true), (1, true),
      (3, true), (2, true), (0, true), (1, true)], hwOneLength⟩
  have hrotation : List.IsRotated SurfaceClassificationWord.abcdAbdc.1 wOne.1 := by
    have hrot := List.isRotated_append
      (l := [(0, true), (1, true)])
      (l' := [(2, true), (3, true), (0, true), (1, true),
        (3, true), (2, true)])
    simpa [SurfaceClassificationWord.abcdAbdc, wOne] using hrot
  have hrotate := PolygonWord.equivalent_of_isRotated
    SurfaceClassificationWord.abcdAbdc wOne hrotation
  have hproperOne : ({wOne} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wOne]
    decide
  have hdecompOne : wOne.1 =
      [(2, true), (3, true), (0, true)] ++ [(1, true)] ++
        [(3, true), (2, true), (0, true)] ++ [(1, true)] ++ [] := by
    rfl
  have hwTwoLength :
      3 ≤ ([(1, true), (1, true), (2, true), (3, true),
        (0, true), (0, false), (2, false), (3, false)] :
          List (ℕ × Bool)).length := by decide
  let wTwo : PolygonWord ℕ :=
    ⟨[(1, true), (1, true), (2, true), (3, true),
      (0, true), (0, false), (2, false), (3, false)], hwTwoLength⟩
  have hfront :
      LabellingScheme.Equivalent ({wOne} : LabellingScheme ℕ) {wTwo} := by
    simpa [wOne, wTwo, PolygonWord.pairFront, FreeGroup.invRev] using
      PolygonWord.equivalent_pairFront wOne
        [(2, true), (3, true), (0, true)]
          [(3, true), (2, true), (0, true)] []
            (1, true) hproperOne hdecompOne
  have hproperTwo : ({wTwo} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wTwo]
    decide
  have hdecompTwo : wTwo.1 =
      [(1, true), (1, true), (2, true), (3, true)] ++
        [(0, true), (0, false)] ++ [(2, false), (3, false)] := by
    rfl
  have hremain :
      4 ≤ ([(1, true), (1, true), (2, true), (3, true)] ++
        [(2, false), (3, false)]).length := by decide
  have hwThreeLength :
      3 ≤ ([(1, true), (1, true), (2, true), (3, true),
        (2, false), (3, false)] : List (ℕ × Bool)).length := by decide
  let wThree : PolygonWord ℕ :=
    ⟨[(1, true), (1, true), (2, true), (3, true),
      (2, false), (3, false)], hwThreeLength⟩
  have hcancel :
      LabellingScheme.Equivalent ({wTwo} : LabellingScheme ℕ) {wThree} := by
    simpa [wTwo, wThree] using
      PolygonWord.equivalentCancelPair wTwo
        [(1, true), (1, true), (2, true), (3, true)]
          [(2, false), (3, false)] 0 hproperTwo hdecompTwo hremain
  have hwFourLength :
      3 ≤ ([(1, true), (1, true), (2, true), (0, true),
        (2, false), (0, false)] : List (ℕ × Bool)).length := by decide
  let wFour : PolygonWord ℕ :=
    ⟨[(1, true), (1, true), (2, true), (0, true),
      (2, false), (0, false)], hwFourLength⟩
  have hfresh : ({wThree} : LabellingScheme ℕ).AvoidsLabel 0 := by
    rw [LabellingScheme.singleton_avoidsLabel_iff]
    simp [wThree]
  have hthree_ne_zero : (3 : ℕ) ≠ 0 := by decide
  have hrenameWord : wThree.relabel (PolygonWord.swapLabels 3 0) = wFour := by
    apply Subtype.ext
    rw [PolygonWord.relabel_val]
    simp [wThree, wFour, PolygonWord.swapLabels, Equiv.swap_apply_def]
  have hrename := PolygonWord.equivalent_renameLabel_eq
    wThree wFour 3 0 hthree_ne_zero hfresh hrenameWord
  have hproperFour : ({wFour} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wFour]
    decide
  have hdecompFour : wFour.1 = [] ++
      [(1, true), (1, true), (2, true), (0, true), (2, false), (0, false)] ++
        [] := by
    rfl
  have hwFiveLength :
      3 ≤ ([(2, true), (2, true), (0, true), (0, true),
        (1, true), (1, true)] : List (ℕ × Bool)).length := by decide
  let wFive : PolygonWord ℕ :=
    ⟨[(2, true), (2, true), (0, true), (0, true),
      (1, true), (1, true)], hwFiveLength⟩
  have hpair :
      LabellingScheme.Equivalent ({wFour} : LabellingScheme ℕ) {wFive} := by
    simpa [wFour, wFive, PolygonWord.pairCommutator] using
      PolygonWord.equivalent_pairCommutator wFour [] [] 2 0 1
        hproperFour hdecompFour
  have hrotationFinal :
      List.IsRotated wFive.1 SurfaceClassificationWord.threeCrosscap.1 := by
    have hrot := List.isRotated_append
      (l := [(2, true), (2, true)])
      (l' := [(0, true), (0, true), (1, true), (1, true)])
    simpa [wFive, SurfaceClassificationWord.threeCrosscap] using hrot
  have hrotateFinal := PolygonWord.equivalent_of_isRotated wFive
    SurfaceClassificationWord.threeCrosscap hrotationFinal
  exact hrotate.trans (hfront.trans
    (hcancel.trans (hrename.trans (hpair.trans hrotateFinal))))

/-- Exercise 77.3 (12): The scheme `abcdabcd` reduces to `abab`. -/
theorem reduceAbcdAbcd :
    LabellingScheme.Equivalent ({SurfaceClassificationWord.abcdAbcd} :
      LabellingScheme ℕ) ({SurfaceClassificationWord.projectivePlane} :
        LabellingScheme ℕ) := by
  -- Move the two `a` edges forward, formally inverting the intervening `bcd` block.
  have hproperSource :
      ({SurfaceClassificationWord.abcdAbcd} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    decide
  have hdecompSource : SurfaceClassificationWord.abcdAbcd.1 =
      [] ++ [(0, true)] ++ [(1, true), (2, true), (3, true)] ++
        [(0, true)] ++ [(1, true), (2, true), (3, true)] := by
    rfl
  have hwOneLength :
      3 ≤ ([(0, true), (0, true), (3, false), (2, false),
        (1, false), (1, true), (2, true), (3, true)] :
          List (ℕ × Bool)).length := by decide
  let wOne : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (3, false), (2, false),
      (1, false), (1, true), (2, true), (3, true)], hwOneLength⟩
  have hfront :
      LabellingScheme.Equivalent ({SurfaceClassificationWord.abcdAbcd} :
        LabellingScheme ℕ) {wOne} := by
    simpa [SurfaceClassificationWord.abcdAbcd, wOne,
      PolygonWord.pairFront, FreeGroup.invRev] using
        PolygonWord.equivalent_pairFront SurfaceClassificationWord.abcdAbcd
          [] [(1, true), (2, true), (3, true)]
            [(1, true), (2, true), (3, true)] (0, true)
              hproperSource hdecompSource
  have hwTwoLength :
      3 ≤ ([(0, true), (0, true), (3, false), (2, false),
        (1, true), (1, false), (2, true), (3, true)] :
          List (ℕ × Bool)).length := by decide
  let wTwo : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (3, false), (2, false),
      (1, true), (1, false), (2, true), (3, true)], hwTwoLength⟩
  have hreverseBWord : wOne.reverseLabel 1 = wTwo := by
    apply Subtype.ext
    rw [PolygonWord.reverseLabel_val]
    simp [wOne, wTwo, PolygonWord.reverseSignAt]
  have hreverseB := PolygonWord.equivalent_reverseLabel_eq
    wOne wTwo 1 hreverseBWord
  have hproperTwo : ({wTwo} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wTwo]
    decide
  have hdecompTwo : wTwo.1 =
      [(0, true), (0, true), (3, false), (2, false)] ++
        [(1, true), (1, false)] ++ [(2, true), (3, true)] := by
    rfl
  have hremainB :
      4 ≤ ([(0, true), (0, true), (3, false), (2, false)] ++
        [(2, true), (3, true)]).length := by decide
  have hwThreeLength :
      3 ≤ ([(0, true), (0, true), (3, false), (2, false),
        (2, true), (3, true)] : List (ℕ × Bool)).length := by decide
  let wThree : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (3, false), (2, false),
      (2, true), (3, true)], hwThreeLength⟩
  have hcancelB :
      LabellingScheme.Equivalent ({wTwo} : LabellingScheme ℕ) {wThree} := by
    simpa [wTwo, wThree] using
      PolygonWord.equivalentCancelPair wTwo
        [(0, true), (0, true), (3, false), (2, false)]
          [(2, true), (3, true)] 1 hproperTwo hdecompTwo hremainB
  have hwFourLength :
      3 ≤ ([(0, true), (0, true), (3, false), (2, true),
        (2, false), (3, true)] : List (ℕ × Bool)).length := by decide
  let wFour : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (3, false), (2, true),
      (2, false), (3, true)], hwFourLength⟩
  have hreverseCWord : wThree.reverseLabel 2 = wFour := by
    apply Subtype.ext
    rw [PolygonWord.reverseLabel_val]
    simp [wThree, wFour, PolygonWord.reverseSignAt]
  have hreverseC := PolygonWord.equivalent_reverseLabel_eq
    wThree wFour 2 hreverseCWord
  have hproperFour : ({wFour} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wFour]
    decide
  have hdecompFour : wFour.1 =
      [(0, true), (0, true), (3, false)] ++ [(2, true), (2, false)] ++
        [(3, true)] := by
    rfl
  have hremainC :
      4 ≤ ([(0, true), (0, true), (3, false)] ++ [(3, true)]).length := by
    decide
  have hwFiveLength :
      3 ≤ ([(0, true), (0, true), (3, false), (3, true)] :
        List (ℕ × Bool)).length := by decide
  let wFive : PolygonWord ℕ :=
    ⟨[(0, true), (0, true), (3, false), (3, true)], hwFiveLength⟩
  have hcancelC :
      LabellingScheme.Equivalent ({wFour} : LabellingScheme ℕ) {wFive} := by
    simpa [wFour, wFive] using
      PolygonWord.equivalentCancelPair wFour
        [(0, true), (0, true), (3, false)] [(3, true)] 2
          hproperFour hdecompFour hremainC
  -- Read pair-front backwards to turn `aa d⁻¹d` into the alternating word `adad`.
  have hwSixLength :
      3 ≤ ([(0, true), (3, true), (0, true), (3, true)] :
        List (ℕ × Bool)).length := by decide
  let wSix : PolygonWord ℕ :=
    ⟨[(0, true), (3, true), (0, true), (3, true)], hwSixLength⟩
  have hproperSix : ({wSix} : LabellingScheme ℕ).Proper := by
    rw [LabellingScheme.proper_singleton_iff]
    simp only [wSix]
    decide
  have hdecompSix : wSix.1 = [] ++ [(0, true)] ++ [(3, true)] ++
      [(0, true)] ++ [(3, true)] := by
    rfl
  have hpairForward :
      LabellingScheme.Equivalent ({wSix} : LabellingScheme ℕ) {wFive} := by
    simpa [wSix, wFive, PolygonWord.pairFront, FreeGroup.invRev] using
      PolygonWord.equivalent_pairFront wSix [] [(3, true)] [(3, true)]
        (0, true) hproperSix hdecompSix
  have hpairBackward := hpairForward.symm
  have hfresh : ({wSix} : LabellingScheme ℕ).AvoidsLabel 1 := by
    rw [LabellingScheme.singleton_avoidsLabel_iff]
    simp [wSix]
  have hthree_ne_one : (3 : ℕ) ≠ 1 := by decide
  have hrenameWord :
      wSix.relabel (PolygonWord.swapLabels 3 1) =
        SurfaceClassificationWord.projectivePlane := by
    apply Subtype.ext
    rw [PolygonWord.relabel_val]
    simp [wSix, SurfaceClassificationWord.projectivePlane,
      PolygonWord.swapLabels, Equiv.swap_apply_def]
  have hrename := PolygonWord.equivalent_renameLabel_eq wSix
    SurfaceClassificationWord.projectivePlane 3 1 hthree_ne_one hfresh hrenameWord
  exact hfront.trans (hreverseB.trans (hcancelB.trans
    (hreverseC.trans (hcancelC.trans (hpairBackward.trans hrename)))))
