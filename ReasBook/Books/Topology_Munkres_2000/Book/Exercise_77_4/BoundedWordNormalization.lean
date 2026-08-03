module

public import Topology_Munkres_2000.Book.Exercise_77_4.BoundaryWord
public import Topology_Munkres_2000.Book.Algorithm_76_3.Cancel
public import Topology_Munkres_2000.Book.Definition_76_6.Permutation
public import Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Definition_77_1.Proper
public import Mathlib.Data.List.Cycle

public section

namespace CyclicPolygon.EdgePasting

/-- Helper for Exercise 77.4: in a proper labelling scheme, twice the number
of distinct labels is the number of label occurrences. -/
theorem proper_twice_labelRank_eq_card {α : Type*} [DecidableEq α]
    (scheme : LabellingScheme α) (hproper : scheme.Proper) :
    2 * scheme.labels.toFinset.card = scheme.labels.card := by
  classical
  -- Sum the properness equation `count c = 2` over the finite label support.
  calc
    2 * scheme.labels.toFinset.card =
        ∑ _c ∈ scheme.labels.toFinset, 2 := by simp [mul_comm]
    _ = ∑ c ∈ scheme.labels.toFinset, Multiset.count c scheme.labels := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (LabellingScheme.proper_iff.mp hproper c
        (Multiset.mem_toFinset.mp hc)).symm
    _ = scheme.labels.card := Multiset.toFinset_sum_count_eq scheme.labels

/-- Helper for Exercise 77.4: for a proper singleton polygon scheme, twice
its distinct-label rank is the boundary-word length. -/
theorem properSingleton_twice_labelRank_eq_length {α : Type*} [DecidableEq α]
    (word : PolygonWord α) (hproper : ({word} : LabellingScheme α).Proper) :
    2 * ({word} : LabellingScheme α).labels.toFinset.card = word.val.length := by
  -- Specialize the scheme-level rank equation, then compute the singleton bind.
  calc
    2 * ({word} : LabellingScheme α).labels.toFinset.card =
        ({word} : LabellingScheme α).labels.card :=
      proper_twice_labelRank_eq_card ({word} : LabellingScheme α) hproper
    _ = word.val.length := by
      simp only [LabellingScheme.labels, Multiset.singleton_bind,
        Multiset.coe_card, List.length_map]

/-- Helper for Exercise 77.4: a proper polygon word of length at most ten has
at most five distinct edge labels. -/
theorem properSingleton_labelRank_le_five {α : Type*} [DecidableEq α]
    (word : PolygonWord α) (hproper : ({word} : LabellingScheme α).Proper)
    (hlength : word.val.length ≤ 10) :
    ({word} : LabellingScheme α).labels.toFinset.card ≤ 5 := by
  -- The exact rank equation turns the ten-letter bound into the desired estimate.
  have hrank := properSingleton_twice_labelRank_eq_length word hproper
  omega

/-- Helper for Exercise 77.4: every proper polygon word has at least four
boundary letters. -/
theorem properSingleton_four_le_length {α : Type*}
    (word : PolygonWord α) (hproper : ({word} : LabellingScheme α).Proper) :
    4 ≤ word.val.length := by
  classical
  -- Properness makes the length even, while the polygon-word invariant rules
  -- out the only smaller positive even lengths.
  have hrank := properSingleton_twice_labelRank_eq_length word hproper
  have hthree := word.property
  omega

/-- Helper for Exercise 77.4: the length of a proper polygon word with at most
ten letters is one of `4`, `6`, `8`, or `10`. -/
theorem properSingleton_length_cases_le_ten {α : Type*}
    (word : PolygonWord α) (hproper : ({word} : LabellingScheme α).Proper)
    (hlength : word.val.length ≤ 10) :
    word.val.length = 4 ∨ word.val.length = 6 ∨
      word.val.length = 8 ∨ word.val.length = 10 := by
  classical
  -- Combine the exact twice-rank formula with the lower and upper bounds.
  have hrank := properSingleton_twice_labelRank_eq_length word hproper
  have hfour := properSingleton_four_le_length word hproper
  omega

/-- Helper for Exercise 77.4: failure of the cyclic adjacency condition exposes
an oppositely signed pair at the head of a cyclic rotation. -/
theorem existsRotatedOppositePairAtHead {α : Type*}
    (word : PolygonWord α)
    (hadjacent : ¬ Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.val) :
    ∃ residual : List (α × Bool), ∃ a : α, ∃ b : Bool,
      List.IsRotated word.val ([(a, b), (a, !b)] ++ residual) := by
  -- Convert cyclic-chain failure into a bad adjacent pair in the list with
  -- its first letter appended at the end.
  obtain ⟨letters, hlength⟩ := word
  cases letters with
  | nil =>
      simp only [List.length_nil] at hlength
      omega
  | cons head tail =>
      rw [Cycle.chain_coe_cons,
        List.isChain_iff_forall_rel_of_append_cons_cons] at hadjacent
      push Not at hadjacent
      obtain ⟨left, right, before, after, hsplit, hbad⟩ := hadjacent
      rcases left with ⟨leftLabel, leftSign⟩
      rcases right with ⟨rightLabel, rightSign⟩
      have hlabels : rightLabel = leftLabel := hbad.1.symm
      have hsigns : rightSign = !leftSign := Bool.eq_not_iff.mpr hbad.2.symm
      subst rightLabel
      subst rightSign
      -- Rotate either an internal bad pair or the closing-first bad pair to
      -- the beginning of the word.
      induction after using List.reverseRecOn with
      | nil =>
          rcases before with _ | ⟨first, middle⟩
          · have hlengthSplit := congrArg List.length hsplit
            simp only [List.nil_append, List.length_append,
              List.length_cons, List.length_nil] at hlengthSplit hlength
            omega
          · simp only [List.cons_append, List.cons.injEq] at hsplit
            obtain ⟨rfl, htail⟩ := hsplit
            have htailReverse := congrArg List.reverse htail
            simp only [List.reverse_append, List.reverse_cons] at htailReverse
            obtain ⟨hhead, hmiddle⟩ := List.cons.inj htailReverse
            have hform : tail = middle ++ [(leftLabel, leftSign)] := by
              have hreversed := congrArg List.reverse hmiddle
              simpa using hreversed
            symm at hhead
            subst head
            refine ⟨middle, leftLabel, leftSign, ?_⟩
            simpa [hform, List.append_assoc] using
              (List.isRotated_append
                (l := (leftLabel, !leftSign) :: middle)
                (l' := [(leftLabel, leftSign)]))
      | append_singleton middle last =>
          have hsplitReverse := congrArg List.reverse hsplit
          simp only [List.reverse_append, List.reverse_cons] at hsplitReverse
          obtain ⟨hlast, hcore⟩ := List.cons.inj hsplitReverse
          subst last
          have hword : head :: tail = before ++
              (leftLabel, leftSign) :: (leftLabel, !leftSign) :: middle := by
            have hreversed := congrArg List.reverse hcore
            simpa using hreversed
          have hrotation : List.IsRotated (head :: tail)
              ([(leftLabel, leftSign), (leftLabel, !leftSign)] ++
                middle ++ before) := by
            rw [hword]
            simpa [List.append_assoc] using
              (List.isRotated_append
                (l := before)
                (l' := (leftLabel, leftSign) ::
                  (leftLabel, !leftSign) :: middle))
          exact ⟨middle ++ before, leftLabel, leftSign, hrotation⟩

/-- Helper for Exercise 77.4: in a proper word longer than four letters, an
opposite-sign adjacency can be rotated between two fragments of length at least two,
and its label occurs in neither fragment. -/
theorem existsSeparatedRotatedOppositePair {α : Type*}
    (word : PolygonWord α)
    (hproper : ({word} : LabellingScheme α).Proper)
    (hlength : 4 < word.val.length)
    (hadjacent : ¬ Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.val) :
    ∃ y₀ y₁ : List (α × Bool), ∃ a : α, ∃ b : Bool,
      2 ≤ y₀.length ∧ 2 ≤ y₁.length ∧
        List.IsRotated word.val (y₀ ++ [(a, b), (a, !b)] ++ y₁) ∧
          (∀ letter ∈ y₀, letter.1 ≠ a) ∧
            ∀ letter ∈ y₁, letter.1 ≠ a := by
  classical
  obtain ⟨residual, a, b, hpair⟩ :=
    existsRotatedOppositePairAtHead word hadjacent
  let y₁ := residual.take (residual.length - 2)
  let y₀ := residual.drop (residual.length - 2)
  have hresidualLength : residual.length + 2 = word.val.length := by
    have hlengthEq := hpair.perm.length_eq
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hlengthEq
    omega
  have hresidualFour : 4 ≤ residual.length := by
    have hrank := properSingleton_twice_labelRank_eq_length word hproper
    omega
  have hy₀Length : 2 ≤ y₀.length := by
    simp only [y₀, List.length_drop]
    omega
  have hy₁Length : 2 ≤ y₁.length := by
    simp only [y₁, List.length_take]
    rw [Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  have hresidual : y₁ ++ y₀ = residual :=
    List.take_append_drop (residual.length - 2) residual
  have hsecondRotation : List.IsRotated
      ([(a, b), (a, !b)] ++ residual)
      (y₀ ++ [(a, b), (a, !b)] ++ y₁) := by
    rw [← hresidual]
    simpa [List.append_assoc] using
      (List.isRotated_append
        (l := [(a, b), (a, !b)] ++ y₁) (l' := y₀))
  have hrotation := hpair.trans hsecondRotation
  -- Properness makes the displayed two occurrences exhaustive for their label.
  have haInWord : (a, b) ∈ word.val :=
    hrotation.mem_iff.mpr (by simp)
  have haInLabels : a ∈ ({word} : LabellingScheme α).labels :=
    LabellingScheme.mem_labels_iff.mpr
      ⟨word, by simp, b, haInWord⟩
  have haCountWord : List.count a (word.val.map Prod.fst) = 2 := by
    simpa only [LabellingScheme.labels, Multiset.singleton_bind,
      Multiset.map_coe, Multiset.coe_count] using
      (LabellingScheme.proper_iff.mp hproper a haInLabels)
  have haCountRotated :
      List.count a
        ((y₀ ++ [(a, b), (a, !b)] ++ y₁).map Prod.fst) = 2 := by
    rw [← hrotation.perm.map Prod.fst |>.count a]
    exact haCountWord
  have hy₀Fresh : ∀ letter ∈ y₀, letter.1 ≠ a := by
    intro letter hletter heq
    have hpositive : 0 < List.count a (y₀.map Prod.fst) := by
      rw [List.count_pos_iff]
      exact List.mem_map.mpr ⟨letter, hletter, heq⟩
    simp at haCountRotated
    omega
  have hy₁Fresh : ∀ letter ∈ y₁, letter.1 ≠ a := by
    intro letter hletter heq
    have hpositive : 0 < List.count a (y₁.map Prod.fst) := by
      rw [List.count_pos_iff]
      exact List.mem_map.mpr ⟨letter, hletter, heq⟩
    simp at haCountRotated
    omega
  exact ⟨y₀, y₁, a, b, hy₀Length, hy₁Length, hrotation,
    hy₀Fresh, hy₁Fresh⟩

/-- Helper for Exercise 77.4: deleting an exposed opposite-sign pair whose
label is absent from both residual fragments preserves singleton properness. -/
theorem properSingleton_ofRotatedCancelPair {α : Type*}
    (word : PolygonWord α) (y₀ y₁ : List (α × Bool)) (a : α) (b : Bool)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hrotation :
      List.IsRotated word.val (y₀ ++ [(a, b), (a, !b)] ++ y₁))
    (hy₀Fresh : ∀ letter ∈ y₀, letter.1 ≠ a)
    (hy₁Fresh : ∀ letter ∈ y₁, letter.1 ≠ a)
    (hproper : ({word} : LabellingScheme α).Proper) :
    ({(⟨y₀ ++ y₁,
        PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ :
        PolygonWord α)} : LabellingScheme α).Proper := by
  classical
  rw [LabellingScheme.proper_iff]
  intro c hc
  -- Any label surviving the deletion occurs in a residual fragment and is
  -- therefore different from the cancelled label.
  obtain ⟨shorter, hshorter, occurrenceSign, hoccurrence⟩ :=
    LabellingScheme.mem_labels_iff.mp hc
  simp only [Multiset.mem_singleton] at hshorter
  subst shorter
  have hcNe : c ≠ a := by
    rcases List.mem_append.mp hoccurrence with hleft | hright
    · exact hy₀Fresh (c, occurrenceSign) hleft
    · exact hy₁Fresh (c, occurrenceSign) hright
  have hcInWord : c ∈ ({word} : LabellingScheme α).labels := by
    apply LabellingScheme.mem_labels_iff.mpr
    refine ⟨word, by simp, occurrenceSign, ?_⟩
    apply hrotation.mem_iff.mpr
    rw [List.mem_append]
    rcases List.mem_append.mp hoccurrence with hleft | hright
    · exact Or.inl (List.mem_append.mpr (Or.inl hleft))
    · exact Or.inr hright
  have hcountWord : List.count c (word.val.map Prod.fst) = 2 := by
    simpa only [LabellingScheme.labels, Multiset.singleton_bind,
      Multiset.map_coe, Multiset.coe_count] using
      (LabellingScheme.proper_iff.mp hproper c hcInWord)
  have hcountRotated :
      List.count c
        ((y₀ ++ [(a, b), (a, !b)] ++ y₁).map Prod.fst) = 2 := by
    rw [← hrotation.perm.map Prod.fst |>.count c]
    exact hcountWord
  have hcountShorter : List.count c ((y₀ ++ y₁).map Prod.fst) = 2 := by
    -- The displayed pair contributes nothing to the count of a surviving label.
    simpa [hcNe, Ne.symm hcNe] using hcountRotated
  simpa only [LabellingScheme.labels, Multiset.singleton_bind,
    Multiset.map_coe, Multiset.coe_count] using hcountShorter

/-- Helper for Exercise 77.4: deleting an exposed opposite-sign pair whose
label is absent from both residual fragments preserves torus type. -/
theorem TorusType.ofRotatedCancelPair {α : Type*}
    (word : PolygonWord α) (y₀ y₁ : List (α × Bool)) (a : α) (b : Bool)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hrotation :
      List.IsRotated word.val (y₀ ++ [(a, b), (a, !b)] ++ y₁))
    (hy₀Fresh : ∀ letter ∈ y₀, letter.1 ≠ a)
    (hy₁Fresh : ∀ letter ∈ y₁, letter.1 ≠ a)
    (htorus : word.TorusType) :
    PolygonWord.TorusType
      (⟨y₀ ++ y₁,
        PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ :
        PolygonWord α) := by
  classical
  rw [PolygonWord.torusType_iff_count]
  intro c hc sign
  -- Membership in the shortened word proves that its label differs from the
  -- deleted one and also supplies the corresponding occurrence in `word`.
  obtain ⟨shorter, hshorter, occurrenceSign, hoccurrence⟩ :=
    LabellingScheme.mem_labels_iff.mp hc
  simp only [Multiset.mem_singleton] at hshorter
  subst shorter
  have hcNe : c ≠ a := by
    rcases List.mem_append.mp hoccurrence with hleft | hright
    · exact hy₀Fresh (c, occurrenceSign) hleft
    · exact hy₁Fresh (c, occurrenceSign) hright
  have hcInWord : c ∈ ({word} : LabellingScheme α).labels := by
    apply LabellingScheme.mem_labels_iff.mpr
    refine ⟨word, by simp, occurrenceSign, ?_⟩
    apply hrotation.mem_iff.mpr
    rw [List.mem_append]
    rcases List.mem_append.mp hoccurrence with hleft | hright
    · exact Or.inl (List.mem_append.mpr (Or.inl hleft))
    · exact Or.inr hright
  have hcountWord :=
    PolygonWord.torusType_iff_count.mp htorus c hcInWord sign
  have hcountRotated :
      Multiset.count (c, sign)
        ((y₀ ++ [(a, b), (a, !b)] ++ y₁ : List (α × Bool)) :
          Multiset (α × Bool)) = 1 := by
    have hmultiset : (word.val : Multiset (α × Bool)) =
        ((y₀ ++ [(a, b), (a, !b)] ++ y₁ : List (α × Bool)) :
          Multiset (α × Bool)) :=
      Multiset.coe_eq_coe.mpr hrotation.perm
    rwa [← hmultiset]
  -- Counts of every residual signed letter are unchanged by deleting the pair.
  simpa [hcNe, Ne.symm hcNe] using hcountRotated

/-- Helper for Exercise 77.4: inserting a fresh opposite-sign pair into a
torus-type residual and then cyclically rotating it preserves torus type. -/
theorem TorusType.ofInsertedRotatedCancelPair {α : Type*}
    (word : PolygonWord α) (y₀ y₁ : List (α × Bool)) (a : α) (b : Bool)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hrotation :
      List.IsRotated word.val (y₀ ++ [(a, b), (a, !b)] ++ y₁))
    (hy₀Fresh : ∀ letter ∈ y₀, letter.1 ≠ a)
    (hy₁Fresh : ∀ letter ∈ y₁, letter.1 ≠ a)
    (hshorter :
      PolygonWord.TorusType
        (⟨y₀ ++ y₁,
          PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ :
          PolygonWord α)) :
    word.TorusType := by
  classical
  rw [PolygonWord.torusType_iff_count]
  intro c hc sign
  have hmultiset : (word.val : Multiset (α × Bool)) =
      ((y₀ ++ [(a, b), (a, !b)] ++ y₁ : List (α × Bool)) :
        Multiset (α × Bool)) :=
    Multiset.coe_eq_coe.mpr hrotation.perm
  rw [hmultiset]
  by_cases hcCancelled : c = a
  · subst c
    -- Freshness makes the displayed positive/negative pair the two and only
    -- two occurrences of the reinserted label.
    have hy₀Count (s : Bool) :
        Multiset.count (a, s) (y₀ : Multiset (α × Bool)) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact hy₀Fresh (a, s) (Multiset.mem_coe.mp hmem) rfl
    have hy₁Count (s : Bool) :
        Multiset.count (a, s) (y₁ : Multiset (α × Bool)) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact hy₁Fresh (a, s) (Multiset.mem_coe.mp hmem) rfl
    rw [← Multiset.coe_add, ← Multiset.coe_add,
      Multiset.count_add, Multiset.count_add,
      hy₀Count sign, hy₁Count sign]
    cases sign <;> cases b <;> simp
  · -- Every other occurring label must occur in the residual word, where its
    -- signed count is one by the residual torus-type hypothesis.
    obtain ⟨original, horiginal, occurrenceSign, hoccurrence⟩ :=
      LabellingScheme.mem_labels_iff.mp hc
    simp only [Multiset.mem_singleton] at horiginal
    subst original
    have hresidualOccurrence : (c, occurrenceSign) ∈ y₀ ++ y₁ := by
      have hrotatedOccurrence := hrotation.mem_iff.mp hoccurrence
      apply List.mem_append.mpr
      rcases List.mem_append.mp hrotatedOccurrence with hprefix | hright
      · rcases List.mem_append.mp hprefix with hleft | hpair
        · exact Or.inl hleft
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
          rcases hpair with heq | heq
          · exact (hcCancelled (congrArg Prod.fst heq)).elim
          · exact (hcCancelled (congrArg Prod.fst heq)).elim
      · exact Or.inr hright
    have hcInShorter :
        c ∈ ({(⟨y₀ ++ y₁,
            PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ :
            PolygonWord α)} : LabellingScheme α).labels := by
      exact LabellingScheme.mem_labels_iff.mpr
        ⟨(⟨y₀ ++ y₁,
            PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ :
            PolygonWord α), by simp, occurrenceSign, hresidualOccurrence⟩
    have hcountShorter :=
      PolygonWord.torusType_iff_count.mp hshorter c hcInShorter sign
    simpa [hcCancelled, Ne.symm hcCancelled] using hcountShorter

/-- Helper for Exercise 77.4: a proper polygon word longer than four letters
either satisfies the no-opposite-adjacency condition or admits one explicit cyclic
permutation followed by cancellation, decreasing its length by two. -/
theorem existsCancellationStepOrNoOppositeAdjacent {α : Type*}
    (word : PolygonWord α)
    (hproper : ({word} : LabellingScheme α).Proper)
    (hlength : 4 < word.val.length) :
    Cycle.Chain (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.val ∨
      ∃ rotated shorter : PolygonWord α,
        LabellingScheme.Permute ({word} : LabellingScheme α) {rotated} ∧
          LabellingScheme.Cancel ({rotated} : LabellingScheme α) {shorter} ∧
            shorter.val.length + 2 = word.val.length ∧
              ({shorter} : LabellingScheme α).Proper ∧
                (shorter.TorusType ↔ word.TorusType) := by
  classical
  by_cases hadjacent : Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.val
  · exact Or.inl hadjacent
  · right
    obtain ⟨y₀, y₁, a, b, hy₀Length, hy₁Length, hrotation,
      hy₀Fresh, hy₁Fresh⟩ :=
      existsSeparatedRotatedOppositePair word hproper hlength hadjacent
    let rotated : PolygonWord α :=
      ⟨y₀ ++ [(a, b), (a, !b)] ++ y₁,
        PolygonWord.insertCancelPair_length y₀ y₁ a b hy₀Length⟩
    let shorter : PolygonWord α :=
      ⟨y₀ ++ y₁,
        PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩
    have hpermute : LabellingScheme.Permute
        ({word} : LabellingScheme α) {rotated} := by
      simpa only [rotated, Multiset.cons_zero] using
        LabellingScheme.Permute.of word rotated 0 hrotation
    have hemptyAvoid : LabellingScheme.AvoidsLabel
        (0 : LabellingScheme α) a := by
      rw [LabellingScheme.avoidsLabel_iff]
      intro emptyWord hword
      simp at hword
    have hcancel : LabellingScheme.Cancel
        ({rotated} : LabellingScheme α) {shorter} := by
      simpa only [rotated, shorter, Multiset.cons_zero] using
        LabellingScheme.Cancel.of y₀ y₁ a b 0 hy₀Length hy₁Length
          hy₀Fresh hy₁Fresh hemptyAvoid
    have hshorterLength : shorter.val.length + 2 = word.val.length := by
      have hrotationLength := hrotation.perm.length_eq
      simp only [shorter, List.length_append]
      simp only [List.length_append, List.length_cons, List.length_nil]
        at hrotationLength
      omega
    have hshorterProper : ({shorter} : LabellingScheme α).Proper := by
      -- Remove the fresh inverse pair without changing any surviving unsigned count.
      exact properSingleton_ofRotatedCancelPair word y₀ y₁ a b
        hy₀Length hy₁Length hrotation hy₀Fresh hy₁Fresh hproper
    have htorusPreserved : shorter.TorusType ↔ word.TorusType := by
      constructor
      · -- Reinserting the fresh inverse pair restores one occurrence of each sign.
        exact TorusType.ofInsertedRotatedCancelPair word y₀ y₁ a b
          hy₀Length hy₁Length hrotation hy₀Fresh hy₁Fresh
      · -- Deleting that pair leaves every residual signed count unchanged.
        exact TorusType.ofRotatedCancelPair word y₀ y₁ a b
          hy₀Length hy₁Length hrotation hy₀Fresh hy₁Fresh
    exact ⟨rotated, shorter, hpermute, hcancel, hshorterLength,
      hshorterProper, htorusPreserved⟩

/-- Helper for Exercise 77.4: bounded proper words are either terminal
four-letter words, satisfy the handle-extraction adjacency condition, or admit an
explicit rank-decreasing cancellation. -/
theorem boundedCancellationFrontier {α : Type*}
    (word : PolygonWord α)
    (hproper : ({word} : LabellingScheme α).Proper)
    (hlength : word.val.length ≤ 10) :
    word.val.length = 4 ∨
      Cycle.Chain (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.val ∨
        ∃ rotated shorter : PolygonWord α,
          LabellingScheme.Permute ({word} : LabellingScheme α) {rotated} ∧
            LabellingScheme.Cancel ({rotated} : LabellingScheme α) {shorter} ∧
              shorter.val.length + 2 = word.val.length ∧
                ({shorter} : LabellingScheme α).Proper ∧
                  (shorter.TorusType ↔ word.TorusType) := by
  -- Separate the terminal rank; every remaining allowed length is strictly
  -- greater than four and therefore enters the cancellation dichotomy.
  by_cases hterminal : word.val.length = 4
  · exact Or.inl hterminal
  · right
    have hfour := properSingleton_four_le_length word hproper
    have hstrict : 4 < word.val.length := by omega
    exact existsCancellationStepOrNoOppositeAdjacent word hproper hstrict

end CyclicPolygon.EdgePasting

end
