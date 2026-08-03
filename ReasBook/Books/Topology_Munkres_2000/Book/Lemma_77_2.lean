module

public import Topology_Munkres_2000.Book.Algorithm_76_3.Cancel
public import Topology_Munkres_2000.Book.Definition_76_6.Permutation
public import Topology_Munkres_2000.Book.Definition_76_10.Equivalence
public import Topology_Munkres_2000.Book.Definition_77_1.Proper
public import Topology_Munkres_2000.Book.Proposition_77_1.NormalForm
public import Mathlib.Data.List.Cycle
import all Topology_Munkres_2000.Book.Definition_76_6.Relabel
import all Topology_Munkres_2000.Book.Definition_76_10.Equivalence
import all Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Proposition_77_1.NormalForm

public section

universe u

namespace PolygonWord

/-- Helper for Lemma 77.2: failure of the cyclic adjacency relation exposes an
oppositely signed pair at the beginning of a cyclic rotation. -/
private lemma existsRotatedCancelPairAtHead {α : Type u} (word : PolygonWord α)
    (hadjacent : ¬ Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.1) :
    ∃ residual : List (α × Bool), ∃ a : α, ∃ b : Bool,
      List.IsRotated word.1 ([(a, b), (a, !b)] ++ residual) := by
  -- A polygon word is nonempty, so cyclic failure is ordinary chain failure
  -- after its first letter is appended at the end.
  obtain ⟨letters, hlength⟩ := word
  cases letters with
  | nil =>
      simp only [List.length_nil] at hlength
      omega
  | cons head tail =>
      rw [Cycle.chain_coe_cons, List.isChain_iff_forall_rel_of_append_cons_cons]
        at hadjacent
      push Not at hadjacent
      obtain ⟨left, right, before, after, hsplit, hbad⟩ := hadjacent
      rcases left with ⟨leftLabel, leftSign⟩
      rcases right with ⟨rightLabel, rightSign⟩
      have hlabels : rightLabel = leftLabel := hbad.1.symm
      have hsigns : rightSign = !leftSign := Bool.eq_not_iff.mpr hbad.2.symm
      subst rightLabel
      subst rightSign
      -- If the displayed bad pair is internal, rotate its preceding fragment to
      -- the end.  If it uses the closing-first edge, rotate the final letter first.
      induction after using List.reverseRecOn with
      | nil =>
          rcases before with _ | ⟨first, middle⟩
          · have hlengthSplit := congrArg List.length hsplit
            simp only [List.nil_append, List.append_nil, List.length_append,
              List.length_cons, List.length_nil] at hlengthSplit hlength
            omega
          · simp only [List.cons_append, List.cons.injEq] at hsplit
            obtain ⟨rfl, htail⟩ := hsplit
            have htailReverse := congrArg List.reverse htail
            simp only [List.reverse_append, List.reverse_singleton,
              List.singleton_append, List.reverse_cons] at htailReverse
            obtain ⟨hhead, hmiddle⟩ := List.cons.inj htailReverse
            have hform : tail = middle ++ [(leftLabel, leftSign)] := by
              have := congrArg List.reverse hmiddle
              simpa using this
            symm at hhead
            subst head
            refine ⟨middle, leftLabel, leftSign, ?_⟩
            simpa [hform, List.append_assoc] using
              (List.isRotated_append (l := (leftLabel, !leftSign) :: middle)
                (l' := [(leftLabel, leftSign)]))
      | append_singleton middle last =>
          have hsplitReverse := congrArg List.reverse hsplit
          simp only [List.reverse_append, List.reverse_singleton,
            List.singleton_append, List.reverse_cons] at hsplitReverse
          obtain ⟨hlast, hcore⟩ := List.cons.inj hsplitReverse
          subst last
          have hword : head :: tail = before ++
              (leftLabel, leftSign) :: (leftLabel, !leftSign) :: middle := by
            have := congrArg List.reverse hcore
            simpa using this
          have hrotation : List.IsRotated (head :: tail)
              ([(leftLabel, leftSign), (leftLabel, !leftSign)] ++ middle ++ before) := by
            rw [hword]
            simpa [List.append_assoc] using
              (List.isRotated_append
                (l := before)
                (l' := (leftLabel, leftSign) :: (leftLabel, !leftSign) :: middle))
          exact ⟨middle ++ before, leftLabel, leftSign, hrotation⟩

/-- Helper for Lemma 77.2: a finite multiset in which every occurring element
has multiplicity two has even cardinality. -/
private theorem multisetCard_eq_twice_of_count_eq_two {α : Type u} [DecidableEq α]
    (labels : Multiset α)
    (hcount : ∀ c ∈ labels, Multiset.count c labels = 2) :
    ∃ rank : ℕ, labels.card = 2 * rank := by
  by_cases hempty : labels = 0
  · subst labels
    exact ⟨0, rfl⟩
  · obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hempty
    let rest := (labels.erase c).erase c
    have hcAfter : c ∈ labels.erase c := by
      rw [← Multiset.count_pos, Multiset.count_erase_self, hcount c hc]
      decide
    have hdecomposition : labels = c ::ₘ c ::ₘ rest := by
      calc
        labels = c ::ₘ labels.erase c := (Multiset.cons_erase hc).symm
        _ = c ::ₘ c ::ₘ rest :=
          congrArg (Multiset.cons c) (Multiset.cons_erase hcAfter).symm
    have hcRest : c ∉ rest := by
      rw [← Multiset.count_eq_zero]
      simp only [rest, Multiset.count_erase_self, hcount c hc]
    have hrestCount : ∀ d ∈ rest, Multiset.count d rest = 2 := by
      intro d hd
      have hdc : d ≠ c := by
        intro heq
        subst d
        exact hcRest hd
      have hdLabels : d ∈ labels := by
        rw [hdecomposition]
        simp only [Multiset.mem_cons]
        exact Or.inr (Or.inr hd)
      have hdCount := hcount d hdLabels
      rw [hdecomposition, Multiset.count_cons, Multiset.count_cons] at hdCount
      simpa only [if_neg hdc, Nat.add_zero] using hdCount
    have hrestCard : rest.card < labels.card := by
      rw [hdecomposition, Multiset.card_cons, Multiset.card_cons]
      omega
    obtain ⟨rank, hrank⟩ :=
      multisetCard_eq_twice_of_count_eq_two rest hrestCount
    refine ⟨rank + 1, ?_⟩
    rw [hdecomposition, Multiset.card_cons, Multiset.card_cons, hrank]
    omega
termination_by labels.card
decreasing_by
  exact hrestCard

/-- Helper for Lemma 77.2: the length of a proper singleton polygon scheme is
twice the number of its distinct unsigned labels. -/
private lemma properSingleton_length_eq_twiceLabelCount {α : Type u}
    (word : PolygonWord α) (hproper : ({word} : LabellingScheme α).Proper) :
    ∃ rank : ℕ, word.1.length = 2 * rank := by
  classical
  -- Apply the multiset parity statement to the unsigned-label multiset, then
  -- compute the cardinality of the singleton bind.
  obtain ⟨rank, hrank⟩ := multisetCard_eq_twice_of_count_eq_two
    ({word} : LabellingScheme α).labels
    (LabellingScheme.proper_iff.mp hproper)
  refine ⟨rank, ?_⟩
  calc
    word.1.length = ({word} : LabellingScheme α).labels.card := by
      simp only [LabellingScheme.labels, Multiset.singleton_bind,
        Multiset.coe_card, List.length_map]
    _ = 2 * rank := hrank

/-- Helper for Lemma 77.2: in a proper word of length greater than four, a cyclic
opposite-sign adjacency can be placed between two fresh fragments of length at least two. -/
private lemma existsRotatedCancelPair {α : Type u} (word : PolygonWord α)
    (hproper : ({word} : LabellingScheme α).Proper) (hlength : 4 < word.1.length)
    (hadjacent : ¬ Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.1) :
    ∃ y₀ y₁ : List (α × Bool), ∃ a : α, ∃ b : Bool,
      2 ≤ y₀.length ∧ 2 ≤ y₁.length ∧
        List.IsRotated word.1 (y₀ ++ [(a, b), (a, !b)] ++ y₁) ∧
          (∀ letter ∈ y₀, letter.1 ≠ a) ∧ (∀ letter ∈ y₁, letter.1 ≠ a) := by
  classical
  obtain ⟨residual, a, b, hpair⟩ := existsRotatedCancelPairAtHead word hadjacent
  -- Split the residual two letters from its end; after one more rotation these
  -- become the leading cancellation fragment.
  let y₁ := residual.take (residual.length - 2)
  let y₀ := residual.drop (residual.length - 2)
  have hresidualLength : residual.length + 2 = word.1.length := by
    have hlengthEq := hpair.perm.length_eq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlengthEq
    omega
  have hresidualFour : 4 ≤ residual.length := by
    obtain ⟨rank, hrank⟩ := properSingleton_length_eq_twiceLabelCount word hproper
    omega
  have hy₀Length : 2 ≤ y₀.length := by
    simp only [y₀, List.length_drop]
    omega
  have hy₁Length : 2 ≤ y₁.length := by
    simp only [y₁, List.length_take]
    rw [Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  have hresidual : y₁ ++ y₀ = residual := by
    exact List.take_append_drop (residual.length - 2) residual
  have hsecondRotation : List.IsRotated
      ([(a, b), (a, !b)] ++ residual)
      (y₀ ++ [(a, b), (a, !b)] ++ y₁) := by
    rw [← hresidual]
    simpa [List.append_assoc] using
      (List.isRotated_append
        (l := [(a, b), (a, !b)] ++ y₁) (l' := y₀))
  have hrotation := hpair.trans hsecondRotation
  -- Properness says the exposed label occurs exactly twice, so neither
  -- residual fragment can contain a third occurrence.
  have haInWord : (a, b) ∈ word.1 := by
    exact hrotation.mem_iff.mpr (by simp)
  have haInLabels : a ∈ ({word} : LabellingScheme α).labels := by
    exact LabellingScheme.mem_labels_iff.mpr
      ⟨word, by simp, b, haInWord⟩
  have haCountWord : List.count a (word.1.map Prod.fst) = 2 := by
    simpa only [LabellingScheme.labels, Multiset.singleton_bind,
      Multiset.map_coe, Multiset.coe_count] using
        (LabellingScheme.proper_iff.mp hproper a haInLabels)
  have haCountRotated :
      List.count a ((y₀ ++ [(a, b), (a, !b)] ++ y₁).map Prod.fst) = 2 := by
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

/-- Helper for Lemma 77.2: deleting an exposed opposite-sign pair from a torus-type
word preserves torus type when the pair's label is absent from the residual fragments. -/
private lemma TorusType.ofRotatedCancelPair {α : Type u} (word : PolygonWord α)
    (y₀ y₁ : List (α × Bool)) (a : α) (b : Bool)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hrotation : List.IsRotated word.1 (y₀ ++ [(a, b), (a, !b)] ++ y₁))
    (hy₀Fresh : ∀ letter ∈ y₀, letter.1 ≠ a)
    (hy₁Fresh : ∀ letter ∈ y₁, letter.1 ≠ a)
    (htorus : word.TorusType) :
    PolygonWord.TorusType
      (⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ :
        PolygonWord α) := by
  classical
  rw [PolygonWord.torusType_iff_count]
  intro c hc sign
  -- Membership in the shortened word supplies a residual occurrence and hence
  -- proves that its label differs from the cancelled label.
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
  have hcountWord := PolygonWord.torusType_iff_count.mp htorus c hcInWord sign
  have hcountRotated :
      Multiset.count (c, sign)
        ((y₀ ++ [(a, b), (a, !b)] ++ y₁ : List (α × Bool)) :
          Multiset (α × Bool)) = 1 := by
    have hmultiset : (word.1 : Multiset (α × Bool)) =
        ((y₀ ++ [(a, b), (a, !b)] ++ y₁ : List (α × Bool)) :
          Multiset (α × Bool)) :=
      Multiset.coe_eq_coe.mpr hrotation.perm
    rwa [← hmultiset]
  simpa [hcNe, Ne.symm hcNe] using hcountRotated

/-- Helper for Lemma 77.2: avoiding a label is equivalent to its absence from
the unsigned-label multiset. -/
private lemma avoidsLabel_iff_not_mem_labels {α : Type u}
    {scheme : LabellingScheme α} {c : α} :
    scheme.AvoidsLabel c ↔ c ∉ scheme.labels := by
  constructor
  · intro havoid hc
    obtain ⟨word, hword, sign, hletter⟩ :=
      LabellingScheme.mem_labels_iff.mp hc
    exact (LabellingScheme.avoidsLabel_iff.mp havoid word hword
      (c, sign) hletter) rfl
  · intro hc
    rw [LabellingScheme.avoidsLabel_iff]
    rintro word hword ⟨label, sign⟩ hletter rfl
    exact hc (LabellingScheme.mem_labels_iff.mpr
      ⟨word, hword, sign, hletter⟩)

/-- Helper for Lemma 77.2: properness only depends on the multiset of
unsigned labels. -/
private lemma proper_iff_of_labels_eq {α : Type u}
    {first second : LabellingScheme α}
    (hlabels : first.labels = second.labels) :
    first.Proper ↔ second.Proper := by
  -- Rewrite the defining decompositions through the common label multiset.
  unfold LabellingScheme.Proper
  rw [hlabels]

/-- Helper for Lemma 77.2: adjoining exactly two occurrences of a fresh label
preserves the properness condition. -/
private lemma proper_iff_of_labels_eq_fresh_pair {α : Type u}
    {larger smaller : LabellingScheme α} {c : α}
    (hlabels : larger.labels = c ::ₘ c ::ₘ smaller.labels)
    (hfresh : c ∉ smaller.labels) :
    larger.Proper ↔ smaller.Proper := by
  classical
  rw [LabellingScheme.proper_iff, LabellingScheme.proper_iff, hlabels]
  constructor
  · intro hproper a ha
    have haLarger : a ∈ c ::ₘ c ::ₘ smaller.labels := by
      simp only [Multiset.mem_cons]
      exact Or.inr (Or.inr ha)
    have hcount := hproper a haLarger
    have hac : a ≠ c := by
      intro hac
      subst a
      exact hfresh ha
    simpa [hac, Ne.symm hac] using hcount
  · intro hproper a ha
    simp only [Multiset.mem_cons] at ha
    rcases ha with hac | hac | ha
    · subst a
      simp only [Multiset.count_cons_self,
        Multiset.count_eq_zero.mpr hfresh]
    · subst a
      simp only [Multiset.count_cons_self,
        Multiset.count_eq_zero.mpr hfresh]
    · have hac : a ≠ c := by
        intro hac
        subst a
        exact hfresh ha
      simpa [hac, Ne.symm hac] using hproper a ha

/-- Helper for Lemma 77.2: the unsigned labels in a relabelled word are the
image of its original unsigned labels. -/
private lemma relabel_unsignedLabels {α : Type u} {β : Type*}
    (e : α ≃ β) (word : PolygonWord α) :
    (word.relabel e).1.map Prod.fst = word.1.map (e ∘ Prod.fst) := by
  -- Projecting after relabelling is pointwise application of the label equivalence.
  rw [PolygonWord.relabel_val, List.map_map]
  rfl

/-- Helper for Lemma 77.2: reversing signs at one label leaves every unsigned
label in a word unchanged. -/
private lemma reverseLabel_unsignedLabels {α : Type u} (a : α)
    (word : PolygonWord α) :
    (word.reverseLabel a).1.map Prod.fst = word.1.map Prod.fst := by
  classical
  rw [PolygonWord.reverseLabel_val, List.map_map]
  -- The conditional sign change never alters the first projection.
  apply List.map_congr_left
  rintro ⟨label, sign⟩ _
  by_cases hlabel : label = a
  · subst label
    simp [PolygonWord.reverseSignAt]
  · simp [PolygonWord.reverseSignAt, hlabel]

/-- Helper for Lemma 77.2: relabelling a scheme maps its unsigned-label
multiset along the same equivalence. -/
private lemma labels_relabel {α : Type u} {β : Type*}
    (e : α ≃ β) (scheme : LabellingScheme α) :
    (scheme.relabel e).labels = scheme.labels.map e := by
  unfold LabellingScheme.labels LabellingScheme.relabel
  rw [Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr
  intro word _
  rw [relabel_unsignedLabels]
  simp only [Multiset.map_coe, List.map_map]

/-- Helper for Lemma 77.2: a bijective relabelling preserves properness. -/
private lemma relabelProper_iff {α : Type u} {β : Type*}
    (e : α ≃ β) (scheme : LabellingScheme α) :
    (scheme.relabel e).Proper ↔ scheme.Proper := by
  classical
  rw [LabellingScheme.proper_iff, LabellingScheme.proper_iff,
    labels_relabel]
  constructor
  · intro hproper c hc
    have hmem : e c ∈ scheme.labels.map e :=
      Multiset.mem_map.mpr ⟨c, hc, rfl⟩
    have hcount := hproper (e c) hmem
    rwa [Multiset.count_map_eq_count' e scheme.labels e.injective c] at hcount
  · intro hproper c hc
    obtain ⟨original, horiginal, rfl⟩ := Multiset.mem_map.mp hc
    rw [Multiset.count_map_eq_count' e scheme.labels e.injective original]
    exact hproper original horiginal

/-- Helper for Lemma 77.2: reversing the signs attached to one label preserves
properness of the whole scheme. -/
private lemma reverseLabelProper_iff {α : Type u}
    (scheme : LabellingScheme α) (a : α) :
    (scheme.reverseLabel a).Proper ↔ scheme.Proper := by
  apply proper_iff_of_labels_eq
  unfold LabellingScheme.labels LabellingScheme.reverseLabel
  rw [Multiset.bind_map]
  apply Multiset.bind_congr
  intro word _
  rw [reverseLabel_unsignedLabels]

/-- Helper for Lemma 77.2: splitting a word by a fresh cut adds precisely two
unsigned occurrences of the cutting label. -/
private lemma cutProper_iff {α : Type u}
    {before after : LabellingScheme α}
    (step : LabellingScheme.Cut before after) :
    before.Proper ↔ after.Proper := by
  classical
  rcases step with
    ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
  let joined : PolygonWord α :=
    ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩
  let left : PolygonWord α :=
    ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
  let right : PolygonWord α :=
    ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
  have hfreshScheme :
      LabellingScheme.AvoidsLabel (joined ::ₘ rest : LabellingScheme α) c := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro word hword letter hletter
    simp only [Multiset.mem_cons] at hword
    rcases hword with rfl | hword
    · rcases List.mem_append.mp hletter with hletter | hletter
      · exact hy₀ letter hletter
      · exact hy₁ letter hletter
    · exact LabellingScheme.avoidsLabel_iff.mp hrest word hword letter hletter
  have hlabels :
      LabellingScheme.labels (left ::ₘ right ::ₘ rest : LabellingScheme α) =
        c ::ₘ c ::ₘ
          LabellingScheme.labels (joined ::ₘ rest : LabellingScheme α) := by
    ext label
    unfold LabellingScheme.labels
    simp only [left, right, joined, Multiset.cons_bind, List.map_append,
      List.map_cons, List.map_nil,
      Multiset.count_add, Multiset.coe_count, List.count_append,
      List.count_cons, List.count_nil]
    by_cases hlabel : label = c
    · subst label
      simp
      omega
    · simp [hlabel, Ne.symm hlabel]
      omega
  -- Read the cut backwards as deletion of the fresh double occurrence.
  simpa only [joined, left, right] using
    (proper_iff_of_labels_eq_fresh_pair hlabels
      (avoidsLabel_iff_not_mem_labels.mp hfreshScheme)).symm

/-- Helper for Lemma 77.2: cancelling an isolated inverse pair removes exactly
two occurrences of one fresh label and preserves properness. -/
private lemma cancelProper_iff {α : Type u}
    {before after : LabellingScheme α}
    (step : LabellingScheme.Cancel before after) :
    before.Proper ↔ after.Proper := by
  classical
  rcases step with
    ⟨y₀, y₁, a, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
  let longer : PolygonWord α :=
    ⟨y₀ ++ [(a, b), (a, !b)] ++ y₁,
      PolygonWord.insertCancelPair_length y₀ y₁ a b hy₀Length⟩
  let shorter : PolygonWord α :=
    ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩
  have hfreshScheme :
      LabellingScheme.AvoidsLabel (shorter ::ₘ rest : LabellingScheme α) a := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro word hword letter hletter
    simp only [Multiset.mem_cons] at hword
    rcases hword with rfl | hword
    · rcases List.mem_append.mp hletter with hletter | hletter
      · exact hy₀ letter hletter
      · exact hy₁ letter hletter
    · exact LabellingScheme.avoidsLabel_iff.mp hrest word hword letter hletter
  have hlabels :
      LabellingScheme.labels (longer ::ₘ rest : LabellingScheme α) =
        a ::ₘ a ::ₘ
          LabellingScheme.labels (shorter ::ₘ rest : LabellingScheme α) := by
    ext label
    unfold LabellingScheme.labels
    simp only [longer, shorter, Multiset.cons_bind, List.map_append,
      List.map_cons, List.map_nil,
      Multiset.count_add, Multiset.coe_count, List.count_append,
      List.count_cons, List.count_nil]
    by_cases hlabel : label = a
    · subst label
      simp
      omega
    · simp [hlabel, Ne.symm hlabel]
  simpa only [longer, shorter] using
    proper_iff_of_labels_eq_fresh_pair hlabels
      (avoidsLabel_iff_not_mem_labels.mp hfreshScheme)

/-- Helper for Lemma 77.2: formal inversion of one polygon word preserves the
unsigned-label multiset and hence properness. -/
private lemma flipProper_iff {α : Type u}
    {before after : LabellingScheme α}
    (step : LabellingScheme.Flip before after) :
    before.Proper ↔ after.Proper := by
  rcases step with ⟨word, rest⟩
  apply proper_iff_of_labels_eq
  unfold LabellingScheme.labels
  simp only [Multiset.cons_bind]
  rw [PolygonWord.formalInverse_val]
  simp only [List.map_map, List.map_reverse, Multiset.coe_reverse]
  rfl

/-- Helper for Lemma 77.2: cyclic permutation of one polygon word preserves
the unsigned-label multiset and hence properness. -/
private lemma permuteProper_iff {α : Type u}
    {before after : LabellingScheme α}
    (step : LabellingScheme.Permute before after) :
    before.Proper ↔ after.Proper := by
  rcases step with ⟨word, rotated, rest, hrotation⟩
  apply proper_iff_of_labels_eq
  unfold LabellingScheme.labels
  simp only [Multiset.cons_bind]
  have hlabels : (word.1.map Prod.fst : Multiset α) =
      (rotated.1.map Prod.fst : Multiset α) :=
    Multiset.coe_eq_coe.mpr (hrotation.perm.map Prod.fst)
  rw [hlabels]

/-- Helper for Lemma 77.2: every elementary labelling-scheme operation
preserves properness in both directions. -/
private lemma elementaryStepProper_iff {α : Type u}
    {before after : LabellingScheme α}
    (step : LabellingScheme.ElementaryStep before after) :
    before.Proper ↔ after.Proper := by
  cases step with
  | cut step => exact cutProper_iff step
  | paste step =>
      exact (cutProper_iff (LabellingScheme.paste_iff_cut.mp step)).symm
  | flip step => exact flipProper_iff step
  | permute step => exact permuteProper_iff step
  | rename a c hne hfresh =>
      exact (relabelProper_iff (PolygonWord.swapLabels a c) before).symm
  | reverse a => exact reverseLabelProper_iff before a |>.symm
  | cancel step => exact cancelProper_iff step
  | uncancel step =>
      exact (cancelProper_iff (LabellingScheme.uncancel_iff.mp step)).symm

/-- Helper for Lemma 77.2: a finite chain of elementary operations preserves
properness. -/
private lemma equivalentProper_iff {α : Type u}
    {before after : LabellingScheme α}
    (h : LabellingScheme.Equivalent before after) :
    before.Proper ↔ after.Proper := by
  unfold LabellingScheme.Equivalent at h
  induction h with
  | refl => exact Iff.rfl
  | tail h step ih =>
      -- Compose the invariant for the established prefix with the final step.
      exact ih.trans (elementaryStepProper_iff step)

/-- Helper for Lemma 77.2: duplicating every signed letter doubles the count
of each unsigned label. -/
private lemma countLabelInDuplicatedPrefix {α : Type u} [DecidableEq α]
    (pairs : List (α × Bool)) (c : α) :
    List.count c
        ((pairs.flatMap (fun letter ↦ [letter, letter])).map Prod.fst) =
      2 * List.count c (pairs.map Prod.fst) := by
  induction pairs with
  | nil => simp
  | cons letter pairs ih =>
      -- Separate the two new copies from the recursively duplicated suffix.
      simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
        List.count_append, List.count_cons, List.count_nil, ih]
      by_cases hlabel : c = letter.1
      · simp [hlabel]
        omega
      · simp
        omega

/-- Helper for Lemma 77.2: a proper duplicated-prefix presentation with a
torus-type tail is already a projective normal form. -/
private lemma projectiveNormalFormOfProperDuplicatedPrefix {α : Type u}
    (model tail : PolygonWord α) (pairs : List (α × Bool))
    (hpairs : pairs ≠ [])
    (hmodel : model.1 =
      pairs.flatMap (fun letter ↦ [letter, letter]) ++ tail.1)
    (hproper : ({model} : LabellingScheme α).Proper)
    (htorus : tail.TorusType) :
    model.ProjectiveNormalForm := by
  classical
  have hcounts : ∀ c ∈ pairs.map Prod.fst,
      List.count c (pairs.map Prod.fst) = 1 ∧
        List.count c (tail.1.map Prod.fst) = 0 := by
    intro c hc
    have hcModel : c ∈ ({model} : LabellingScheme α).labels := by
      obtain ⟨⟨label, sign⟩, hletter, rfl⟩ := List.mem_map.mp hc
      apply LabellingScheme.mem_labels_iff.mpr
      refine ⟨model, by simp, sign, ?_⟩
      rw [hmodel, List.mem_append]
      exact Or.inl (List.mem_flatMap.mpr
        ⟨(label, sign), hletter, by simp⟩)
    have hcountModel : List.count c (model.1.map Prod.fst) = 2 := by
      simpa only [LabellingScheme.labels, Multiset.singleton_bind,
        Multiset.map_coe, Multiset.coe_count] using
          (LabellingScheme.proper_iff.mp hproper c hcModel)
    rw [hmodel, List.map_append, List.count_append,
      countLabelInDuplicatedPrefix] at hcountModel
    have hpositive : 0 < List.count c (pairs.map Prod.fst) :=
      List.count_pos_iff.mpr hc
    omega
  rw [PolygonWord.projectiveNormalForm_iff]
  refine ⟨pairs, hpairs, tail.1, ⟨hmodel, ?_, ?_⟩,
    Or.inr ((PolygonWord.torusResidual_iff_torusType tail.property).mpr htorus)⟩
  · -- Count one for every occurring prefix label is exactly pairwise distinctness.
    exact List.nodup_iff_count_eq_one.mpr fun c hc ↦ (hcounts c hc).1
  · intro letter hletter tailLetter htailLetter hequal
    have hprefix : letter.1 ∈ pairs.map Prod.fst :=
      List.mem_map.mpr ⟨letter, hletter, rfl⟩
    have hzero := (hcounts letter.1 hprefix).2
    have htail : letter.1 ∈ tail.1.map Prod.fst :=
      List.mem_map.mpr ⟨tailLetter, htailLetter, hequal.symm⟩
    rw [← List.count_pos_iff] at htail
    omega

/-- Lemma 77.2: A proper polygon word of length greater than four that is either of torus
type or equivalent to a nonempty duplicated-pair prefix with a torus-type tail can be
cyclically permuted and cancelled to a word shorter by two that is of torus type or
equivalent to a projective normal form. -/
theorem existsCancelToClassificationForm {α : Type u}
    (word : PolygonWord α) (hproper : ({word} : LabellingScheme α).Proper)
    (hlength : 4 < word.1.length)
    (hclassification : word.TorusType ∨
      ∃ pairs : List (α × Bool), pairs ≠ [] ∧
        ∃ tail model : PolygonWord α,
          model.1 = pairs.flatMap (fun letter ↦ [letter, letter]) ++ tail.1 ∧
            LabellingScheme.Equivalent ({word} : LabellingScheme α) {model} ∧
              tail.TorusType)
    (hadjacent : ¬ Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.1) :
    ∃ rotated shorter : PolygonWord α,
      LabellingScheme.Permute ({word} : LabellingScheme α) {rotated} ∧
        LabellingScheme.Cancel ({rotated} : LabellingScheme α) {shorter} ∧
          shorter.1.length + 2 = word.1.length ∧
            (shorter.TorusType ∨
              ∃ normalized : PolygonWord α,
                LabellingScheme.Equivalent
                    ({shorter} : LabellingScheme α) {normalized} ∧
                  normalized.ProjectiveNormalForm) := by
  obtain ⟨y₀, y₁, a, b, hy₀Length, hy₁Length, hrotation,
    hy₀Fresh, hy₁Fresh⟩ :=
    existsRotatedCancelPair word hproper hlength hadjacent
  let rotated : PolygonWord α :=
    ⟨y₀ ++ [(a, b), (a, !b)] ++ y₁,
      PolygonWord.insertCancelPair_length y₀ y₁ a b hy₀Length⟩
  let shorter : PolygonWord α :=
    ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩
  -- Package the cyclic rotation and the exposed inverse-pair deletion as the
  -- two elementary operations asserted by the conclusion.
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
  have hshorterLength : shorter.1.length + 2 = word.1.length := by
    have hrotationLength := hrotation.perm.length_eq
    simp only [shorter, List.length_append]
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hrotationLength
    omega
  refine ⟨rotated, shorter, hpermute, hcancel, hshorterLength, ?_⟩
  rcases hclassification with htorus | ⟨pairs, hpairs, tail, model,
    hmodel, hequivalent, htail⟩
  · -- In the orientable branch the opposite pair contributes one occurrence
    -- of each sign, so deleting it leaves all residual signed counts equal to one.
    exact Or.inl (TorusType.ofRotatedCancelPair word y₀ y₁ a b
      hy₀Length hy₁Length hrotation hy₀Fresh hy₁Fresh htorus)
  · -- In the projective branch transport properness to the supplied model;
    -- its duplicated prefix is then distinct and disjoint from the torus tail.
    have hmodelProper : ({model} : LabellingScheme α).Proper :=
      (equivalentProper_iff hequivalent).mp hproper
    have hnormal : model.ProjectiveNormalForm :=
      projectiveNormalFormOfProperDuplicatedPrefix model tail pairs hpairs
        hmodel hmodelProper htail
    have hshorterModel : LabellingScheme.Equivalent
        ({shorter} : LabellingScheme α) {model} := by
      exact LabellingScheme.Equivalent.trans
        (LabellingScheme.Equivalent.ofElementary
          (LabellingScheme.ElementaryStep.cancel hcancel)).symm
        (LabellingScheme.Equivalent.trans
          (LabellingScheme.Equivalent.ofElementary
            (LabellingScheme.ElementaryStep.permute hpermute)).symm
          hequivalent)
    exact Or.inr ⟨model, hshorterModel, hnormal⟩

end PolygonWord
