module

public import Topology_Munkres_2000.Book.Definition_76_10.Equivalence
public import Topology_Munkres_2000.Book.Definition_77_2.OrientationType
public import Mathlib.Data.Finite.Defs
import all Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Definition_76_6.Relabel
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find

public section

universe u

namespace PolygonWord

/-- A torus-handle form consists of two distinct handle labels followed by a residual
signed word that is either empty or of torus type.  Its handle and residual together
have the prescribed suffix length. -/
structure TorusHandleForm {α : Type u} (normalized : PolygonWord α)
    (initial : List (α × Bool)) (suffixLength : ℕ) where
  firstLabel : α
  secondLabel : α
  tail : List (α × Bool)
  labels_ne : firstLabel ≠ secondLabel
  word_eq :
    normalized.1 =
      initial ++ [(firstLabel, true), (secondLabel, true),
        (firstLabel, false), (secondLabel, false)] ++ tail
  length_eq :
    ([(firstLabel, true), (secondLabel, true),
      (firstLabel, false), (secondLabel, false)] ++ tail).length = suffixLength
  tail_torus_or_empty :
    tail = [] ∨
      ∀ c ∈ tail.map Prod.fst,
        ∃ rest : Multiset (α × Bool),
          (tail : Multiset (α × Bool)) =
              (c, true) ::ₘ (c, false) ::ₘ rest ∧
            ∀ sign : Bool, (c, sign) ∉ rest

/-- Construct a torus-handle form from its two handle labels and residual signed word. -/
def TorusHandleForm.ofWords {α : Type u} {normalized : PolygonWord α}
    {initial : List (α × Bool)} {suffixLength : ℕ}
    (firstLabel secondLabel : α) (tail : List (α × Bool))
    (labels_ne : firstLabel ≠ secondLabel)
    (word_eq :
      normalized.1 =
        initial ++ [(firstLabel, true), (secondLabel, true),
          (firstLabel, false), (secondLabel, false)] ++ tail)
    (length_eq :
      ([(firstLabel, true), (secondLabel, true),
        (firstLabel, false), (secondLabel, false)] ++ tail).length = suffixLength)
    (tail_torus_or_empty :
      tail = [] ∨
        ∀ c ∈ tail.map Prod.fst,
          ∃ rest : Multiset (α × Bool),
            (tail : Multiset (α × Bool)) =
                (c, true) ::ₘ (c, false) ::ₘ rest ∧
              ∀ sign : Bool, (c, sign) ∉ rest) :
    TorusHandleForm normalized initial suffixLength :=
  { firstLabel := firstLabel
    secondLabel := secondLabel
    tail := tail
    labels_ne := labels_ne
    word_eq := word_eq
    length_eq := length_eq
    tail_torus_or_empty := tail_torus_or_empty }

/-- Helper for Lemma 77.3: forgetting the sign counts the two Boolean sign fibers. -/
private lemma count_map_fst_eq_signedCounts {α : Type u} [DecidableEq α]
    (letters : List (α × Bool)) (c : α) :
    Multiset.count c (letters.map Prod.fst : Multiset α) =
      Multiset.count (c, false) (letters : Multiset (α × Bool)) +
        Multiset.count (c, true) (letters : Multiset (α × Bool)) := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      obtain ⟨d, sign⟩ := letter
      have hlabelsCons :
          ((((d, sign) :: letters).map Prod.fst : List α) : Multiset α) =
            d ::ₘ (letters.map Prod.fst : Multiset α) := by
        rfl
      have hlettersCons :
          (((d, sign) :: letters : List (α × Bool)) : Multiset (α × Bool)) =
            (d, sign) ::ₘ (letters : Multiset (α × Bool)) := by
        rfl
      have htrueFalse : (c, true) ≠ (c, false) := by simp
      have hfalseTrue : (c, false) ≠ (c, true) := by simp
      by_cases hdc : d = c
      · subst d
        cases sign
        · rw [hlabelsCons, hlettersCons, Multiset.count_cons_self,
            Multiset.count_cons_self,
            Multiset.count_cons_of_ne htrueFalse]
          omega
        · rw [hlabelsCons, hlettersCons, Multiset.count_cons_self,
            Multiset.count_cons_of_ne hfalseTrue,
            Multiset.count_cons_self]
          omega
      · have hcd : c ≠ d := Ne.symm hdc
        have hfalse : (c, false) ≠ (d, sign) := by
          intro hpair
          exact hdc (congrArg Prod.fst hpair).symm
        have htrue : (c, true) ≠ (d, sign) := by
          intro hpair
          exact hdc (congrArg Prod.fst hpair).symm
        rw [hlabelsCons, hlettersCons,
          Multiset.count_cons_of_ne hcd,
          Multiset.count_cons_of_ne hfalse,
          Multiset.count_cons_of_ne htrue]
        exact ih

/-- Helper for Lemma 77.3: signed multiplicity one splits a multiset into the
two signs of a label and a residual multiset avoiding that label. -/
private lemma signedPairDecomposition_of_count {α : Type u} [DecidableEq α]
    {letters : Multiset (α × Bool)} {c : α}
    (hcount : ∀ sign : Bool, Multiset.count (c, sign) letters = 1) :
    ∃ rest : Multiset (α × Bool),
      letters = (c, true) ::ₘ (c, false) ::ₘ rest ∧
        ∀ sign : Bool, (c, sign) ∉ rest := by
  have hpositive : (c, true) ∈ letters := by
    rw [← Multiset.count_pos, hcount true]
    decide
  have hnegative : (c, false) ∈ letters := by
    rw [← Multiset.count_pos, hcount false]
    decide
  have hfalseTrue : (c, false) ≠ (c, true) := by simp
  have htrueFalse : (c, true) ≠ (c, false) := by simp
  have hnegativeAfter : (c, false) ∈ letters.erase (c, true) :=
    (Multiset.mem_erase_of_ne hfalseTrue).mpr hnegative
  refine ⟨(letters.erase (c, true)).erase (c, false), ?_, ?_⟩
  · -- Remove the two unique signed occurrences in their displayed order.
    calc
      letters = (c, true) ::ₘ letters.erase (c, true) :=
        (Multiset.cons_erase hpositive).symm
      _ = (c, true) ::ₘ (c, false) ::ₘ
          (letters.erase (c, true)).erase (c, false) :=
        congrArg (Multiset.cons (c, true))
          (Multiset.cons_erase hnegativeAfter).symm
  · intro sign
    -- Erasing the sole occurrence leaves signed count zero.
    rw [← Multiset.count_eq_zero]
    cases sign
    · rw [Multiset.count_erase_self, Multiset.count_erase_of_ne hfalseTrue,
        hcount false]
    · rw [Multiset.count_erase_of_ne htrueFalse, Multiset.count_erase_self,
        hcount true]

/-- Helper for Lemma 77.3: properness keeps every label of the torus suffix
out of the fixed initial fragment. -/
private lemma properPrefixAvoidsTorusLabels {α : Type u}
    (word suffix : PolygonWord α) (initial : List (α × Bool))
    (hproper : ({word} : LabellingScheme α).Proper)
    (hdecomp : word.1 = initial ++ suffix.1) (htorus : suffix.TorusType) :
    ∀ c ∈ suffix.1.map Prod.fst, ∀ letter ∈ initial, letter.1 ≠ c := by
  classical
  have hproperCount := LabellingScheme.proper_iff.mp hproper
  have htorusCount := PolygonWord.torusType_iff_count.mp htorus
  -- Compare unsigned multiplicities in the whole word and in its suffix.
  intro c hc letter hletter hlabel
  subst c
  have hsuffixLabel : letter.1 ∈ ({suffix} : LabellingScheme α).labels := by
    rw [LabellingScheme.mem_labels_iff]
    obtain ⟨signed, hsigned, hsignedLabel⟩ := List.mem_map.mp hc
    obtain ⟨label, sign⟩ := signed
    simp only at hsignedLabel
    subst label
    have hsuffixMem : suffix ∈ ({suffix} : LabellingScheme α) := by simp
    exact ⟨suffix, hsuffixMem, sign, hsigned⟩
  have hwordLabel : letter.1 ∈ ({word} : LabellingScheme α).labels := by
    rw [LabellingScheme.mem_labels_iff]
    have hwordMem : word ∈ ({word} : LabellingScheme α) := by simp
    have hletterWord : letter ∈ word.1 := by
      rw [hdecomp]
      simp [hletter]
    exact ⟨word, hwordMem, letter.2, hletterWord⟩
  have hwordCount := hproperCount letter.1 hwordLabel
  have hsuffixFalse := htorusCount letter.1 hsuffixLabel false
  have hsuffixTrue := htorusCount letter.1 hsuffixLabel true
  have hsuffixUnsigned :
      Multiset.count letter.1 (suffix.1.map Prod.fst : Multiset α) = 2 := by
    rw [count_map_fst_eq_signedCounts]
    omega
  have hinitialPositive :
      0 < Multiset.count letter.1 (initial.map Prod.fst : Multiset α) := by
    rw [Multiset.count_pos]
    exact List.mem_map.mpr ⟨letter, hletter, rfl⟩
  have hwordUnsigned :
      Multiset.count letter.1 (word.1.map Prod.fst : Multiset α) = 2 := by
    simpa [LabellingScheme.labels] using hwordCount
  rw [Multiset.coe_count] at hinitialPositive hsuffixUnsigned hwordUnsigned
  rw [hdecomp, List.map_append, List.count_append, hsuffixUnsigned] at hwordUnsigned
  omega

/-- Helper for Lemma 77.3: the four displayed letters exhaust both labels in
an interlaced signed-count decomposition. -/
private lemma interlacedFragmentsAvoidLabels {α : Type u} [DecidableEq α]
    (letters : List (α × Bool)) (a b : α) (sa sb : Bool)
    (y₁ y₂ y₃ y₄ y₅ : List (α × Bool))
    (hcount : ∀ c ∈ letters.map Prod.fst,
      ∀ sign : Bool,
        Multiset.count (c, sign) (letters : Multiset (α × Bool)) = 1)
    (hab : a ≠ b)
    (hdecomp : letters = y₁ ++ [(a, sa)] ++ y₂ ++ [(b, sb)] ++ y₃ ++
      [(a, !sa)] ++ y₄ ++ [(b, !sb)] ++ y₅) :
    (∀ letter ∈ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ a) ∧
      ∀ letter ∈ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ b := by
  have haMem : a ∈ letters.map Prod.fst := by
    rw [hdecomp]
    simp
  have hbMem : b ∈ letters.map Prod.fst := by
    rw [hdecomp]
    simp
  have haUnsigned :
      Multiset.count a (letters.map Prod.fst : Multiset α) = 2 := by
    rw [count_map_fst_eq_signedCounts]
    have haFalse := hcount a haMem false
    have haTrue := hcount a haMem true
    omega
  have hbUnsigned :
      Multiset.count b (letters.map Prod.fst : Multiset α) = 2 := by
    rw [count_map_fst_eq_signedCounts]
    have hbFalse := hcount b hbMem false
    have hbTrue := hcount b hbMem true
    omega
  rw [Multiset.coe_count] at haUnsigned hbUnsigned
  rw [hdecomp] at haUnsigned hbUnsigned
  have hba : b ≠ a := Ne.symm hab
  simp only [List.map_append, List.map_cons, List.map_nil, List.count_append,
    List.count_cons, List.count_nil, beq_iff_eq] at haUnsigned hbUnsigned
  simp only [hab, hba, ↓reduceIte] at haUnsigned hbUnsigned
  have haResidual :
      ((y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅).map Prod.fst).count a = 0 := by
    simp only [List.map_append, List.count_append]
    omega
  have hbResidual :
      ((y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅).map Prod.fst).count b = 0 := by
    simp only [List.map_append, List.count_append]
    omega
  constructor
  · intro letter hletter hlabel
    apply List.not_mem_of_count_eq_zero haResidual
    rw [← hlabel]
    exact List.mem_map.mpr ⟨letter, hletter, rfl⟩
  · intro letter hletter hlabel
    apply List.not_mem_of_count_eq_zero hbResidual
    rw [← hlabel]
    exact List.mem_map.mpr ⟨letter, hletter, rfl⟩

/-- Helper for Lemma 77.3: a paired signed word with no equal adjacent labels
contains two oppositely signed label pairs whose occurrences interlace. -/
private lemma existsInterlacedOppositePairs {α : Type u} [DecidableEq α]
    (letters : List (α × Bool)) (hnonempty : letters ≠ [])
    (hcount : ∀ c ∈ letters.map Prod.fst,
      ∀ sign : Bool,
        Multiset.count (c, sign) (letters : Multiset (α × Bool)) = 1)
    (hadjacent : letters.IsChain (fun x y : α × Bool ↦ x.1 ≠ y.1)) :
    ∃ a b : α, ∃ sa sb : Bool,
      ∃ y₁ y₂ y₃ y₄ y₅ : List (α × Bool),
        a ≠ b ∧
          (∀ letter ∈ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ a) ∧
          (∀ letter ∈ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ b) ∧
            letters = y₁ ++ [(a, sa)] ++ y₂ ++ [(b, sb)] ++ y₃ ++
              [(a, !sa)] ++ y₄ ++ [(b, !sb)] ++ y₅ := by
  -- Minimize the interval between paired occurrences, as in the source proof.
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ a : α, ∃ sa sj : Bool, ∃ y₁ middle y₅ : List (α × Bool),
      letters = y₁ ++ [(a, sa)] ++ middle ++ [(a, sj)] ++ y₅ ∧
        middle.length = n
  have hP : ∃ n, P n := by
    -- The mate of the first letter supplies at least one paired interval.
    obtain ⟨head, rest, hletters⟩ := List.exists_cons_of_ne_nil hnonempty
    obtain ⟨a, sa⟩ := head
    have haMem : a ∈ letters.map Prod.fst := by
      rw [hletters]
      simp
    have hmateCount := hcount a haMem (!sa)
    have hmateLetters : (a, !sa) ∈ letters := by
      rw [← Multiset.mem_coe, ← Multiset.count_pos, hmateCount]
      decide
    have hmateRest : (a, !sa) ∈ rest := by
      rw [hletters] at hmateLetters
      cases sa <;> simpa using hmateLetters
    rw [List.mem_iff_append] at hmateRest
    obtain ⟨middle, after, hrest⟩ := hmateRest
    refine ⟨middle.length, a, sa, !sa, [], middle, after, ?_, rfl⟩
    rw [hletters, hrest]
    simp
  obtain ⟨a, sa, sj, y₁, middle, y₅, hdecomp, hmiddleLength⟩ :=
    Nat.find_spec hP
  have haMem : a ∈ letters.map Prod.fst := by
    rw [hdecomp]
    simp
  have hsj : sj = !sa := by
    cases sa <;> cases sj
    · have htwo := hcount a haMem false
      rw [hdecomp] at htwo
      simp [Multiset.coe_count, List.count_append] at htwo
      omega
    · rfl
    · rfl
    · have htwo := hcount a haMem true
      rw [hdecomp] at htwo
      simp [Multiset.coe_count, List.count_append] at htwo
      omega
  have hmiddle : middle ≠ [] := by
    intro hempty
    have hall := List.isChain_iff_forall_rel_of_append_cons_cons.mp hadjacent
    have hadjacentEq : letters = y₁ ++ (a, sa) :: (a, sj) :: y₅ := by
      simpa [hempty, List.append_assoc] using hdecomp
    have hadj : a ≠ a := hall hadjacentEq
    exact hadj rfl
  obtain ⟨first, middleTail, hmiddleEq⟩ := List.exists_cons_of_ne_nil hmiddle
  obtain ⟨b, sb⟩ := first
  rw [hmiddleEq] at hdecomp hmiddleLength
  have hab : a ≠ b := by
    -- The first interior letter is adjacent to the first endpoint.
    have hall := List.isChain_iff_forall_rel_of_append_cons_cons.mp hadjacent
    have hadjacentEq : letters =
        y₁ ++ (a, sa) :: (b, sb) :: (middleTail ++ [(a, sj)] ++ y₅) := by
      simpa [List.append_assoc] using hdecomp
    exact hall hadjacentEq
  have hbMem : b ∈ letters.map Prod.fst := by
    rw [hdecomp]
    simp
  have hmateCount := hcount b hbMem (!sb)
  have hmateLetters : (b, !sb) ∈ letters := by
    rw [← Multiset.mem_coe, ← Multiset.count_pos, hmateCount]
    decide
  have hnotFirstA : (b, !sb) ≠ (a, sa) := by
    intro hpair
    exact hab (congrArg Prod.fst hpair).symm
  have hnotSecondA : (b, !sb) ≠ (a, sj) := by
    intro hpair
    exact hab (congrArg Prod.fst hpair).symm
  have hnotB : (b, !sb) ≠ (b, sb) := by
    cases sb <;> simp
  have hmateCases :
      (b, !sb) ∈ y₁ ∨ (b, !sb) ∈ middleTail ∨ (b, !sb) ∈ y₅ := by
    rw [hdecomp] at hmateLetters
    simpa [List.mem_append, hnotFirstA, hnotSecondA, hnotB] using hmateLetters
  rcases hmateCases with hbefore | hinside | hafter
  · rw [List.mem_iff_append] at hbefore
    obtain ⟨z₁, z₂, hy₁⟩ := hbefore
    have hout : letters =
        z₁ ++ [(b, !sb)] ++ z₂ ++ [(a, sa)] ++ [] ++ [(b, !(!sb))] ++
          middleTail ++ [(a, !sa)] ++ y₅ := by
      rw [hdecomp, hy₁, hsj]
      simp [List.append_assoc]
    have hfresh := interlacedFragmentsAvoidLabels letters b a (!sb) sa
      z₁ z₂ [] middleTail y₅ hcount (Ne.symm hab) hout
    exact ⟨b, a, !sb, sa, z₁, z₂, [], middleTail, y₅,
      Ne.symm hab, hfresh.1, hfresh.2, hout⟩
  · rw [List.mem_iff_append] at hinside
    obtain ⟨z₁, z₂, hmiddleTail⟩ := hinside
    have hsmaller : P z₁.length := by
      refine ⟨b, sb, !sb, y₁ ++ [(a, sa)], z₁,
        z₂ ++ [(a, sj)] ++ y₅, ?_, rfl⟩
      rw [hdecomp, hmiddleTail]
      simp [List.append_assoc]
    -- An interior mate would contradict minimality of the chosen interval.
    have hminimal : Nat.find hP ≤ z₁.length := Nat.find_min' hP hsmaller
    have hstrict : z₁.length < Nat.find hP := by
      rw [← hmiddleLength, hmiddleTail]
      simp
      omega
    exact (Nat.not_lt_of_ge hminimal hstrict).elim
  · rw [List.mem_iff_append] at hafter
    obtain ⟨z₄, z₅, hy₅⟩ := hafter
    have hout : letters =
        y₁ ++ [(a, sa)] ++ [] ++ [(b, sb)] ++ middleTail ++
          [(a, !sa)] ++ z₄ ++ [(b, !sb)] ++ z₅ := by
      rw [hdecomp, hy₅, hsj]
      simp [List.append_assoc]
    have hfresh := interlacedFragmentsAvoidLabels letters a b sa sb
      y₁ [] middleTail z₄ z₅ hcount hab hout
    exact ⟨a, b, sa, sb, y₁, [], middleTail, z₄, z₅,
      hab, hfresh.1, hfresh.2, hout⟩

/-- Helper for Lemma 77.3: deleting an interlaced pair and permuting the five
residual fragments leaves either no letters or another torus-type signed multiset. -/
private lemma interlacedResidualTorusOrEmpty {α : Type u} [DecidableEq α]
    (letters : List (α × Bool)) (a b : α) (sa sb : Bool)
    (y₁ y₂ y₃ y₄ y₅ : List (α × Bool))
    (hcount : ∀ c ∈ letters.map Prod.fst,
      ∀ sign : Bool,
        Multiset.count (c, sign) (letters : Multiset (α × Bool)) = 1)
    (havoidA : ∀ letter ∈ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ a)
    (havoidB : ∀ letter ∈ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ b)
    (hdecomp : letters = y₁ ++ [(a, sa)] ++ y₂ ++ [(b, sb)] ++ y₃ ++
      [(a, !sa)] ++ y₄ ++ [(b, !sb)] ++ y₅) :
    let tail := y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅
    tail = [] ∨
      ∀ c ∈ tail.map Prod.fst,
        ∃ rest : Multiset (α × Bool),
          (tail : Multiset (α × Bool)) =
              (c, true) ::ₘ (c, false) ::ₘ rest ∧
            ∀ sign : Bool, (c, sign) ∉ rest := by
  classical
  dsimp only
  by_cases htail : y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅ = []
  · exact Or.inl htail
  · refine Or.inr ?_
    intro c hc
    obtain ⟨letter, hletter, hletterLabel⟩ := List.mem_map.mp hc
    have hletterResidual : letter ∈ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅ := by
      simp only [List.mem_append] at hletter ⊢
      rcases hletter with (((hy₁ | hy₄) | hy₃) | hy₂) | hy₅
      · exact Or.inl (Or.inl (Or.inl (Or.inl hy₁)))
      · exact Or.inl (Or.inr hy₄)
      · exact Or.inl (Or.inl (Or.inr hy₃))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hy₂)))
      · exact Or.inr hy₅
    have hca : c ≠ a := by
      rw [← hletterLabel]
      exact havoidA letter hletterResidual
    have hcb : c ≠ b := by
      rw [← hletterLabel]
      exact havoidB letter hletterResidual
    have hac : a ≠ c := Ne.symm hca
    have hbc : b ≠ c := Ne.symm hcb
    have hcLetters : c ∈ letters.map Prod.fst := by
      rw [hdecomp]
      apply List.mem_map.mpr
      refine ⟨letter, ?_, hletterLabel⟩
      simp only [List.mem_append] at hletterResidual
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      aesop
    have htailCount : ∀ sign : Bool,
        Multiset.count (c, sign)
          (y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅ : List (α × Bool)) = 1 := by
      intro sign
      have hcCount := hcount c hcLetters sign
      rw [hdecomp] at hcCount
      simp [Multiset.coe_count, hac, hbc] at hcCount
      simp only [Multiset.coe_count, List.count_append]
      omega
    apply signedPairDecomposition_of_count
    intro sign
    exact htailCount sign

/-- Helper for Lemma 77.3: an infinite label type supplies a label avoided by a
finite labelling scheme. -/
private lemma existsAvoidedLabel {α : Type u} [Infinite α]
    (scheme : LabellingScheme α) : ∃ c, scheme.AvoidsLabel c := by
  classical
  -- Choose outside the finite unsigned support, then translate support membership.
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset scheme.labels.toFinset
  refine ⟨c, ?_⟩
  rw [LabellingScheme.avoidsLabel_iff]
  intro word hword letter hletter heq
  subst heq
  apply hc
  rw [Multiset.mem_toFinset, LabellingScheme.mem_labels_iff]
  exact ⟨word, hword, letter.2, hletter⟩

/-- Helper for Lemma 77.3: swapping two labels fixes a signed-letter list that
avoids both labels. -/
private lemma mapSwapLabels_eq_self_of_avoids {α : Type u}
    (letters : List (α × Bool)) (a c : α)
    (ha : ∀ letter ∈ letters, letter.1 ≠ a)
    (hc : ∀ letter ∈ letters, letter.1 ≠ c) :
    letters.map (fun letter ↦ (swapLabels a c letter.1, letter.2)) = letters := by
  classical
  -- The transposition fixes every letter pointwise away from its endpoints.
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head ∈ head :: tail := List.mem_cons_self
      have htailA : ∀ letter ∈ tail, letter.1 ≠ a := by
        intro letter hletter
        exact ha letter (List.mem_cons_of_mem head hletter)
      have htailC : ∀ letter ∈ tail, letter.1 ≠ c := by
        intro letter hletter
        exact hc letter (List.mem_cons_of_mem head hletter)
      rw [List.map_cons, ih htailA htailC]
      have hswap : swapLabels a c head.1 = head.1 :=
        Equiv.swap_apply_of_ne_of_ne (ha head hhead) (hc head hhead)
      rw [hswap]

/-- Helper for Lemma 77.3: reversing a label fixes every signed letter whose
unsigned label is different. -/
private lemma mapReverseSignAt_eq_self_of_avoids {α : Type u}
    (letters : List (α × Bool)) (a : α)
    (ha : ∀ letter ∈ letters, letter.1 ≠ a) :
    letters.map (reverseSignAt a) = letters := by
  classical
  -- The conditional reversal takes its unchanged branch at every letter.
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head ∈ head :: tail := List.mem_cons_self
      have htail : ∀ letter ∈ tail, letter.1 ≠ a := by
        intro letter hletter
        exact ha letter (List.mem_cons_of_mem head hletter)
      rw [List.map_cons, ih htail]
      simp only [reverseSignAt, if_neg (ha head hhead)]

/-- Helper for Lemma 77.3: the cut-and-paste exchange preserves the minimum
polygon-word length. -/
private lemma cutPasteReorder_length {α : Type u} (word : PolygonWord α)
    (w x y z t : List (α × Bool)) (p c : α)
    (hdecomp : word.1 =
      w ++ x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t) :
    3 ≤ (w ++ [(c, true)] ++ z ++ y ++ [(c, false)] ++ x ++ t).length := by
  -- Only the order of the residual fragments and the names of two edges change.
  have hlength := word.property
  rw [hdecomp] at hlength
  simp only [List.length_append, List.length_cons, List.length_nil] at hlength ⊢
  omega

/-- Helper for Lemma 77.3: cutting at a fresh label and pasting along an
oppositely signed pair exchanges the two intervening fragments. -/
private lemma equivalentCutPasteReorder {α : Type u} (word : PolygonWord α)
    (w x y z t : List (α × Bool)) (p c : α)
    (hdecomp : word.1 =
      w ++ x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t)
    (hc : ({word} : LabellingScheme α).AvoidsLabel c)
    (hp : ∀ letter ∈ w ++ x ++ y ++ z ++ t, letter.1 ≠ p)
    (hleft : 2 ≤ (x ++ [(p, true)] ++ y).length)
    (hright : 2 ≤ (z ++ [(p, false)] ++ t ++ w).length) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({⟨w ++ [(c, true)] ++ z ++ y ++ [(c, false)] ++ x ++ t,
        cutPasteReorder_length word w x y z t p c hdecomp⟩} :
        LabellingScheme α) := by
  classical
  let left := x ++ [(p, true)] ++ y
  let right := z ++ [(p, false)] ++ t ++ w
  have hwordMem : word ∈ ({word} : LabellingScheme α) := by simp
  have hcWord : ∀ letter ∈ word.1, letter.1 ≠ c := by
    rw [LabellingScheme.avoidsLabel_iff] at hc
    exact hc word hwordMem
  have hpNeC : p ≠ c := by
    apply hcWord (p, true)
    rw [hdecomp]
    simp
  have hcNeP : c ≠ p := Ne.symm hpNeC
  have hleftFreshC : ∀ letter ∈ left, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [hdecomp]
    simp only [left, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hletter ⊢
    aesop
  have hrightFreshC : ∀ letter ∈ right, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [hdecomp]
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
  have hleftLength : 2 ≤ left.length := by
    simpa only [left] using hleft
  have hrightLength : 2 ≤ right.length := by
    simpa only [right] using hright
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
    · simpa only [hcLetter, Prod.fst] using hcNeP
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
    · simpa only [hcLetter, Prod.fst] using hcNeP
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
      cutPasteReorder_length word w x y z t p c hdecomp⟩
  have hsourceRotation : List.IsRotated word.val rotated.val := by
    have hrotation := List.isRotated_append
      (l := w) (l' := x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t)
    simpa only [rotated, left, right, hdecomp, List.append_assoc] using hrotation
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
      (l := y ++ [(c, false)] ++ x ++ t) (l' := w ++ [(c, true)] ++ z)
    simpa only [pasted, target, List.append_assoc] using hrotation
  -- Compose the source rotation, cut, two component rotations, paste, and target rotation.
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
      simpa [firstPasted, secondPasted, pasted, List.append_assoc] using
        hpasteConstruction
    exact LabellingScheme.Equivalent.ofElementary (.paste hpasteStep)
  have hrotateTarget :
      LabellingScheme.Equivalent ({pasted} : LabellingScheme α) {target} := by
    exact LabellingScheme.Equivalent.ofElementary (.permute
      (.of pasted target 0 htargetRotation))
  exact hrotateSource.trans (hcut.trans
    (hrotateCut.trans (hpaste.trans hrotateTarget)))

/-- Helper for Lemma 77.3: the cut-and-paste exchange can be renamed back from
its fresh cut label and identified with any prescribed rearranged target. -/
private lemma equivalentPairExchangeTo {α : Type u}
    (word target : PolygonWord α) (w x y z t : List (α × Bool)) (p c : α)
    (hdecomp : word.1 =
      w ++ x ++ [(p, true)] ++ y ++ z ++ [(p, false)] ++ t)
    (htarget : target.1 =
      w ++ [(p, true)] ++ z ++ y ++ [(p, false)] ++ x ++ t)
    (hc : ({word} : LabellingScheme α).AvoidsLabel c)
    (hp : ∀ letter ∈ w ++ x ++ y ++ z ++ t, letter.1 ≠ p)
    (hleft : 2 ≤ (x ++ [(p, true)] ++ y).length)
    (hright : 2 ≤ (z ++ [(p, false)] ++ t ++ w).length) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({target} : LabellingScheme α) := by
  classical
  let freshTarget : PolygonWord α :=
    ⟨w ++ [(c, true)] ++ z ++ y ++ [(c, false)] ++ x ++ t,
      cutPasteReorder_length word w x y z t p c hdecomp⟩
  have hcutPaste :
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {freshTarget} := by
    simpa only [freshTarget] using
      equivalentCutPasteReorder word w x y z t p c hdecomp hc hp hleft hright
  have hwordMem : word ∈ ({word} : LabellingScheme α) := by simp
  have hcWord : ∀ letter ∈ word.1, letter.1 ≠ c := by
    rw [LabellingScheme.avoidsLabel_iff] at hc
    exact hc word hwordMem
  have hpNeC : p ≠ c := by
    apply hcWord (p, true)
    rw [hdecomp]
    simp
  have hcNeP : c ≠ p := Ne.symm hpNeC
  have hcResidual : ∀ letter ∈ w ++ x ++ y ++ z ++ t, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [hdecomp]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hletter ⊢
    aesop
  have hfreshAvoidsP : ({freshTarget} : LabellingScheme α).AvoidsLabel p := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro candidate hcandidate letter hletter
    simp only [Multiset.mem_singleton] at hcandidate
    subst candidate
    simp only [freshTarget, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hletter
    rcases hletter with (((((hw | hcFirst) | hz) | hy) | hcSecond) | hx) | ht
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · simpa only [hcFirst, Prod.fst] using hcNeP
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · simpa only [hcSecond, Prod.fst] using hcNeP
    · apply hp letter
      simp only [List.mem_append]
      aesop
    · apply hp letter
      simp only [List.mem_append]
      aesop
  -- Normalize every residual fragment through one parameterized swap fact.
  have hfix (letters : List (α × Bool))
      (hmem : ∀ letter ∈ letters, letter ∈ w ++ x ++ y ++ z ++ t) :
      letters.map (fun letter ↦ (swapLabels c p letter.1, letter.2)) = letters := by
    apply mapSwapLabels_eq_self_of_avoids letters c p
    · intro letter hletter
      exact hcResidual letter (hmem letter hletter)
    · intro letter hletter
      exact hp letter (hmem letter hletter)
  have hwMem : ∀ letter ∈ w, letter ∈ w ++ x ++ y ++ z ++ t := by
    intro letter hletter
    simp only [List.mem_append]
    aesop
  have hxMem : ∀ letter ∈ x, letter ∈ w ++ x ++ y ++ z ++ t := by
    intro letter hletter
    simp only [List.mem_append]
    aesop
  have hyMem : ∀ letter ∈ y, letter ∈ w ++ x ++ y ++ z ++ t := by
    intro letter hletter
    simp only [List.mem_append]
    aesop
  have hzMem : ∀ letter ∈ z, letter ∈ w ++ x ++ y ++ z ++ t := by
    intro letter hletter
    simp only [List.mem_append]
    aesop
  have htMem : ∀ letter ∈ t, letter ∈ w ++ x ++ y ++ z ++ t := by
    intro letter hletter
    simp only [List.mem_append]
    aesop
  have hrenameVal :
      freshTarget.1.map
          (fun letter ↦ (swapLabels c p letter.1, letter.2)) = target.1 := by
    simp only [freshTarget, List.map_append, List.map_cons, List.map_nil]
    rw [hfix w hwMem, hfix x hxMem, hfix y hyMem, hfix z hzMem, hfix t htMem]
    simp only [swapLabels, Equiv.swap_apply_left]
    exact htarget.symm
  have hrenameWord : freshTarget.relabel (swapLabels c p) = target := by
    apply Subtype.ext
    simpa only [PolygonWord.relabel_val] using hrenameVal
  have hrenameScheme :
      ({freshTarget} : LabellingScheme α).renameLabel c p =
        ({target} : LabellingScheme α) := by
    unfold LabellingScheme.renameLabel LabellingScheme.relabel
    simp only [Multiset.map_singleton, hrenameWord]
  have hrename :
      LabellingScheme.Equivalent ({freshTarget} : LabellingScheme α) {target} := by
    have hstep := LabellingScheme.Equivalent.ofElementary
      (.rename ({freshTarget} : LabellingScheme α) c p hcNeP hfreshAvoidsP)
    rwa [hrenameScheme] at hstep
  exact hcutPaste.trans hrename

/-- Helper for Lemma 77.3: concatenating two signed-letter fragments that avoid
a label produces another fragment avoiding that label. -/
private lemma forallFstNe_append {α : Type u} (left right : List (α × Bool)) (a : α)
    (hleft : ∀ letter ∈ left, letter.1 ≠ a)
    (hright : ∀ letter ∈ right, letter.1 ≠ a) :
    ∀ letter ∈ left ++ right, letter.1 ≠ a := by
  -- Split membership in the concatenation and use the corresponding hypothesis.
  intro letter hletter
  rw [List.mem_append] at hletter
  exact hletter.elim (hleft letter) (hright letter)

/-- Helper for Lemma 77.3: a singleton signed letter avoids every distinct
unsigned label. -/
private lemma forallFstNe_singleton {α : Type u} (a c : α) (sign : Bool)
    (h : a ≠ c) : ∀ letter ∈ [(a, sign)], letter.1 ≠ c := by
  -- Membership identifies the unique signed letter.
  intro letter hletter
  simp only [List.mem_singleton] at hletter
  simpa only [hletter, Prod.fst] using h

/-- Helper for Lemma 77.3: a positively oriented interlaced label pair can be
moved to a leading commutator block without changing the residual fragments. -/
private lemma equivalentPositiveInterlacedPairToHandle {α : Type u} [Infinite α]
    (word target : PolygonWord α) (initial : List (α × Bool))
    (a b : α) (y₁ y₂ y₃ y₄ y₅ : List (α × Bool))
    (hab : a ≠ b)
    (havoidA : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ a)
    (havoidB : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ b)
    (hsource : word.1 =
      initial ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
        [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅)
    (htarget : target.1 =
      initial ++ [(a, true), (b, true), (a, false), (b, false)] ++
        y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {target} := by
  classical
  have hba : b ≠ a := Ne.symm hab
  have haInitial : ∀ letter ∈ initial, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₁ : ∀ letter ∈ y₁, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₂ : ∀ letter ∈ y₂, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₃ : ∀ letter ∈ y₃, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₄ : ∀ letter ∈ y₄, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₅ : ∀ letter ∈ y₅, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have hbInitial : ∀ letter ∈ initial, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₁ : ∀ letter ∈ y₁, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₂ : ∀ letter ∈ y₂, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₃ : ∀ letter ∈ y₃, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₄ : ∀ letter ∈ y₄, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₅ : ∀ letter ∈ y₅, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have haBPos := forallFstNe_singleton b a true hba
  have haBNeg := forallFstNe_singleton b a false hba
  have hbAPos := forallFstNe_singleton a b true hab
  have hbANeg := forallFstNe_singleton a b false hab
  have hnilA : ∀ letter ∈ ([] : List (α × Bool)), letter.1 ≠ a := by simp
  have hnilB : ∀ letter ∈ ([] : List (α × Bool)), letter.1 ≠ b := by simp
  -- Assemble the four exact avoidance shapes consumed by the exchange interface.
  have haMiddle := forallFstNe_append (y₂ ++ [(b, true)]) y₃ a
    (forallFstNe_append y₂ [(b, true)] a haY₂ haBPos) haY₃
  have haTail := forallFstNe_append (y₄ ++ [(b, false)]) y₅ a
    (forallFstNe_append y₄ [(b, false)] a haY₄ haBNeg) haY₅
  have hresOne := forallFstNe_append
    (initial ++ y₁ ++ (y₂ ++ [(b, true)] ++ y₃) ++ [])
      (y₄ ++ [(b, false)] ++ y₅) a
      (forallFstNe_append (initial ++ y₁ ++ (y₂ ++ [(b, true)] ++ y₃)) [] a
        (forallFstNe_append (initial ++ y₁) (y₂ ++ [(b, true)] ++ y₃) a
          (forallFstNe_append initial y₁ a haInitial haY₁) haMiddle) hnilA)
      haTail
  have hbPrefix := forallFstNe_append initial [(a, true)] b hbInitial hbAPos
  have hbSignedY₃ := forallFstNe_append y₃ [(a, false)] b hbY₃ hbANeg
  have hbY₁Y₄ := forallFstNe_append y₁ y₄ b hbY₁ hbY₄
  have hresTwo := forallFstNe_append
    ((initial ++ [(a, true)]) ++ y₂ ++ (y₃ ++ [(a, false)]) ++ (y₁ ++ y₄))
      y₅ b
      (forallFstNe_append
        ((initial ++ [(a, true)]) ++ y₂ ++ (y₃ ++ [(a, false)]))
          (y₁ ++ y₄) b
          (forallFstNe_append ((initial ++ [(a, true)]) ++ y₂)
            (y₃ ++ [(a, false)]) b
            (forallFstNe_append (initial ++ [(a, true)]) y₂ b hbPrefix hbY₂)
              hbSignedY₃) hbY₁Y₄) hbY₅
  have haBlock := forallFstNe_append (y₁ ++ y₄) y₃ a
    (forallFstNe_append y₁ y₄ a haY₁ haY₄) haY₃
  have haLast := forallFstNe_append ([(b, false)] ++ y₂) y₅ a
    (forallFstNe_append [(b, false)] y₂ a haBNeg haY₂) haY₅
  have hresThree := forallFstNe_append
    (initial ++ [] ++ [(b, true)] ++ (y₁ ++ y₄ ++ y₃))
      ([(b, false)] ++ y₂ ++ y₅) a
      (forallFstNe_append (initial ++ [] ++ [(b, true)])
        (y₁ ++ y₄ ++ y₃) a
        (forallFstNe_append (initial ++ []) [(b, true)] a
          (forallFstNe_append initial [] a haInitial hnilA) haBPos) haBlock)
      haLast
  have hbBlock := forallFstNe_append (y₁ ++ y₄) y₃ b
    (forallFstNe_append y₁ y₄ b hbY₁ hbY₄) hbY₃
  have hbLast := forallFstNe_append y₂ y₅ b hbY₂ hbY₅
  have hresFour := forallFstNe_append
    ((initial ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃) ++ [] ++ [(a, false)])
      (y₂ ++ y₅) b
      (forallFstNe_append
        ((initial ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃) ++ [])
          [(a, false)] b
          (forallFstNe_append
            ((initial ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃)) [] b
            (forallFstNe_append (initial ++ [(a, true)])
              (y₁ ++ y₄ ++ y₃) b hbPrefix hbBlock) hnilB) hbANeg) hbLast
  -- Name the three intermediate words so the four exchanges use stable endpoints.
  have hstageOneLength : 3 ≤
      (initial ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++ [(a, false)] ++
        y₁ ++ y₄ ++ [(b, false)] ++ y₅).length := by
    have hlength := word.property
    rw [hsource] at hlength
    simp only [List.length_append, List.length_cons, List.length_nil] at hlength ⊢
    omega
  let stageOne : PolygonWord α :=
    ⟨initial ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++ [(a, false)] ++
      y₁ ++ y₄ ++ [(b, false)] ++ y₅, hstageOneLength⟩
  have hstageTwoLength : 3 ≤
      (initial ++ [(a, true), (b, true)] ++ y₁ ++ y₄ ++ y₃ ++
        [(a, false), (b, false)] ++ y₂ ++ y₅).length := by
    have hlength := stageOne.property
    simp only [stageOne, List.length_append, List.length_cons,
      List.length_nil] at hlength ⊢
    omega
  let stageTwo : PolygonWord α :=
    ⟨initial ++ [(a, true), (b, true)] ++ y₁ ++ y₄ ++ y₃ ++
      [(a, false), (b, false)] ++ y₂ ++ y₅, hstageTwoLength⟩
  have hstageThreeLength : 3 ≤
      (initial ++ [(a, true)] ++ y₁ ++ y₄ ++ y₃ ++
        [(b, true), (a, false), (b, false)] ++ y₂ ++ y₅).length := by
    have hlength := stageTwo.property
    simp only [stageTwo, List.length_append, List.length_cons,
      List.length_nil] at hlength ⊢
    omega
  let stageThree : PolygonWord α :=
    ⟨initial ++ [(a, true)] ++ y₁ ++ y₄ ++ y₃ ++
      [(b, true), (a, false), (b, false)] ++ y₂ ++ y₅, hstageThreeLength⟩
  obtain ⟨c₁, hc₁⟩ := existsAvoidedLabel ({word} : LabellingScheme α)
  have hdecompOne : word.1 = initial ++ y₁ ++ [(a, true)] ++
      (y₂ ++ [(b, true)] ++ y₃) ++ [] ++ [(a, false)] ++
        (y₄ ++ [(b, false)] ++ y₅) := by
    simpa [List.append_assoc] using hsource
  have htargetOne : stageOne.1 = initial ++ [(a, true)] ++ [] ++
      (y₂ ++ [(b, true)] ++ y₃) ++ [(a, false)] ++ y₁ ++
        (y₄ ++ [(b, false)] ++ y₅) := by
    simp [stageOne, List.append_assoc]
  have hleftOne : 2 ≤
      (y₁ ++ [(a, true)] ++ (y₂ ++ [(b, true)] ++ y₃)).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hrightOne : 2 ≤
      ([] ++ [(a, false)] ++ (y₄ ++ [(b, false)] ++ y₅) ++ initial).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hfirst := equivalentPairExchangeTo word stageOne
    initial y₁ (y₂ ++ [(b, true)] ++ y₃) [] (y₄ ++ [(b, false)] ++ y₅)
      a c₁ hdecompOne htargetOne hc₁ hresOne hleftOne hrightOne
  obtain ⟨c₂, hc₂⟩ := existsAvoidedLabel ({stageOne} : LabellingScheme α)
  have hdecompTwo : stageOne.1 = (initial ++ [(a, true)]) ++ y₂ ++
      [(b, true)] ++ (y₃ ++ [(a, false)]) ++ (y₁ ++ y₄) ++
        [(b, false)] ++ y₅ := by
    simp [stageOne, List.append_assoc]
  have htargetTwo : stageTwo.1 = (initial ++ [(a, true)]) ++ [(b, true)] ++
      (y₁ ++ y₄) ++ (y₃ ++ [(a, false)]) ++ [(b, false)] ++ y₂ ++ y₅ := by
    simp [stageTwo, List.append_assoc]
  have hleftTwo : 2 ≤
      (y₂ ++ [(b, true)] ++ (y₃ ++ [(a, false)])).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hrightTwo : 2 ≤
      ((y₁ ++ y₄) ++ [(b, false)] ++ y₅ ++
        (initial ++ [(a, true)])).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hsecond := equivalentPairExchangeTo stageOne stageTwo
    (initial ++ [(a, true)]) y₂ (y₃ ++ [(a, false)]) (y₁ ++ y₄) y₅
      b c₂ hdecompTwo htargetTwo hc₂ hresTwo hleftTwo hrightTwo
  obtain ⟨c₃, hc₃⟩ := existsAvoidedLabel ({stageTwo} : LabellingScheme α)
  have hdecompThree : stageTwo.1 = initial ++ [] ++ [(a, true)] ++
      [(b, true)] ++ (y₁ ++ y₄ ++ y₃) ++ [(a, false)] ++
        ([(b, false)] ++ y₂ ++ y₅) := by
    simp [stageTwo, List.append_assoc]
  have htargetThree : stageThree.1 = initial ++ [(a, true)] ++
      (y₁ ++ y₄ ++ y₃) ++ [(b, true)] ++ [(a, false)] ++ [] ++
        ([(b, false)] ++ y₂ ++ y₅) := by
    simp [stageThree, List.append_assoc]
  have hleftThree : 2 ≤ ([] ++ [(a, true)] ++ [(b, true)]).length := by
    simp
  have hrightThree : 2 ≤
      ((y₁ ++ y₄ ++ y₃) ++ [(a, false)] ++
        ([(b, false)] ++ y₂ ++ y₅) ++ initial).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hthird := equivalentPairExchangeTo stageTwo stageThree
    initial [] [(b, true)] (y₁ ++ y₄ ++ y₃) ([(b, false)] ++ y₂ ++ y₅)
      a c₃ hdecompThree htargetThree hc₃ hresThree hleftThree hrightThree
  obtain ⟨c₄, hc₄⟩ := existsAvoidedLabel ({stageThree} : LabellingScheme α)
  have hdecompFour : stageThree.1 = (initial ++ [(a, true)]) ++
      (y₁ ++ y₄ ++ y₃) ++ [(b, true)] ++ [(a, false)] ++ [] ++
        [(b, false)] ++ (y₂ ++ y₅) := by
    simp [stageThree, List.append_assoc]
  have htargetFour : target.1 = (initial ++ [(a, true)]) ++ [(b, true)] ++
      [] ++ [(a, false)] ++ [(b, false)] ++ (y₁ ++ y₄ ++ y₃) ++
        (y₂ ++ y₅) := by
    simpa [List.append_assoc] using htarget
  have hleftFour : 2 ≤
      ((y₁ ++ y₄ ++ y₃) ++ [(b, true)] ++ [(a, false)]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hrightFour : 2 ≤
      ([] ++ [(b, false)] ++ (y₂ ++ y₅) ++
        (initial ++ [(a, true)])).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hresFour' : ∀ letter ∈
      (initial ++ [(a, true)]) ++ (y₁ ++ y₄ ++ y₃) ++ [(a, false)] ++ [] ++
        (y₂ ++ y₅), letter.1 ≠ b := by
    simpa only [List.append_nil, List.append_assoc] using hresFour
  have hfourth := equivalentPairExchangeTo stageThree target
    (initial ++ [(a, true)]) (y₁ ++ y₄ ++ y₃) [(a, false)] [] (y₂ ++ y₅)
      b c₄ hdecompFour htargetFour hc₄ hresFour' hleftFour hrightFour
  -- The source proof's four exchanges now compose without exposing their cut data.
  exact hfirst.trans (hsecond.trans (hthird.trans hfourth))

/-- Helper for Lemma 77.3: reversing a label interchanges the signs of its two
displayed opposite occurrences while fixing the avoiding fragments. -/
private lemma reverseOppositePair_val {α : Type u} (word : PolygonWord α)
    (before middle after : List (α × Bool)) (a : α) (sign : Bool)
    (hdecomp : word.1 =
      before ++ [(a, sign)] ++ middle ++ [(a, !sign)] ++ after)
    (havoid : ∀ letter ∈ before ++ middle ++ after, letter.1 ≠ a) :
    (word.reverseLabel a).1 =
      before ++ [(a, !sign)] ++ middle ++ [(a, sign)] ++ after := by
  have hbefore : ∀ letter ∈ before, letter.1 ≠ a := by
    intro letter hletter
    apply havoid letter
    simp only [List.mem_append]
    exact Or.inl (Or.inl hletter)
  have hmiddle : ∀ letter ∈ middle, letter.1 ≠ a := by
    intro letter hletter
    apply havoid letter
    simp only [List.mem_append]
    exact Or.inl (Or.inr hletter)
  have hafter : ∀ letter ∈ after, letter.1 ≠ a := by
    intro letter hletter
    apply havoid letter
    simp only [List.mem_append]
    exact Or.inr hletter
  -- Map the reversal over the decomposition and normalize its three fixed fragments.
  rw [PolygonWord.reverseLabel_val, hdecomp]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [mapReverseSignAt_eq_self_of_avoids before a hbefore,
    mapReverseSignAt_eq_self_of_avoids middle a hmiddle,
    mapReverseSignAt_eq_self_of_avoids after a hafter]
  simp [reverseSignAt]

/-- Helper for Lemma 77.3: reversing one label in a singleton scheme is an
elementary equivalence to the reversed polygon word. -/
private lemma equivalentReverseLabel {α : Type u} (word : PolygonWord α) (a : α) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({word.reverseLabel a} : LabellingScheme α) := by
  -- The scheme operation maps its sole polygon word to the word-level reversal.
  have hstep := LabellingScheme.Equivalent.ofElementary
    (.reverse ({word} : LabellingScheme α) a)
  simpa only [LabellingScheme.reverseLabel, Multiset.map_singleton] using hstep

/-- Helper for Lemma 77.3: the three fragments around the first displayed pair
avoid its label, even after inserting the distinct second pair. -/
private lemma interlacedFirstAvoidance {α : Type u}
    (initial y₁ y₂ y₃ y₄ y₅ : List (α × Bool)) (a b : α) (sb : Bool)
    (hab : a ≠ b)
    (havoidA : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ a) :
    ∀ letter ∈
      (initial ++ y₁) ++ (y₂ ++ [(b, sb)] ++ y₃) ++
        (y₄ ++ [(b, !sb)] ++ y₅), letter.1 ≠ a := by
  have hba : b ≠ a := Ne.symm hab
  have haInitial : ∀ letter ∈ initial, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₁ : ∀ letter ∈ y₁, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₂ : ∀ letter ∈ y₂, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₃ : ∀ letter ∈ y₃, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₄ : ∀ letter ∈ y₄, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  have haY₅ : ∀ letter ∈ y₅, letter.1 ≠ a := by
    intro letter hletter
    apply havoidA letter
    simp only [List.mem_append]
    aesop
  -- Concatenate the fixed fragments with the two distinct `b`-letters.
  simpa only [List.append_assoc] using forallFstNe_append (initial ++ y₁)
    ((y₂ ++ [(b, sb)] ++ y₃) ++ (y₄ ++ [(b, !sb)] ++ y₅)) a
    (forallFstNe_append initial y₁ a haInitial haY₁)
    (forallFstNe_append (y₂ ++ [(b, sb)] ++ y₃)
      (y₄ ++ [(b, !sb)] ++ y₅) a
      (forallFstNe_append (y₂ ++ [(b, sb)]) y₃ a
        (forallFstNe_append y₂ [(b, sb)] a haY₂
          (forallFstNe_singleton b a sb hba)) haY₃)
      (forallFstNe_append (y₄ ++ [(b, !sb)]) y₅ a
        (forallFstNe_append y₄ [(b, !sb)] a haY₄
          (forallFstNe_singleton b a (!sb) hba)) haY₅))

/-- Helper for Lemma 77.3: the three fragments around the second displayed pair
avoid its label, even after inserting the distinct first pair. -/
private lemma interlacedSecondAvoidance {α : Type u}
    (initial y₁ y₂ y₃ y₄ y₅ : List (α × Bool)) (a b : α) (sa : Bool)
    (hab : a ≠ b)
    (havoidB : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ b) :
    ∀ letter ∈
      (initial ++ y₁ ++ [(a, sa)] ++ y₂) ++
        (y₃ ++ [(a, !sa)] ++ y₄) ++ y₅, letter.1 ≠ b := by
  have hbInitial : ∀ letter ∈ initial, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₁ : ∀ letter ∈ y₁, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₂ : ∀ letter ∈ y₂, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₃ : ∀ letter ∈ y₃, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₄ : ∀ letter ∈ y₄, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  have hbY₅ : ∀ letter ∈ y₅, letter.1 ≠ b := by
    intro letter hletter
    apply havoidB letter
    simp only [List.mem_append]
    aesop
  -- Concatenate the fixed fragments with the two distinct `a`-letters.
  simpa only [List.append_assoc] using forallFstNe_append
    (initial ++ y₁ ++ [(a, sa)] ++ y₂) (y₃ ++ [(a, !sa)] ++ y₄ ++ y₅) b
    (forallFstNe_append (initial ++ y₁ ++ [(a, sa)]) y₂ b
      (forallFstNe_append (initial ++ y₁) [(a, sa)] b
        (forallFstNe_append initial y₁ b hbInitial hbY₁)
          (forallFstNe_singleton a b sa hab)) hbY₂)
    (forallFstNe_append (y₃ ++ [(a, !sa)] ++ y₄) y₅ b
      (forallFstNe_append (y₃ ++ [(a, !sa)]) y₄ b
        (forallFstNe_append y₃ [(a, !sa)] b hbY₃
          (forallFstNe_singleton a b (!sa) hab)) hbY₄) hbY₅)

/-- Helper for Lemma 77.3: reversing the first label of an interlaced pair
flips exactly its two displayed signs. -/
private lemma reverseInterlacedFirst_val {α : Type u} (word : PolygonWord α)
    (initial : List (α × Bool)) (a b : α) (sa sb : Bool)
    (y₁ y₂ y₃ y₄ y₅ : List (α × Bool)) (hab : a ≠ b)
    (havoidA : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ a)
    (hsource : word.1 = initial ++ y₁ ++ [(a, sa)] ++ y₂ ++ [(b, sb)] ++
      y₃ ++ [(a, !sa)] ++ y₄ ++ [(b, !sb)] ++ y₅) :
    (word.reverseLabel a).1 =
      initial ++ y₁ ++ [(a, !sa)] ++ y₂ ++ [(b, sb)] ++ y₃ ++
        [(a, sa)] ++ y₄ ++ [(b, !sb)] ++ y₅ := by
  have hgroup : word.1 = (initial ++ y₁) ++ [(a, sa)] ++
      (y₂ ++ [(b, sb)] ++ y₃) ++ [(a, !sa)] ++
        (y₄ ++ [(b, !sb)] ++ y₅) := by
    simpa [List.append_assoc] using hsource
  have havoid := interlacedFirstAvoidance initial y₁ y₂ y₃ y₄ y₅
    a b sb hab havoidA
  -- Apply the two-occurrence reversal bridge and reassociate its output.
  have hreversed := reverseOppositePair_val word (initial ++ y₁)
    (y₂ ++ [(b, sb)] ++ y₃) (y₄ ++ [(b, !sb)] ++ y₅)
      a sa hgroup havoid
  simpa [List.append_assoc] using hreversed

/-- Helper for Lemma 77.3: reversing the second label of an interlaced pair
flips exactly its two displayed signs. -/
private lemma reverseInterlacedSecond_val {α : Type u} (word : PolygonWord α)
    (initial : List (α × Bool)) (a b : α) (sa sb : Bool)
    (y₁ y₂ y₃ y₄ y₅ : List (α × Bool)) (hab : a ≠ b)
    (havoidB : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ b)
    (hsource : word.1 = initial ++ y₁ ++ [(a, sa)] ++ y₂ ++ [(b, sb)] ++
      y₃ ++ [(a, !sa)] ++ y₄ ++ [(b, !sb)] ++ y₅) :
    (word.reverseLabel b).1 =
      initial ++ y₁ ++ [(a, sa)] ++ y₂ ++ [(b, !sb)] ++ y₃ ++
        [(a, !sa)] ++ y₄ ++ [(b, sb)] ++ y₅ := by
  have hgroup : word.1 =
      (initial ++ y₁ ++ [(a, sa)] ++ y₂) ++ [(b, sb)] ++
        (y₃ ++ [(a, !sa)] ++ y₄) ++ [(b, !sb)] ++ y₅ := by
    simpa [List.append_assoc] using hsource
  have havoid := interlacedSecondAvoidance initial y₁ y₂ y₃ y₄ y₅
    a b sa hab havoidB
  -- Apply the two-occurrence reversal bridge and reassociate its output.
  have hreversed := reverseOppositePair_val word
    (initial ++ y₁ ++ [(a, sa)] ++ y₂) (y₃ ++ [(a, !sa)] ++ y₄) y₅
      b sb hgroup havoid
  simpa [List.append_assoc] using hreversed

/-- Helper for Lemma 77.3: an interlaced pair in a proper word can be oriented
and moved to a commutator block while preserving the displayed prefix. -/
private lemma equivalentInterlacedPairToHandle {α : Type u} [Infinite α]
    (word target : PolygonWord α) (initial : List (α × Bool))
    (a b : α) (sa sb : Bool) (y₁ y₂ y₃ y₄ y₅ : List (α × Bool))
    (hab : a ≠ b)
    (havoidA : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ a)
    (havoidB : ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅,
      letter.1 ≠ b)
    (hsource : word.1 = initial ++ y₁ ++ [(a, sa)] ++ y₂ ++ [(b, sb)] ++
      y₃ ++ [(a, !sa)] ++ y₄ ++ [(b, !sb)] ++ y₅)
    (htarget : target.1 =
      initial ++ [(a, true), (b, true), (a, false), (b, false)] ++
        y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {target} := by
  -- Route correction: normalize signs outside the cut-and-paste construction,
  -- then invoke the positive four-exchange interface exactly once in each case.
  cases sa with
  | false =>
      cases sb with
      | false =>
          have hsourceA : (word.reverseLabel a).1 =
              initial ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, false)] ++ y₃ ++
                [(a, false)] ++ y₄ ++ [(b, true)] ++ y₅ :=
            reverseInterlacedFirst_val word initial a b false false
              y₁ y₂ y₃ y₄ y₅ hab havoidA hsource
          have hsourcePositive : ((word.reverseLabel a).reverseLabel b).1 =
              initial ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
                [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅ :=
            reverseInterlacedSecond_val (word.reverseLabel a) initial
              a b true false y₁ y₂ y₃ y₄ y₅ hab havoidB hsourceA
          have haStep := equivalentReverseLabel word a
          have hbStep := equivalentReverseLabel (word.reverseLabel a) b
          have hpositive := equivalentPositiveInterlacedPairToHandle
            ((word.reverseLabel a).reverseLabel b) target initial a b
              y₁ y₂ y₃ y₄ y₅ hab havoidA havoidB hsourcePositive htarget
          exact haStep.trans (hbStep.trans hpositive)
      | true =>
          have hsourcePositive : (word.reverseLabel a).1 =
              initial ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
                [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅ :=
            reverseInterlacedFirst_val word initial a b false true
              y₁ y₂ y₃ y₄ y₅ hab havoidA hsource
          have haStep := equivalentReverseLabel word a
          have hpositive := equivalentPositiveInterlacedPairToHandle
            (word.reverseLabel a) target initial a b y₁ y₂ y₃ y₄ y₅
              hab havoidA havoidB hsourcePositive htarget
          exact haStep.trans hpositive
  | true =>
      cases sb with
      | false =>
          have hsourcePositive : (word.reverseLabel b).1 =
              initial ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
                [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅ :=
            reverseInterlacedSecond_val word initial a b true false
              y₁ y₂ y₃ y₄ y₅ hab havoidB hsource
          have hbStep := equivalentReverseLabel word b
          have hpositive := equivalentPositiveInterlacedPairToHandle
            (word.reverseLabel b) target initial a b y₁ y₂ y₃ y₄ y₅
              hab havoidA havoidB hsourcePositive htarget
          exact hbStep.trans hpositive
      | true =>
          have hsourcePositive : word.1 =
              initial ++ y₁ ++ [(a, true)] ++ y₂ ++ [(b, true)] ++ y₃ ++
                [(a, false)] ++ y₄ ++ [(b, false)] ++ y₅ := by
            simpa using hsource
          exact equivalentPositiveInterlacedPairToHandle word target initial a b
            y₁ y₂ y₃ y₄ y₅ hab havoidA havoidB hsourcePositive htarget

/-- Lemma 77.3: A proper word with a torus-type suffix whose adjacent terms
have distinct labels is equivalent to one with the same prefix and a torus handle followed
by an empty or torus-type tail of the same total suffix length. -/
theorem existsEquivalentTorusHandle {α : Type u} [Infinite α]
    (word suffix : PolygonWord α) (initial : List (α × Bool))
    (hproper : ({word} : LabellingScheme α).Proper)
    (hdecomp : word.1 = initial ++ suffix.1) (htorus : suffix.TorusType)
    (hadjacent : suffix.1.IsChain (fun x y : α × Bool ↦ x.1 ≠ y.1)) :
    ∃ normalized : PolygonWord α,
      ∃ form : TorusHandleForm normalized initial suffix.1.length,
        LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} := by
  classical
  -- Route correction: the generated equivalence API is now available, so the
  -- proof can follow the source's crossing-pair and cut-and-paste architecture.
  have hcount : ∀ c ∈ suffix.1.map Prod.fst,
      ∀ sign : Bool,
        Multiset.count (c, sign) (suffix.1 : Multiset (α × Bool)) = 1 := by
    intro c hc sign
    obtain ⟨letter, hletter, hletterLabel⟩ := List.mem_map.mp hc
    obtain ⟨label, letterSign⟩ := letter
    simp only at hletterLabel
    subst label
    have hcLabels : c ∈ ({suffix} : LabellingScheme α).labels := by
      rw [LabellingScheme.mem_labels_iff]
      have hsuffixMem : suffix ∈ ({suffix} : LabellingScheme α) := by simp
      exact ⟨suffix, hsuffixMem, letterSign, hletter⟩
    exact PolygonWord.torusType_iff_count.mp htorus c hcLabels sign
  have hsuffixNonempty : suffix.1 ≠ [] := by
    intro hsuffix
    have hsuffixLength := suffix.property
    rw [hsuffix] at hsuffixLength
    simp at hsuffixLength
  obtain ⟨a, b, sa, sb, y₁, y₂, y₃, y₄, y₅, hab, havoidA, havoidB,
    hsuffix⟩ :=
    existsInterlacedOppositePairs suffix.1 hsuffixNonempty hcount hadjacent
  have hprefixAvoid := properPrefixAvoidsTorusLabels word suffix initial
    hproper hdecomp htorus
  have haSuffix : a ∈ suffix.1.map Prod.fst := by
    rw [hsuffix]
    simp
  have hbSuffix : b ∈ suffix.1.map Prod.fst := by
    rw [hsuffix]
    simp
  have havoidGlobalA :
      ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ a := by
    intro letter hletter
    simp only [List.mem_append] at hletter
    rcases hletter with ((((hinitial | hy₁) | hy₂) | hy₃) | hy₄) | hy₅
    · exact hprefixAvoid a haSuffix letter hinitial
    · apply havoidA letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hy₁)))
    · apply havoidA letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hy₂)))
    · apply havoidA letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr hy₃))
    · apply havoidA letter
      simp only [List.mem_append]
      exact Or.inl (Or.inr hy₄)
    · apply havoidA letter
      simp only [List.mem_append]
      exact Or.inr hy₅
  have havoidGlobalB :
      ∀ letter ∈ initial ++ y₁ ++ y₂ ++ y₃ ++ y₄ ++ y₅, letter.1 ≠ b := by
    intro letter hletter
    simp only [List.mem_append] at hletter
    rcases hletter with ((((hinitial | hy₁) | hy₂) | hy₃) | hy₄) | hy₅
    · exact hprefixAvoid b hbSuffix letter hinitial
    · apply havoidB letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hy₁)))
    · apply havoidB letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hy₂)))
    · apply havoidB letter
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr hy₃))
    · apply havoidB letter
      simp only [List.mem_append]
      exact Or.inl (Or.inr hy₄)
    · apply havoidB letter
      simp only [List.mem_append]
      exact Or.inr hy₅
  let tail := y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅
  have htail : tail = [] ∨
      ∀ c ∈ tail.map Prod.fst,
        ∃ rest : Multiset (α × Bool),
          (tail : Multiset (α × Bool)) =
              (c, true) ::ₘ (c, false) ::ₘ rest ∧
            ∀ sign : Bool, (c, sign) ∉ rest := by
    -- The residual count calculation is insensitive to its fragment order.
    simpa only [tail] using interlacedResidualTorusOrEmpty suffix.1 a b sa sb
      y₁ y₂ y₃ y₄ y₅ hcount havoidA havoidB hsuffix
  have hnormalizedLength : 3 ≤
      (initial ++ [(a, true), (b, true), (a, false), (b, false)] ++ tail).length := by
    have hwordLength := word.property
    rw [hdecomp, hsuffix] at hwordLength
    simp only [tail, List.length_append, List.length_cons, List.length_nil] at hwordLength ⊢
    omega
  let normalized : PolygonWord α :=
    ⟨initial ++ [(a, true), (b, true), (a, false), (b, false)] ++ tail,
      hnormalizedLength⟩
  have hnormalizedValue : normalized.1 =
      initial ++ [(a, true), (b, true), (a, false), (b, false)] ++ tail := by
    rfl
  have htailLength :
      ([(a, true), (b, true), (a, false), (b, false)] ++ tail).length =
        suffix.1.length := by
    rw [hsuffix]
    simp only [tail, List.length_append, List.length_cons, List.length_nil]
    omega
  let form : TorusHandleForm normalized initial suffix.1.length :=
    TorusHandleForm.ofWords a b tail hab hnormalizedValue htailLength htail
  have hsource : word.1 =
      initial ++ y₁ ++ [(a, sa)] ++ y₂ ++ [(b, sb)] ++ y₃ ++
        [(a, !sa)] ++ y₄ ++ [(b, !sb)] ++ y₅ := by
    rw [hdecomp, hsuffix]
    simp only [List.append_assoc]
  have hequivalent :
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} := by
    have htarget : normalized.1 =
        initial ++ [(a, true), (b, true), (a, false), (b, false)] ++
          y₁ ++ y₄ ++ y₃ ++ y₂ ++ y₅ := by
      simpa only [tail, List.append_assoc] using hnormalizedValue
    exact equivalentInterlacedPairToHandle word normalized initial a b sa sb
      y₁ y₂ y₃ y₄ y₅ hab havoidGlobalA havoidGlobalB hsource htarget
  -- Package the normalized word, its handle form, and the composed equivalence.
  exact ⟨normalized, form, hequivalent⟩


end PolygonWord
