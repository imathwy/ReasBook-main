module

public import Topology_Munkres_2000.Book.Exercise_77_4.BoundedWordNormalization
public import Topology_Munkres_2000.Book.Proposition_77_1
public import Topology_Munkres_2000.Book.Lemma_77_4
public import Topology_Munkres_2000.Book.Lemma_77_5
import all Topology_Munkres_2000.Book.Definition_74_4

public section

universe u

namespace PolygonWord

/-- Helper for Exercise 77.4: duplicating every signed letter doubles the
length of the resulting boundary fragment. -/
theorem duplicatedSignedPairs_length {α : Type u} (pairs : List (α × Bool)) :
    (pairs.flatMap (fun letter ↦ [letter, letter])).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons letter pairs ih =>
      -- Remove the leading two-letter block and use the induction hypothesis.
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, zero_add, ih]
      omega

/-- Helper for Exercise 77.4: a two-letter torus residual is exactly one
oppositely signed pair; it is kept as a list rather than forced into the
`PolygonWord` subtype. -/
theorem TorusResidual.eq_oppositePair_of_length_two {α : Type u}
    {tail : List (α × Bool)} (hresidual : TorusResidual tail)
    (hlength : tail.length = 2) :
    ∃ a : α, ∃ sign : Bool, tail = [(a, sign), (a, !sign)] := by
  rw [torusResidual_iff] at hresidual
  cases tail with
  | nil =>
      simp only [List.length_nil] at hlength
      omega
  | cons first tail =>
      cases tail with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlength
          omega
      | cons second tail =>
          cases tail with
          | cons third tail =>
              simp only [List.length_cons, Nat.succ.injEq] at hlength
              omega
          | nil =>
              obtain ⟨a, sign⟩ := first
              obtain ⟨c, secondSign⟩ := second
              obtain ⟨rest, hletters, _hrest⟩ := hresidual a (by simp)
              have hrestCard : rest.card = 0 := by
                have hcards := congrArg Multiset.card hletters
                simp only [Multiset.coe_card, List.length_cons,
                  List.length_nil, Multiset.card_cons] at hcards
                omega
              have hrestZero : rest = 0 := Multiset.card_eq_zero.mp hrestCard
              subst rest
              cases sign
              · -- Cancel the first negative occurrence after commuting the target pair.
                have hcancel :
                    (a, false) ::ₘ (c, secondSign) ::ₘ 0 =
                      (a, false) ::ₘ (a, true) ::ₘ 0 :=
                  hletters.trans
                    (Multiset.cons_swap (a, true) (a, false) 0)
                have hsingleton :=
                  (Multiset.cons_inj_right (a, false)).mp hcancel
                have hsecond : (c, secondSign) = (a, true) :=
                  Multiset.singleton_inj.mp hsingleton
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsecond
                exact ⟨c, false, rfl⟩
              · -- With a positive first occurrence, cancellation is already aligned.
                have hcancel :
                    (a, true) ::ₘ (c, secondSign) ::ₘ 0 =
                      (a, true) ::ₘ (a, false) ::ₘ 0 := hletters
                have hsingleton :=
                  (Multiset.cons_inj_right (a, true)).mp hcancel
                have hsecond : (c, secondSign) = (a, false) :=
                  Multiset.singleton_inj.mp hsingleton
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsecond
                exact ⟨c, true, rfl⟩

/-- Helper for Exercise 77.4: a four-letter projective normal form is either
one duplicated pair followed by a two-letter torus residual, or two duplicated
pairs with no residual. -/
def FourLetterProjectiveNormalForm {α : Type u}
    (normalized : PolygonWord α) : Prop :=
  ∃ pairs tail : List (α × Bool),
    normalized.IsDuplicatedPrefix pairs tail ∧
      ((pairs.length = 1 ∧ tail.length = 2 ∧ TorusResidual tail) ∨
        (pairs.length = 2 ∧ tail = []))

/-- Helper for Exercise 77.4: Proposition 77.1 specializes at length four to
the two exact projective terminal forms. -/
theorem ProjectiveType.existsEquivalentFourLetterNormalForm
    {α : Type u} [Infinite α] {word : PolygonWord α}
    (hword : word.ProjectiveType) (hlength : word.length = 4) :
    ∃ normalized : PolygonWord α,
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} ∧
        normalized.FourLetterProjectiveNormalForm := by
  obtain ⟨normalized, hequivalent, hnormalizedLength, hnormal⟩ :=
    hword.existsEquivalentNormalForm
  rw [projectiveNormalForm_iff] at hnormal
  obtain ⟨pairs, hpairs, tail, hprefix, htail⟩ := hnormal
  have hwordEq := (isDuplicatedPrefix_iff.mp hprefix).1
  have hlengthEq := congrArg List.length hwordEq
  have hnormalizedValLength : normalized.val.length = word.val.length := by
    unfold PolygonWord.length at hnormalizedLength
    exact hnormalizedLength
  have hwordValLength : word.val.length = 4 := by
    unfold PolygonWord.length at hlength
    exact hlength
  rw [List.length_append, duplicatedSignedPairs_length,
    hnormalizedValLength, hwordValLength] at hlengthEq
  refine ⟨normalized, hequivalent, pairs, tail, hprefix, ?_⟩
  rcases htail with htailEmpty | htailTorus
  · -- An empty residual uses both duplicated pairs.
    subst tail
    right
    simp only [List.length_nil] at hlengthEq
    exact ⟨by omega, rfl⟩
  · by_cases htailEmpty : tail = []
    · -- The residual predicate also permits the empty word; it is the same
      -- two-pair terminal case.
      subst tail
      right
      simp only [List.length_nil] at hlengthEq
      exact ⟨by omega, rfl⟩
    · -- Otherwise nonemptiness and the total length force one pair and a
      -- two-letter residual.
      left
      have hpairsPositive : 0 < pairs.length := List.length_pos_of_ne_nil hpairs
      have htailPositive : 0 < tail.length := List.length_pos_of_ne_nil htailEmpty
      exact ⟨by omega, by omega, htailTorus⟩

/-- Helper for Exercise 77.4: the sphere terminal form consists of two
distinct oppositely signed pairs. -/
def FourLetterSphereForm {α : Type u} (normalized : PolygonWord α) : Prop :=
  ∃ a c : α, ∃ firstSign secondSign : Bool,
    a ≠ c ∧ normalized.val =
      [(a, firstSign), (a, !firstSign),
        (c, secondSign), (c, !secondSign)]

/-- Helper for Exercise 77.4: after exposing one inverse pair in a four-letter
torus word, the remaining two letters are a distinct inverse pair. -/
theorem TorusType.twoLetterResidual_of_rotatedOppositePair
    {α : Type u} {word : PolygonWord α} (hword : word.TorusType)
    {a : α} {sign : Bool} {tail : List (α × Bool)}
    (hrotation : List.IsRotated word.val
      ([(a, sign), (a, !sign)] ++ tail))
    (htailLength : tail.length = 2) :
    ∃ c : α, ∃ tailSign : Bool,
      a ≠ c ∧ tail = [(c, tailSign), (c, !tailSign)] := by
  classical
  cases tail with
  | nil =>
      simp only [List.length_nil] at htailLength
      omega
  | cons first tail =>
      cases tail with
      | nil =>
          simp only [List.length_cons, List.length_nil] at htailLength
          omega
      | cons second tail =>
          cases tail with
          | cons third tail =>
              simp only [List.length_cons, Nat.succ.injEq] at htailLength
              omega
          | nil =>
              obtain ⟨c, tailSign⟩ := first
              obtain ⟨d, lastSign⟩ := second
              have hmultiset : (word.val : Multiset (α × Bool)) =
                  ([(a, sign), (a, !sign), (c, tailSign),
                    (d, lastSign)] : List (α × Bool)) :=
                Multiset.coe_eq_coe.mpr hrotation.perm
              have hcInWord :
                  c ∈ ({word} : LabellingScheme α).labels := by
                apply LabellingScheme.mem_labels_iff.mpr
                refine ⟨word, by simp, tailSign, ?_⟩
                apply hrotation.mem_iff.mpr
                simp
              have hcountFalse :=
                PolygonWord.torusType_iff_count.mp hword c hcInWord false
              have hcountTrue :=
                PolygonWord.torusType_iff_count.mp hword c hcInWord true
              rw [hmultiset] at hcountFalse hcountTrue
              have hac : a ≠ c := by
                intro hac
                subst c
                cases sign <;> cases tailSign <;>
                  simp at hcountFalse hcountTrue
              have hdc : d = c := by
                by_contra hdc
                cases tailSign <;>
                  simp [hac, Ne.symm hac, Ne.symm hdc] at hcountFalse hcountTrue
              subst d
              have hlast : lastSign = !tailSign := by
                cases tailSign <;> cases lastSign <;>
                  simp [hac, Ne.symm hac] at hcountFalse hcountTrue ⊢
              subst lastSign
              exact ⟨c, tailSign, hac, rfl⟩

/-- Helper for Exercise 77.4: the two possible four-letter torus terminals
are the sphere pair form and a single handle form. -/
def FourLetterTorusNormalForm {α : Type u}
    (normalized : PolygonWord α) : Prop :=
  normalized.FourLetterSphereForm ∨
    Nonempty (TorusHandleForm normalized [] 4)

/-- Helper for Exercise 77.4: under the ten-letter bound, the residual of a
first torus handle has one of the four finite lengths needed by completion. -/
theorem TorusHandleForm.tail_length_cases_of_le_ten
    {α : Type u} {normalized : PolygonWord α}
    (form : TorusHandleForm normalized [] normalized.val.length)
    (hproper : ({normalized} : LabellingScheme α).Proper)
    (hlength : normalized.val.length ≤ 10) :
    form.tail.length = 0 ∨ form.tail.length = 2 ∨
      form.tail.length = 4 ∨ form.tail.length = 6 := by
  have hformLength := form.length_eq
  simp only [List.length_cons, List.length_nil, List.length_append,
    zero_add] at hformLength
  have htotalCases :=
    CyclicPolygon.EdgePasting.properSingleton_length_cases_le_ten
      normalized hproper hlength
  rcases htotalCases with hfour | hsix | height | hten <;> omega

/-- Helper for Exercise 77.4: a proper projective normal form of length at
most ten exposes only the five finite residual lengths used by completion. -/
theorem ProjectiveNormalForm.exists_data_with_residual_length_cases
    {α : Type u} {normalized : PolygonWord α}
    (hnormal : normalized.ProjectiveNormalForm)
    (hproper : ({normalized} : LabellingScheme α).Proper)
    (hlength : normalized.val.length ≤ 10) :
    ∃ pairs : List (α × Bool), pairs ≠ [] ∧
      ∃ tail : List (α × Bool),
        normalized.IsDuplicatedPrefix pairs tail ∧
          (tail = [] ∨ TorusResidual tail) ∧
            (tail.length = 0 ∨ tail.length = 2 ∨ tail.length = 4 ∨
              tail.length = 6 ∨ tail.length = 8) := by
  rw [projectiveNormalForm_iff] at hnormal
  obtain ⟨pairs, hpairs, tail, hprefix, htail⟩ := hnormal
  have hwordEq := (isDuplicatedPrefix_iff.mp hprefix).1
  have hdecompositionLength := congrArg List.length hwordEq
  rw [List.length_append, duplicatedSignedPairs_length] at hdecompositionLength
  have htotalCases :=
    CyclicPolygon.EdgePasting.properSingleton_length_cases_le_ten
      normalized hproper hlength
  refine ⟨pairs, hpairs, tail, hprefix, htail, ?_⟩
  have hpairsPositive : 0 < pairs.length := List.length_pos_of_ne_nil hpairs
  rcases htotalCases with hfour | hsix | height | hten <;> omega

/-- Helper for Exercise 77.4: the no-opposite-adjacency branch of a four-letter
torus word is equivalent to one explicit handle with empty residual. -/
theorem TorusType.existsEquivalentFourLetterHandleForm
    {α : Type u} [Infinite α] {word : PolygonWord α}
    (hword : word.TorusType) (hlength : word.length = 4)
    (hadjacent : Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.val) :
    ∃ normalized : PolygonWord α,
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} ∧
        Nonempty (TorusHandleForm normalized [] 4) := by
  obtain ⟨normalized, form, hequivalent⟩ :=
    existsEquivalentCommutatorOfTorusType word hword hadjacent
  -- The source theorem preserves the full suffix length, which is four here.
  have hwordValLength : word.val.length = 4 := by
    unfold PolygonWord.length at hlength
    exact hlength
  rw [hwordValLength] at form
  exact ⟨normalized, hequivalent, ⟨form⟩⟩

/-- Helper for Exercise 77.4: every four-letter torus word is equivalent to
one of its two exact terminal normal forms. -/
theorem TorusType.existsEquivalentFourLetterNormalForm
    {α : Type u} [Infinite α] {word : PolygonWord α}
    (hword : word.TorusType) (hlength : word.val.length = 4) :
    ∃ normalized : PolygonWord α,
      LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} ∧
        normalized.FourLetterTorusNormalForm := by
  by_cases hadjacent : Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.val
  · have hlengthApi : word.length = 4 := by
      unfold PolygonWord.length
      exact hlength
    obtain ⟨normalized, hequivalent, hhandle⟩ :=
      hword.existsEquivalentFourLetterHandleForm hlengthApi hadjacent
    exact ⟨normalized, hequivalent, Or.inr hhandle⟩
  · obtain ⟨tail, a, sign, hrotation⟩ :=
      CyclicPolygon.EdgePasting.existsRotatedOppositePairAtHead word hadjacent
    have htailLength : tail.length = 2 := by
      have hrotationLength := hrotation.perm.length_eq
      simp only [List.length_append, List.length_cons, List.length_nil]
        at hrotationLength
      omega
    obtain ⟨c, tailSign, hac, htail⟩ :=
      hword.twoLetterResidual_of_rotatedOppositePair hrotation htailLength
    let normalized : PolygonWord α :=
      ⟨[(a, sign), (a, !sign), (c, tailSign), (c, !tailSign)], by simp⟩
    have hnormalizedRotation : List.IsRotated word.val normalized.val := by
      simpa only [normalized, htail, List.append_eq,
        List.cons_append, List.nil_append] using hrotation
    have hequivalent : LabellingScheme.Equivalent
        ({word} : LabellingScheme α) {normalized} :=
      LabellingScheme.Equivalent.ofElementary
        (.permute (.of word normalized 0 hnormalizedRotation))
    refine ⟨normalized, hequivalent, Or.inl ?_⟩
    exact ⟨a, c, sign, tailSign, hac, rfl⟩

end PolygonWord

end
