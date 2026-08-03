module

public import Topology_Munkres_2000.Book.Definition_76_10.Equivalence
public import Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Definition_76_6.Relabel
import all Topology_Munkres_2000.Book.Definition_77_1.Proper
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.FreeGroup.Basic

public section

universe u

namespace PolygonWord

/-- Moving two equal signed letters to the front preserves the minimum polygon-word length. -/
theorem pairFront_length {α : Type u} (word : PolygonWord α)
    (y₀ y₁ y₂ : List (α × Bool)) (a : α × Bool)
    (h_decomp : word.1 = y₀ ++ [a] ++ y₁ ++ [a] ++ y₂) :
    3 ≤ ([a, a] ++ y₀ ++ FreeGroup.invRev y₁ ++ y₂).length := by
  have h_length := word.property
  rw [h_decomp] at h_length
  simp only [List.length_append, List.length_cons, List.length_nil,
    FreeGroup.invRev_length] at h_length ⊢
  omega

/-- The polygon word obtained by moving two equal signed letters to the front and formally
inverting the fragment between them. -/
@[expose]
def pairFront {α : Type u} (word : PolygonWord α)
    (y₀ y₁ y₂ : List (α × Bool)) (a : α × Bool)
    (h_decomp : word.1 = y₀ ++ [a] ++ y₁ ++ [a] ++ y₂) : PolygonWord α :=
  ⟨[a, a] ++ y₀ ++ FreeGroup.invRev y₁ ++ y₂,
    pairFront_length word y₀ y₁ y₂ a h_decomp⟩

/-- The signed-label list underlying `pairFront`. -/
@[simp]
theorem pairFront_val {α : Type u} (word : PolygonWord α)
    (y₀ y₁ y₂ : List (α × Bool)) (a : α × Bool)
    (h_decomp : word.1 = y₀ ++ [a] ++ y₁ ++ [a] ++ y₂) :
    (pairFront word y₀ y₁ y₂ a h_decomp).1 =
      [a, a] ++ y₀ ++ FreeGroup.invRev y₁ ++ y₂ := rfl

/-- Helper for Lemma 77.1: an infinite label type contains a label avoided by a scheme
and excluded from any prescribed finite set. -/
private theorem existsAvoidedLabelOutside {α : Type u} [Infinite α]
    (scheme : LabellingScheme α) (forbidden : Finset α) :
    ∃ c, scheme.AvoidsLabel c ∧ c ∉ forbidden := by
  classical
  -- Choose outside both the finite label support and the additional forbidden set.
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (scheme.labels.toFinset ∪ forbidden)
  refine ⟨c, ?_, ?_⟩
  · rw [LabellingScheme.avoidsLabel_iff]
    intro word hword letter hletter heq
    subst c
    apply hc
    simp only [Finset.mem_union, Multiset.mem_toFinset,
      LabellingScheme.mem_labels_iff]
    exact Or.inl ⟨word, hword, letter.2, hletter⟩
  · intro hforbidden
    apply hc
    exact Finset.mem_union_right scheme.labels.toFinset hforbidden

/-- Helper for Lemma 77.1: formal inversion preserves avoidance of an unsigned label. -/
private theorem forallFstNe_invRev_iff {α : Type u}
    (letters : List (α × Bool)) (c : α) :
    (∀ letter ∈ FreeGroup.invRev letters, letter.1 ≠ c) ↔
      ∀ letter ∈ letters, letter.1 ≠ c := by
  -- Membership in `invRev` is membership in the sign-negated list, read backwards.
  constructor
  · intro h letter hletter
    apply h (letter.1, !letter.2)
    rw [FreeGroup.invRev, List.mem_reverse]
    exact List.mem_map.mpr ⟨letter, hletter, rfl⟩
  · intro h letter hletter
    rw [FreeGroup.invRev, List.mem_reverse] at hletter
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hletter
    exact h original horiginal

/-- Helper for Lemma 77.1: swapping two absent labels fixes a signed-letter list. -/
private theorem mapSwapLabels_eq_self_of_avoids {α : Type u}
    (letters : List (α × Bool)) (a c : α)
    (ha : ∀ letter ∈ letters, letter.1 ≠ a)
    (hc : ∀ letter ∈ letters, letter.1 ≠ c) :
    letters.map (fun letter ↦ (swapLabels a c letter.1, letter.2)) = letters := by
  classical
  -- Induct pointwise; the transposition fixes every head away from its endpoints.
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

/-- Helper for Lemma 77.1: reversing a label absent from a list fixes that list. -/
private theorem mapReverseSignAt_eq_self_of_avoids {α : Type u}
    (letters : List (α × Bool)) (a : α)
    (ha : ∀ letter ∈ letters, letter.1 ≠ a) :
    letters.map (reverseSignAt a) = letters := by
  classical
  -- The conditional sign reversal takes its false branch at every letter.
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head ∈ head :: tail := List.mem_cons_self
      have htail : ∀ letter ∈ tail, letter.1 ≠ a := by
        intro letter hletter
        exact ha letter (List.mem_cons_of_mem head hletter)
      rw [List.map_cons, ih htail]
      simp only [reverseSignAt, if_neg (ha head hhead)]

/-- Helper for Lemma 77.1: the two displayed equal signed letters exhaust their
unsigned label in every residual fragment of a proper singleton scheme. -/
private theorem fragmentsAvoidLabelOfRepeatedSignedLetter {α : Type u}
    (word : PolygonWord α) (y₀ y₁ y₂ : List (α × Bool)) (a : α × Bool)
    (h_proper : ({word} : LabellingScheme α).Proper)
    (h_decomp : word.1 = y₀ ++ [a] ++ y₁ ++ [a] ++ y₂) :
    (∀ letter ∈ y₀, letter.1 ≠ a.1) ∧
      (∀ letter ∈ y₁, letter.1 ≠ a.1) ∧
      ∀ letter ∈ y₂, letter.1 ≠ a.1 := by
  classical
  -- Properness makes the total multiplicity of the displayed label exactly two.
  have haMem : a.1 ∈ ({word} : LabellingScheme α).labels := by
    rw [LabellingScheme.mem_labels_iff]
    have hwordMem : word ∈ ({word} : LabellingScheme α) := by simp
    refine ⟨word, hwordMem, a.2, ?_⟩
    rw [h_decomp]
    simp
  have haCount := LabellingScheme.proper_iff.mp h_proper a.1 haMem
  have haWordCount : (word.1.map Prod.fst).count a.1 = 2 := by
    simpa [LabellingScheme.labels] using haCount
  rw [h_decomp] at haWordCount
  simp only [List.map_append, List.map_cons, List.map_nil, List.count_append,
    List.count_cons, List.count_nil, beq_self_eq_true, ite_true] at haWordCount
  have hy₀Count : (y₀.map Prod.fst).count a.1 = 0 := by omega
  have hy₁Count : (y₁.map Prod.fst).count a.1 = 0 := by omega
  have hy₂Count : (y₂.map Prod.fst).count a.1 = 0 := by omega
  -- A residual occurrence would give a positive count in its corresponding fragment.
  constructor
  · intro letter hletter heq
    apply List.not_mem_of_count_eq_zero hy₀Count
    have hlabel : letter.1 = a.1 := heq
    exact List.mem_map.mpr ⟨letter, hletter, hlabel⟩
  constructor
  · intro letter hletter heq
    apply List.not_mem_of_count_eq_zero hy₁Count
    have hlabel : letter.1 = a.1 := heq
    exact List.mem_map.mpr ⟨letter, hletter, hlabel⟩
  · intro letter hletter heq
    apply List.not_mem_of_count_eq_zero hy₂Count
    have hlabel : letter.1 = a.1 := heq
    exact List.mem_map.mpr ⟨letter, hletter, hlabel⟩

/-- Helper for Lemma 77.1: a cyclic rotation induces an elementary equivalence
between singleton schemes. -/
private theorem equivalentOfIsRotated {α : Type u} (word rotated : PolygonWord α)
    (h : List.IsRotated word.1 rotated.1) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {rotated} := by
  -- Package the list rotation as a singleton permutation step.
  exact LabellingScheme.Equivalent.ofElementary (.permute (.of word rotated 0 h))

/-- Helper for Lemma 77.1: formally inverting a polygon word is an elementary
equivalence of singleton schemes. -/
private theorem equivalentFormalInverse {α : Type u} (word : PolygonWord α) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {word.formalInverse} := by
  -- Select the unique polygon word for the flip operation.
  exact LabellingScheme.Equivalent.ofElementary (.flip (.of word 0))

/-- Helper for Lemma 77.1: the concrete formal inverse has underlying list
`FreeGroup.invRev word.1`. -/
private theorem formalInverse_val_eq_invRev {α : Type u} (word : PolygonWord α) :
    word.formalInverse.1 = FreeGroup.invRev word.1 := by
  -- Commute mapping with reversal to match the canonical free-group spelling.
  rw [PolygonWord.formalInverse_val, FreeGroup.invRev, List.map_reverse]

/-- Helper for Lemma 77.1: reversing all occurrences of one label is an elementary
equivalence of singleton schemes. -/
private theorem equivalentReverseLabel {α : Type u} (word : PolygonWord α) (a : α) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {word.reverseLabel a} := by
  -- Compute the map of a singleton after applying the elementary sign reversal.
  have hstep := LabellingScheme.Equivalent.ofElementary
    (.reverse ({word} : LabellingScheme α) a)
  simpa only [LabellingScheme.reverseLabel, Multiset.map_singleton] using hstep

/-- Helper for Lemma 77.1: a computed fresh transposition gives an elementary
equivalence between singleton schemes. -/
private theorem equivalentRenameLabel {α : Type u} (word target : PolygonWord α)
    (a c : α) (h_ne : a ≠ c)
    (h_fresh : ({word} : LabellingScheme α).AvoidsLabel c)
    (hword : word.relabel (swapLabels a c) = target) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {target} := by
  -- Rewrite the endpoint of the elementary rename using the word-level computation.
  have hstep := LabellingScheme.Equivalent.ofElementary
    (.rename ({word} : LabellingScheme α) a c h_ne h_fresh)
  simpa only [LabellingScheme.renameLabel, LabellingScheme.relabel,
    Multiset.map_singleton, hword] using hstep

/-- Helper for Lemma 77.1: if the fragments on both sides of two equal signed
letters are nonempty, cut–flip–paste moves the pair to the front. -/
private theorem equivalentPairAtFrontOfNonempty {α : Type u} [Infinite α]
    (word target : PolygonWord α) (middle suffix : List (α × Bool))
    (a : α × Bool)
    (h_source : word.1 = [a] ++ middle ++ [a] ++ suffix)
    (h_target : target.1 = [a, a] ++ FreeGroup.invRev middle ++ suffix)
    (hmiddle : middle ≠ []) (hsuffix : suffix ≠ [])
    (hmiddleAvoid : ∀ letter ∈ middle, letter.1 ≠ a.1)
    (hsuffixAvoid : ∀ letter ∈ suffix, letter.1 ≠ a.1) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {target} := by
  classical
  obtain ⟨p, sign⟩ := a
  -- Choose the auxiliary cut label away from the complete source scheme.
  obtain ⟨c, hc, _⟩ := existsAvoidedLabelOutside
    ({word} : LabellingScheme α) ∅
  have hwordMem : word ∈ ({word} : LabellingScheme α) := by simp
  have hcWord : ∀ letter ∈ word.1, letter.1 ≠ c :=
    LabellingScheme.avoidsLabel_iff.mp hc word hwordMem
  have ha_ne_c : p ≠ c := by
    apply hcWord (p, sign)
    rw [h_source]
    simp
  have hc_ne_a : c ≠ p := Ne.symm ha_ne_c
  have hmiddleFreshC : ∀ letter ∈ middle, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_source]
    simp [hletter]
  have hsuffixFreshC : ∀ letter ∈ suffix, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_source]
    simp [hletter]
  have hinverseAvoid :
      ∀ letter ∈ FreeGroup.invRev middle, letter.1 ≠ p :=
    (forallFstNe_invRev_iff middle p).mpr hmiddleAvoid
  have hinverseFreshC :
      ∀ letter ∈ FreeGroup.invRev middle, letter.1 ≠ c :=
    (forallFstNe_invRev_iff middle c).mpr hmiddleFreshC
  have hzeroC : (0 : LabellingScheme α).AvoidsLabel c := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro remaining hremaining
    simp at hremaining
  have hzeroA : (0 : LabellingScheme α).AvoidsLabel p := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro remaining hremaining
    simp at hremaining
  -- Record all length obligations before constructing the intermediate polygon words.
  have hmiddleLength : 0 < middle.length := List.length_pos_of_ne_nil hmiddle
  have hsuffixLength : 0 < suffix.length := List.length_pos_of_ne_nil hsuffix
  have hleftLength : 2 ≤ ((p, sign) :: middle).length := by
    simp only [List.length_cons]
    omega
  have hrightLength : 2 ≤ ((p, sign) :: suffix).length := by
    simp only [List.length_cons]
    omega
  have hpasteLeftLength :
      2 ≤ ((c, sign) :: FreeGroup.invRev middle).length := by
    simp only [List.length_cons, FreeGroup.invRev_length]
    omega
  have hpasteRightLength : 2 ≤ (suffix ++ [(c, sign)]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hfreshTargetLength :
      3 ≤ ([(c, sign), (c, sign)] ++ FreeGroup.invRev middle ++ suffix).length := by
    have hlength := target.property
    rw [h_target] at hlength
    simp only [List.length_append, List.length_cons, List.length_nil,
      FreeGroup.invRev_length] at hlength ⊢
    omega
  let normalized : PolygonWord α :=
    ⟨((p, sign) :: middle) ++ ((p, sign) :: suffix),
      PolygonWord.append_length ((p, sign) :: middle) ((p, sign) :: suffix)
        hleftLength hrightLength⟩
  let firstCut : PolygonWord α :=
    ⟨((p, sign) :: middle) ++ [(c, !sign)],
      PolygonWord.appendLetter_length
        ((p, sign) :: middle) (c, !sign) hleftLength⟩
  let secondCut : PolygonWord α :=
    ⟨(c, sign) :: ((p, sign) :: suffix),
      PolygonWord.consLetter_length
        (c, sign) ((p, sign) :: suffix) hrightLength⟩
  let pasteFirst : PolygonWord α :=
    ⟨((c, sign) :: FreeGroup.invRev middle) ++ [(p, !sign)],
      PolygonWord.appendLetter_length
        ((c, sign) :: FreeGroup.invRev middle) (p, !sign) hpasteLeftLength⟩
  let pasteSecond : PolygonWord α :=
    ⟨(p, sign) :: (suffix ++ [(c, sign)]),
      PolygonWord.consLetter_length (p, sign)
        (suffix ++ [(c, sign)]) hpasteRightLength⟩
  let pasted : PolygonWord α :=
    ⟨((c, sign) :: FreeGroup.invRev middle) ++ (suffix ++ [(c, sign)]),
      PolygonWord.append_length ((c, sign) :: FreeGroup.invRev middle)
        (suffix ++ [(c, sign)]) hpasteLeftLength hpasteRightLength⟩
  let freshTarget : PolygonWord α :=
    ⟨[(c, sign), (c, sign)] ++ FreeGroup.invRev middle ++ suffix,
      hfreshTargetLength⟩
  -- Identify the source normalization and the flipped first cut word propositionally.
  have hnormalized : normalized = word := by
    apply Subtype.ext
    simpa only [normalized, List.singleton_append, List.append_assoc] using h_source.symm
  have hflippedFirst : firstCut.formalInverse = pasteFirst := by
    apply Subtype.ext
    simp only [PolygonWord.formalInverse_val, firstCut, pasteFirst]
    simp [FreeGroup.invRev, List.map_reverse, List.map_append]
  have hsecondRotation : List.IsRotated secondCut.1 pasteSecond.1 := by
    have hrotation := List.isRotated_append
      (l := [(c, sign)]) (l' := (p, sign) :: suffix)
    simpa [secondCut, pasteSecond, List.append_assoc] using hrotation
  have hpastedRotation : List.IsRotated pasted.1 freshTarget.1 := by
    have hrotation := List.isRotated_append
      (l := (c, sign) :: FreeGroup.invRev middle ++ suffix)
      (l' := [(c, sign)])
    simpa [pasted, freshTarget, List.append_assoc] using hrotation
  -- Execute cut, flip, rotation, paste, and the final rotation as elementary steps.
  have hleftFreshC :
      ∀ letter ∈ (p, sign) :: middle, letter.1 ≠ c := by
    intro letter hletter
    rcases List.mem_cons.mp hletter with hletter | hletter
    · simpa only [hletter, Prod.fst] using ha_ne_c
    · exact hmiddleFreshC letter hletter
  have hrightFreshC :
      ∀ letter ∈ (p, sign) :: suffix, letter.1 ≠ c := by
    intro letter hletter
    rcases List.mem_cons.mp hletter with hletter | hletter
    · simpa only [hletter, Prod.fst] using ha_ne_c
    · exact hsuffixFreshC letter hletter
  have hcutConstruction := LabellingScheme.Cut.of
    ((p, sign) :: middle) ((p, sign) :: suffix) c sign 0
    hleftLength hrightLength hleftFreshC hrightFreshC hzeroC
  have hcut : LabellingScheme.Equivalent ({word} : LabellingScheme α)
      (firstCut ::ₘ secondCut ::ₘ 0) := by
    rw [← hnormalized]
    simpa only [Multiset.cons_zero] using
      LabellingScheme.Equivalent.ofElementary (.cut hcutConstruction)
  have hflip : LabellingScheme.Equivalent
      (firstCut ::ₘ secondCut ::ₘ 0) (pasteFirst ::ₘ secondCut ::ₘ 0) := by
    have hstep := LabellingScheme.Equivalent.ofElementary
      (.flip (.of firstCut (secondCut ::ₘ 0)))
    rwa [hflippedFirst] at hstep
  have hrotateSecond : LabellingScheme.Equivalent
      (pasteFirst ::ₘ secondCut ::ₘ 0) (pasteFirst ::ₘ pasteSecond ::ₘ 0) := by
    have hstep := LabellingScheme.Equivalent.ofElementary
      (.permute (.of secondCut pasteSecond (pasteFirst ::ₘ 0) hsecondRotation))
    rw [Multiset.cons_swap pasteFirst secondCut 0,
      Multiset.cons_swap pasteFirst pasteSecond 0]
    exact hstep
  have hpasteLeftFresh :
      ∀ letter ∈ (c, sign) :: FreeGroup.invRev middle, letter.1 ≠ p := by
    intro letter hletter
    rcases List.mem_cons.mp hletter with hletter | hletter
    · simpa only [hletter, Prod.fst] using hc_ne_a
    · exact hinverseAvoid letter hletter
  have hpasteRightFresh :
      ∀ letter ∈ suffix ++ [(c, sign)], letter.1 ≠ p := by
    intro letter hletter
    rcases List.mem_append.mp hletter with hletter | hletter
    · exact hsuffixAvoid letter hletter
    · simp only [List.mem_singleton] at hletter
      simpa only [hletter, Prod.fst] using hc_ne_a
  have hpasteConstruction := LabellingScheme.Paste.of
    ((c, sign) :: FreeGroup.invRev middle) (suffix ++ [(c, sign)])
    p sign 0 hpasteLeftLength hpasteRightLength
    hpasteLeftFresh hpasteRightFresh hzeroA
  have hpaste : LabellingScheme.Equivalent
      (pasteFirst ::ₘ pasteSecond ::ₘ 0) ({pasted} : LabellingScheme α) := by
    have hpasteStep : LabellingScheme.Paste
        (pasteFirst ::ₘ pasteSecond ::ₘ 0) (pasted ::ₘ 0) := by
      simpa only [pasteFirst, pasteSecond, pasted, List.append_assoc] using
        hpasteConstruction
    simpa only [Multiset.cons_zero] using
      LabellingScheme.Equivalent.ofElementary (.paste hpasteStep)
  have hrotatePasted : LabellingScheme.Equivalent
      ({pasted} : LabellingScheme α) {freshTarget} :=
    equivalentOfIsRotated pasted freshTarget hpastedRotation
  -- The fresh pair is renamed to the original label while all residual letters stay fixed.
  have hfreshAvoidA : ({freshTarget} : LabellingScheme α).AvoidsLabel p := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro onlyWord hmem
    simp only [Multiset.mem_singleton] at hmem
    subst onlyWord
    intro letter hletter
    simp only [freshTarget, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hletter
    rcases hletter with ((hletter | hletter) | hletter) | hletter
    · simpa only [hletter, Prod.fst] using hc_ne_a
    · simpa only [hletter, Prod.fst] using hc_ne_a
    · exact hinverseAvoid letter hletter
    · exact hsuffixAvoid letter hletter
  have hfixInverse :
      (FreeGroup.invRev middle).map
          (fun letter ↦ (swapLabels c p letter.1, letter.2)) =
        FreeGroup.invRev middle :=
    mapSwapLabels_eq_self_of_avoids (FreeGroup.invRev middle) c p
      hinverseFreshC hinverseAvoid
  have hfixSuffix :
      suffix.map (fun letter ↦ (swapLabels c p letter.1, letter.2)) = suffix :=
    mapSwapLabels_eq_self_of_avoids suffix c p hsuffixFreshC hsuffixAvoid
  have hrenameWord : freshTarget.relabel (swapLabels c p) = target := by
    apply Subtype.ext
    rw [PolygonWord.relabel_val, h_target]
    simp only [freshTarget, List.map_append, List.map_cons, List.map_nil,
      hfixInverse, hfixSuffix]
    simp only [swapLabels, Equiv.swap_apply_left]
  have hrename : LabellingScheme.Equivalent
      ({freshTarget} : LabellingScheme α) {target} :=
    equivalentRenameLabel freshTarget target c p hc_ne_a hfreshAvoidA hrenameWord
  exact hcut.trans (hflip.trans
    (hrotateSecond.trans (hpaste.trans (hrotatePasted.trans hrename))))

/-- Helper for Lemma 77.1: when the suffix is empty, flipping and reversing the
repeated label puts its equal signed occurrences at the front. -/
private theorem equivalentPairAtFrontOfEmptySuffix {α : Type u}
    (word target : PolygonWord α) (middle : List (α × Bool)) (a : α × Bool)
    (h_source : word.1 = [a] ++ middle ++ [a])
    (h_target : target.1 = [a, a] ++ FreeGroup.invRev middle)
    (hmiddleAvoid : ∀ letter ∈ middle, letter.1 ≠ a.1) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {target} := by
  classical
  obtain ⟨p, sign⟩ := a
  let flipped := word.formalInverse
  let oriented := flipped.reverseLabel p
  have hflippedValue : flipped.1 =
      [(p, !sign)] ++ FreeGroup.invRev middle ++ [(p, !sign)] := by
    dsimp only [flipped]
    rw [formalInverse_val_eq_invRev, h_source]
    simp [FreeGroup.invRev]
  have hinverseAvoid :
      ∀ letter ∈ FreeGroup.invRev middle, letter.1 ≠ p :=
    (forallFstNe_invRev_iff middle p).mpr hmiddleAvoid
  have hfixInverse :
      (FreeGroup.invRev middle).map (reverseSignAt p) =
        FreeGroup.invRev middle :=
    mapReverseSignAt_eq_self_of_avoids (FreeGroup.invRev middle) p hinverseAvoid
  have horientedValue : oriented.1 =
      [(p, sign)] ++ FreeGroup.invRev middle ++ [(p, sign)] := by
    dsimp only [oriented]
    rw [PolygonWord.reverseLabel_val, hflippedValue]
    simp only [List.map_append, List.map_cons, List.map_nil, hfixInverse]
    simp [reverseSignAt]
  have hrotation : List.IsRotated oriented.1 target.1 := by
    have hrotate := List.isRotated_append
      (l := [(p, sign)] ++ FreeGroup.invRev middle)
      (l' := [(p, sign)])
    have htargetValue : target.1 =
        (p, sign) :: (p, sign) :: FreeGroup.invRev middle := by
      rw [h_target]
      simp only [List.cons_append, List.nil_append]
    rw [horientedValue, htargetValue]
    simpa only [List.singleton_append, List.append_assoc] using hrotate
  -- Compose the flip, the sign normalization, and the final cyclic rotation.
  exact (equivalentFormalInverse word).trans
    ((equivalentReverseLabel flipped p).trans
      (equivalentOfIsRotated oriented target hrotation))

/-- Helper for Lemma 77.1: the mirrored cut–flip–paste configuration sends
`prefix a middle a` to `aa middle prefix⁻¹` when both fragments are nonempty. -/
private theorem equivalentPairAtEndOfNonempty {α : Type u} [Infinite α]
    (word target : PolygonWord α) (firstFragment middle : List (α × Bool))
    (a : α × Bool)
    (h_source : word.1 = firstFragment ++ [a] ++ middle ++ [a])
    (h_target : target.1 = [a, a] ++ middle ++ FreeGroup.invRev firstFragment)
    (hfirstFragment : firstFragment ≠ []) (hmiddle : middle ≠ [])
    (hfirstFragmentAvoid : ∀ letter ∈ firstFragment, letter.1 ≠ a.1)
    (hmiddleAvoid : ∀ letter ∈ middle, letter.1 ≠ a.1) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α) {target} := by
  classical
  obtain ⟨p, sign⟩ := a
  let flipped := word.formalInverse
  let oriented := flipped.reverseLabel p
  have hflippedValue : flipped.1 =
      [(p, !sign)] ++ FreeGroup.invRev middle ++ [(p, !sign)] ++
        FreeGroup.invRev firstFragment := by
    dsimp only [flipped]
    rw [formalInverse_val_eq_invRev, h_source]
    simp [FreeGroup.invRev, List.append_assoc]
  have hinversePrefixAvoid :
      ∀ letter ∈ FreeGroup.invRev firstFragment, letter.1 ≠ p :=
    (forallFstNe_invRev_iff firstFragment p).mpr hfirstFragmentAvoid
  have hinverseMiddleAvoid :
      ∀ letter ∈ FreeGroup.invRev middle, letter.1 ≠ p :=
    (forallFstNe_invRev_iff middle p).mpr hmiddleAvoid
  have hfixPrefix :
      (FreeGroup.invRev firstFragment).map (reverseSignAt p) =
        FreeGroup.invRev firstFragment :=
    mapReverseSignAt_eq_self_of_avoids
      (FreeGroup.invRev firstFragment) p hinversePrefixAvoid
  have hfixMiddle :
      (FreeGroup.invRev middle).map (reverseSignAt p) =
        FreeGroup.invRev middle :=
    mapReverseSignAt_eq_self_of_avoids
      (FreeGroup.invRev middle) p hinverseMiddleAvoid
  have horientedValue : oriented.1 =
      [(p, sign)] ++ FreeGroup.invRev middle ++ [(p, sign)] ++
        FreeGroup.invRev firstFragment := by
    dsimp only [oriented]
    rw [PolygonWord.reverseLabel_val, hflippedValue]
    simp only [List.map_append, List.map_cons, List.map_nil, hfixPrefix, hfixMiddle]
    simp [reverseSignAt]
  have hinversePrefix : FreeGroup.invRev firstFragment ≠ [] := by
    intro hinverse
    have hlength := congrArg List.length hinverse
    simp only [FreeGroup.invRev_length, List.length_nil] at hlength
    exact hfirstFragment (List.length_eq_zero_iff.mp hlength)
  have hinverseMiddle : FreeGroup.invRev middle ≠ [] := by
    intro hinverse
    have hlength := congrArg List.length hinverse
    simp only [FreeGroup.invRev_length, List.length_nil] at hlength
    exact hmiddle (List.length_eq_zero_iff.mp hlength)
  have htargetForOriented : target.1 =
      [(p, sign), (p, sign)] ++
        FreeGroup.invRev (FreeGroup.invRev middle) ++
          FreeGroup.invRev firstFragment := by
    rw [h_target, FreeGroup.invRev_invRev]
  have hfront := equivalentPairAtFrontOfNonempty oriented target
    (FreeGroup.invRev middle) (FreeGroup.invRev firstFragment) (p, sign)
    horientedValue htargetForOriented hinverseMiddle hinversePrefix
    hinverseMiddleAvoid hinversePrefixAvoid
  -- Flip and normalize signs before applying the already-proved front surgery.
  exact (equivalentFormalInverse word).trans
    ((equivalentReverseLabel flipped p).trans hfront)

/-- Helper for Lemma 77.1: with nonempty outer fragments, the first cut–flip–paste
exchange replaces the original pair by a fresh pair surrounding `y₁ ++ y₀⁻¹`. -/
private theorem existsEquivalentFreshExchange {α : Type u} [Infinite α]
    (word : PolygonWord α) (y₀ y₁ y₂ : List (α × Bool)) (a : α × Bool)
    (h_source : word.1 = y₁ ++ [a] ++ y₂ ++ y₀ ++ [a])
    (hy₀ : y₀ ≠ []) (hy₂ : y₂ ≠ [])
    (hy₀Avoid : ∀ letter ∈ y₀, letter.1 ≠ a.1)
    (hy₁Avoid : ∀ letter ∈ y₁, letter.1 ≠ a.1)
    (hy₂Avoid : ∀ letter ∈ y₂, letter.1 ≠ a.1) :
    ∃ c : α, ∃ exchanged : PolygonWord α,
      c ≠ a.1 ∧
        LabellingScheme.Equivalent ({word} : LabellingScheme α) {exchanged} ∧
        exchanged.1 =
          [(c, a.2)] ++ y₁ ++ FreeGroup.invRev y₀ ++ [(c, a.2)] ++ y₂ ∧
        (∀ letter ∈ y₁ ++ FreeGroup.invRev y₀, letter.1 ≠ c) ∧
        ∀ letter ∈ y₂, letter.1 ≠ c := by
  classical
  obtain ⟨p, sign⟩ := a
  -- Choose one cut label fresh for the whole original singleton scheme.
  obtain ⟨c, hc, _⟩ := existsAvoidedLabelOutside
    ({word} : LabellingScheme α) ∅
  have hwordMem : word ∈ ({word} : LabellingScheme α) := by simp
  have hcWord : ∀ letter ∈ word.1, letter.1 ≠ c :=
    LabellingScheme.avoidsLabel_iff.mp hc word hwordMem
  have hp_ne_c : p ≠ c := by
    apply hcWord (p, sign)
    rw [h_source]
    simp
  have hc_ne_p : c ≠ p := Ne.symm hp_ne_c
  have hy₀FreshC : ∀ letter ∈ y₀, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_source]
    simp [hletter]
  have hy₁FreshC : ∀ letter ∈ y₁, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_source]
    simp [hletter]
  have hy₂FreshC : ∀ letter ∈ y₂, letter.1 ≠ c := by
    intro letter hletter
    apply hcWord letter
    rw [h_source]
    simp [hletter]
  have hinverseY₀Avoid :
      ∀ letter ∈ FreeGroup.invRev y₀, letter.1 ≠ p :=
    (forallFstNe_invRev_iff y₀ p).mpr hy₀Avoid
  have hinverseY₀FreshC :
      ∀ letter ∈ FreeGroup.invRev y₀, letter.1 ≠ c :=
    (forallFstNe_invRev_iff y₀ c).mpr hy₀FreshC
  have hzeroC : (0 : LabellingScheme α).AvoidsLabel c := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro remaining hremaining
    simp at hremaining
  have hzeroP : (0 : LabellingScheme α).AvoidsLabel p := by
    rw [LabellingScheme.avoidsLabel_iff]
    intro remaining hremaining
    simp at hremaining
  -- The two nonempty fragments supply every cut and paste length obligation.
  have hy₀Length : 0 < y₀.length := List.length_pos_of_ne_nil hy₀
  have hy₂Length : 0 < y₂.length := List.length_pos_of_ne_nil hy₂
  have hleftLength : 2 ≤ (y₁ ++ [(p, sign)] ++ y₂).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hrightLength : 2 ≤ (y₀ ++ [(p, sign)]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hpasteLeftLength : 2 ≤ (y₂ ++ [(c, sign)] ++ y₁).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hpasteRightLength :
      2 ≤ (FreeGroup.invRev y₀ ++ [(c, sign)]).length := by
    simp only [List.length_append, List.length_singleton, FreeGroup.invRev_length]
    omega
  have hexchangedLength :
      3 ≤ ([(c, sign)] ++ y₁ ++ FreeGroup.invRev y₀ ++
        [(c, sign)] ++ y₂).length := by
    have hlength := word.property
    rw [h_source] at hlength
    simp only [List.length_append, List.length_cons, List.length_nil,
      FreeGroup.invRev_length] at hlength ⊢
    omega
  let normalized : PolygonWord α :=
    ⟨(y₁ ++ [(p, sign)] ++ y₂) ++ (y₀ ++ [(p, sign)]),
      PolygonWord.append_length (y₁ ++ [(p, sign)] ++ y₂)
        (y₀ ++ [(p, sign)]) hleftLength hrightLength⟩
  let firstCut : PolygonWord α :=
    ⟨(y₁ ++ [(p, sign)] ++ y₂) ++ [(c, sign)],
      PolygonWord.appendLetter_length (y₁ ++ [(p, sign)] ++ y₂)
        (c, sign) hleftLength⟩
  let secondCut : PolygonWord α :=
    ⟨(c, !sign) :: (y₀ ++ [(p, sign)]),
      PolygonWord.consLetter_length (c, !sign)
        (y₀ ++ [(p, sign)]) hrightLength⟩
  let pasteFirst : PolygonWord α :=
    ⟨(y₂ ++ [(c, sign)] ++ y₁) ++ [(p, sign)],
      PolygonWord.appendLetter_length (y₂ ++ [(c, sign)] ++ y₁)
        (p, sign) hpasteLeftLength⟩
  let pasteSecond : PolygonWord α :=
    ⟨(p, !sign) :: (FreeGroup.invRev y₀ ++ [(c, sign)]),
      PolygonWord.consLetter_length (p, !sign)
        (FreeGroup.invRev y₀ ++ [(c, sign)]) hpasteRightLength⟩
  let pasted : PolygonWord α :=
    ⟨(y₂ ++ [(c, sign)] ++ y₁) ++
        (FreeGroup.invRev y₀ ++ [(c, sign)]),
      PolygonWord.append_length (y₂ ++ [(c, sign)] ++ y₁)
        (FreeGroup.invRev y₀ ++ [(c, sign)])
        hpasteLeftLength hpasteRightLength⟩
  let exchanged : PolygonWord α :=
    ⟨[(c, sign)] ++ y₁ ++ FreeGroup.invRev y₀ ++ [(c, sign)] ++ y₂,
      hexchangedLength⟩
  -- Compute the two rotations and the flipped second cut word.
  have hnormalized : normalized = word := by
    apply Subtype.ext
    simpa only [normalized, List.append_assoc] using h_source.symm
  have hflippedSecond : secondCut.formalInverse = pasteSecond := by
    apply Subtype.ext
    rw [formalInverse_val_eq_invRev]
    simp [secondCut, pasteSecond, FreeGroup.invRev]
  have hfirstRotation : List.IsRotated firstCut.1 pasteFirst.1 := by
    have hrotation := List.isRotated_append
      (l := y₁ ++ [(p, sign)]) (l' := y₂ ++ [(c, sign)])
    simpa only [firstCut, pasteFirst, List.append_assoc] using hrotation
  have hpastedRotation : List.IsRotated pasted.1 exchanged.1 := by
    have hrotation := List.isRotated_append
      (l := y₂)
      (l' := [(c, sign)] ++ y₁ ++ FreeGroup.invRev y₀ ++ [(c, sign)])
    simpa only [pasted, exchanged, List.append_assoc] using hrotation
  have hleftFreshC :
      ∀ letter ∈ y₁ ++ [(p, sign)] ++ y₂, letter.1 ≠ c := by
    intro letter hletter
    simp only [List.mem_append, List.mem_singleton] at hletter
    rcases hletter with (hletter | hletter) | hletter
    · exact hy₁FreshC letter hletter
    · simpa only [hletter, Prod.fst] using hp_ne_c
    · exact hy₂FreshC letter hletter
  have hrightFreshC :
      ∀ letter ∈ y₀ ++ [(p, sign)], letter.1 ≠ c := by
    intro letter hletter
    rcases List.mem_append.mp hletter with hletter | hletter
    · exact hy₀FreshC letter hletter
    · simp only [List.mem_singleton] at hletter
      simpa only [hletter, Prod.fst] using hp_ne_c
  have hcutConstruction := LabellingScheme.Cut.of
    (y₁ ++ [(p, sign)] ++ y₂) (y₀ ++ [(p, sign)]) c (!sign) 0
    hleftLength hrightLength hleftFreshC hrightFreshC hzeroC
  have hcut : LabellingScheme.Equivalent ({word} : LabellingScheme α)
      (firstCut ::ₘ secondCut ::ₘ 0) := by
    rw [← hnormalized]
    have hstep := LabellingScheme.Equivalent.ofElementary (.cut hcutConstruction)
    simpa only [firstCut, secondCut, Bool.not_not, Multiset.cons_zero] using hstep
  have hflipSecond : LabellingScheme.Equivalent
      (firstCut ::ₘ secondCut ::ₘ 0) (firstCut ::ₘ pasteSecond ::ₘ 0) := by
    have hstep := LabellingScheme.Equivalent.ofElementary
      (.flip (.of secondCut (firstCut ::ₘ 0)))
    rw [hflippedSecond] at hstep
    rw [Multiset.cons_swap firstCut secondCut 0,
      Multiset.cons_swap firstCut pasteSecond 0]
    exact hstep
  have hrotateFirst : LabellingScheme.Equivalent
      (firstCut ::ₘ pasteSecond ::ₘ 0) (pasteFirst ::ₘ pasteSecond ::ₘ 0) :=
    LabellingScheme.Equivalent.ofElementary
      (.permute (.of firstCut pasteFirst (pasteSecond ::ₘ 0) hfirstRotation))
  have hpasteLeftFresh :
      ∀ letter ∈ y₂ ++ [(c, sign)] ++ y₁, letter.1 ≠ p := by
    intro letter hletter
    simp only [List.mem_append, List.mem_singleton] at hletter
    rcases hletter with (hletter | hletter) | hletter
    · exact hy₂Avoid letter hletter
    · simpa only [hletter, Prod.fst] using hc_ne_p
    · exact hy₁Avoid letter hletter
  have hpasteRightFresh :
      ∀ letter ∈ FreeGroup.invRev y₀ ++ [(c, sign)], letter.1 ≠ p := by
    intro letter hletter
    rcases List.mem_append.mp hletter with hletter | hletter
    · exact hinverseY₀Avoid letter hletter
    · simp only [List.mem_singleton] at hletter
      simpa only [hletter, Prod.fst] using hc_ne_p
  have hpasteConstruction := LabellingScheme.Paste.of
    (y₂ ++ [(c, sign)] ++ y₁) (FreeGroup.invRev y₀ ++ [(c, sign)])
    p (!sign) 0 hpasteLeftLength hpasteRightLength
    hpasteLeftFresh hpasteRightFresh hzeroP
  have hpaste : LabellingScheme.Equivalent
      (pasteFirst ::ₘ pasteSecond ::ₘ 0) ({pasted} : LabellingScheme α) := by
    have hpasteStep : LabellingScheme.Paste
        (pasteFirst ::ₘ pasteSecond ::ₘ 0) (pasted ::ₘ 0) := by
      simpa only [pasteFirst, pasteSecond, pasted, Bool.not_not,
        List.append_assoc] using hpasteConstruction
    simpa only [Multiset.cons_zero] using
      LabellingScheme.Equivalent.ofElementary (.paste hpasteStep)
  have hrotatePasted : LabellingScheme.Equivalent
      ({pasted} : LabellingScheme α) {exchanged} :=
    equivalentOfIsRotated pasted exchanged hpastedRotation
  have hexchange : LabellingScheme.Equivalent
      ({word} : LabellingScheme α) {exchanged} :=
    hcut.trans (hflipSecond.trans (hrotateFirst.trans (hpaste.trans hrotatePasted)))
  have hmiddleFreshC :
      ∀ letter ∈ y₁ ++ FreeGroup.invRev y₀, letter.1 ≠ c := by
    intro letter hletter
    rcases List.mem_append.mp hletter with hletter | hletter
    · exact hy₁FreshC letter hletter
    · exact hinverseY₀FreshC letter hletter
  have hexchangedValue : exchanged.1 =
      [(c, sign)] ++ y₁ ++ FreeGroup.invRev y₀ ++ [(c, sign)] ++ y₂ := rfl
  exact ⟨c, exchanged, hc_ne_p, hexchange, hexchangedValue,
    hmiddleFreshC, hy₂FreshC⟩

/-- Lemma 77.1: A proper polygon scheme with two equal signed letters is equivalent to the
scheme obtained by moving them to the front and formally inverting the intervening fragment. -/
theorem equivalent_pairFront {α : Type u} [Infinite α]
    (word : PolygonWord α) (y₀ y₁ y₂ : List (α × Bool)) (a : α × Bool)
    (h_proper : ({word} : LabellingScheme α).Proper)
    (h_decomp : word.1 = y₀ ++ [a] ++ y₁ ++ [a] ++ y₂) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({pairFront word y₀ y₁ y₂ a h_decomp} : LabellingScheme α) := by
  classical
  let target := pairFront word y₀ y₁ y₂ a h_decomp
  have htarget : target.1 = [a, a] ++ y₀ ++ FreeGroup.invRev y₁ ++ y₂ := by
    exact pairFront_val word y₀ y₁ y₂ a h_decomp
  have hfragments := fragmentsAvoidLabelOfRepeatedSignedLetter
    word y₀ y₁ y₂ a h_proper h_decomp
  rcases hfragments with ⟨hy₀Avoid, hy₁Avoid, hy₂Avoid⟩
  -- Empty outer fragments give the immediate and one-stage source configurations.
  by_cases hy₀ : y₀ = []
  · subst y₀
    by_cases hy₁ : y₁ = []
    · subst y₁
      have hwordTarget : word = target := by
        apply Subtype.ext
        rw [h_decomp, htarget]
        simp
      have hscheme : ({word} : LabellingScheme α) = {target} :=
        congrArg (fun polygonWord ↦ ({polygonWord} : LabellingScheme α)) hwordTarget
      have hresult : LabellingScheme.Equivalent
          ({word} : LabellingScheme α) {target} := by
        rw [hscheme]
        exact LabellingScheme.Equivalent.refl ({target} : LabellingScheme α)
      exact hresult
    · by_cases hy₂ : y₂ = []
      · subst y₂
        have hsource : word.1 = [a] ++ y₁ ++ [a] := by
          simpa only [List.nil_append, List.append_nil] using h_decomp
        have htargetEmpty : target.1 = [a, a] ++ FreeGroup.invRev y₁ := by
          simpa only [List.nil_append, List.append_nil] using htarget
        exact equivalentPairAtFrontOfEmptySuffix word target y₁ a
          hsource htargetEmpty hy₁Avoid
      · have hsource : word.1 = [a] ++ y₁ ++ [a] ++ y₂ := by
          simpa only [List.nil_append] using h_decomp
        have htargetFront : target.1 =
            [a, a] ++ FreeGroup.invRev y₁ ++ y₂ := by
          simpa only [List.nil_append, List.append_nil] using htarget
        exact equivalentPairAtFrontOfNonempty word target y₁ y₂ a
          hsource htargetFront hy₁ hy₂ hy₁Avoid hy₂Avoid
  · by_cases hy₂ : y₂ = []
    · subst y₂
      by_cases hy₁ : y₁ = []
      · subst y₁
        have hrotation : List.IsRotated word.1 target.1 := by
          have hrotate := List.isRotated_append (l := y₀) (l' := [a, a])
          rw [h_decomp, htarget]
          simpa [List.append_assoc] using hrotate
        exact equivalentOfIsRotated word target hrotation
      · -- Rotate to `y₁ a y₀ a`, then use the mirrored one-stage surgery.
        have hrotatedLength : 3 ≤ (y₁ ++ [a] ++ y₀ ++ [a]).length := by
          have hlength := word.property
          rw [h_decomp] at hlength
          simp only [List.length_append, List.length_cons, List.length_nil] at hlength ⊢
          omega
        let rotated : PolygonWord α := ⟨y₁ ++ [a] ++ y₀ ++ [a], hrotatedLength⟩
        have hrotation : List.IsRotated word.1 rotated.1 := by
          have hrotate := List.isRotated_append
            (l := y₀ ++ [a]) (l' := y₁ ++ [a])
          rw [h_decomp]
          simpa only [rotated, List.append_nil, List.append_assoc] using hrotate
        have hrotatedSource : rotated.1 = y₁ ++ [a] ++ y₀ ++ [a] := rfl
        have htargetEnd : target.1 =
            [a, a] ++ y₀ ++ FreeGroup.invRev y₁ := by
          simpa only [List.append_nil] using htarget
        have hend := equivalentPairAtEndOfNonempty rotated target y₁ y₀ a
          hrotatedSource htargetEnd hy₁ hy₀ hy₁Avoid hy₀Avoid
        exact (equivalentOfIsRotated word rotated hrotation).trans hend
    · -- In the general case, perform Figure 77.2's first exchange after one rotation.
      have hrotatedLength :
          3 ≤ (y₁ ++ [a] ++ y₂ ++ y₀ ++ [a]).length := by
        have hlength := word.property
        rw [h_decomp] at hlength
        simp only [List.length_append, List.length_cons, List.length_nil] at hlength ⊢
        omega
      let rotated : PolygonWord α :=
        ⟨y₁ ++ [a] ++ y₂ ++ y₀ ++ [a], hrotatedLength⟩
      have hrotation : List.IsRotated word.1 rotated.1 := by
        have hrotate := List.isRotated_append
          (l := y₀ ++ [a]) (l' := y₁ ++ [a] ++ y₂)
        rw [h_decomp]
        simpa only [rotated, List.append_assoc] using hrotate
      have hrotatedSource : rotated.1 =
          y₁ ++ [a] ++ y₂ ++ y₀ ++ [a] := rfl
      obtain ⟨c, exchanged, hc_ne_a, hexchange, hexchangedValue,
          hmiddleFreshC, hy₂FreshC⟩ :=
        existsEquivalentFreshExchange rotated y₀ y₁ y₂ a
          hrotatedSource hy₀ hy₂ hy₀Avoid hy₁Avoid hy₂Avoid
      have hinverseY₀FreshC :
          ∀ letter ∈ FreeGroup.invRev y₀, letter.1 ≠ c := by
        intro letter hletter
        apply hmiddleFreshC letter
        exact List.mem_append_right y₁ hletter
      have hy₀FreshC : ∀ letter ∈ y₀, letter.1 ≠ c :=
        (forallFstNe_invRev_iff y₀ c).mp hinverseY₀FreshC
      have hy₁FreshC : ∀ letter ∈ y₁, letter.1 ≠ c := by
        intro letter hletter
        apply hmiddleFreshC letter
        exact List.mem_append_left (FreeGroup.invRev y₀) hletter
      have hinverseY₁FreshC :
          ∀ letter ∈ FreeGroup.invRev y₁, letter.1 ≠ c :=
        (forallFstNe_invRev_iff y₁ c).mpr hy₁FreshC
      have hinverseY₁Avoid :
          ∀ letter ∈ FreeGroup.invRev y₁, letter.1 ≠ a.1 :=
        (forallFstNe_invRev_iff y₁ a.1).mpr hy₁Avoid
      have hmiddleNonempty : y₁ ++ FreeGroup.invRev y₀ ≠ [] := by
        intro hnil
        have hlength := congrArg List.length hnil
        simp only [List.length_append, FreeGroup.invRev_length, List.length_nil] at hlength
        have hy₀Length : y₀.length = 0 := by omega
        exact hy₀ (List.length_eq_zero_iff.mp hy₀Length)
      have hfreshFrontLength :
          3 ≤ ([(c, a.2), (c, a.2)] ++ y₀ ++
            FreeGroup.invRev y₁ ++ y₂).length := by
        have hlength := target.property
        rw [htarget] at hlength
        simp only [List.length_append, List.length_cons, List.length_nil,
          FreeGroup.invRev_length] at hlength ⊢
        omega
      let freshFront : PolygonWord α :=
        ⟨[(c, a.2), (c, a.2)] ++ y₀ ++ FreeGroup.invRev y₁ ++ y₂,
          hfreshFrontLength⟩
      have hfreshFrontTarget : freshFront.1 =
          [(c, a.2), (c, a.2)] ++
            FreeGroup.invRev (y₁ ++ FreeGroup.invRev y₀) ++ y₂ := by
        simp only [freshFront, FreeGroup.invRev_append,
          FreeGroup.invRev_invRev, List.append_assoc]
      have hsecondExchange := equivalentPairAtFrontOfNonempty
        exchanged freshFront (y₁ ++ FreeGroup.invRev y₀) y₂ (c, a.2)
        hexchangedValue hfreshFrontTarget hmiddleNonempty hy₂
        hmiddleFreshC hy₂FreshC
      -- Rename the fresh front pair back to `a`; every residual fragment is fixed.
      have hc_ne_a : c ≠ a.1 := hc_ne_a
      have hfreshAvoidA : ({freshFront} : LabellingScheme α).AvoidsLabel a.1 := by
        rw [LabellingScheme.avoidsLabel_iff]
        intro onlyWord hmem
        simp only [Multiset.mem_singleton] at hmem
        subst onlyWord
        intro letter hletter
        simp only [freshFront, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hletter
        rcases hletter with (((hletter | hletter) | hletter) | hletter) | hletter
        · simpa only [hletter, Prod.fst] using hc_ne_a
        · simpa only [hletter, Prod.fst] using hc_ne_a
        · exact hy₀Avoid letter hletter
        · exact hinverseY₁Avoid letter hletter
        · exact hy₂Avoid letter hletter
      have hfixY₀ :
          y₀.map (fun letter ↦ (swapLabels c a.1 letter.1, letter.2)) = y₀ :=
        mapSwapLabels_eq_self_of_avoids y₀ c a.1 hy₀FreshC hy₀Avoid
      have hfixInverseY₁ :
          (FreeGroup.invRev y₁).map
              (fun letter ↦ (swapLabels c a.1 letter.1, letter.2)) =
            FreeGroup.invRev y₁ :=
        mapSwapLabels_eq_self_of_avoids (FreeGroup.invRev y₁) c a.1
          hinverseY₁FreshC hinverseY₁Avoid
      have hfixY₂ :
          y₂.map (fun letter ↦ (swapLabels c a.1 letter.1, letter.2)) = y₂ :=
        mapSwapLabels_eq_self_of_avoids y₂ c a.1 hy₂FreshC hy₂Avoid
      have hrenameWord : freshFront.relabel (swapLabels c a.1) = target := by
        apply Subtype.ext
        rw [PolygonWord.relabel_val, htarget]
        simp only [freshFront, List.map_append, List.map_cons, List.map_nil,
          hfixY₀, hfixInverseY₁, hfixY₂]
        simp only [swapLabels, Equiv.swap_apply_left]
      have hrename := equivalentRenameLabel freshFront target c a.1
        hc_ne_a hfreshAvoidA hrenameWord
      have hgeneral := (equivalentOfIsRotated word rotated hrotation).trans
        (hexchange.trans (hsecondExchange.trans hrename))
      simpa only [target] using hgeneral

end PolygonWord
