module

public import Topology_Munkres_2000.Book.Lemma_77_3
public import Mathlib.Data.List.Cycle

public section

universe u

namespace PolygonWord

/-- Helper for Lemma 77.5: the signed letters of a torus-type polygon word are distinct. -/
private lemma TorusType.nodup {α : Type u} {word : PolygonWord α}
    (hword : word.TorusType) : word.1.Nodup := by
  classical
  -- Work through multisets so signed counts use one canonical decidable equality instance.
  have hmultiset : (word.1 : Multiset (α × Bool)).Nodup := by
    rw [Multiset.nodup_iff_count_eq_one]
    intro letter hletter
    obtain ⟨label, sign⟩ := letter
    have hlabel : label ∈ ({word} : LabellingScheme α).labels := by
      rw [LabellingScheme.mem_labels_iff]
      have hwordMem : word ∈ ({word} : LabellingScheme α) := by
        simp
      exact ⟨word, hwordMem, sign, hletter⟩
    exact PolygonWord.torusType_iff_count.mp hword label hlabel sign
  exact Multiset.coe_nodup.mp hmultiset

/-- Helper for Lemma 77.5: cyclic noncancellation for a torus-type word forces
ordinary adjacent labels to be distinct. -/
private lemma TorusType.isChainDistinctLabels {α : Type u} {word : PolygonWord α}
    (hword : word.TorusType)
    (hcycle : Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.1) :
    word.1.IsChain (fun x y : α × Bool ↦ x.1 ≠ y.1) := by
  have hnonempty : word.1 ≠ [] := by
    intro hempty
    have hlength := word.property
    rw [hempty] at hlength
    simp at hlength
  obtain ⟨head, tail, hletters⟩ := List.exists_cons_of_ne_nil hnonempty
  have hcycleAtHead : Cycle.Chain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) (head :: tail) := by
    simpa only [hletters] using hcycle
  have hcyclicLinear : (head :: (tail ++ [head])).IsChain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) := by
    exact Cycle.chain_coe_cons
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) head tail |>.mp hcycleAtHead
  have hlinear : (head :: tail).IsChain
      (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) := by
    have happended : ((head :: tail) ++ [head]).IsChain
        (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) := by
      simpa only [List.cons_append] using hcyclicLinear
    exact happended.left_of_append
  have hnodup : (head :: tail).Nodup := by
    simpa only [hletters] using hword.nodup
  rw [hletters, List.isChain_iff_forall_rel_of_append_cons_cons]
  intro left right before after hsplit
  have hrelation :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hlinear hsplit
  rcases hrelation with hlabels | hsigns
  · exact hlabels
  · -- Equal labels together with equal signs would repeat a signed letter.
    have htailNodup : (left :: right :: after).Nodup := by
      rw [hsplit] at hnodup
      exact hnodup.of_append_right
    have hleftFresh : left ∉ right :: after :=
      (List.nodup_cons.mp htailNodup).1
    intro hlabels
    have hpairs : left = right := Prod.ext hlabels hsigns
    apply hleftFresh
    rw [hpairs]
    exact List.mem_cons_self

/-- Lemma 77.5 (1): A torus-type polygon word with no cyclically adjacent oppositely signed
occurrences of one label is equivalent to a same-length word beginning with a commutator block
and followed by an empty or torus-type residual word. -/
theorem existsEquivalentCommutatorOfTorusType {α : Type u} [Infinite α]
    (word : PolygonWord α)
    (htorus : word.TorusType)
    (hadjacent : Cycle.Chain (fun x y : α × Bool ↦ x.1 ≠ y.1 ∨ x.2 = y.2) word.1) :
    ∃ normalized : PolygonWord α,
      ∃ _form : TorusHandleForm normalized [] word.1.length,
        LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} := by
  -- Use the torus hypotheses to supply the properness and linear-chain interface.
  have hproper : ({word} : LabellingScheme α).Proper := htorus.proper
  have hdecomp : word.1 = [] ++ word.1 := by
    simp only [List.nil_append]
  have hchain : word.1.IsChain (fun x y : α × Bool ↦ x.1 ≠ y.1) :=
    htorus.isChainDistinctLabels hadjacent
  -- The handle-normalization theorem now has exactly the requested empty prefix.
  exact existsEquivalentTorusHandle word word [] hproper hdecomp htorus hchain

/-- Helper for Lemma 77.5: if a polygon word is equivalent to a duplicated projective prefix
followed by a torus-type tail of the same total length, and adjacent terms in that tail have
distinct labels, then it is equivalent to a same-length word preserving the prefix, followed
by a commutator block and an empty or torus-type residual word. -/
theorem existsEquivalentProjectivePrefixCommutator {α : Type u} [Infinite α]
    (word : PolygonWord α)
    (pairs : List (α × Bool)) (tailWord model : PolygonWord α)
    (_hpairs : pairs ≠ []) (hproper : ({model} : LabellingScheme α).Proper)
    (hmodel : model.1 = pairs.flatMap (fun letter ↦ [letter, letter]) ++ tailWord.1)
    (_hlength : model.1.length = word.1.length)
    (hequivalent : LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({model} : LabellingScheme α))
    (htorus : tailWord.TorusType)
    (hadjacent : tailWord.1.IsChain (fun x y : α × Bool ↦ x.1 ≠ y.1)) :
    ∃ normalized : PolygonWord α,
      ∃ _form : TorusHandleForm normalized
          (pairs.flatMap (fun letter ↦ [letter, letter])) tailWord.1.length,
        LabellingScheme.Equivalent ({word} : LabellingScheme α) {normalized} := by
  -- Normalize the supplied proper model while preserving its duplicated prefix.
  obtain ⟨normalized, form, hnormalized⟩ :=
    existsEquivalentTorusHandle model tailWord
      (pairs.flatMap (fun letter ↦ [letter, letter]))
      hproper hmodel htorus hadjacent
  -- Compose the given equivalence with the model's handle normalization.
  have hresult : LabellingScheme.Equivalent
      ({word} : LabellingScheme α) {normalized} :=
    hequivalent.trans hnormalized
  exact ⟨normalized, form, hresult⟩

end PolygonWord
