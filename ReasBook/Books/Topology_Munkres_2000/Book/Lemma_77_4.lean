module

public import Topology_Munkres_2000.Book.Lemma_77_1
import all Topology_Munkres_2000.Book.Definition_77_1.Proper

public section

universe u

namespace PolygonWord

/-- The explicit `aabbcc` replacement has the minimum length required of a polygon word. -/
theorem pairCommutator_length {α : Type u} (w₀ w₁ : List (α × Bool)) (a b c : α) :
    3 ≤ (w₀ ++ [(a, true), (a, true), (b, true), (b, true), (c, true),
      (c, true)] ++ w₁).length := by
  simp
  omega

/-- The polygon word obtained by replacing `ccaba⁻¹b⁻¹` with `aabbcc`. -/
@[expose]
def pairCommutator {α : Type u} (w₀ w₁ : List (α × Bool)) (a b c : α) :
    PolygonWord α :=
  ⟨w₀ ++ [(a, true), (a, true), (b, true), (b, true), (c, true), (c, true)] ++ w₁,
    pairCommutator_length w₀ w₁ a b c⟩

/-- The signed-label list underlying `pairCommutator`. -/
@[simp]
theorem pairCommutator_val {α : Type u} (w₀ w₁ : List (α × Bool)) (a b c : α) :
    (pairCommutator w₀ w₁ a b c).1 =
      w₀ ++ [(a, true), (a, true), (b, true), (b, true), (c, true), (c, true)] ++ w₁ :=
  rfl

/-- Helper for Lemma 77.4: a cyclic rotation of polygon words induces an equivalence
of their singleton labelling schemes. -/
private theorem equivalentSingletonOfIsRotated {α : Type u}
    (source target : PolygonWord α)
    (hrotated : List.IsRotated source.1 target.1) :
    LabellingScheme.Equivalent ({source} : LabellingScheme α) {target} := by
  -- Package the rotation as the permutation elementary step on the unique word.
  exact LabellingScheme.Equivalent.ofElementary
    (.permute (.of source target 0 hrotated))

/-- Helper for Lemma 77.4: cyclic rotation preserves the unsigned labels of a
singleton polygon scheme. -/
private theorem singletonLabels_eq_of_isRotated {α : Type u}
    (source target : PolygonWord α)
    (hrotated : List.IsRotated source.1 target.1) :
    ({target} : LabellingScheme α).labels = ({source} : LabellingScheme α).labels := by
  -- Forget signs after using the list permutation underlying the rotation.
  simp only [LabellingScheme.labels, Multiset.singleton_bind]
  exact Multiset.coe_eq_coe.mpr (hrotated.perm.map Prod.fst).symm

/-- Helper for Lemma 77.4: formal inversion preserves the multiset of unsigned
labels in a signed-letter list. -/
private theorem invRev_labels {α : Type u} (letters : List (α × Bool)) :
    ((FreeGroup.invRev letters).map Prod.fst : Multiset α) =
      (letters.map Prod.fst : Multiset α) := by
  -- Sign negation disappears under `Prod.fst`, and reversal disappears in a multiset.
  simp [FreeGroup.invRev, Function.comp_def]

/-- Helper for Lemma 77.4: moving a repeated signed letter to the front preserves
the unsigned-label multiset. -/
private theorem pairFront_labels {α : Type u} (word : PolygonWord α)
    (y₀ y₁ y₂ : List (α × Bool)) (letter : α × Bool)
    (hdecomp : word.1 = y₀ ++ [letter] ++ y₁ ++ [letter] ++ y₂) :
    ({pairFront word y₀ y₁ y₂ letter hdecomp} : LabellingScheme α).labels =
      ({word} : LabellingScheme α).labels := by
  -- Expand only the value interface; formal inversion changes signs and order, not labels.
  simp only [LabellingScheme.labels, Multiset.singleton_bind, pairFront_val,
    hdecomp, List.map_append, List.map_cons, List.map_nil]
  simp only [← Multiset.coe_add]
  rw [invRev_labels]
  ac_rfl

/-- Helper for Lemma 77.4: equality of unsigned-label multisets transports
properness between singleton polygon schemes. -/
private theorem properSingletonOfLabelsEq {α : Type u}
    (before after : PolygonWord α)
    (hlabels : ({after} : LabellingScheme α).labels =
      ({before} : LabellingScheme α).labels)
    (hproper : ({before} : LabellingScheme α).Proper) :
    ({after} : LabellingScheme α).Proper := by
  -- Rewrite both the membership premise and the required decomposition invariant.
  intro label hlabel
  rw [hlabels] at hlabel ⊢
  exact hproper label hlabel

/-- Helper for Lemma 77.4: the six-letter interleaving used in the source
calculation satisfies the polygon-word length bound. -/
private theorem interleavedPair_length {α : Type u} (tail : List (α × Bool))
    (a b c : α) :
    3 ≤ ([(a, true), (b, true), (c, true), (b, true), (a, true),
      (c, true)] ++ tail).length := by
  -- The displayed prefix alone already has six letters.
  simp

/-- Lemma 77.4: A proper polygon scheme containing the consecutive blocks `cc` and
`aba⁻¹b⁻¹` is equivalent to the scheme obtained by replacing them with `aabbcc`. -/
theorem equivalent_pairCommutator {α : Type u} [Infinite α]
    (word : PolygonWord α) (w₀ w₁ : List (α × Bool)) (a b c : α)
    (hproper : ({word} : LabellingScheme α).Proper)
    (hdecomp : word.1 = w₀ ++ [(c, true), (c, true), (a, true), (b, true),
      (a, false), (b, false)] ++ w₁) :
    LabellingScheme.Equivalent ({word} : LabellingScheme α)
      ({pairCommutator w₀ w₁ a b c} : LabellingScheme α) := by
  let tail := w₁ ++ w₀
  let interleaved : PolygonWord α :=
    ⟨[(a, true), (b, true), (c, true), (b, true), (a, true), (c, true)] ++ tail,
      interleavedPair_length tail a b c⟩
  -- Read Lemma 77.1 backwards at the two `c` occurrences.
  have hcDecomp : interleaved.1 =
      [(a, true), (b, true)] ++ [(c, true)] ++
        [(b, true), (a, true)] ++ [(c, true)] ++ tail := by
    rfl
  let cFront := pairFront interleaved [(a, true), (b, true)]
    [(b, true), (a, true)] tail (c, true) hcDecomp
  have hcFrontVal : cFront.1 =
      [(c, true), (c, true), (a, true), (b, true), (a, false), (b, false)] ++
        tail := by
    simp only [cFront, pairFront_val, FreeGroup.invRev, List.map_cons,
      List.map_nil, List.reverse_cons, List.reverse_nil, Bool.not_true,
      List.nil_append, List.cons_append]
  have hinitialRotation : List.IsRotated word.1 cFront.1 := by
    rw [hdecomp, hcFrontVal]
    simpa only [tail, List.append_assoc] using
      (List.isRotated_append (l := w₀)
        (l' := [(c, true), (c, true), (a, true), (b, true),
          (a, false), (b, false)] ++ w₁))
  have hinterleavedLabels :
      ({interleaved} : LabellingScheme α).labels =
        ({word} : LabellingScheme α).labels :=
    (pairFront_labels interleaved [(a, true), (b, true)]
      [(b, true), (a, true)] tail (c, true) hcDecomp).symm.trans
        (singletonLabels_eq_of_isRotated word cFront hinitialRotation)
  have hinterleavedProper : ({interleaved} : LabellingScheme α).Proper :=
    properSingletonOfLabelsEq word interleaved hinterleavedLabels hproper
  have hfirstExtraction : LabellingScheme.Equivalent
      ({interleaved} : LabellingScheme α) {cFront} :=
    equivalent_pairFront interleaved [(a, true), (b, true)]
      [(b, true), (a, true)] tail (c, true) hinterleavedProper hcDecomp
  -- Apply Lemma 77.1 forward at the two `b` occurrences.
  have hbDecomp : interleaved.1 =
      [(a, true)] ++ [(b, true)] ++ [(c, true)] ++ [(b, true)] ++
        [(a, true), (c, true)] ++ tail := by
    rfl
  let bFront := pairFront interleaved [(a, true)] [(c, true)]
    ([(a, true), (c, true)] ++ tail) (b, true) hbDecomp
  have hbFrontVal : bFront.1 =
      [(b, true), (b, true), (a, true), (c, false), (a, true), (c, true)] ++
        tail := by
    simp only [bFront, pairFront_val, FreeGroup.invRev, List.map_cons,
      List.map_nil, List.reverse_cons, List.reverse_nil, Bool.not_true,
      List.nil_append, List.cons_append]
  have hsecondExtraction : LabellingScheme.Equivalent
      ({interleaved} : LabellingScheme α) {bFront} :=
    equivalent_pairFront interleaved [(a, true)] [(c, true)]
      ([(a, true), (c, true)] ++ tail) (b, true) hinterleavedProper hbDecomp
  have hbFrontProper : ({bFront} : LabellingScheme α).Proper :=
    properSingletonOfLabelsEq interleaved bFront
      (pairFront_labels interleaved [(a, true)] [(c, true)]
        ([(a, true), (c, true)] ++ tail) (b, true) hbDecomp)
      hinterleavedProper
  -- A third application at the two `a` occurrences yields `aabbcc` at the front.
  have haDecomp : bFront.1 =
      [(b, true), (b, true)] ++ [(a, true)] ++ [(c, false)] ++
        [(a, true)] ++ [(c, true)] ++ tail := by
    simpa only [hbFrontVal]
  let aFront := pairFront bFront [(b, true), (b, true)] [(c, false)]
    ([(c, true)] ++ tail) (a, true) haDecomp
  have haFrontVal : aFront.1 =
      [(a, true), (a, true), (b, true), (b, true), (c, true), (c, true)] ++
        tail := by
    simp only [aFront, pairFront_val, FreeGroup.invRev, List.map_cons,
      List.map_nil, List.reverse_cons, List.reverse_nil, Bool.not_false,
      List.nil_append, List.cons_append]
  have hthirdExtraction : LabellingScheme.Equivalent
      ({bFront} : LabellingScheme α) {aFront} :=
    equivalent_pairFront bFront [(b, true), (b, true)] [(c, false)]
      ([(c, true)] ++ tail) (a, true) hbFrontProper haDecomp
  -- Rotate the normalized block past `w₀` and assemble the source calculation.
  have hfinalRotation : List.IsRotated aFront.1 (pairCommutator w₀ w₁ a b c).1 := by
    rw [haFrontVal, pairCommutator_val]
    simpa only [tail, List.append_assoc] using
      (List.isRotated_append
        (l := [(a, true), (a, true), (b, true), (b, true),
          (c, true), (c, true)] ++ w₁) (l' := w₀))
  exact (equivalentSingletonOfIsRotated word cFront hinitialRotation).trans
    (hfirstExtraction.symm.trans
      (hsecondExtraction.trans
        (hthirdExtraction.trans
          (equivalentSingletonOfIsRotated aFront
            (pairCommutator w₀ w₁ a b c) hfinalRotation))))


end PolygonWord
