module

public import Topology_Munkres_2000.Book.Exercise_57_4
public import Topology_Munkres_2000.Book.Remark_50_3.CubicalIncidence

public import Topology_Munkres_2000.Book.Theorem_57_6.BoundaryRidgeMate
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin

public section

namespace StandardSphere
namespace CubicalTucker

/-- Helper for Theorem 57.6: a face is alternating from `initial` when its
vertices can be ordered by strictly increasing unsigned labels with alternating
signs. -/
def IsAlternatingFace {V : Type*} {r ℓ : ℕ} (initial : Bool)
    (label : V → Fin ℓ × Bool) (face : Fin r → V) : Prop :=
  ∃ (vertexOrder : Equiv.Perm (Fin r)) (unsignedOrder : Fin r ↪o Fin ℓ),
    ∀ j, label (face (vertexOrder j)) =
      (unsignedOrder j, if Even j.1 then initial else !initial)

/-- Helper for Theorem 57.6: the mod-two indicator of an alternating signed
face. -/
noncomputable def alternatingFaceWeight {V : Type*} {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool) (face : Fin r → V) :
    ZMod 2 :=
  @ite (ZMod 2) (IsAlternatingFace initial label face)
    (Classical.dec _) 1 0

/-- Helper for Theorem 57.6: the alternating face weight is one exactly for
an alternating signed face. -/
theorem alternatingFaceWeight_eq_one_iff {V : Type*} {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool) (face : Fin r → V) :
    alternatingFaceWeight initial label face = 1 ↔
      IsAlternatingFace initial label face := by
  -- Evaluate the indicator in the two cases of its defining proposition.
  by_cases halternating : IsAlternatingFace initial label face
  · simp [alternatingFaceWeight, halternating]
  · simp [alternatingFaceWeight, halternating]

/-- Helper for Theorem 57.6: being alternating is independent of the chosen
enumeration of a face's vertices. -/
theorem isAlternatingFace_reindex {V : Type*} {r ℓ : ℕ} (initial : Bool)
    (label : V → Fin ℓ × Bool) (face : Fin r → V)
    (reindex : Equiv.Perm (Fin r)) :
    IsAlternatingFace initial label (fun j ↦ face (reindex j)) ↔
      IsAlternatingFace initial label face := by
  -- Compose the witnessing vertex order with the reindexing permutation.
  constructor
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨reindex * vertexOrder, unsignedOrder, ?_⟩
    intro j
    simpa only [Equiv.Perm.mul_apply] using halternating j
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨reindex.symm * vertexOrder, unsignedOrder, ?_⟩
    intro j
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using halternating j

/-- Helper for Theorem 57.6: alternating face weight is invariant under a
permutation of the vertex enumeration. -/
theorem alternatingFaceWeight_reindex {V : Type*} {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool) (face : Fin r → V)
    (reindex : Equiv.Perm (Fin r)) :
    alternatingFaceWeight initial label (fun j ↦ face (reindex j)) =
      alternatingFaceWeight initial label face := by
  -- Rewrite both indicators using the reindexing-invariant proposition.
  have hreindex := isAlternatingFace_reindex initial label face reindex
  by_cases halternating : IsAlternatingFace initial label face
  · have hreindexed := hreindex.mpr halternating
    simp [alternatingFaceWeight, halternating, hreindexed]
  · have hreindexed :
        ¬IsAlternatingFace initial label (fun j ↦ face (reindex j)) :=
      fun h ↦ halternating (hreindex.mp h)
    simp [alternatingFaceWeight, halternating, hreindexed]

/-- Helper for Theorem 57.6: an injective enumeration and another enumeration
of the same finite image differ by a permutation of their common index type. -/
private theorem existsPermCompOfInjectiveImageEq
    {V : Type*} [DecidableEq V] {r : ℕ} (f g : Fin r → V)
    (hf : Function.Injective f)
    (himage : Finset.univ.image f = Finset.univ.image g) :
    ∃ reindex : Equiv.Perm (Fin r), f = g ∘ reindex := by
  classical
  -- Match each value of `f` with an index of `g` using equality of the images.
  have hmatching : ∀ i, ∃ j, g j = f i := by
    intro i
    have hmem : f i ∈ Finset.univ.image g := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    exact ⟨j, hj⟩
  choose reindex hreindex using hmatching
  -- Injectivity of `f` makes the chosen index map, and hence the matching, bijective.
  have hreindexInjective : Function.Injective reindex := by
    intro i j hij
    apply hf
    calc
      f i = g (reindex i) := (hreindex i).symm
      _ = g (reindex j) := congrArg g hij
      _ = f j := hreindex j
  have hreindexBijective : Function.Bijective reindex :=
    (Fintype.bijective_iff_injective_and_card reindex).2
      ⟨hreindexInjective, by simp⟩
  let permutation : Equiv.Perm (Fin r) :=
    Equiv.ofBijective reindex hreindexBijective
  refine ⟨permutation, ?_⟩
  funext i
  simpa only [Function.comp_apply, permutation, Equiv.ofBijective_apply] using
    (hreindex i).symm

/-- Helper for Theorem 57.6: alternating-face weight depends only on the
unordered image of an injective finite vertex enumeration. -/
theorem alternatingFaceWeight_eq_of_injective_image_eq
    {V : Type*} [DecidableEq V] {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool) (f g : Fin r → V)
    (hf : Function.Injective f)
    (himage : Finset.univ.image f = Finset.univ.image g) :
    alternatingFaceWeight initial label f =
      alternatingFaceWeight initial label g := by
  -- Recover the reindexing permutation, then apply the canonical weight API.
  obtain ⟨reindex, hface⟩ :=
    existsPermCompOfInjectiveImageEq f g hf himage
  calc
    alternatingFaceWeight initial label f =
        alternatingFaceWeight initial label (fun j ↦ g (reindex j)) := by
      exact congrArg (alternatingFaceWeight initial label) hface
    _ = alternatingFaceWeight initial label g :=
      alternatingFaceWeight_reindex initial label g reindex

/-- Helper for Theorem 57.6: a permutation preserves inequality from a
chosen omitted position. -/
theorem perm_ne_iff_image_ne {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x a : Fin (n + 1)) : a ≠ x ↔ p a ≠ p x := by
  -- Reflect inequality through injectivity of the permutation.
  exact p.injective.ne_iff.symm

/-- Helper for Theorem 57.6: restrict a permutation to the complements of a
chosen point and its image. -/
def omitPerm {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1)) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv x).trans
    ((Equiv.subtypeEquiv p (perm_ne_iff_image_ne p x)).trans
      (finSuccAboveEquiv (p x)).symm)

/-- Helper for Theorem 57.6: restricting a permutation makes the two
omitted-point enumerations commute. -/
theorem omitPerm_succAbove {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1)) (j : Fin n) :
    (p x).succAbove (omitPerm p x j) = p (x.succAbove j) := by
  -- Pass through the canonical equivalence between `Fin n` and a complement.
  change ((finSuccAboveEquiv (p x)) (omitPerm p x j)).1 = _
  simp only [omitPerm, Equiv.trans_apply, Equiv.apply_symm_apply,
    finSuccAboveEquiv_apply]
  rfl

/-- Helper for Theorem 57.6: an alternating nonempty face has an endpoint
deletion with the same initial sign and weight one. -/
theorem exists_omit_alternatingFaceWeight_eq_one_of_isAlternatingFace
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V) (halternating : IsAlternatingFace initial label face) :
    ∃ k : Fin (r + 1),
      alternatingFaceWeight initial label (fun j ↦ face (k.succAbove j)) = 1 := by
  obtain ⟨vertexOrder, unsignedOrder, hlabels⟩ := halternating
  let k : Fin (r + 1) := vertexOrder (Fin.last r)
  -- Delete the largest vertex in unsigned-label order and restrict both orders.
  refine ⟨k, (alternatingFaceWeight_eq_one_iff _ _ _).2 ?_⟩
  refine ⟨omitPerm vertexOrder (Fin.last r),
    Fin.castSuccOrderEmb.trans unsignedOrder, ?_⟩
  intro j
  dsimp only [k]
  rw [omitPerm_succAbove, Fin.succAbove_last, hlabels j.castSucc]
  rfl

/-- Helper for Theorem 57.6: an alternating face uses each unsigned label at
most once. -/
theorem IsAlternatingFace.unsignedLabel_injective
    {V : Type*} {r ℓ : ℕ} {initial : Bool} {label : V → Fin ℓ × Bool}
    {face : Fin r → V} (halternating : IsAlternatingFace initial label face) :
    Function.Injective (fun j ↦ (label (face j)).1) := by
  obtain ⟨vertexOrder, unsignedOrder, hlabels⟩ := halternating
  have hordered (j : Fin r) :
      (label (face (vertexOrder j))).1 = unsignedOrder j :=
    congrArg Prod.fst (hlabels j)
  -- Compare two labels after transporting their vertices into sorted order.
  intro j k hlabel
  apply vertexOrder.symm.injective
  apply unsignedOrder.injective
  calc
    unsignedOrder (vertexOrder.symm j) = (label (face j)).1 := by
      simpa only [vertexOrder.apply_symm_apply] using
        (hordered (vertexOrder.symm j)).symm
    _ = (label (face k)).1 := hlabel
    _ = unsignedOrder (vertexOrder.symm k) := by
      simpa only [vertexOrder.apply_symm_apply] using
        hordered (vertexOrder.symm k)

/-- Helper for Theorem 57.6: pointwise equality of signed labels preserves
the alternating-face predicate. -/
theorem isAlternatingFace_congr_labels
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face₁ face₂ : Fin r → V)
    (hlabel : ∀ j, label (face₁ j) = label (face₂ j)) :
    IsAlternatingFace initial label face₁ ↔
      IsAlternatingFace initial label face₂ := by
  -- Keep the same vertex and unsigned-label orders, changing only the labels
  -- attached to the enumerated vertices.
  constructor
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨vertexOrder, unsignedOrder, ?_⟩
    intro j
    exact (hlabel (vertexOrder j)).symm.trans (halternating j)
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨vertexOrder, unsignedOrder, ?_⟩
    intro j
    exact (hlabel (vertexOrder j)).trans (halternating j)

/-- Helper for Theorem 57.6: pointwise complementation of the sign labels
toggles the initial sign of an alternating face. -/
theorem isAlternatingFace_complement_labels
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face₁ face₂ : Fin r → V)
    (hlabel : ∀ j, label (face₂ j) =
      ((label (face₁ j)).1, !(label (face₁ j)).2)) :
    IsAlternatingFace initial label face₂ ↔
      IsAlternatingFace (!initial) label face₁ := by
  -- Retain both ordering witnesses; Boolean case analysis converts the
  -- complemented alternating pattern into the pattern starting at `!initial`.
  constructor
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨vertexOrder, unsignedOrder, ?_⟩
    intro j
    have hcomplement := hlabel (vertexOrder j)
    have hface₂ := halternating j
    rcases hface₁Value : label (face₁ (vertexOrder j)) with ⟨u₁, b₁⟩
    rcases hface₂Value : label (face₂ (vertexOrder j)) with ⟨u₂, b₂⟩
    by_cases heven : Even j.1
    · simp only [hface₁Value, hface₂Value, heven, if_pos] at hcomplement hface₂ ⊢
      cases initial <;> cases b₁ <;> cases b₂ <;> simp_all
    · simp only [hface₁Value, hface₂Value, heven] at hcomplement hface₂ ⊢
      cases initial <;> cases b₁ <;> cases b₂ <;> simp_all
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨vertexOrder, unsignedOrder, ?_⟩
    intro j
    have hcomplement := hlabel (vertexOrder j)
    have hface₁ := halternating j
    rcases hface₁Value : label (face₁ (vertexOrder j)) with ⟨u₁, b₁⟩
    rcases hface₂Value : label (face₂ (vertexOrder j)) with ⟨u₂, b₂⟩
    by_cases heven : Even j.1
    · simp only [hface₁Value, hface₂Value, heven, if_pos] at hcomplement hface₁ ⊢
      cases initial <;> cases b₁ <;> cases b₂ <;> simp_all
    · simp only [hface₁Value, hface₂Value, heven] at hcomplement hface₁ ⊢
      cases initial <;> cases b₁ <;> cases b₂ <;> simp_all

/-- Helper for Theorem 57.6: pointwise sign complementation transports the
mod-two alternating-face indicator while toggling its initial sign. -/
theorem alternatingFaceWeight_complement_labels
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face₁ face₂ : Fin r → V)
    (hlabel : ∀ j, label (face₂ j) =
      ((label (face₁ j)).1, !(label (face₁ j)).2)) :
    alternatingFaceWeight initial label face₂ =
      alternatingFaceWeight (!initial) label face₁ := by
  -- Evaluate both indicators using the preceding equivalence of propositions.
  have halternating :=
    isAlternatingFace_complement_labels initial label face₁ face₂ hlabel
  by_cases hface₂ : IsAlternatingFace initial label face₂
  · have hface₁ := halternating.mp hface₂
    simp [alternatingFaceWeight, hface₁, hface₂]
  · have hface₁ : ¬IsAlternatingFace (!initial) label face₁ :=
      fun h ↦ hface₂ (halternating.mpr h)
    simp [alternatingFaceWeight, hface₁, hface₂]

/-- Helper for Theorem 57.6: an alternating deletion from a face with one more
vertex than unsigned labels has a unique other vertex with the deleted label. -/
private theorem existsUnique_duplicateUnsignedLabel_of_omit_alternating
    {V : Type*} {d : ℕ} (initial : Bool) (label : V → Fin d × Bool)
    (face : Fin (d + 1) → V) (k : Fin (d + 1))
    (halternating : IsAlternatingFace initial label
      (fun j ↦ face (k.succAbove j))) :
    ∃! l : Fin (d + 1),
      l ≠ k ∧ (label (face l)).1 = (label (face k)).1 := by
  -- The retained unsigned-label map is an injection between equal finite types,
  -- so it hits the label of the omitted vertex.
  let retainedLabel : Fin d → Fin d :=
    fun j ↦ (label (face (k.succAbove j))).1
  have hinjective : Function.Injective retainedLabel :=
    halternating.unsignedLabel_injective
  have hsurjective : Function.Surjective retainedLabel :=
    ((Fintype.bijective_iff_injective_and_card retainedLabel).2
      ⟨hinjective, by simp⟩).2
  obtain ⟨j, hj⟩ := hsurjective (label (face k)).1
  refine ⟨k.succAbove j, ⟨Fin.succAbove_ne k j, hj⟩, ?_⟩
  -- Every vertex distinct from `k` has a unique `succAbove` presentation, and
  -- injectivity of the retained labels identifies its index with `j`.
  rintro l ⟨hlk, hl⟩
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hlk
  exact congrArg k.succAbove (hinjective (hl.trans hj.symm))

/-- Helper for Theorem 57.6: if equal unsigned labels on the full face have
equal signs, an alternating deletion has a unique equally labeled mate. -/
private theorem existsUnique_duplicateLabel_of_omit_alternating
    {V : Type*} {d : ℕ} (initial : Bool) (label : V → Fin d × Bool)
    (face : Fin (d + 1) → V) (k : Fin (d + 1))
    (hsameSign : ∀ l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2)
    (halternating : IsAlternatingFace initial label
      (fun j ↦ face (k.succAbove j))) :
    ∃! l : Fin (d + 1), l ≠ k ∧ label (face l) = label (face k) := by
  -- First obtain the forced duplicate unsigned label from the equal-cardinality
  -- retained face, then upgrade it to a full signed-label equality.
  obtain ⟨l, ⟨hlk, hlunsigned⟩, hunique⟩ :=
    existsUnique_duplicateUnsignedLabel_of_omit_alternating
      initial label face k halternating
  refine ⟨l, ⟨hlk, Prod.ext hlunsigned (hsameSign l hlunsigned)⟩, ?_⟩
  -- Full-label equality implies the unsigned equality used by the established
  -- uniqueness statement.
  rintro z ⟨hzk, hzlabel⟩
  exact hunique z ⟨hzk, congrArg Prod.fst hzlabel⟩

/-- Helper for Theorem 57.6: deleting either of two equally labeled vertices
produces equivalent alternating-face propositions. -/
theorem isAlternatingFace_omit_iff_of_eq_label
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V) (k l : Fin (r + 1))
    (hlabel : label (face l) = label (face k)) :
    IsAlternatingFace initial label (fun j ↦ face (l.succAbove j)) ↔
      IsAlternatingFace initial label (fun j ↦ face (k.succAbove j)) := by
  classical
  -- Reindex the deletion of `k` by the restriction of the swap `(k l)`.
  let reindex : Equiv.Perm (Fin r) := omitPerm (Equiv.swap k l) l
  have hswapPointwise (j : Fin r) :
      label (face (l.succAbove j)) =
        label (face (k.succAbove (reindex j))) := by
    have hl_ne : l.succAbove j ≠ l := Fin.succAbove_ne l j
    have hcommute := omitPerm_succAbove (Equiv.swap k l) l j
    simp only [Equiv.swap_apply_right] at hcommute
    rw [hcommute]
    by_cases hjk : l.succAbove j = k
    · rw [hjk, Equiv.swap_apply_left]
      exact hlabel.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hjk hl_ne]
  -- Pointwise label congruence reaches the reindexed deletion, and the existing
  -- reindexing theorem removes the auxiliary permutation.
  exact (isAlternatingFace_congr_labels initial label _ _ hswapPointwise).trans
    (isAlternatingFace_reindex initial label
      (fun j ↦ face (k.succAbove j)) reindex)

/-- Helper for Theorem 57.6: when equal unsigned labels on a face have equal
signs, the mod-two sum of its alternating vertex deletions vanishes. -/
theorem sum_alternatingFaceWeight_omit_eq_zero_of_card_succ
    {V : Type*} {d : ℕ} (initial : Bool) (label : V → Fin d × Bool)
    (face : Fin (d + 1) → V)
    (hsameSign : ∀ k l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2) :
    ∑ k : Fin (d + 1),
      alternatingFaceWeight initial label (fun j ↦ face (k.succAbove j)) = 0 := by
  classical
  let omissions := Finset.univ.filter (fun k : Fin (d + 1) ↦
    IsAlternatingFace initial label (fun j ↦ face (k.succAbove j)))
  have hmateExists (k : Fin (d + 1)) (hk : k ∈ omissions) :
      ∃! l : Fin (d + 1), l ≠ k ∧ label (face l) = label (face k) := by
    -- An alternating deletion contains every unsigned label exactly once, so
    -- the omitted vertex has one unique equally labeled mate.
    apply existsUnique_duplicateLabel_of_omit_alternating initial label face k
      (hsameSign k)
    exact (Finset.mem_filter.mp hk).2
  let mate : ∀ k, k ∈ omissions → Fin (d + 1) :=
    fun k hk ↦ (hmateExists k hk).choose
  have hmateSpec (k : Fin (d + 1)) (hk : k ∈ omissions) :
      mate k hk ≠ k ∧ label (face (mate k hk)) = label (face k) := by
    -- Record both defining properties of the uniquely chosen mate.
    exact (hmateExists k hk).choose_spec.1
  have hmateMem (k : Fin (d + 1)) (hk : k ∈ omissions) :
      mate k hk ∈ omissions := by
    -- Equal-label deletion invariance makes the mate another alternating omission.
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply (isAlternatingFace_omit_iff_of_eq_label initial label face k
      (mate k hk) (hmateSpec k hk).2).mpr
    exact (Finset.mem_filter.mp hk).2
  have hmateInvolutive (k : Fin (d + 1)) (hk : k ∈ omissions) :
      mate (mate k hk) (hmateMem k hk) = k := by
    -- For the mate's deletion, the original vertex satisfies the same unique
    -- duplicate-label specification, forcing the second choice back to `k`.
    apply (hmateExists (mate k hk) (hmateMem k hk)).unique
    · exact hmateSpec (mate k hk) (hmateMem k hk)
    · exact ⟨(hmateSpec k hk).1.symm, (hmateSpec k hk).2.symm⟩
  -- Expand the indicator sum to the filtered alternating omissions, then pair
  -- each term with its distinct involutive mate. Each pair is `1 + 1 = 0`.
  simp only [alternatingFaceWeight, Finset.sum_ite, Finset.sum_const_zero,
    add_zero]
  exact Finset.sum_involution (fun k hk ↦ mate k hk)
    (fun _ _ ↦ CharTwo.add_self_eq_zero 1)
    (fun k hk _ ↦ (hmateSpec k hk).1)
    hmateMem hmateInvolutive

/-- Helper for Theorem 57.6: the local sign obtained after alternating `n`
times from an initial Boolean sign. -/
private def alternatingFaceSignAt (initial : Bool) : ℕ → Bool
  | 0 => initial
  | n + 1 => !(alternatingFaceSignAt initial n)

/-- Helper for Theorem 57.6: shifting the local alternating sign sequence
toggles its initial sign. -/
private theorem alternatingFaceSignAt_succ (initial : Bool) (n : ℕ) :
    alternatingFaceSignAt initial (n + 1) =
      alternatingFaceSignAt (!initial) n := by
  -- Induct through the two simultaneous Boolean toggles.
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
      simpa only [alternatingFaceSignAt] using
        congrArg Bool.not (ih initial)

/-- Helper for Theorem 57.6: a Boolean tuple follows the local alternating
sign sequence. -/
private def IsAlternatingFaceSign {r : ℕ} (initial : Bool)
    (sign : Fin r → Bool) : Prop :=
  ∀ j, sign j = alternatingFaceSignAt initial j.1

/-- Helper for Theorem 57.6: the mod-two indicator of the local alternating
sign predicate. -/
private noncomputable def alternatingFaceSignWeight {r : ℕ} (initial : Bool)
    (sign : Fin r → Bool) : ZMod 2 :=
  @ite (ZMod 2) (IsAlternatingFaceSign initial sign) (Classical.dec _) 1 0

/-- Helper for Theorem 57.6: adjoining a head sign reduces the alternating
indicator to the opposite-initial indicator of the tail. -/
private theorem alternatingFaceSignWeight_cons {r : ℕ}
    (initial head : Bool) (tail : Fin r → Bool) :
    alternatingFaceSignWeight initial (Fin.cons head tail) =
      if head = initial then alternatingFaceSignWeight (!initial) tail else 0 := by
  have hiff : IsAlternatingFaceSign initial (Fin.cons head tail) ↔
      head = initial ∧ IsAlternatingFaceSign (!initial) tail := by
    constructor
    · intro halternating
      constructor
      · have hhead := halternating (0 : Fin (r + 1))
        exact hhead
      · intro j
        simpa only [Fin.cons_succ, Fin.val_succ,
          alternatingFaceSignAt_succ] using halternating j.succ
    · rintro ⟨rfl, halternating⟩ j
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · rfl
      · simpa only [Fin.cons_succ, Fin.val_succ,
          alternatingFaceSignAt_succ] using halternating k
  -- Evaluate both indicators through the head-and-tail characterization.
  by_cases hhead : head = initial
  · subst head
    by_cases htail : IsAlternatingFaceSign (!initial) tail
    · have hcons : IsAlternatingFaceSign initial (Fin.cons initial tail) :=
        hiff.mpr ⟨rfl, htail⟩
      simp [alternatingFaceSignWeight, htail, hcons]
    · have hcons : ¬IsAlternatingFaceSign initial (Fin.cons initial tail) :=
        fun h ↦ htail (hiff.mp h).2
      simp [alternatingFaceSignWeight, htail, hcons]
  · have hcons : ¬IsAlternatingFaceSign initial (Fin.cons head tail) :=
      fun h ↦ hhead (hiff.mp h).1
    simp [alternatingFaceSignWeight, hhead, hcons]

/-- Helper for Theorem 57.6: the boundary sum of local alternating sign
weights is the sum of the two orientations of the full sign tuple. -/
private theorem sum_alternatingFaceSignWeight_omit (r : ℕ) (initial : Bool)
    (sign : Fin (r + 1) → Bool) :
    ∑ k : Fin (r + 1),
        alternatingFaceSignWeight initial (fun j ↦ sign (k.succAbove j)) =
      alternatingFaceSignWeight initial sign +
        alternatingFaceSignWeight (!initial) sign := by
  -- Peel off the head; successor omissions invoke the identity for the tail.
  induction r generalizing initial with
  | zero =>
      cases initial <;> cases hsign : sign 0 <;>
        simp [alternatingFaceSignWeight, IsAlternatingFaceSign,
          alternatingFaceSignAt, hsign]
  | succ r ih =>
      let head := sign 0
      let tail := Fin.tail sign
      have hsign : sign = Fin.cons head tail := (Fin.cons_self_tail sign).symm
      rw [hsign, Fin.sum_univ_succ]
      have homitZero :
          (fun j : Fin (r + 1) ↦
            (Fin.cons head tail : Fin (r + 2) → Bool)
              ((0 : Fin (r + 2)).succAbove j)) = tail := by
        funext j
        simp only [Fin.zero_succAbove, Fin.cons_succ]
      have homitSucc (k : Fin (r + 1)) :
          (fun j : Fin (r + 1) ↦
            (Fin.cons head tail : Fin (r + 2) → Bool)
              (k.succ.succAbove j)) =
            Fin.cons head (fun j ↦ tail (k.succAbove j)) := by
        funext j
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · simp only [Fin.succ_succAbove_zero, Fin.cons_zero]
        · simp only [Fin.succ_succAbove_succ, Fin.cons_succ]
      rw [homitZero]
      simp_rw [homitSucc, alternatingFaceSignWeight_cons]
      have hcharTwo (a b : ZMod 2) : a + (b + a) = b := by
        calc
          a + (b + a) = (a + a) + b := by ac_rfl
          _ = 0 + b := by rw [CharTwo.add_self_eq_zero]
          _ = b := zero_add b
      cases initial <;> cases head <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte, ih]
      all_goals
        simp only [Finset.sum_const_zero, add_zero, zero_add, hcharTwo]

/-- Helper for Theorem 57.6: the local recursive alternating sign is exactly
the parity pattern used by an alternating labeled face. -/
private theorem alternatingFaceSignAt_eq_ite_even
    (initial : Bool) (n : ℕ) :
    alternatingFaceSignAt initial n =
      if Even n then initial else !initial := by
  -- A successor toggles both the recursive sign and the parity test.
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
      rw [alternatingFaceSignAt_succ, ih]
      by_cases hn : Even n
      · simp [Nat.even_add_one, hn]
      · simp [Nat.even_add_one, hn]

/-- Helper for Theorem 57.6: simultaneously permuting a face and its omitted
vertex preserves the total alternating deletion weight. -/
private theorem sum_alternatingFaceWeight_omit_reindex
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V) (reindex : Equiv.Perm (Fin (r + 1))) :
    ∑ k : Fin (r + 1), alternatingFaceWeight initial label
        (fun j ↦ face (reindex (k.succAbove j))) =
      ∑ k : Fin (r + 1), alternatingFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) := by
  -- Restrict the ambient permutation to each complement, then reindex the sum.
  calc
    ∑ k : Fin (r + 1), alternatingFaceWeight initial label
          (fun j ↦ face (reindex (k.succAbove j))) =
        ∑ k : Fin (r + 1), alternatingFaceWeight initial label
          (fun j ↦ face ((reindex k).succAbove j)) := by
      apply Finset.sum_congr rfl
      intro k _
      have hface :
          (fun j ↦ face (reindex (k.succAbove j))) =
            fun j ↦ face ((reindex k).succAbove (omitPerm reindex k j)) := by
        funext j
        rw [omitPerm_succAbove]
      rw [hface]
      exact alternatingFaceWeight_reindex initial label
        (fun j ↦ face ((reindex k).succAbove j)) (omitPerm reindex k)
    _ = ∑ k : Fin (r + 1), alternatingFaceWeight initial label
          (fun j ↦ face (k.succAbove j)) := by
      simpa only [] using Equiv.sum_comp reindex
        (fun k ↦ alternatingFaceWeight initial label
          (fun j ↦ face (k.succAbove j)))

/-- Helper for Theorem 57.6: on a face already ordered by unsigned labels,
the labeled alternating weight is the pure alternating-sign weight. -/
private theorem alternatingFaceWeight_eq_signWeight_of_strictMono
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin r → V)
    (hstrict : StrictMono (fun j ↦ (label (face j)).1)) :
    alternatingFaceWeight initial label face =
      alternatingFaceSignWeight initial (fun j ↦ (label (face j)).2) := by
  have hiff : IsAlternatingFace initial label face ↔
      IsAlternatingFaceSign initial (fun j ↦ (label (face j)).2) := by
    constructor
    · rintro ⟨vertexOrder, unsignedOrder, hlabels⟩
      have hordered (j : Fin r) :
          (label (face (vertexOrder j))).1 = unsignedOrder j :=
        congrArg Prod.fst (hlabels j)
      have hpermutedStrict :
          StrictMono ((fun j ↦ (label (face j)).1) ∘ vertexOrder) := by
        intro j k hjk
        simpa only [Function.comp_apply, hordered] using
          unsignedOrder.strictMono hjk
      have hsameOrder :
          (fun j ↦ (label (face j)).1) ∘ vertexOrder =
            (fun j ↦ (label (face j)).1) ∘ Equiv.refl _ :=
        Tuple.unique_monotone hpermutedStrict.monotone hstrict.monotone
      have hvertexOrder : vertexOrder = Equiv.refl _ := by
        apply Equiv.ext
        intro j
        apply hstrict.injective
        exact congrFun hsameOrder j
      intro j
      have hsign := congrArg Prod.snd (hlabels j)
      rw [hvertexOrder] at hsign
      simpa only [Equiv.refl_apply,
        alternatingFaceSignAt_eq_ite_even] using hsign
    · intro hsign
      refine ⟨Equiv.refl _, OrderEmbedding.ofStrictMono _ hstrict, ?_⟩
      intro j
      apply Prod.ext
      · rfl
      · simpa only [Equiv.refl_apply,
          alternatingFaceSignAt_eq_ite_even] using
          hsign j
  -- The equivalent propositions define equal characteristic functions.
  by_cases halternating : IsAlternatingFace initial label face
  · have hsign := hiff.mp halternating
    simp [alternatingFaceWeight, alternatingFaceSignWeight, halternating, hsign]
  · have hsign :
        ¬IsAlternatingFaceSign initial (fun j ↦ (label (face j)).2) :=
      fun h ↦ halternating (hiff.mpr h)
    simp [alternatingFaceWeight, alternatingFaceSignWeight, halternating, hsign]

/-- Helper for Theorem 57.6: the Fan coboundary identity holds when the full
face has pairwise distinct unsigned labels. -/
private theorem sum_alternatingFaceWeight_omit_of_injective
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V)
    (hinjective : Function.Injective (fun j ↦ (label (face j)).1)) :
    ∑ k : Fin (r + 1), alternatingFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) =
      alternatingFaceWeight initial label face +
        alternatingFaceWeight (!initial) label face := by
  let unsigned : Fin (r + 1) → Fin ℓ := fun j ↦ (label (face j)).1
  let reindex : Equiv.Perm (Fin (r + 1)) := Tuple.sort unsigned
  let sortedFace : Fin (r + 1) → V := fun j ↦ face (reindex j)
  have hsortedStrict : StrictMono (fun j ↦ (label (sortedFace j)).1) := by
    apply (Tuple.monotone_sort unsigned).strictMono_of_injective
    exact hinjective.comp reindex.injective
  have hdeletedStrict (k : Fin (r + 1)) :
      StrictMono (fun j ↦ (label (sortedFace (k.succAbove j))).1) :=
    hsortedStrict.comp (Fin.strictMono_succAbove k)
  -- Sort once, apply the pure sign boundary identity, then forget the sorting.
  calc
    ∑ k : Fin (r + 1), alternatingFaceWeight initial label
          (fun j ↦ face (k.succAbove j)) =
        ∑ k : Fin (r + 1), alternatingFaceWeight initial label
          (fun j ↦ sortedFace (k.succAbove j)) :=
      (sum_alternatingFaceWeight_omit_reindex
        initial label face reindex).symm
    _ = ∑ k : Fin (r + 1), alternatingFaceSignWeight initial
          (fun j ↦ (label (sortedFace (k.succAbove j))).2) := by
      apply Finset.sum_congr rfl
      intro k _
      exact alternatingFaceWeight_eq_signWeight_of_strictMono
        initial label _ (hdeletedStrict k)
    _ = alternatingFaceSignWeight initial
          (fun j ↦ (label (sortedFace j)).2) +
          alternatingFaceSignWeight (!initial)
            (fun j ↦ (label (sortedFace j)).2) := by
      simpa only [] using sum_alternatingFaceSignWeight_omit r initial
        (fun j ↦ (label (sortedFace j)).2)
    _ = alternatingFaceWeight initial label sortedFace +
          alternatingFaceWeight (!initial) label sortedFace := by
      rw [alternatingFaceWeight_eq_signWeight_of_strictMono
        initial label sortedFace hsortedStrict,
        alternatingFaceWeight_eq_signWeight_of_strictMono
          (!initial) label sortedFace hsortedStrict]
    _ = alternatingFaceWeight initial label face +
          alternatingFaceWeight (!initial) label face := by
      rw [alternatingFaceWeight_reindex initial label face reindex,
        alternatingFaceWeight_reindex (!initial) label face reindex]

/-- Helper for Theorem 57.6: if the full unsigned-label tuple is not
injective, every alternating deletion has a unique equal-label mate. -/
private theorem existsUnique_equalLabel_of_omit_alternating
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V) (k : Fin (r + 1))
    (hsameSign : ∀ l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2)
    (hnoninjective : ¬Function.Injective (fun j ↦ (label (face j)).1))
    (halternating : IsAlternatingFace initial label
      (fun j ↦ face (k.succAbove j))) :
    ∃! l : Fin (r + 1), l ≠ k ∧ label (face l) = label (face k) := by
  have hretained : Function.Injective
      (fun j ↦ (label (face (k.succAbove j))).1) :=
    halternating.unsignedLabel_injective
  obtain ⟨a, b, hab, habne⟩ := Function.not_injective_iff.mp hnoninjective
  have haorb : a = k ∨ b = k := by
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne.1
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne.2
    have hretainedEq :
        (label (face (k.succAbove i))).1 =
          (label (face (k.succAbove j))).1 := by
      rw [hi, hj]
      exact hab
    apply habne
    exact hi.symm.trans ((congrArg k.succAbove (hretained hretainedEq)).trans hj)
  -- The collision involving the omitted vertex supplies the mate; retained
  -- injectivity proves it is the only one.
  rcases haorb with ha | hb
  · refine ⟨b, ?_, ?_⟩
    · have hbk : b ≠ k := by
        intro hbk
        exact habne (ha.trans hbk.symm)
      have hubk : (label (face b)).1 = (label (face k)).1 := by
        rw [← ha]
        exact hab.symm
      exact ⟨hbk, Prod.ext hubk (hsameSign b hubk)⟩
    · rintro z ⟨hzk, hzlabel⟩
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hzk
      have hbk : b ≠ k := by
        intro hbk
        exact habne (ha.trans hbk.symm)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hbk
      have hretainedEq :
          (label (face (k.succAbove i))).1 =
            (label (face (k.succAbove j))).1 := by
        rw [hi, hj]
        exact (congrArg Prod.fst hzlabel).trans
          ((congrArg (fun t ↦ (label (face t)).1) ha).symm.trans hab)
      exact hi.symm.trans ((congrArg k.succAbove (hretained hretainedEq)).trans hj)
  · refine ⟨a, ?_, ?_⟩
    · have hak : a ≠ k := by
        intro hak
        exact habne (hak.trans hb.symm)
      have huak : (label (face a)).1 = (label (face k)).1 := by
        rw [← hb]
        exact hab
      exact ⟨hak, Prod.ext huak (hsameSign a huak)⟩
    · rintro z ⟨hzk, hzlabel⟩
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hzk
      have hak : a ≠ k := by
        intro hak
        exact habne (hak.trans hb.symm)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hak
      have hretainedEq :
          (label (face (k.succAbove i))).1 =
            (label (face (k.succAbove j))).1 := by
        rw [hi, hj]
        exact (congrArg Prod.fst hzlabel).trans
          ((congrArg (fun t ↦ (label (face t)).1) hb).symm.trans hab.symm)
      exact hi.symm.trans ((congrArg k.succAbove (hretained hretainedEq)).trans hj)

/-- Helper for Theorem 57.6: repeated unsigned labels make all alternating
deletion weights cancel in equal-label pairs. -/
private theorem sum_alternatingFaceWeight_omit_of_not_injective
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V)
    (hsameSign : ∀ k l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2)
    (hnoninjective : ¬Function.Injective (fun j ↦ (label (face j)).1)) :
    ∑ k : Fin (r + 1), alternatingFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) = 0 := by
  classical
  let omissions := Finset.univ.filter (fun k : Fin (r + 1) ↦
    IsAlternatingFace initial label (fun j ↦ face (k.succAbove j)))
  have hmateExists (k : Fin (r + 1)) (hk : k ∈ omissions) :
      ∃! l : Fin (r + 1), l ≠ k ∧ label (face l) = label (face k) := by
    apply existsUnique_equalLabel_of_omit_alternating
      initial label face k (hsameSign k) hnoninjective
    exact (Finset.mem_filter.mp hk).2
  let mate : ∀ k, k ∈ omissions → Fin (r + 1) :=
    fun k hk ↦ (hmateExists k hk).choose
  have hmateSpec (k : Fin (r + 1)) (hk : k ∈ omissions) :
      mate k hk ≠ k ∧ label (face (mate k hk)) = label (face k) :=
    (hmateExists k hk).choose_spec.1
  have hmateMem (k : Fin (r + 1)) (hk : k ∈ omissions) :
      mate k hk ∈ omissions := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply (isAlternatingFace_omit_iff_of_eq_label initial label face k
      (mate k hk) (hmateSpec k hk).2).mpr
    exact (Finset.mem_filter.mp hk).2
  have hmateInvolutive (k : Fin (r + 1)) (hk : k ∈ omissions) :
      mate (mate k hk) (hmateMem k hk) = k := by
    apply (hmateExists (mate k hk) (hmateMem k hk)).unique
    · exact hmateSpec (mate k hk) (hmateMem k hk)
    · exact ⟨(hmateSpec k hk).1.symm, (hmateSpec k hk).2.symm⟩
  -- Expand to the alternating omissions and cancel the fixed-point-free mate
  -- involution in characteristic two.
  simp only [alternatingFaceWeight, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  exact Finset.sum_involution (fun k hk ↦ mate k hk)
    (fun _ _ ↦ CharTwo.add_self_eq_zero 1)
    (fun k hk _ ↦ (hmateSpec k hk).1)
    hmateMem hmateInvolutive

/-- Helper for Theorem 57.6: the mod-two sum of all alternating vertex
deletions is the sum of the two alternating orientations of the full face. -/
theorem sum_alternatingFaceWeight_omit
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V)
    (hsameSign : ∀ k l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2) :
    ∑ k : Fin (r + 1), alternatingFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) =
      alternatingFaceWeight initial label face +
        alternatingFaceWeight (!initial) label face := by
  -- Split on whether sorting is strict; collisions use the mate involution.
  by_cases hinjective : Function.Injective (fun j ↦ (label (face j)).1)
  · exact sum_alternatingFaceWeight_omit_of_injective
      initial label face hinjective
  · have hfullInitial : alternatingFaceWeight initial label face = 0 := by
      rw [alternatingFaceWeight, if_neg]
      intro halternating
      exact hinjective halternating.unsignedLabel_injective
    have hfullOpposite : alternatingFaceWeight (!initial) label face = 0 := by
      rw [alternatingFaceWeight, if_neg]
      intro halternating
      exact hinjective halternating.unsignedLabel_injective
    rw [sum_alternatingFaceWeight_omit_of_not_injective
      initial label face hsameSign hinjective, hfullInitial, hfullOpposite,
      add_zero]

/-- Helper for Theorem 57.6: a face with more vertices than available
unsigned labels has zero alternating weight. -/
theorem alternatingFaceWeight_eq_zero_of_card_lt {V : Type*} {r ℓ : ℕ}
    (hcard : ℓ < r) (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin r → V) : alternatingFaceWeight initial label face = 0 := by
  -- Route correction: use the unsigned-label order stored by the
  -- permutation-invariant Fan weight, rather than the face's vertex order.
  rw [alternatingFaceWeight, if_neg]
  rintro ⟨-, unsignedOrder, -⟩
  have hleCard : Fintype.card (Fin r) ≤ Fintype.card (Fin ℓ) :=
    Fintype.card_le_of_injective _ unsignedOrder.injective
  have hle : r ≤ ℓ := by
    simpa only [Fintype.card_fin] using hleCard
  exact (Nat.not_le_of_gt hcard) hle

/-- Helper for Theorem 57.6: if no neighboring pair is complementary, then
neighboring vertices with the same unsigned label have the same sign. -/
theorem sameSignOfNoComplementaryNeighbor {d m : ℕ}
    (label : CenteredGrid d m → Fin d × Bool)
    (hno : ∀ a b, centeredGridNeighbor a b →
      label b ≠ ((label a).1, !(label a).2))
    {a b : CenteredGrid d m} (hab : centeredGridNeighbor a b)
    (hlabel : (label b).1 = (label a).1) : (label b).2 = (label a).2 := by
  -- Distinct Boolean signs are negations, which would give the forbidden pair.
  by_contra hsign
  apply hno a b hab
  apply Prod.ext
  · exact hlabel
  · cases ha : (label a).2 <;> cases hb : (label b).2 <;> simp_all

/-- Helper for Theorem 57.6: normalized and raw shared facets have the same
alternating signed-label weight. -/
theorem SharedFacet.normalizeAlternatingFaceWeight {d m ℓ : ℕ}
    (hm : 0 < m) (τ : SharedFacet d m) (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool) :
    alternatingFaceWeight initial label (fun j ↦ (normalize hm τ).1.vertex j) =
      alternatingFaceWeight initial label τ.vertex := by
  -- Transport the weight across the pointwise vertex normalization theorem.
  apply congrArg (alternatingFaceWeight initial label)
  funext j
  exact τ.normalize_vertex hm j

/-- Helper for Theorem 57.6: on an extreme boundary facet, centered reflection
toggles the initial alternating sign and preserves the mod-two weight. -/
theorem SharedFacet.alternatingFaceWeight_reflect {d m ℓ : ℕ}
    (τ : NormalizedSharedFacet d m)
    (hlevel : τ.1.level.1 = 0 ∨ τ.1.level.1 = 2 * m)
    (initial : Bool) (label : CenteredGrid (d + 1) m → Fin ℓ × Bool)
    (hboundary : ∀ v, centeredGridBoundary v →
      label (centeredGridNeg v) = ((label v).1, !(label v).2)) :
    alternatingFaceWeight initial label (SharedFacet.reflect τ).1.vertex =
      alternatingFaceWeight (!initial) label τ.1.vertex := by
  -- First transport labels through the vertex reflection formula; then remove
  -- the harmless reversal of the original vertex enumeration.
  calc
    alternatingFaceWeight initial label (SharedFacet.reflect τ).1.vertex =
        alternatingFaceWeight (!initial) label
          (fun j ↦ τ.1.vertex (Fin.rev j)) := by
      apply alternatingFaceWeight_complement_labels
      intro j
      rw [SharedFacet.reflect_vertex τ j]
      exact hboundary _
        (τ.1.vertex_boundary_of_level_extreme hlevel (Fin.rev j))
    _ = alternatingFaceWeight (!initial) label τ.1.vertex := by
      simpa only [Fin.revPerm_apply] using
        (alternatingFaceWeight_reindex (!initial) label τ.1.vertex Fin.revPerm)

/-- Helper for Theorem 57.6: tagged boundary reflection toggles the initial
sign of alternating-face weight. -/
theorem BoundarySharedFacet.alternatingFaceWeight_reflect {d m ℓ : ℕ}
    (facet : BoundarySharedFacet d m) (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool)
    (hboundary : ∀ v, centeredGridBoundary v →
      label (centeredGridNeg v) = ((label v).1, !(label v).2)) :
    alternatingFaceWeight initial label
        (BoundarySharedFacet.reflect facet).vertex =
      alternatingFaceWeight (!initial) label facet.vertex := by
  -- Forget the boundary tags and invoke normalized-facet reflection on the
  -- corresponding extreme level.
  cases facet with
  | inl top =>
      calc
        alternatingFaceWeight initial label
            (BoundarySharedFacet.reflect (Sum.inl top)).vertex =
            alternatingFaceWeight initial label
              (SharedFacet.reflect top.1).1.vertex := by
          apply congrArg (alternatingFaceWeight initial label)
          funext j
          rw [BoundarySharedFacet.reflect_inl,
            BoundarySharedFacet.vertex_eq_normalizedFacet,
            BoundarySharedFacet.normalizedFacet_inr,
            SharedFacet.reflectTopBoundary_val]
        _ = alternatingFaceWeight (!initial) label top.1.1.vertex :=
          SharedFacet.alternatingFaceWeight_reflect top.1 (Or.inr top.2)
            initial label hboundary
        _ = alternatingFaceWeight (!initial) label
            (BoundarySharedFacet.vertex (Sum.inl top)) := by
          apply congrArg (alternatingFaceWeight (!initial) label)
          funext j
          rw [BoundarySharedFacet.vertex_eq_normalizedFacet,
            BoundarySharedFacet.normalizedFacet_inl]
  | inr bottom =>
      calc
        alternatingFaceWeight initial label
            (BoundarySharedFacet.reflect (Sum.inr bottom)).vertex =
            alternatingFaceWeight initial label
              (SharedFacet.reflect bottom.1).1.vertex := by
          apply congrArg (alternatingFaceWeight initial label)
          funext j
          rw [BoundarySharedFacet.reflect_inr,
            BoundarySharedFacet.vertex_eq_normalizedFacet,
            BoundarySharedFacet.normalizedFacet_inl,
            SharedFacet.reflectBottomBoundary_val]
        _ = alternatingFaceWeight (!initial) label bottom.1.1.vertex :=
          SharedFacet.alternatingFaceWeight_reflect bottom.1 (Or.inl bottom.2)
            initial label hboundary
        _ = alternatingFaceWeight (!initial) label
            (BoundarySharedFacet.vertex (Sum.inr bottom)) := by
          apply congrArg (alternatingFaceWeight (!initial) label)
          funext j
          rw [BoundarySharedFacet.vertex_eq_normalizedFacet,
            BoundarySharedFacet.normalizedFacet_inr]

/-- Helper for Theorem 57.6: the complete boundary alternating sum is the
sum of both initial-sign weights over the positive hemisphere. -/
theorem sum_boundaryAlternatingFaceWeight_eq_positiveHemisphere
    {d m ℓ : ℕ} (hm : 0 < m) (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool)
    (hboundary : ∀ v, centeredGridBoundary v →
      label (centeredGridNeg v) = ((label v).1, !(label v).2)) :
    (∑ facet : BoundarySharedFacet d m,
        alternatingFaceWeight initial label facet.vertex) =
      (∑ facet : PositiveHemisphereBoundaryFacet d m,
        alternatingFaceWeight initial label facet.1.vertex) +
      ∑ facet : PositiveHemisphereBoundaryFacet d m,
        alternatingFaceWeight (!initial) label facet.1.vertex := by
  -- Reindex by the hemisphere equivalence.  Its reflected branch is converted
  -- to the opposite initial sign by boundary antipodality.
  calc
    (∑ facet : BoundarySharedFacet d m,
        alternatingFaceWeight initial label facet.vertex) =
        ∑ facet : PositiveHemisphereBoundaryFacet d m ⊕
            PositiveHemisphereBoundaryFacet d m,
          Sum.elim
            (fun positive ↦ alternatingFaceWeight initial label positive.1.vertex)
            (fun positive ↦ alternatingFaceWeight (!initial) label positive.1.vertex)
            facet := by
      apply Fintype.sum_equiv (boundaryFacetHemisphereEquiv hm)
      intro facet
      by_cases hpositive :
          ∀ j, centeredGridPositiveHemisphere (facet.vertex j)
      · rw [boundaryFacetHemisphereEquiv_apply_of_positive hm facet hpositive]
        rfl
      · rw [boundaryFacetHemisphereEquiv_apply_of_not_positive hm facet hpositive]
        rw [Sum.elim_inr]
        simpa only [Bool.not_not] using
          (BoundarySharedFacet.alternatingFaceWeight_reflect facet
            (!initial) label hboundary).symm
    _ = (∑ facet : PositiveHemisphereBoundaryFacet d m,
          alternatingFaceWeight initial label facet.1.vertex) +
        ∑ facet : PositiveHemisphereBoundaryFacet d m,
          alternatingFaceWeight (!initial) label facet.1.vertex :=
      Fintype.sum_sum_type _

/-- Helper for Theorem 57.6: antipodal reflection identifies the lower-boundary
alternating-weight sum with the top-boundary sum of the opposite initial sign. -/
theorem sum_bottomBoundaryAlternatingFaceWeight_eq_top {d m ℓ : ℕ}
    (initial : Bool) (label : CenteredGrid (d + 1) m → Fin ℓ × Bool)
    (hboundary : ∀ v, centeredGridBoundary v →
      label (centeredGridNeg v) = ((label v).1, !(label v).2)) :
    (∑ τ : BottomBoundaryNormalizedSharedFacet d m,
        alternatingFaceWeight initial label τ.1.1.vertex) =
      ∑ τ : TopBoundaryNormalizedSharedFacet d m,
        alternatingFaceWeight (!initial) label τ.1.1.vertex := by
  -- Reindex the top sum through the canonical boundary reflection equivalence
  -- and use the facet-level antipodal weight computation.
  symm
  apply Fintype.sum_equiv (SharedFacet.boundaryReflectEquiv d m)
  intro τ
  rw [SharedFacet.boundaryReflectEquiv_apply]
  exact
      (SharedFacet.alternatingFaceWeight_reflect τ.1 (Or.inr τ.2)
        initial label hboundary).symm

/-- Helper for Theorem 57.6: the endpoint-occurrence sum is the sum of the
lower and upper normalized shared-facet presentations. -/
theorem sum_endpointStaircaseFaceOccurrence_eq_sum_sharedFacets
    {d m : ℕ} {A : Type*} [AddCommMonoid A]
    (weight : (Fin (d + 1) → CenteredGrid (d + 1) m) → A) :
    ∑ τ : EndpointStaircaseFaceOccurrence d m, weight τ.1.vertex =
      (∑ facet : PositiveNormalizedSharedFacet d m, weight facet.1.1.vertex) +
        ∑ facet : BelowTopNormalizedSharedFacet d m, weight facet.1.1.vertex := by
  -- Reindex by the combined equivalence, using its vertex rule to transport
  -- the weight, then split the disjoint-union sum.
  have hvertex (τ : EndpointStaircaseFaceOccurrence d m) :
      τ.1.vertex = Sum.elim
        (fun lower ↦ lower.1.1.vertex)
        (fun upper ↦ upper.1.1.vertex)
        (endpointStaircaseFaceEquiv d m τ) := by
    exact endpointStaircaseFaceEquiv_vertex τ
  calc
    ∑ τ : EndpointStaircaseFaceOccurrence d m, weight τ.1.vertex =
        ∑ facet : PositiveNormalizedSharedFacet d m ⊕
            BelowTopNormalizedSharedFacet d m,
          weight (Sum.elim
            (fun lower ↦ lower.1.1.vertex)
            (fun upper ↦ upper.1.1.vertex) facet) :=
      Fintype.sum_equiv (endpointStaircaseFaceEquiv d m) _ _
        (fun τ ↦ congrArg weight (hvertex τ))
    _ = (∑ facet : PositiveNormalizedSharedFacet d m,
          weight facet.1.1.vertex) +
        ∑ facet : BelowTopNormalizedSharedFacet d m,
          weight facet.1.1.vertex := Fintype.sum_sum_type _

/-- Helper for Theorem 57.6: a shared facet together with its lower or upper
endpoint presentation. -/
abbrev SharedFacetSide (d m : ℕ) :=
  PositiveNormalizedSharedFacet d m ⊕ BelowTopNormalizedSharedFacet d m

/-- Helper for Theorem 57.6: exchange the two presentations of an internal
shared facet and fix the sole presentation of a boundary facet. -/
def sharedFacetSideMate {d m : ℕ} : SharedFacetSide d m → SharedFacetSide d m :=
  fun
  | Sum.inl facet =>
      if hupper : facet.1.1.level.1 < 2 * m then
        Sum.inr ⟨facet.1, hupper⟩
      else Sum.inl facet
  | Sum.inr facet =>
      if hlower : 0 < facet.1.1.level.1 then
        Sum.inl ⟨facet.1, hlower⟩
      else Sum.inr facet

/-- Helper for Theorem 57.6: exchanging the two internal presentations twice
returns the original shared-facet side. -/
theorem sharedFacetSideMate_involutive {d m : ℕ} :
    Function.Involutive (sharedFacetSideMate : SharedFacetSide d m →
      SharedFacetSide d m) := by
  -- In an internal facet the two side conditions supply one another; at a
  -- boundary level the relevant branch is fixed.
  intro side
  cases side with
  | inl facet =>
      by_cases hupper : facet.1.1.level.1 < 2 * m
      · simp [sharedFacetSideMate, hupper, facet.2]
      · simp [sharedFacetSideMate, hupper]
  | inr facet =>
      by_cases hlower : 0 < facet.1.1.level.1
      · simp [sharedFacetSideMate, hlower, facet.2]
      · simp [sharedFacetSideMate, hlower]

/-- Helper for Theorem 57.6: a lower-side presentation is fixed exactly at
the top cubical boundary. -/
theorem sharedFacetSideMate_inl_eq_self_iff {d m : ℕ}
    (facet : PositiveNormalizedSharedFacet d m) :
    sharedFacetSideMate (Sum.inl facet) = Sum.inl facet ↔
      facet.1.1.level.1 = 2 * m := by
  -- Below the top level the mate changes summands; the finite level bound
  -- leaves equality with `2m` as the only fixed case.
  constructor
  · intro hfixed
    by_contra hlevel
    have hupper : facet.1.1.level.1 < 2 * m := by
      have hbound := facet.1.1.level.isLt
      omega
    simp [sharedFacetSideMate, hupper] at hfixed
  · intro hlevel
    have hupper : ¬facet.1.1.level.1 < 2 * m := by omega
    simp [sharedFacetSideMate, hupper]

/-- Helper for Theorem 57.6: an upper-side presentation is fixed exactly at
the lower cubical boundary. -/
theorem sharedFacetSideMate_inr_eq_self_iff {d m : ℕ}
    (facet : BelowTopNormalizedSharedFacet d m) :
    sharedFacetSideMate (Sum.inr facet) = Sum.inr facet ↔
      facet.1.1.level.1 = 0 := by
  -- Above level zero the mate changes summands; a natural-valued level not
  -- above zero is exactly zero.
  constructor
  · intro hfixed
    by_contra hlevel
    have hlower : 0 < facet.1.1.level.1 := Nat.pos_of_ne_zero hlevel
    simp [sharedFacetSideMate, hlower] at hfixed
  · intro hlevel
    have hlower : ¬0 < facet.1.1.level.1 := by omega
    simp [sharedFacetSideMate, hlower]

/-- Helper for Theorem 57.6: a top boundary facet has a valid positive-level
presentation when the grid radius is positive. -/
private theorem topBoundaryLevel_pos {d m : ℕ} (hm : 0 < m)
    (facet : TopBoundaryNormalizedSharedFacet d m) :
    0 < facet.1.1.level.1 := by
  -- Substitute the top level and use positivity of twice the radius.
  rw [facet.2]
  omega

/-- Helper for Theorem 57.6: a bottom boundary facet has a valid below-top
presentation when the grid radius is positive. -/
private theorem bottomBoundaryLevel_lt_top {d m : ℕ} (hm : 0 < m)
    (facet : BottomBoundaryNormalizedSharedFacet d m) :
    facet.1.1.level.1 < 2 * m := by
  -- Substitute the bottom level and use positivity of twice the radius.
  rw [facet.2]
  omega

/-- Helper for Theorem 57.6: view a top boundary facet as the positive side
used by the endpoint-incidence involution. -/
private def topBoundaryToPositiveSide {d m : ℕ} (hm : 0 < m)
    (facet : TopBoundaryNormalizedSharedFacet d m) :
    PositiveNormalizedSharedFacet d m :=
  ⟨facet.1, topBoundaryLevel_pos hm facet⟩

/-- Helper for Theorem 57.6: forgetting the positivity certificate recovers
the normalized top boundary facet. -/
private theorem topBoundaryToPositiveSide_val {d m : ℕ} (hm : 0 < m)
    (facet : TopBoundaryNormalizedSharedFacet d m) :
    (topBoundaryToPositiveSide hm facet).1 = facet.1 := by
  -- Evaluate the data projection of the subtype constructor.
  rfl

/-- Helper for Theorem 57.6: view a bottom boundary facet as the below-top
side used by the endpoint-incidence involution. -/
private def bottomBoundaryToBelowTopSide {d m : ℕ} (hm : 0 < m)
    (facet : BottomBoundaryNormalizedSharedFacet d m) :
    BelowTopNormalizedSharedFacet d m :=
  ⟨facet.1, bottomBoundaryLevel_lt_top hm facet⟩

/-- Helper for Theorem 57.6: forgetting the below-top certificate recovers
the normalized bottom boundary facet. -/
private theorem bottomBoundaryToBelowTopSide_val {d m : ℕ} (hm : 0 < m)
    (facet : BottomBoundaryNormalizedSharedFacet d m) :
    (bottomBoundaryToBelowTopSide hm facet).1 = facet.1 := by
  -- Evaluate the data projection of the subtype constructor.
  rfl

/-- Helper for Theorem 57.6: the positive-side presentation of a top boundary
facet is fixed by the side mate. -/
private theorem topBoundarySide_fixed {d m : ℕ} (hm : 0 < m)
    (facet : TopBoundaryNormalizedSharedFacet d m) :
    sharedFacetSideMate (Sum.inl (topBoundaryToPositiveSide hm facet)) =
      Sum.inl (topBoundaryToPositiveSide hm facet) := by
  -- Use the fixed-side characterization after exposing the stored level.
  apply (sharedFacetSideMate_inl_eq_self_iff _).mpr
  rw [topBoundaryToPositiveSide_val]
  exact facet.2

/-- Helper for Theorem 57.6: the below-top presentation of a bottom boundary
facet is fixed by the side mate. -/
private theorem bottomBoundarySide_fixed {d m : ℕ} (hm : 0 < m)
    (facet : BottomBoundaryNormalizedSharedFacet d m) :
    sharedFacetSideMate (Sum.inr (bottomBoundaryToBelowTopSide hm facet)) =
      Sum.inr (bottomBoundaryToBelowTopSide hm facet) := by
  -- Use the fixed-side characterization after exposing the stored level.
  apply (sharedFacetSideMate_inr_eq_self_iff _).mpr
  rw [bottomBoundaryToBelowTopSide_val]
  exact facet.2

/-- Helper for Theorem 57.6: turn a tagged boundary facet into its unique
fixed endpoint-side presentation. -/
private def boundaryFacetToFixedSide {d m : ℕ} (hm : 0 < m) :
    BoundarySharedFacet d m →
      {side : SharedFacetSide d m // sharedFacetSideMate side = side} :=
  fun
  | Sum.inl facet =>
      ⟨Sum.inl (topBoundaryToPositiveSide hm facet),
        topBoundarySide_fixed hm facet⟩
  | Sum.inr facet =>
      ⟨Sum.inr (bottomBoundaryToBelowTopSide hm facet),
        bottomBoundarySide_fixed hm facet⟩

/-- Helper for Theorem 57.6: forget a fixed endpoint-side presentation and
recover its tagged top or bottom boundary facet. -/
private def fixedSideToBoundaryFacet {d m : ℕ} :
    {side : SharedFacetSide d m // sharedFacetSideMate side = side} →
      BoundarySharedFacet d m :=
  fun
  | ⟨Sum.inl facet, hfixed⟩ =>
      Sum.inl ⟨facet.1, (sharedFacetSideMate_inl_eq_self_iff facet).mp hfixed⟩
  | ⟨Sum.inr facet, hfixed⟩ =>
      Sum.inr ⟨facet.1, (sharedFacetSideMate_inr_eq_self_iff facet).mp hfixed⟩

/-- Helper for Theorem 57.6: fixed-side recovery is a left inverse of the
boundary-facet presentation map. -/
private theorem fixedSideToBoundaryFacet_leftInverse {d m : ℕ} (hm : 0 < m)
    (facet : BoundarySharedFacet d m) :
    fixedSideToBoundaryFacet (boundaryFacetToFixedSide hm facet) = facet := by
  -- Split the boundary tag; only subtype certificates differ after recovery.
  cases facet with
  | inl top =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact topBoundaryToPositiveSide_val hm top
  | inr bottom =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact bottomBoundaryToBelowTopSide_val hm bottom

/-- Helper for Theorem 57.6: boundary-facet presentation is a left inverse of
fixed-side recovery. -/
private theorem boundaryFacetToFixedSide_leftInverse {d m : ℕ} (hm : 0 < m)
    (side : {side : SharedFacetSide d m // sharedFacetSideMate side = side}) :
    boundaryFacetToFixedSide hm (fixedSideToBoundaryFacet side) = side := by
  -- Split the side tag and compare only the stored normalized facet data.
  rcases side with ⟨side, hfixed⟩
  cases side with
  | inl facet =>
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Subtype.ext
      exact topBoundaryToPositiveSide_val hm
        ⟨facet.1, (sharedFacetSideMate_inl_eq_self_iff facet).mp hfixed⟩
  | inr facet =>
      apply Subtype.ext
      apply congrArg Sum.inr
      apply Subtype.ext
      exact bottomBoundaryToBelowTopSide_val hm
        ⟨facet.1, (sharedFacetSideMate_inr_eq_self_iff facet).mp hfixed⟩

/-- Helper for Theorem 57.6: fixed shared-facet sides are canonically the
tagged boundary shared facets at positive grid radius. -/
private def fixedSharedFacetSideEquivBoundaryFacet {d m : ℕ} (hm : 0 < m) :
    {side : SharedFacetSide d m // sharedFacetSideMate side = side} ≃
      BoundarySharedFacet d m :=
  { toFun := fixedSideToBoundaryFacet
    invFun := boundaryFacetToFixedSide hm
    left_inv := boundaryFacetToFixedSide_leftInverse hm
    right_inv := fixedSideToBoundaryFacet_leftInverse hm }

/-- Helper for Theorem 57.6: the fixed-side equivalence sends a positive side
to the corresponding top-tagged boundary facet. -/
private theorem fixedSharedFacetSideEquivBoundaryFacet_inl {d m : ℕ}
    (hm : 0 < m) (facet : PositiveNormalizedSharedFacet d m)
    (hfixed : sharedFacetSideMate (Sum.inl facet) = Sum.inl facet) :
    fixedSharedFacetSideEquivBoundaryFacet hm ⟨Sum.inl facet, hfixed⟩ =
      Sum.inl ⟨facet.1,
        (sharedFacetSideMate_inl_eq_self_iff facet).mp hfixed⟩ := by
  -- Evaluate the positive-side branch of the equivalence.
  rfl

/-- Helper for Theorem 57.6: the fixed-side equivalence sends a below-top side
to the corresponding bottom-tagged boundary facet. -/
private theorem fixedSharedFacetSideEquivBoundaryFacet_inr {d m : ℕ}
    (hm : 0 < m) (facet : BelowTopNormalizedSharedFacet d m)
    (hfixed : sharedFacetSideMate (Sum.inr facet) = Sum.inr facet) :
    fixedSharedFacetSideEquivBoundaryFacet hm ⟨Sum.inr facet, hfixed⟩ =
      Sum.inr ⟨facet.1,
        (sharedFacetSideMate_inr_eq_self_iff facet).mp hfixed⟩ := by
  -- Evaluate the below-top branch of the equivalence.
  rfl

/-- Helper for Theorem 57.6: evaluate a vertex-face weight on either side of
a normalized shared facet. -/
def sharedFacetSideWeight {d m : ℕ} {A : Type*}
    (weight : (Fin (d + 1) → CenteredGrid (d + 1) m) → A) :
    SharedFacetSide d m → A :=
  Sum.elim (fun facet ↦ weight facet.1.1.vertex)
    (fun facet ↦ weight facet.1.1.vertex)

/-- Helper for Theorem 57.6: the fixed-side equivalence preserves every
weight that depends only on the normalized facet vertices. -/
private theorem fixedSharedFacetSideEquivBoundaryFacet_weight {d m : ℕ}
    (hm : 0 < m) {A : Type*}
    (weight : (Fin (d + 1) → CenteredGrid (d + 1) m) → A)
    (side : {side : SharedFacetSide d m // sharedFacetSideMate side = side}) :
    sharedFacetSideWeight weight side.1 =
      weight ((fixedSharedFacetSideEquivBoundaryFacet hm side).vertex) := by
  -- Split the endpoint side and compare the common normalized vertex function.
  rcases side with ⟨side, hfixed⟩
  cases side with
  | inl facet =>
      apply congrArg weight
      funext j
      rw [fixedSharedFacetSideEquivBoundaryFacet_inl,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl]
  | inr facet =>
      apply congrArg weight
      funext j
      rw [fixedSharedFacetSideEquivBoundaryFacet_inr,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr]

/-- Helper for Theorem 57.6: the fixed-side subtype sum transports to the
tagged boundary-facet sum. -/
private theorem sum_fixedSharedFacetSideSubtype_eq_boundary {d m : ℕ}
    (hm : 0 < m) {A : Type*} [AddCommMonoid A]
    (weight : (Fin (d + 1) → CenteredGrid (d + 1) m) → A) :
    (∑ side : {side : SharedFacetSide d m // sharedFacetSideMate side = side},
        sharedFacetSideWeight weight side.1) =
      ∑ facet : BoundarySharedFacet d m, weight facet.vertex := by
  -- Reindex directly through the already verified fixed-side equivalence.
  apply Fintype.sum_equiv (fixedSharedFacetSideEquivBoundaryFacet hm)
  intro side
  exact fixedSharedFacetSideEquivBoundaryFacet_weight hm weight side

/-- Helper for Theorem 57.6: summing a vertex-dependent weight over fixed
endpoint sides is the same as summing it over all tagged boundary facets. -/
private theorem sum_fixedSharedFacetSideWeight_eq_boundary {d m : ℕ}
    (hm : 0 < m) {A : Type*} [AddCommMonoid A]
    (weight : (Fin (d + 1) → CenteredGrid (d + 1) m) → A) :
    ∑ side : SharedFacetSide d m with sharedFacetSideMate side = side,
        sharedFacetSideWeight weight side =
      ∑ facet : BoundarySharedFacet d m, weight facet.vertex := by
  classical
  -- Replace the filtered sum by its subtype form, then use the fixed-side equivalence.
  rw [← Finset.sum_subtype_eq_sum_filter]
  have hfixedUniv :
      Finset.subtype
          (fun side : SharedFacetSide d m ↦ sharedFacetSideMate side = side)
          Finset.univ = Finset.univ := by
    -- The subtype of the ambient universal finset enumerates every fixed side.
    ext side
    simp
  rw [hfixedUniv]
  exact sum_fixedSharedFacetSideSubtype_eq_boundary hm weight

/-- Helper for Theorem 57.6: exchanging the two sides of an internal facet
does not change any weight depending only on its normalized vertices. -/
theorem sharedFacetSideWeight_mate {d m : ℕ} {A : Type*}
    (weight : (Fin (d + 1) → CenteredGrid (d + 1) m) → A)
    (side : SharedFacetSide d m) :
    sharedFacetSideWeight weight (sharedFacetSideMate side) =
      sharedFacetSideWeight weight side := by
  -- Both branches retain the same underlying normalized facet.
  cases side with
  | inl facet =>
      by_cases hupper : facet.1.1.level.1 < 2 * m
      · simp [sharedFacetSideMate, sharedFacetSideWeight, hupper]
      · simp [sharedFacetSideMate, sharedFacetSideWeight, hupper]
  | inr facet =>
      by_cases hlower : 0 < facet.1.1.level.1
      · simp [sharedFacetSideMate, sharedFacetSideWeight, hlower]
      · simp [sharedFacetSideMate, sharedFacetSideWeight, hlower]

/-- Helper for Theorem 57.6: the non-fixed points of an involution on a finite
type contribute zero to any invariant `ZMod 2` weight. -/
theorem sum_nonfixed_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (move : α → α)
    (hmove : Function.Involutive move) (weight : α → ZMod 2)
    (hweight : ∀ x, weight (move x) = weight x) :
    ∑ x with move x ≠ x, weight x = 0 := by
  classical
  -- Pair every non-fixed occurrence with its distinct involutive mate.
  exact Finset.sum_involution (fun x _ ↦ move x)
    (fun x _ ↦ by
      rw [hweight x]
      exact CharTwo.add_self_eq_zero (weight x))
    (fun x hx _ ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx)
    (fun x hx ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact fun hfixed ↦ hx (((hmove x).symm.trans hfixed).symm))
    (fun x _ ↦ hmove x)

/-- Helper for Theorem 57.6: modulo two, an involution-invariant finite sum is
supported exactly on the fixed occurrences. -/
theorem sum_eq_sum_fixedPoints {α : Type*} [Fintype α] [DecidableEq α]
    (move : α → α)
    (hmove : Function.Involutive move) (weight : α → ZMod 2)
    (hweight : ∀ x, weight (move x) = weight x) :
    ∑ x, weight x = ∑ x with move x = x, weight x := by
  classical
  -- Split all occurrences into fixed and non-fixed parts, then cancel the latter.
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x ↦ move x = x) weight
  calc
    ∑ x, weight x =
        (∑ x with move x = x, weight x) +
          ∑ x with move x ≠ x, weight x := hsplit.symm
    _ = (∑ x with move x = x, weight x) + 0 := by
      rw [sum_nonfixed_eq_zero move hmove weight hweight]
    _ = ∑ x with move x = x, weight x := add_zero _

/-- Helper for Theorem 57.6: a constant weight on a finite fiber of size one
or two contributes its representative weight on a boundary fiber and zero
otherwise. -/
private theorem sum_fiber_eq_of_card_one_or_two
    {α β : Type*} [Fintype α] [DecidableEq β]
    (fiberMap : α → β) (representative : β → α)
    (hrepresentative : ∀ b, fiberMap (representative b) = b)
    (boundary : β → Prop) [DecidablePred boundary]
    (hcard : ∀ b, Nat.card {a // fiberMap a = b} =
      if boundary b then 1 else 2)
    (weight : α → ZMod 2)
    (hweight : ∀ a c, fiberMap a = fiberMap c → weight a = weight c)
    (b : β) :
    (∑ a : {a // fiberMap a = b}, weight a) =
      if boundary b then weight (representative b) else 0 := by
  -- Split on the boundary condition, so the cardinality formula becomes a
  -- concrete singleton or two-element fiber count.
  by_cases hb : boundary b
  · have hcardOne : Nat.card {a // fiberMap a = b} = 1 := by
      simpa only [hb, if_true] using hcard b
    have hsubsingleton : Subsingleton {a // fiberMap a = b} :=
      (Nat.card_eq_one_iff_unique.mp hcardOne).1
    -- Local instance justification (finite singleton fiber): the cardinality
    -- theorem supplies the non-inferable subsingleton structure used by the
    -- canonical finite-sum lemma.
    letI : Subsingleton {a // fiberMap a = b} := hsubsingleton
    let fiberRepresentative : {a // fiberMap a = b} :=
      ⟨representative b, hrepresentative b⟩
    rw [if_pos hb]
    exact Fintype.sum_subsingleton
      (fun a : {a // fiberMap a = b} ↦ weight a.1) fiberRepresentative
  · -- In a two-element fiber, constancy turns the sum into a doubled
    -- representative weight, which vanishes in characteristic two.
    have hcardTwo : Nat.card {a // fiberMap a = b} = 2 := by
      simpa only [hb, if_false] using hcard b
    rw [if_neg hb]
    calc
      (∑ a : {a // fiberMap a = b}, weight a) =
          ∑ _a : {a // fiberMap a = b}, weight (representative b) := by
        apply Fintype.sum_congr
        intro a
        exact hweight a (representative b)
          (a.property.trans (hrepresentative b).symm)
      _ = Fintype.card {a // fiberMap a = b} • weight (representative b) := by
        simp only [Finset.sum_const, Finset.card_univ]
      _ = 2 • weight (representative b) := by
        rw [Fintype.card_eq_nat_card, hcardTwo]
      _ = weight (representative b) + weight (representative b) := two_nsmul _
      _ = 0 := CharTwo.add_self_eq_zero (weight (representative b))

/-- Helper for Theorem 57.6: modulo two, a finite map with singleton boundary
fibers and two-element interior fibers has total weight equal to its boundary
sum. -/
private theorem sum_eq_sum_boundary_of_fiber_card
    {α β : Type*} [Fintype α] [Fintype β]
    (fiberMap : α → β) (representative : β → α)
    (hrepresentative : ∀ b, fiberMap (representative b) = b)
    (boundary : β → Prop) [DecidablePred boundary]
    (hcard : ∀ b, Nat.card {a // fiberMap a = b} =
      if boundary b then 1 else 2)
    (weight : α → ZMod 2)
    (hweight : ∀ a c, fiberMap a = fiberMap c → weight a = weight c) :
    ∑ a, weight a = ∑ b with boundary b, weight (representative b) := by
  classical
  -- Partition the total sum into fibers, evaluate each fiber with the
  -- one-or-two formula, and fold the conditional sum into a filter.
  calc
    ∑ a, weight a = ∑ b, ∑ a : {a // fiberMap a = b}, weight a :=
      (Fintype.sum_fiberwise fiberMap weight).symm
    _ = ∑ b, if boundary b then weight (representative b) else 0 := by
      apply Fintype.sum_congr
      intro b
      exact sum_fiber_eq_of_card_one_or_two fiberMap representative
        hrepresentative boundary hcard weight hweight b
    _ = ∑ b with boundary b, weight (representative b) :=
      (Finset.sum_filter boundary (fun b ↦ weight (representative b))).symm

/-- Helper for Theorem 57.6: after the two presentations of every internal
shared facet cancel, a side-weight sum is supported on boundary facets. -/
theorem sum_sharedFacetSideWeight_eq_sum_fixed {d m : ℕ}
    (weight : (Fin (d + 1) → CenteredGrid (d + 1) m) → ZMod 2) :
    ∑ side : SharedFacetSide d m, sharedFacetSideWeight weight side =
      ∑ side with sharedFacetSideMate side = side,
        sharedFacetSideWeight weight side := by
  -- Apply the generic characteristic-two involution theorem; the side mate
  -- preserves the normalized facet and therefore its vertex-dependent weight.
  exact sum_eq_sum_fixedPoints sharedFacetSideMate
    sharedFacetSideMate_involutive (sharedFacetSideWeight weight)
    (sharedFacetSideWeight_mate weight)

/-- Helper for Theorem 57.6: an invariant `ZMod 2` sum for a fixed-point-free
involution vanishes. -/
theorem sum_eq_zero_of_fixedPointFree {α : Type*} [Fintype α]
    (move : α → α) (hmove : Function.Involutive move)
    (hfixed : ∀ x, move x ≠ x) (weight : α → ZMod 2)
    (hweight : ∀ x, weight (move x) = weight x) :
    ∑ x, weight x = 0 := by
  classical
  -- First cancel non-fixed pairs, then observe that the fixed-point sum is empty.
  rw [sum_eq_sum_fixedPoints move hmove weight hweight]
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact (hfixed x hx).elim

/-- Helper for Theorem 57.6: every weight depending only on the enumerated
vertices of an internal staircase face cancels modulo two. -/
theorem sum_internalStaircaseFaceWeight_eq_zero {d m : ℕ}
    (weight : (Fin d → CenteredGrid d m) → ZMod 2) :
    ∑ τ : InternalStaircaseFace d m,
      weight (fun j ↦ τ.1.vertex j) = 0 := by
  -- Pair the two adjacent-order presentations; their vertex enumerations agree.
  apply sum_eq_zero_of_fixedPointFree internalStaircaseFaceMate
    internalStaircaseFaceMate_involutive internalStaircaseFaceMate_ne
  intro τ
  apply congrArg weight
  funext j
  exact internalStaircaseFaceMate_vertex τ j

/-- Helper for Theorem 57.6: internal staircase faces contribute zero to the
alternating signed-label sum. -/
theorem sum_internalAlternatingFaceWeight_eq_zero {d m ℓ : ℕ}
    (initial : Bool) (label : CenteredGrid d m → Fin ℓ × Bool) :
    ∑ τ : InternalStaircaseFace d m,
      alternatingFaceWeight initial label (fun j ↦ τ.1.vertex j) = 0 := by
  -- Specialize the vertex-invariant cancellation theorem to alternating weight.
  exact sum_internalStaircaseFaceWeight_eq_zero
    (alternatingFaceWeight initial label)

/-- Helper for Theorem 57.6: an invariant `ZMod 2` sum with one fixed
occurrence equals the weight of that occurrence. -/
theorem sum_eq_of_uniqueFixedPoint {α : Type*} [Fintype α]
    (move : α → α) (hmove : Function.Involutive move) (start : α)
    (hfixed : ∀ x, move x = x ↔ x = start) (weight : α → ZMod 2)
    (hweight : ∀ x, weight (move x) = weight x) :
    ∑ x, weight x = weight start := by
  classical
  -- Cancellation leaves the singleton fixed-point set, whose sum is its weight.
  rw [sum_eq_sum_fixedPoints move hmove weight hweight]
  have hfilter : Finset.univ.filter (fun x ↦ move x = x) = {start} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hfixed x
  rw [hfilter, Finset.sum_singleton]

/-- Helper for Theorem 57.6: a `d`-element subset of an injectively
enumerated `d + 1`-element set is obtained by deleting a unique index. -/
private theorem existsUnique_omitted_of_card_subset
    {V : Type*} [DecidableEq V] {d : ℕ}
    (vertex : Fin (d + 1) → V) (hvertex : Function.Injective vertex)
    (ridge : Finset V) (hridgeCard : ridge.card = d)
    (hridgeSubset : ridge ⊆ Finset.univ.image vertex) :
    ∃! omitted : Fin (d + 1),
      Finset.univ.image (fun j ↦ vertex (omitted.succAbove j)) = ridge := by
  -- A strict subset of the full vertex set omits at least one enumerated vertex.
  have hfullCard : (Finset.univ.image vertex).card = d + 1 := by
    calc
      (Finset.univ.image vertex).card =
          (Finset.univ : Finset (Fin (d + 1))).card :=
        Finset.card_image_of_injective Finset.univ hvertex
      _ = d + 1 := Fintype.card_fin (d + 1)
  have hridgeNe : ridge ≠ Finset.univ.image vertex := by
    intro heq
    have hcardEq := congrArg Finset.card heq
    rw [hridgeCard, hfullCard] at hcardEq
    omega
  have hridgeProper : ridge ⊂ Finset.univ.image vertex :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hridgeSubset, hridgeNe⟩
  obtain ⟨missingVertex, hmissingFull, hridgeErase⟩ :=
    Finset.ssubset_iff_exists_subset_erase.mp hridgeProper
  obtain ⟨omitted, _, hmissingEq⟩ := Finset.mem_image.mp hmissingFull
  subst missingVertex
  have hridgeEqErase :
      ridge = (Finset.univ.image vertex).erase (vertex omitted) := by
    apply Finset.eq_of_subset_of_card_le hridgeErase
    rw [Finset.card_erase_of_mem hmissingFull, hfullCard, hridgeCard]
    omega
  -- The deletion image lies in the chosen erase and has the same cardinality.
  have hdeletionSubset :
      Finset.univ.image (fun j ↦ vertex (omitted.succAbove j)) ⊆ ridge := by
    intro value hvalue
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hvalue
    rw [hridgeEqErase]
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      exact Fin.succAbove_ne omitted j (hvertex heq)
    · exact Finset.mem_image.mpr
        ⟨omitted.succAbove j, Finset.mem_univ _, rfl⟩
  have hdeletion :
      Finset.univ.image (fun j ↦ vertex (omitted.succAbove j)) = ridge := by
    apply Finset.eq_of_subset_of_card_le hdeletionSubset
    rw [finsetImage_succAbove_card_of_injective vertex hvertex omitted,
      hridgeCard]
  refine ⟨omitted, hdeletion, ?_⟩
  -- Injectivity of deletion images gives uniqueness of the missing index.
  intro other hother
  exact finsetImage_succAbove_injective_of_injective vertex hvertex
    (hother.trans hdeletion.symm)

/-- Helper for Theorem 57.6: a ridge occurrence's retained vertices are
contained in the complete vertex set of its positive boundary facet. -/
theorem PositiveHemisphereFaceOccurrence.ridgeVertexSet_subset_facetVertexSet
    {d m : ℕ} (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.ridgeVertexSet ⊆
      Finset.univ.image occurrence.facet.1.vertex := by
  -- A retained position is the same facet vertex at its `succAbove` index.
  intro vertex hvertex
  rw [occurrence.ridgeVertexSet_eq_facetImage] at hvertex
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hvertex
  exact Finset.mem_image.mpr
    ⟨occurrence.omitted.succAbove j, Finset.mem_univ _, rfl⟩

/-- Helper for Theorem 57.6: choose the unique omitted vertex that presents
the fixed ridge inside a positive boundary cofacet. -/
private noncomputable def PositiveHemisphereFaceOccurrence.cofacetOmitted
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (cofacet : {facet : PositiveHemisphereBoundaryFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex}) :
    Fin (d + 1) :=
  Classical.choose (existsUnique_omitted_of_card_subset cofacet.1.1.vertex
    cofacet.1.1.vertex_injective base.ridgeVertexSet
    base.ridgeVertexSet_card cofacet.2)

/-- Helper for Theorem 57.6: deleting the chosen cofacet vertex recovers the
fixed unordered ridge. -/
private theorem PositiveHemisphereFaceOccurrence.cofacetOmitted_spec
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (cofacet : {facet : PositiveHemisphereBoundaryFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex}) :
    Finset.univ.image (fun j ↦ cofacet.1.1.vertex
      ((base.cofacetOmitted cofacet).succAbove j)) = base.ridgeVertexSet := by
  -- Unpack the specification of the uniquely chosen omitted index.
  exact (Classical.choose_spec
    (existsUnique_omitted_of_card_subset cofacet.1.1.vertex
      cofacet.1.1.vertex_injective base.ridgeVertexSet
      base.ridgeVertexSet_card cofacet.2)).1

/-- Helper for Theorem 57.6: rebuild the occurrence of the fixed ridge in a
chosen positive boundary cofacet. -/
private noncomputable def PositiveHemisphereFaceOccurrence.ofCofacet
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (cofacet : {facet : PositiveHemisphereBoundaryFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex}) :
    PositiveHemisphereFaceOccurrence d m :=
  { facet := cofacet.1
    omitted := base.cofacetOmitted cofacet }

/-- Helper for Theorem 57.6: the occurrence rebuilt from a cofacet presents
the fixed unordered ridge. -/
private theorem PositiveHemisphereFaceOccurrence.ofCofacet_ridgeVertexSet
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (cofacet : {facet : PositiveHemisphereBoundaryFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex}) :
    (base.ofCofacet cofacet).ridgeVertexSet = base.ridgeVertexSet := by
  -- The ridge-set definition is exactly the chosen deletion image.
  rw [(base.ofCofacet cofacet).ridgeVertexSet_eq_facetImage]
  simpa only [PositiveHemisphereFaceOccurrence.ofCofacet] using
    base.cofacetOmitted_spec cofacet

/-- Helper for Theorem 57.6: forgetting an occurrence's omitted index leaves
a positive boundary cofacet containing the fixed ridge. -/
private theorem PositiveHemisphereFaceOccurrence.ridgeVertexSet_subset_cofacet
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (occurrence : {occurrence : PositiveHemisphereFaceOccurrence d m //
      occurrence.ridgeVertexSet = base.ridgeVertexSet}) :
    base.ridgeVertexSet ⊆
      Finset.univ.image occurrence.1.facet.1.vertex := by
  -- Replace the fixed ridge by this presentation, then use facet containment.
  intro vertex hvertex
  have hpresented : vertex ∈ occurrence.1.ridgeVertexSet :=
    occurrence.2.symm ▸ hvertex
  exact occurrence.1.ridgeVertexSet_subset_facetVertexSet hpresented

/-- Helper for Theorem 57.6: forgetting an occurrence's omitted index leaves
a positive boundary cofacet containing the fixed ridge. -/
private def PositiveHemisphereFaceOccurrence.toCofacet
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (occurrence : {occurrence : PositiveHemisphereFaceOccurrence d m //
      occurrence.ridgeVertexSet = base.ridgeVertexSet}) :
    {facet : PositiveHemisphereBoundaryFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex} :=
  ⟨occurrence.1.facet, base.ridgeVertexSet_subset_cofacet occurrence⟩

/-- Helper for Theorem 57.6: forgetting a presentation preserves the
underlying boundary facet. -/
private theorem PositiveHemisphereFaceOccurrence.toCofacet_facet_val
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (occurrence : {occurrence : PositiveHemisphereFaceOccurrence d m //
      occurrence.ridgeVertexSet = base.ridgeVertexSet}) :
    (base.toCofacet occurrence).1.1 = occurrence.1.facet.1 := by
  -- The cofacet constructor stores the occurrence facet verbatim.
  rfl

/-- Helper for Theorem 57.6: rebuilding a ridge presentation after forgetting
its omitted index returns the original presentation. -/
private theorem PositiveHemisphereFaceOccurrence.ofCofacet_toCofacet
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (occurrence : {occurrence : PositiveHemisphereFaceOccurrence d m //
      occurrence.ridgeVertexSet = base.ridgeVertexSet}) :
    ⟨base.ofCofacet (base.toCofacet occurrence),
      base.ofCofacet_ridgeVertexSet (base.toCofacet occurrence)⟩ = occurrence := by
  -- Facets agree directly; uniqueness of the deleted index identifies omissions.
  apply Subtype.ext
  have homitted :
      (base.ofCofacet (base.toCofacet occurrence)).omitted =
        occurrence.1.omitted := by
    apply (existsUnique_omitted_of_card_subset
        occurrence.1.facet.1.vertex occurrence.1.facet.1.vertex_injective
        base.ridgeVertexSet base.ridgeVertexSet_card
        (base.toCofacet occurrence).2).unique
    · exact base.cofacetOmitted_spec (base.toCofacet occurrence)
    · exact occurrence.1.ridgeVertexSet_eq_facetImage.symm.trans occurrence.2
  exact congrArg₂ PositiveHemisphereFaceOccurrence.mk
    (Subtype.ext (base.toCofacet_facet_val occurrence)) homitted

/-- Helper for Theorem 57.6: forgetting the rebuilt presentation recovers
the original positive boundary cofacet. -/
private theorem PositiveHemisphereFaceOccurrence.ofCofacet_facet_val
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (cofacet : {facet : PositiveHemisphereBoundaryFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex}) :
    (base.ofCofacet cofacet).facet.1 = cofacet.1.1 := by
  -- The rebuilt occurrence stores the supplied boundary facet verbatim.
  rfl

/-- Helper for Theorem 57.6: forgetting the rebuilt presentation recovers
the original positive boundary cofacet. -/
private theorem PositiveHemisphereFaceOccurrence.toCofacet_ofCofacet
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (cofacet : {facet : PositiveHemisphereBoundaryFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex}) :
    base.toCofacet
      ⟨base.ofCofacet cofacet, base.ofCofacet_ridgeVertexSet cofacet⟩ =
        cofacet := by
  -- Both cofacets store the same positive boundary facet.
  apply Subtype.ext
  apply Subtype.ext
  exact base.ofCofacet_facet_val cofacet

/-- Helper for Theorem 57.6: presentations of one unordered ridge are
canonically equivalent to its positive boundary cofacets. -/
noncomputable def PositiveHemisphereFaceOccurrence.ridgePresentationEquivCofacet
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m) :
    {occurrence : PositiveHemisphereFaceOccurrence d m //
      occurrence.ridgeVertexSet = base.ridgeVertexSet} ≃
      {facet : PositiveHemisphereBoundaryFacet d m //
        base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex} :=
  { toFun := base.toCofacet
    invFun := fun cofacet ↦
      ⟨base.ofCofacet cofacet, base.ofCofacet_ridgeVertexSet cofacet⟩
    left_inv := base.ofCofacet_toCofacet
    right_inv := base.toCofacet_ofCofacet }

/-- Helper for Theorem 57.6: the number of presentations of an unordered
ridge equals the number of positive boundary cofacets that contain it. -/
theorem PositiveHemisphereFaceOccurrence.ridgePresentation_card_eq_cofacet_card
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m) :
    Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
        occurrence.ridgeVertexSet = base.ridgeVertexSet} =
      Nat.card {facet : PositiveHemisphereBoundaryFacet d m //
        base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex} := by
  -- Transport finite cardinality through the canonical presentation equivalence.
  exact Nat.card_congr base.ridgePresentationEquivCofacet

/-- Helper for Theorem 57.6: every presentation of an equatorial unordered
ridge has all of its retained vertices on the centered equator. -/
theorem PositiveHemisphereFaceOccurrence.vertices_onEquator_of_ridgeVertexSet_eq
    {d m : ℕ} {first second : PositiveHemisphereFaceOccurrence d m}
    (hridge : first.ridgeVertexSet = second.ridgeVertexSet)
    (hfirst : ∀ j, centeredGridOnEquator (first.vertex j)) :
    ∀ j, centeredGridOnEquator (second.vertex j) := by
  -- Transfer the pointwise equator condition through membership in the common ridge.
  intro j
  have hmem : second.vertex j ∈ first.ridgeVertexSet := by
    rw [hridge, second.ridgeVertexSet_eq_facetImage]
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_univ j, (second.vertex_eq_facetVertex j).symm⟩
  rw [first.ridgeVertexSet_eq_facetImage] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  have hvertices : first.vertex i = second.vertex j :=
    (first.vertex_eq_facetVertex i).trans hi
  apply (centeredGridOnEquator_iff (second.vertex j)).mpr
  rw [← hvertices]
  exact (centeredGridOnEquator_iff (first.vertex i)).mp (hfirst i)

/-- Helper for Theorem 57.6: retained vertices of a positive-hemisphere
ridge occurrence are enumerated injectively. -/
theorem PositiveHemisphereFaceOccurrence.vertex_injective
    {d m : ℕ} (occurrence : PositiveHemisphereFaceOccurrence d m) :
    Function.Injective occurrence.vertex := by
  -- Compare retained indices through the injective complete facet enumeration.
  intro j k heq
  have hindices : occurrence.omitted.succAbove j =
      occurrence.omitted.succAbove k := by
    apply occurrence.facet.1.vertex_injective
    simpa only [occurrence.vertex_eq_facetVertex] using heq
  exact Fin.succAbove_right_injective hindices

/-- Helper for Theorem 57.6: two presentations of the same unordered positive-
hemisphere ridge are equatorial simultaneously. -/
theorem PositiveHemisphereFaceOccurrence.vertices_onEquator_iff_of_ridgeVertexSet_eq
    {d m : ℕ} {first second : PositiveHemisphereFaceOccurrence d m}
    (hridge : first.ridgeVertexSet = second.ridgeVertexSet) :
    (∀ j, centeredGridOnEquator (first.vertex j)) ↔
      ∀ j, centeredGridOnEquator (second.vertex j) := by
  -- Transfer the equator condition forward and backward through the common
  -- unordered ridge set.
  constructor
  · intro hfirst
    exact first.vertices_onEquator_of_ridgeVertexSet_eq hridge hfirst
  · intro hsecond
    exact second.vertices_onEquator_of_ridgeVertexSet_eq hridge.symm hsecond

/-- Helper for Theorem 57.6: every ambient boundary cofacet containing a
positive ridge with a retained vertex off the equator lies in the positive
closed hemisphere. -/
theorem PositiveHemisphereFaceOccurrence.cofacet_positive_of_exists_vertex_not_onEquator
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (hoffEquator : ∃ i, ¬centeredGridOnEquator (base.vertex i))
    (facet : BoundarySharedFacet d m)
    (hcontains : base.ridgeVertexSet ⊆ Finset.univ.image facet.vertex) :
    ∀ j, centeredGridPositiveHemisphere (facet.vertex j) := by
  -- A non-equatorial retained vertex is strictly above the equator because
  -- every retained vertex already belongs to the positive hemisphere.
  obtain ⟨i, hi⟩ := hoffEquator
  have hstrict : m < (base.vertex i 0).1 := by
    have hpositive :=
      (centeredGridPositiveHemisphere_iff (base.vertex i)).mp
        (base.vertex_positive i)
    have hne : (base.vertex i 0).1 ≠ m := by
      intro heq
      exact hi ((centeredGridOnEquator_iff (base.vertex i)).mpr heq)
    omega
  have hbaseMem : base.vertex i ∈ base.ridgeVertexSet := by
    rw [base.ridgeVertexSet_eq_facetImage]
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, (base.vertex_eq_facetVertex i).symm⟩
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hcontains hbaseMem)
  -- All vertices of one boundary facet are cubical neighbors, so the other
  -- vertices can fall by at most one from this strictly positive vertex.
  intro j
  apply (centeredGridPositiveHemisphere_iff (facet.vertex j)).mpr
  have hneighbor :=
    facet.normalizedFacet.1.vertices_neighbor k j (0 : Fin (d + 1))
  rw [← facet.vertex_eq_normalizedFacet,
    ← facet.vertex_eq_normalizedFacet] at hneighbor
  have hcoordinate := congrArg
    (fun v : CenteredGrid (d + 1) m ↦ (v 0).1) hk
  omega

/-- Helper for Theorem 57.6: when a positive ridge has a retained vertex off
the equator, forgetting positivity is an equivalence between its positive and
ambient boundary cofacets. -/
def PositiveHemisphereFaceOccurrence.cofacetEquivAmbientCofacet_of_exists_vertex_not_onEquator
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (hoffEquator : ∃ i, ¬centeredGridOnEquator (base.vertex i)) :
    {facet : PositiveHemisphereBoundaryFacet d m //
        base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex} ≃
      {facet : BoundarySharedFacet d m //
        base.ridgeVertexSet ⊆ Finset.univ.image facet.vertex} :=
  Equiv.subtypeSubtypeEquivSubtype
    (fun hcontains ↦
      base.cofacet_positive_of_exists_vertex_not_onEquator
        hoffEquator _ hcontains)

/-- Helper for Theorem 57.6: if a positive ridge has a retained vertex off the
equator, its positive and ambient cofacet types have the same cardinality. -/
theorem PositiveHemisphereFaceOccurrence.cofacet_card_eq_ambient_of_offEquator
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (hoffEquator : ∃ i, ¬centeredGridOnEquator (base.vertex i)) :
    Nat.card {facet : PositiveHemisphereBoundaryFacet d m //
        base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex} =
      Nat.card {facet : BoundarySharedFacet d m //
        base.ridgeVertexSet ⊆ Finset.univ.image facet.vertex} := by
  -- Count through the equivalence supplied by geometric positivity propagation.
  exact Nat.card_congr
    (base.cofacetEquivAmbientCofacet_of_exists_vertex_not_onEquator
      hoffEquator)

/-- Helper for Theorem 57.6: an ambient two-cofacet count proves the
off-equator branch of the positive ridge-presentation classifier. -/
theorem PositiveHemisphereFaceOccurrence.ridgePresentation_card_eq_two_of_ambientCofacet_card
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (hoffEquator : ∃ i, ¬centeredGridOnEquator (base.vertex i))
    (hambient : Nat.card {facet : BoundarySharedFacet d m //
      base.ridgeVertexSet ⊆ Finset.univ.image facet.vertex} = 2) :
    Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
      occurrence.ridgeVertexSet = base.ridgeVertexSet} = 2 := by
  -- First forget the presentation index, then forget positivity using the
  -- preceding non-equatorial cofacet equivalence.
  calc
    Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
        occurrence.ridgeVertexSet = base.ridgeVertexSet} =
        Nat.card {facet : PositiveHemisphereBoundaryFacet d m //
          base.ridgeVertexSet ⊆ Finset.univ.image facet.1.vertex} :=
      base.ridgePresentation_card_eq_cofacet_card
    _ = Nat.card {facet : BoundarySharedFacet d m //
        base.ridgeVertexSet ⊆ Finset.univ.image facet.vertex} :=
      base.cofacet_card_eq_ambient_of_offEquator hoffEquator
    _ = 2 := hambient

/-- Helper for Theorem 57.6: an internal presentation of a non-equatorial
positive ridge has a distinct positive presentation of the same ridge. -/
theorem PositiveHemisphereFaceOccurrence.exists_distinct_ridgePresentation_of_internal
    {d m : ℕ} (base : PositiveHemisphereFaceOccurrence d m)
    (hoffEquator : ∃ i, ¬centeredGridOnEquator (base.vertex i))
    (hzero : base.omitted ≠ 0)
    (hlast : base.omitted ≠ Fin.last d) :
    ∃ second : PositiveHemisphereFaceOccurrence d m,
      second ≠ base ∧ second.ridgeVertexSet = base.ridgeVertexSet := by
  have hboundaryZero : base.toBoundary.omitted ≠ 0 := by
    rw [base.toBoundary_omitted]
    exact hzero
  have hboundaryLast : base.toBoundary.omitted ≠ Fin.last d := by
    rw [base.toBoundary_omitted]
    exact hlast
  let internal : InternalBoundaryFaceOccurrence d m :=
    ⟨base.toBoundary, ⟨hboundaryZero, hboundaryLast⟩⟩
  let ambientMate : BoundaryFaceOccurrence d m :=
    (internalBoundaryFaceOccurrenceMate internal).1
  -- The established adjacent-order pivot supplies a distinct ambient
  -- occurrence with exactly the same retained ridge.
  have hambientRidge :
      ambientMate.ridgeVertexSet = base.ridgeVertexSet := by
    calc
      ambientMate.ridgeVertexSet = internal.1.ridgeVertexSet := by
        simpa only [ambientMate] using
          internalBoundaryFaceOccurrenceMate_ridgeVertexSet internal
      _ = base.ridgeVertexSet := by
        simpa only [internal] using base.toBoundary_ridgeVertexSet
  have hcontains :
      base.ridgeVertexSet ⊆ Finset.univ.image ambientMate.facet.vertex := by
    rw [← hambientRidge]
    exact ambientMate.ridgeVertexSet_subset_facetVertexSet
  have hpositive :
      ∀ j, centeredGridPositiveHemisphere (ambientMate.facet.vertex j) :=
    base.cofacet_positive_of_exists_vertex_not_onEquator hoffEquator
      ambientMate.facet hcontains
  let second : PositiveHemisphereFaceOccurrence d m :=
    { facet := ⟨ambientMate.facet, hpositive⟩
      omitted := ambientMate.omitted }
  have hsecondBoundary : second.toBoundary = ambientMate := by
    -- Forgetting the newly supplied positivity certificate recovers the
    -- ambient mate without changing either data field.
    have hfacet : second.toBoundary.facet = ambientMate.facet := by
      rw [second.toBoundary_facet]
    have homitted : second.toBoundary.omitted = ambientMate.omitted := by
      rw [second.toBoundary_omitted]
    calc
      second.toBoundary = BoundaryFaceOccurrence.mk
          second.toBoundary.facet second.toBoundary.omitted :=
        second.toBoundary.mk_eq_self.symm
      _ = BoundaryFaceOccurrence.mk ambientMate.facet ambientMate.omitted :=
        congrArg₂ BoundaryFaceOccurrence.mk hfacet homitted
      _ = ambientMate := ambientMate.mk_eq_self
  refine ⟨second, ?_, ?_⟩
  · intro hsecond
    have hboundary : second.toBoundary = base.toBoundary :=
      congrArg PositiveHemisphereFaceOccurrence.toBoundary hsecond
    have hmateValue : ambientMate = internal.1 := by
      simpa only [internal] using hsecondBoundary.symm.trans hboundary
    exact internalBoundaryFaceOccurrenceMate_ne internal
      (Subtype.ext hmateValue)
  · calc
      second.ridgeVertexSet = second.toBoundary.ridgeVertexSet :=
        second.toBoundary_ridgeVertexSet.symm
      _ = ambientMate.ridgeVertexSet :=
        congrArg BoundaryFaceOccurrence.ridgeVertexSet hsecondBoundary
      _ = base.ridgeVertexSet := hambientRidge

/-- Helper for Theorem 57.6: alternating weight depends only on the unordered
vertex set of a positive-hemisphere ridge occurrence. -/
theorem PositiveHemisphereFaceOccurrence.alternatingFaceWeight_eq_of_ridgeVertexSet_eq
    {d m ℓ : ℕ} (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool)
    {first second : PositiveHemisphereFaceOccurrence d m}
    (hridge : first.ridgeVertexSet = second.ridgeVertexSet) :
    alternatingFaceWeight initial label first.vertex =
      alternatingFaceWeight initial label second.vertex := by
  -- Expose the ridge sets as finite images, then invoke permutation
  -- invariance of alternating weight for injective enumerations.
  apply alternatingFaceWeight_eq_of_injective_image_eq initial label
    first.vertex second.vertex first.vertex_injective
  calc
    Finset.univ.image first.vertex = first.ridgeVertexSet := by
      rw [first.ridgeVertexSet_eq_facetImage]
      apply Finset.image_congr
      intro j _
      exact first.vertex_eq_facetVertex j
    _ = second.ridgeVertexSet := hridge
    _ = Finset.univ.image second.vertex := by
      rw [second.ridgeVertexSet_eq_facetImage]
      apply Finset.image_congr
      intro j _
      exact (second.vertex_eq_facetVertex j).symm

/-- Helper for Theorem 57.6: two presentations of one unordered ridge have
alternating weights whose sum vanishes in `ZMod 2`. -/
theorem PositiveHemisphereFaceOccurrence.alternatingFaceWeight_add_eq_zero_of_ridgeVertexSet_eq
    {d m ℓ : ℕ} (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool)
    {first second : PositiveHemisphereFaceOccurrence d m}
    (hridge : first.ridgeVertexSet = second.ridgeVertexSet) :
    alternatingFaceWeight initial label first.vertex +
      alternatingFaceWeight initial label second.vertex = 0 := by
  -- Identify both weights through the unordered ridge, then cancel the
  -- resulting double term in characteristic two.
  rw [first.alternatingFaceWeight_eq_of_ridgeVertexSet_eq
    initial label hridge]
  exact CharTwo.add_self_eq_zero _

/-- Helper for Theorem 57.6: every positive-hemisphere ridge occurrence
presents its own unordered ridge vertex set. -/
private theorem PositiveHemisphereFaceOccurrence.exists_ridgeVertexSet_presentation
    {d m : ℕ} (occurrence : PositiveHemisphereFaceOccurrence d m) :
    ∃ presentation : PositiveHemisphereFaceOccurrence d m,
      presentation.ridgeVertexSet = occurrence.ridgeVertexSet := by
  -- The occurrence itself supplies the required presentation.
  exact ⟨occurrence, rfl⟩

/-- Helper for Theorem 57.6: an unordered positive-hemisphere ridge is a
finite vertex set equipped with a positive boundary-facet presentation. -/
private abbrev PositiveHemisphereRidge (d m : ℕ) :=
  {ridge : Finset (CenteredGrid (d + 1) m) //
    ∃ occurrence : PositiveHemisphereFaceOccurrence d m,
      occurrence.ridgeVertexSet = ridge}

/-- Helper for Theorem 57.6: unordered positive-hemisphere ridges form a
finite type. -/
private noncomputable instance positiveHemisphereRidgeFintype (d m : ℕ) :
    Fintype (PositiveHemisphereRidge d m) :=
  Fintype.ofFinite _

/-- Helper for Theorem 57.6: forget a ridge occurrence's chosen cofacet and
retain only its unordered vertex set. -/
private def PositiveHemisphereFaceOccurrence.ridgeKey {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    PositiveHemisphereRidge d m :=
  ⟨occurrence.ridgeVertexSet,
    occurrence.exists_ridgeVertexSet_presentation⟩

/-- Helper for Theorem 57.6: the value of an occurrence's ridge key is its
unordered ridge vertex set. -/
private theorem PositiveHemisphereFaceOccurrence.ridgeKey_val {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.ridgeKey.1 = occurrence.ridgeVertexSet := by
  -- Expose the data projection without unfolding the key in later proofs.
  rfl

/-- Helper for Theorem 57.6: choose one positive boundary-facet occurrence
presenting each unordered positive-hemisphere ridge. -/
private noncomputable def PositiveHemisphereRidge.representative {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    PositiveHemisphereFaceOccurrence d m :=
  Classical.choose ridge.2

/-- Helper for Theorem 57.6: the chosen occurrence presents exactly the
stored unordered ridge. -/
private theorem PositiveHemisphereRidge.representative_spec {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    ridge.representative.ridgeVertexSet = ridge.1 := by
  -- Read the equation from the presentation witness stored in the subtype.
  exact Classical.choose_spec ridge.2

/-- Helper for Theorem 57.6: applying the ridge key to the chosen
representative recovers the original unordered ridge. -/
private theorem PositiveHemisphereRidge.representative_key {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    ridge.representative.ridgeKey = ridge := by
  -- Equality of ridge subtypes is equality of their stored finite sets.
  apply Subtype.ext
  rw [ridge.representative.ridgeKey_val]
  exact ridge.representative_spec

/-- Helper for Theorem 57.6: an unordered positive-hemisphere ridge is
equatorial when its chosen presentation lies on the centered equator. -/
private def PositiveHemisphereRidge.IsEquatorial {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) : Prop :=
  ridge.representative.IsEquatorial

/-- Helper for Theorem 57.6: equatoriality of a finite unordered ridge is
classically decidable. -/
private noncomputable instance positiveHemisphereRidgeIsEquatorialDecidable
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m) :
    Decidable ridge.IsEquatorial :=
  Classical.dec _

/-- Helper for Theorem 57.6: equatoriality of a positive-hemisphere ridge
occurrence is classically decidable. -/
private noncomputable instance positiveHemisphereFaceOccurrenceIsEquatorialDecidable
    {d m : ℕ} (occurrence : PositiveHemisphereFaceOccurrence d m) :
    Decidable occurrence.IsEquatorial :=
  Classical.dec _

/-- Helper for Theorem 57.6: membership in an unordered-ridge fiber is
equivalent to presenting the chosen representative's finite vertex set. -/
private theorem PositiveHemisphereRidge.ridgeKey_eq_iff_ridgeVertexSet_eq
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m)
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.ridgeKey = ridge ↔
      occurrence.ridgeVertexSet = ridge.representative.ridgeVertexSet := by
  -- Compare subtype values and use the representative's specification.
  constructor
  · intro hkey
    have hvalue := congrArg Subtype.val hkey
    rw [occurrence.ridgeKey_val] at hvalue
    exact hvalue.trans ridge.representative_spec.symm
  · intro hridge
    apply Subtype.ext
    rw [occurrence.ridgeKey_val]
    exact hridge.trans ridge.representative_spec

/-- Helper for Theorem 57.6: the fiber of the unordered-ridge key is
canonically the fiber over the chosen representative's ridge set. -/
private def PositiveHemisphereRidge.fiberEquivRepresentativeFiber
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m) :
    {occurrence : PositiveHemisphereFaceOccurrence d m //
        occurrence.ridgeKey = ridge} ≃
      {occurrence : PositiveHemisphereFaceOccurrence d m //
        occurrence.ridgeVertexSet = ridge.representative.ridgeVertexSet} :=
  Equiv.subtypeEquiv (Equiv.refl _)
    (ridge.ridgeKey_eq_iff_ridgeVertexSet_eq)

/-- Helper for Theorem 57.6: a one-or-two presentation count for every
occurrence induces the corresponding count for unordered-ridge fibers. -/
private theorem positiveHemisphereRidgeFiber_card_of_ridgePresentation_card
    {d m : ℕ}
    (hcard : ∀ base : PositiveHemisphereFaceOccurrence d m,
      Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
          occurrence.ridgeVertexSet = base.ridgeVertexSet} =
        if base.IsEquatorial then 1 else 2)
    (ridge : PositiveHemisphereRidge d m) :
    Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
        occurrence.ridgeKey = ridge} =
      if ridge.IsEquatorial then 1 else 2 := by
  -- Transport cardinality to the representative fiber, where the assumed
  -- geometric classifier applies directly.
  calc
    Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
        occurrence.ridgeKey = ridge} =
        Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
          occurrence.ridgeVertexSet = ridge.representative.ridgeVertexSet} :=
      Nat.card_congr ridge.fiberEquivRepresentativeFiber
    _ = if ridge.IsEquatorial then 1 else 2 := hcard ridge.representative

/-- Helper for Theorem 57.6: alternating weight is constant on every fiber
of the unordered positive-hemisphere ridge key. -/
private theorem PositiveHemisphereFaceOccurrence.alternatingFaceWeight_eq_of_ridgeKey_eq
    {d m ℓ : ℕ} (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool)
    {first second : PositiveHemisphereFaceOccurrence d m}
    (hkey : first.ridgeKey = second.ridgeKey) :
    alternatingFaceWeight initial label first.vertex =
      alternatingFaceWeight initial label second.vertex := by
  -- Forget the subtype certificates and reuse unordered-image invariance.
  apply first.alternatingFaceWeight_eq_of_ridgeVertexSet_eq initial label
  have hvalue := congrArg Subtype.val hkey
  simpa only [first.ridgeKey_val, second.ridgeKey_val] using hvalue

/-- Helper for Theorem 57.6: if every unordered positive-hemisphere ridge
has one presentation on the equator and two presentations off it, then the
total alternating occurrence sum is supported on equatorial ridges. -/
private theorem sum_positiveHemisphereFaceOccurrence_eq_equatorial_of_ridgeFiber_card
    {d m ℓ : ℕ}
    (hcard : ∀ ridge : PositiveHemisphereRidge d m,
      Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
          occurrence.ridgeKey = ridge} =
        if ridge.IsEquatorial then 1 else 2)
    (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool) :
    (∑ occurrence : PositiveHemisphereFaceOccurrence d m,
        alternatingFaceWeight initial label occurrence.vertex) =
      ∑ ridge : PositiveHemisphereRidge d m with ridge.IsEquatorial,
        alternatingFaceWeight initial label ridge.representative.vertex := by
  classical
  -- Partition by unordered ridges. Singleton equatorial fibers survive,
  -- while constant two-element fibers cancel in `ZMod 2`.
  apply sum_eq_sum_boundary_of_fiber_card
    PositiveHemisphereFaceOccurrence.ridgeKey
    PositiveHemisphereRidge.representative
    PositiveHemisphereRidge.representative_key
    PositiveHemisphereRidge.IsEquatorial hcard
  intro first second hkey
  exact first.alternatingFaceWeight_eq_of_ridgeKey_eq initial label hkey

/-- Helper for Theorem 57.6: the geometric one-or-two presentation
classifier reduces the total positive-hemisphere occurrence sum to its
equatorial unordered ridges. -/
private theorem sum_positiveHemisphereFaceOccurrence_eq_equatorial
    {d m ℓ : ℕ}
    (hcard : ∀ base : PositiveHemisphereFaceOccurrence d m,
      Nat.card {occurrence : PositiveHemisphereFaceOccurrence d m //
          occurrence.ridgeVertexSet = base.ridgeVertexSet} =
        if base.IsEquatorial then 1 else 2)
    (initial : Bool)
    (label : CenteredGrid (d + 1) m → Fin ℓ × Bool) :
    (∑ occurrence : PositiveHemisphereFaceOccurrence d m,
        alternatingFaceWeight initial label occurrence.vertex) =
      ∑ ridge : PositiveHemisphereRidge d m with ridge.IsEquatorial,
        alternatingFaceWeight initial label ridge.representative.vertex := by
  -- Feed the canonical fiber-cardinality adapter into the verified
  -- characteristic-two reduction.
  apply sum_positiveHemisphereFaceOccurrence_eq_equatorial_of_ridgeFiber_card
  exact positiveHemisphereRidgeFiber_card_of_ridgePresentation_card hcard

end CubicalTucker

/-- Helper for Theorem 57.6: in dimension at least two, an antipodal labeling
of the centered cubical boundary has a complementarily labeled neighboring
pair. -/
theorem exists_complementary_centeredGridNeighbors_of_two_le
    (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (label : CenteredGrid d m → Fin d × Bool)
    (hboundary : ∀ v, centeredGridBoundary v →
      label (centeredGridNeg v) = ((label v).1, !(label v).2)) :
    ∃ a b, centeredGridNeighbor a b ∧
      label b = ((label a).1, !(label a).2) := by
  -- Route correction: the former Kuhn pivot-frame obligation is replaced by
  -- a mod-two cubical occurrence count. The cancellation API above will pair
  -- every internal occurrence and retain only antipodal boundary occurrences.
  by_contra hcomplementary
  push Not at hcomplementary
  -- On each staircase, equal unsigned labels now have equal signs.
  have hsameSign (σ : CubicalTucker.ElementaryStaircase d m)
      (k l : Fin (d + 1))
      (hlabel : (label (σ.vertex l)).1 = (label (σ.vertex k)).1) :
      (label (σ.vertex l)).2 = (label (σ.vertex k)).2 :=
    CubicalTucker.sameSignOfNoComplementaryNeighbor label hcomplementary
      (σ.vertices_neighbor k l) hlabel
  -- Pair the alternating vertex deletions of each top simplex. This is the
  -- local boundary identity that will be summed over the cubical triangulation.
  have hsimplexBoundaryZero (initial : Bool)
      (σ : CubicalTucker.ElementaryStaircase d m) :
      ∑ k : Fin (d + 1), CubicalTucker.alternatingFaceWeight initial label
        (fun j ↦ σ.vertex (k.succAbove j)) = 0 :=
    by
      -- Apply the full Fan coboundary identity; the two top-dimensional
      -- weights vanish because a `d`-label set cannot alternate on `d + 1`
      -- vertices.
      rw [CubicalTucker.sum_alternatingFaceWeight_omit
        initial label σ.vertex (hsameSign σ),
        CubicalTucker.alternatingFaceWeight_eq_zero_of_card_lt
          (Nat.lt_succ_self d) initial label σ.vertex,
        CubicalTucker.alternatingFaceWeight_eq_zero_of_card_lt
          (Nat.lt_succ_self d) (!initial) label σ.vertex,
        add_zero]
  have hallSimplexBoundariesZero (initial : Bool) :
      ∑ σ : CubicalTucker.ElementaryStaircase d m,
        ∑ k : Fin (d + 1), CubicalTucker.alternatingFaceWeight initial label
          (fun j ↦ σ.vertex (k.succAbove j)) = 0 := by
    -- Sum the verified local boundary identity over every staircase simplex.
    apply Finset.sum_eq_zero
    intro σ _
    exact hsimplexBoundaryZero initial σ
  have hallFaceOccurrencesZero (initial : Bool) :
      ∑ τ : CubicalTucker.StaircaseFaceOccurrence d m,
        CubicalTucker.alternatingFaceWeight initial label τ.vertex = 0 := by
    -- Reindex the double sum by the canonical face-occurrence product model.
    rw [CubicalTucker.sum_staircaseFaceOccurrence_eq_sum_simplex_omissions]
    simpa only [CubicalTucker.StaircaseFaceOccurrence.mk_vertex_eq] using
      hallSimplexBoundariesZero initial
  have hinternalBoundariesZero (initial : Bool) :
      ∑ τ : CubicalTucker.InternalStaircaseFace d m,
        CubicalTucker.alternatingFaceWeight initial label
          (fun j ↦ τ.1.vertex j) = 0 :=
    CubicalTucker.sum_internalAlternatingFaceWeight_eq_zero initial label
  have hendpointOccurrencesZero (initial : Bool) :
      ∑ τ : {τ : CubicalTucker.StaircaseFaceOccurrence d m //
          ¬(τ.omitted ≠ 0 ∧ τ.omitted ≠ Fin.last d)},
        CubicalTucker.alternatingFaceWeight initial label
          (fun j ↦ τ.1.vertex j) = 0 := by
    -- Split all face occurrences into internal and endpoint omissions; the
    -- total and internal sums already vanish.
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun τ : CubicalTucker.StaircaseFaceOccurrence d m ↦
        τ.omitted ≠ 0 ∧ τ.omitted ≠ Fin.last d)
      (fun τ ↦ CubicalTucker.alternatingFaceWeight initial label τ.vertex)
    rw [hinternalBoundariesZero initial, hallFaceOccurrencesZero initial] at hsplit
    simpa only [zero_add] using hsplit
  have hdpos : 0 < d := by omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  have hsharedFacetPresentationsZero (initial : Bool) :
      (∑ facet : CubicalTucker.PositiveNormalizedSharedFacet q m,
          CubicalTucker.alternatingFaceWeight initial label facet.1.1.vertex) +
        ∑ facet : CubicalTucker.BelowTopNormalizedSharedFacet q m,
          CubicalTucker.alternatingFaceWeight initial label facet.1.1.vertex = 0 := by
    -- Reindex the endpoint sum by the canonical normalized shared-facet
    -- equivalence, whose vertex theorem transports the alternating weight.
    rw [← CubicalTucker.sum_endpointStaircaseFaceOccurrence_eq_sum_sharedFacets]
    exact hendpointOccurrencesZero initial
  have hboundaryFacetSidesZero (initial : Bool) :
      ∑ side : CubicalTucker.SharedFacetSide q m with
          CubicalTucker.sharedFacetSideMate side = side,
        CubicalTucker.sharedFacetSideWeight
          (CubicalTucker.alternatingFaceWeight initial label) side = 0 := by
    -- Cancel the lower/upper pair of every internal facet. The fixed sides are
    -- exactly the lower-level-zero and upper-level-`2m` boundary facets.
    rw [← CubicalTucker.sum_sharedFacetSideWeight_eq_sum_fixed]
    simpa [CubicalTucker.sharedFacetSideWeight, Fintype.sum_sum_type] using
      hsharedFacetPresentationsZero initial
  have hboundaryAlternatingSumZero (initial : Bool) :
      ∑ facet : CubicalTucker.BoundarySharedFacet q m,
        CubicalTucker.alternatingFaceWeight initial label facet.vertex = 0 := by
    -- Transport the fixed endpoint-side sum to its canonical tagged boundary
    -- facet presentation.
    rw [← CubicalTucker.sum_fixedSharedFacetSideWeight_eq_boundary hm]
    exact hboundaryFacetSidesZero initial
  have hpositiveHemisphereAlternatingSumZero (initial : Bool) :
      (∑ facet : CubicalTucker.PositiveHemisphereBoundaryFacet q m,
          CubicalTucker.alternatingFaceWeight initial label facet.1.vertex) +
        ∑ facet : CubicalTucker.PositiveHemisphereBoundaryFacet q m,
          CubicalTucker.alternatingFaceWeight (!initial) label facet.1.vertex =
        0 := by
    -- Decompose the boundary into positive representatives and their reflected
    -- partners, converting reflection into the opposite initial sign.
    rw [← CubicalTucker.sum_boundaryAlternatingFaceWeight_eq_positiveHemisphere
      hm initial label hboundary]
    exact hboundaryAlternatingSumZero initial
  have hqpos : 0 < q := by omega
  have hendpointDistinctMate
      (occurrence : CubicalTucker.EndpointBoundaryFaceOccurrence q m) :
      ∃ mate : CubicalTucker.BoundaryFaceOccurrence q m,
        mate ≠ occurrence.1 ∧
          mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
    -- The extracted corner exchange completes the existing interior endpoint
    -- mate construction in every positive boundary dimension.
    exact occurrence.exists_distinct_mate_of_pos hqpos
  -- Route correction: endpoint geometry is now complete, including both
  -- extreme corners. The remaining step is coherence: turn the available
  -- ridge mates into a deterministic involution and identify its equatorial
  -- quotient with the lower-dimensional boundary recurrence.
  -- The corner transpose is now packaged as an endpoint occurrence, preserves
  -- its ridge, and normalizes through the exchanged active presentation.  The
  -- remaining geometric step is its explicit outer-side normal form and
  -- round-trip law; after that, the equatorial incidence recurrence can cancel
  -- the positive-hemisphere sum above.
  sorry

end StandardSphere
