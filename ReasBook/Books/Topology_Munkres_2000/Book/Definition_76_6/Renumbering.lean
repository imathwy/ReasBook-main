module

public import Topology_Munkres_2000.Book.Definition_76_6.Permutation
public import Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Logic.Equiv.Fin.Rotate
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

universe u v

namespace LabellingScheme.PolygonalRegions

variable {α : Type u}
/-- Concrete occurrence and cyclic edge-index data implementing one scheme permutation. -/
structure Renumbering (before after : LabellingScheme α) where
  permute : before.Permute after
  regionEquiv : before.Occurrence ≃ after.Occurrence
  edgeEquiv (region : after.Occurrence) :
    Fin (regionEquiv.symm region).1.1.length ≃ Fin region.1.1.length
  letter_eq (region : after.Occurrence) (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      (regionEquiv.symm region).1.1.get ((edgeEquiv region).symm edge)

namespace Renumbering

variable {before after : LabellingScheme α}

/-- The occurrence equivalence for the displayed append swap maps the newly adjoined
polygon occurrence to the newly adjoined swapped occurrence and fixes the remainder. -/
noncomputable def appendRegionEquiv (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length) :
    Occurrence (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest) ≃
      Occurrence (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest) :=
  (consOccurrenceEquiv ⟨y₀ ++ y₁, hLength⟩ rest).trans
    (consOccurrenceEquiv
      ⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ rest).symm

/-- The cyclic edge offset is `y₀.length` on the swapped polygon and zero on
each unchanged polygon occurrence. -/
noncomputable def appendEdgeOffset (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest)) : ℕ :=
  match consOccurrenceEquiv
    ⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ rest region with
  | none => y₀.length
  | some _ => 0

/-- Helper for Definition 76.6: the distinguished occurrence adjoined to a scheme has the
boundary length of the adjoined polygon word. -/
theorem consOccurrenceEquiv_symm_none_length (word : PolygonWord α)
    (scheme : LabellingScheme α) :
    ((consOccurrenceEquiv word scheme).symm none).1.1.length = word.1.length := by
  -- Project the boundary length from the explicit inverse image of `none`.
  have hselected := @Multiset.consEquiv_symm_none (PolygonWord α)
    (Classical.decEq _) scheme word
  exact congrArg (fun region : Occurrence (word ::ₘ scheme) ↦ region.1.1.length) hselected

/-- Helper for Definition 76.6: the distinguished occurrence adjoined to a scheme carries
exactly the adjoined polygon word. -/
theorem consOccurrenceEquiv_symm_none_word (word : PolygonWord α)
    (scheme : LabellingScheme α) :
    ((consOccurrenceEquiv word scheme).symm none).1 = word := by
  -- Project the polygon word from the explicit inverse image of `none`.
  have hselected := @Multiset.consEquiv_symm_none (PolygonWord α)
    (Classical.decEq _) scheme word
  exact congrArg (fun region : Occurrence (word ::ₘ scheme) ↦ region.1) hselected

/-- Helper for Definition 76.6: adjoining a polygon word leaves the boundary length of every
pre-existing occurrence unchanged. -/
theorem consOccurrenceEquiv_symm_some_length (word : PolygonWord α)
    (scheme : LabellingScheme α) (region : Occurrence scheme) :
    ((consOccurrenceEquiv word scheme).symm (some region)).1.1.length =
      region.1.1.length := by
  -- Project the boundary length from the explicit inverse image of a remainder occurrence.
  have hremainder := @Multiset.consEquiv_symm_some (PolygonWord α)
    (Classical.decEq _) scheme word region
  exact congrArg (fun occurrence : Occurrence (word ::ₘ scheme) ↦ occurrence.1.1.length)
    hremainder

/-- Helper for Definition 76.6: adjoining a polygon word leaves the polygon word of every
pre-existing occurrence unchanged. -/
theorem consOccurrenceEquiv_symm_some_word (word : PolygonWord α)
    (scheme : LabellingScheme α) (region : Occurrence scheme) :
    ((consOccurrenceEquiv word scheme).symm (some region)).1 = region.1 := by
  -- Project the polygon word from the explicit inverse image of a remainder occurrence.
  have hremainder := @Multiset.consEquiv_symm_some (PolygonWord α)
    (Classical.decEq _) scheme word region
  exact congrArg (fun occurrence : Occurrence (word ::ₘ scheme) ↦ occurrence.1) hremainder

/-- Helper for Definition 76.6: the append-swap occurrence equivalence preserves every
polygon boundary length. -/
theorem appendRegion_length (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest)) :
    ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length =
      region.1.1.length := by
  -- Split the target occurrence into the selected polygon or an unchanged remainder polygon.
  let sourceWord : PolygonWord α := ⟨y₀ ++ y₁, hLength⟩
  let targetWord : PolygonWord α :=
    ⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩
  let sourceEquiv := consOccurrenceEquiv sourceWord rest
  let targetEquiv := consOccurrenceEquiv targetWord rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have horiginal :
          (appendRegionEquiv y₀ y₁ rest hLength).symm (targetEquiv.symm none) =
            sourceEquiv.symm none := by
        change sourceEquiv.symm (targetEquiv (targetEquiv.symm none)) = sourceEquiv.symm none
        rw [targetEquiv.apply_symm_apply]
      rw [horiginal, consOccurrenceEquiv_symm_none_length,
        consOccurrenceEquiv_symm_none_length]
      simp [sourceWord, targetWord, List.length_append, Nat.add_comm]
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have horiginal :
          (appendRegionEquiv y₀ y₁ rest hLength).symm
              (targetEquiv.symm (some remainder)) =
            sourceEquiv.symm (some remainder) := by
        change sourceEquiv.symm (targetEquiv (targetEquiv.symm (some remainder))) =
          sourceEquiv.symm (some remainder)
        rw [targetEquiv.apply_symm_apply]
      rw [horiginal, consOccurrenceEquiv_symm_some_length,
        consOccurrenceEquiv_symm_some_length]

/-- Helper for Definition 76.6: adding a modular offset and then its complement restores an
index already lying below the modulus. -/
theorem addMod_complement_cancel {index offset modulus : ℕ}
    (hindex : index < modulus) (hoffset : offset ≤ modulus) :
    ((index + offset) % modulus + (modulus - offset)) % modulus = index := by
  -- Remove the inner remainder, cancel `offset` with its complement, and reduce the index.
  rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_sub_of_le hoffset]
  simpa [Nat.add_mod] using Nat.mod_eq_of_lt hindex

/-- Helper for Definition 76.6: adding a modular complement and then the original offset
restores an index already lying below the modulus. -/
theorem addComplement_mod_cancel {index offset modulus : ℕ}
    (hindex : index < modulus) (hoffset : offset ≤ modulus) :
    ((index + (modulus - offset)) % modulus + offset) % modulus = index := by
  -- Remove the inner remainder, cancel the complement, and reduce the original index.
  rw [Nat.mod_add_mod, Nat.add_assoc, Nat.sub_add_cancel hoffset]
  simpa [Nat.add_mod] using Nat.mod_eq_of_lt hindex

/-- Helper for Definition 76.6: list lookup is preserved when both the list and the finite
index value are identified. -/
theorem get_eq_of_list_eq_of_val_eq {γ : Type*} {first second : List γ}
    (firstIndex : Fin first.length) (secondIndex : Fin second.length)
    (hlists : first = second) (hvalues : firstIndex.1 = secondIndex.1) :
    first.get firstIndex = second.get secondIndex := by
  -- Package each list with its dependent finite index and compare the resulting sigma values.
  have hboundary :
      (⟨first, firstIndex⟩ : (list : List γ) × Fin list.length) =
        ⟨second, secondIndex⟩ := by
    apply Sigma.ext hlists
    exact (Fin.heq_ext_iff (congrArg List.length hlists)).mpr hvalues
  exact congrArg (fun p : (list : List γ) × Fin list.length ↦ p.1.get p.2) hboundary

/-- The modular index defining the inverse cyclic edge shift is in range. -/
theorem appendEdgeBackward_lt (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest))
    (edge : Fin region.1.1.length) :
    (edge + appendEdgeOffset y₀ y₁ rest hLength region) %
        ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length <
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length := by
  -- Every occurrence is a polygon word, so its boundary length is positive.
  have hpolygon := ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.2
  apply Nat.mod_lt
  omega

/-- The inverse edge map adds the cut position modulo the polygon length on the
selected polygon and acts trivially on every occurrence from the remainder. -/
noncomputable def appendEdgeBackward (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest))
    (edge : Fin region.1.1.length) :
    Fin ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length :=
  ⟨(edge + appendEdgeOffset y₀ y₁ rest hLength region) %
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length,
    appendEdgeBackward_lt y₀ y₁ rest hLength region edge⟩

/-- The modular index defining the forward cyclic edge shift is in range. -/
theorem appendEdgeForward_lt (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest))
    (edge : Fin ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length) :
    (edge + (region.1.1.length - appendEdgeOffset y₀ y₁ rest hLength region %
        region.1.1.length)) % region.1.1.length < region.1.1.length := by
  -- The target occurrence likewise has at least three boundary edges.
  have hpolygon := region.1.2
  apply Nat.mod_lt
  omega

/-- The explicit forward and backward modular edge shifts are inverse in the
original edge-index type. -/
theorem appendEdgeForward_leftInv (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest)) :
    Function.LeftInverse (appendEdgeBackward y₀ y₁ rest hLength region)
      (fun edge ↦
        ⟨(edge + (region.1.1.length - appendEdgeOffset y₀ y₁ rest hLength region %
            region.1.1.length)) % region.1.1.length,
          appendEdgeForward_lt y₀ y₁ rest hLength region edge⟩) := by
  intro edge
  -- Normalize both finite types to the common boundary length, then solve the modular identity.
  apply Fin.ext
  simp only [appendEdgeBackward]
  have hsame := appendRegion_length y₀ y₁ rest hLength region
  have hpolygon := region.1.2
  have hoffset : appendEdgeOffset y₀ y₁ rest hLength region % region.1.1.length ≤
      region.1.1.length := Nat.le_of_lt (Nat.mod_lt _ (by omega))
  have hindex : edge.1 < region.1.1.length := hsame ▸ edge.2
  have hcancel := addComplement_mod_cancel hindex hoffset
  let shifted :=
    (edge.1 + (region.1.1.length - appendEdgeOffset y₀ y₁ rest hLength region %
      region.1.1.length)) % region.1.1.length
  calc
    (shifted + appendEdgeOffset y₀ y₁ rest hLength region) %
        ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length =
      (shifted + appendEdgeOffset y₀ y₁ rest hLength region) %
        region.1.1.length := congrArg
          (fun modulus ↦ (shifted + appendEdgeOffset y₀ y₁ rest hLength region) % modulus)
          hsame
    _ = (shifted + appendEdgeOffset y₀ y₁ rest hLength region %
        region.1.1.length) % region.1.1.length :=
      (Nat.add_mod_mod shifted (appendEdgeOffset y₀ y₁ rest hLength region)
        region.1.1.length).symm
    _ = edge.1 := hcancel

/-- The explicit forward and backward modular edge shifts are inverse in the
swapped edge-index type. -/
theorem appendEdgeForward_rightInv (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest)) :
    Function.RightInverse (appendEdgeBackward y₀ y₁ rest hLength region)
      (fun edge ↦
        ⟨(edge + (region.1.1.length - appendEdgeOffset y₀ y₁ rest hLength region %
            region.1.1.length)) % region.1.1.length,
          appendEdgeForward_lt y₀ y₁ rest hLength region edge⟩) := by
  intro edge
  -- The inverse modular shift followed by the forward shift cancels modulo the same length.
  apply Fin.ext
  simp only [appendEdgeBackward]
  have hsame := appendRegion_length y₀ y₁ rest hLength region
  have hpolygon := region.1.2
  have hoffset : appendEdgeOffset y₀ y₁ rest hLength region % region.1.1.length ≤
      region.1.1.length := Nat.le_of_lt (Nat.mod_lt _ (by omega))
  rw [hsame, ← Nat.add_mod_mod edge.1
    (appendEdgeOffset y₀ y₁ rest hLength region) region.1.1.length]
  exact addMod_complement_cancel edge.2 hoffset

/-- The edge equivalence for the append swap is the cyclic shift whose inverse
adds `y₀.length` modulo the boundary length. -/
noncomputable def appendEdgeEquiv (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest)) :
    Fin ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length ≃
      Fin region.1.1.length where
  toFun edge :=
    ⟨(edge + (region.1.1.length - appendEdgeOffset y₀ y₁ rest hLength region %
        region.1.1.length)) % region.1.1.length,
      appendEdgeForward_lt y₀ y₁ rest hLength region edge⟩
  invFun := appendEdgeBackward y₀ y₁ rest hLength region
  left_inv := appendEdgeForward_leftInv y₀ y₁ rest hLength region
  right_inv := appendEdgeForward_rightInv y₀ y₁ rest hLength region

/-- The forward append-swap edge equivalence is addition of its fixed offset
complement modulo the target boundary length. -/
theorem appendEdgeEquiv_val (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest))
    (edge : Fin
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length) :
    (appendEdgeEquiv y₀ y₁ rest hLength region edge).1 =
      (edge.1 + (region.1.1.length -
        appendEdgeOffset y₀ y₁ rest hLength region % region.1.1.length)) %
          region.1.1.length := by
  -- This is the value projection of the forward modular shift.
  rfl

/-- The append-swap edge equivalence commutes with cyclic successor on every
polygon occurrence. -/
theorem appendEdgeEquiv_finRotate (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest))
    (edge : Fin
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length) :
    appendEdgeEquiv y₀ y₁ rest hLength region
        (finRotate _ edge) =
      finRotate _ (appendEdgeEquiv y₀ y₁ rest hLength region edge) := by
  -- Both sides add the fixed cyclic offset and one, in opposite orders.
  apply Fin.ext
  have hlength := appendRegion_length y₀ y₁ rest hLength region
  let shift := region.1.1.length -
    appendEdgeOffset y₀ y₁ rest hLength region % region.1.1.length
  letI : NeZero
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num)
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.2)⟩
  letI : NeZero region.1.1.length :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) region.1.2)⟩
  have honeSource :
      ((1 : Fin ((appendRegionEquiv y₀ y₁ rest hLength).symm
        region).1.1.length) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le (by norm_num)
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.2
  have hrotateSource :
      (finRotate
        ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.length edge).1 =
        (edge.1 + 1) % region.1.1.length := by
    rw [finRotate_apply, Fin.val_add]
    rw [honeSource]
    exact congrArg (fun modulus ↦ (edge.1 + 1) % modulus) hlength
  have honeTarget : ((1 : Fin region.1.1.length) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le (by norm_num) region.1.2
  have hrotateTarget :
      (finRotate region.1.1.length
        (appendEdgeEquiv y₀ y₁ rest hLength region edge)).1 =
        ((appendEdgeEquiv y₀ y₁ rest hLength region edge).1 + 1) %
          region.1.1.length := by
    rw [finRotate_apply, Fin.val_add, honeTarget]
  calc
    (appendEdgeEquiv y₀ y₁ rest hLength region
        (finRotate _ edge)).1 =
        ((finRotate _ edge).1 + shift) % region.1.1.length :=
      appendEdgeEquiv_val y₀ y₁ rest hLength region (finRotate _ edge)
    _ = (((edge.1 + 1) % region.1.1.length) + shift) %
        region.1.1.length := congrArg
          (fun index ↦ (index + shift) % region.1.1.length) hrotateSource
    _ = (edge.1 + 1 + shift) % region.1.1.length := by
      rw [Nat.mod_add_mod]
    _ = (edge.1 + shift + 1) % region.1.1.length := by
      congr 1
      omega
    _ = (((edge.1 + shift) % region.1.1.length) + 1) %
        region.1.1.length := by
      rw [Nat.mod_add_mod]
    _ = ((appendEdgeEquiv y₀ y₁ rest hLength region edge).1 + 1) %
        region.1.1.length := congrArg
          (fun index ↦ (index + 1) % region.1.1.length)
          (appendEdgeEquiv_val y₀ y₁ rest hLength region edge).symm
    _ = (finRotate region.1.1.length
        (appendEdgeEquiv y₀ y₁ rest hLength region edge)).1 :=
      hrotateTarget.symm

/-- The append-swap occurrence and cyclic edge maps preserve every signed edge label. -/
theorem appendLetter_eq (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest))
    (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      ((appendRegionEquiv y₀ y₁ rest hLength).symm region).1.1.get
        ((appendEdgeEquiv y₀ y₁ rest hLength region).symm edge) := by
  -- Split the target occurrence into the rotated polygon and an unchanged remainder polygon.
  let sourceWord : PolygonWord α := ⟨y₀ ++ y₁, hLength⟩
  let targetWord : PolygonWord α :=
    ⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩
  let sourceEquiv := consOccurrenceEquiv sourceWord rest
  let targetEquiv := consOccurrenceEquiv targetWord rest
  cases hposition : targetEquiv region with
  | none =>
      have hregion : region = targetEquiv.symm none :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have horiginal :
          (appendRegionEquiv y₀ y₁ rest hLength).symm (targetEquiv.symm none) =
            sourceEquiv.symm none := by
        change sourceEquiv.symm (targetEquiv (targetEquiv.symm none)) = sourceEquiv.symm none
        rw [targetEquiv.apply_symm_apply]
      have htargetList : (targetEquiv.symm none).1.1 =
          (y₀ ++ y₁).rotate y₀.length := by
        calc
          (targetEquiv.symm none).1.1 = targetWord.1 :=
            congrArg Subtype.val (consOccurrenceEquiv_symm_none_word targetWord rest)
          _ = y₁ ++ y₀ := rfl
          _ = (y₀ ++ y₁).rotate y₀.length :=
            (List.rotate_append_length_eq y₀ y₁).symm
      have horiginalList :
          ((appendRegionEquiv y₀ y₁ rest hLength).symm
            (targetEquiv.symm none)).1.1 = y₀ ++ y₁ := by
        calc
          _ = (sourceEquiv.symm none).1.1 := congrArg (fun r ↦ r.1.1) horiginal
          _ = sourceWord.1 :=
            congrArg Subtype.val (consOccurrenceEquiv_symm_none_word sourceWord rest)
          _ = y₀ ++ y₁ := rfl
      let rotatedEdge : Fin ((y₀ ++ y₁).rotate y₀.length).length :=
        ⟨edge.1, by rw [← htargetList]; exact edge.2⟩
      have hoffset : appendEdgeOffset y₀ y₁ rest hLength (targetEquiv.symm none) =
          y₀.length := by
        change (match targetEquiv (targetEquiv.symm none) with
          | none => y₀.length
          | some _ => 0) = y₀.length
        rw [targetEquiv.apply_symm_apply]
      have hbackward :
          ((appendEdgeEquiv y₀ y₁ rest hLength (targetEquiv.symm none)).symm edge).1 =
            (edge.1 + y₀.length) % (y₀ ++ y₁).length := by
        change (edge.1 + appendEdgeOffset y₀ y₁ rest hLength
          (targetEquiv.symm none)) %
            ((appendRegionEquiv y₀ y₁ rest hLength).symm
              (targetEquiv.symm none)).1.1.length = _
        rw [hoffset, congrArg List.length horiginalList]
      calc
        (targetEquiv.symm none).1.1.get edge =
            ((y₀ ++ y₁).rotate y₀.length).get rotatedEdge :=
          get_eq_of_list_eq_of_val_eq edge rotatedEdge htargetList rfl
        _ = (y₀ ++ y₁).get
            ⟨(rotatedEdge + y₀.length) % (y₀ ++ y₁).length,
              Nat.mod_lt _ (List.length_rotate (y₀ ++ y₁) y₀.length ▸ rotatedEdge.pos)⟩ :=
          List.get_rotate (y₀ ++ y₁) y₀.length rotatedEdge
        _ = ((appendRegionEquiv y₀ y₁ rest hLength).symm
              (targetEquiv.symm none)).1.1.get
            ((appendEdgeEquiv y₀ y₁ rest hLength
              (targetEquiv.symm none)).symm edge) :=
          get_eq_of_list_eq_of_val_eq _ _ horiginalList.symm hbackward.symm
  | some remainder =>
      have hregion : region = targetEquiv.symm (some remainder) :=
        targetEquiv.apply_eq_iff_eq_symm_apply.mp hposition
      subst region
      have horiginal :
          (appendRegionEquiv y₀ y₁ rest hLength).symm
              (targetEquiv.symm (some remainder)) =
            sourceEquiv.symm (some remainder) := by
        change sourceEquiv.symm (targetEquiv (targetEquiv.symm (some remainder))) =
          sourceEquiv.symm (some remainder)
        rw [targetEquiv.apply_symm_apply]
      have htargetList : (targetEquiv.symm (some remainder)).1.1 = remainder.1.1 :=
        congrArg Subtype.val (consOccurrenceEquiv_symm_some_word targetWord rest remainder)
      have horiginalList :
          ((appendRegionEquiv y₀ y₁ rest hLength).symm
            (targetEquiv.symm (some remainder))).1.1 = remainder.1.1 := by
        calc
          _ = (sourceEquiv.symm (some remainder)).1.1 := congrArg (fun r ↦ r.1.1) horiginal
          _ = remainder.1.1 :=
            congrArg Subtype.val (consOccurrenceEquiv_symm_some_word sourceWord rest remainder)
      have hoffset : appendEdgeOffset y₀ y₁ rest hLength
          (targetEquiv.symm (some remainder)) = 0 := by
        change (match targetEquiv (targetEquiv.symm (some remainder)) with
          | none => y₀.length
          | some _ => 0) = 0
        rw [targetEquiv.apply_symm_apply]
      have hedgeLt : edge.1 < remainder.1.1.length :=
        edge.2.trans_eq (congrArg List.length htargetList)
      have hbackward :
          ((appendEdgeEquiv y₀ y₁ rest hLength
            (targetEquiv.symm (some remainder))).symm edge).1 = edge.1 := by
        change (edge.1 + appendEdgeOffset y₀ y₁ rest hLength
          (targetEquiv.symm (some remainder))) %
            ((appendRegionEquiv y₀ y₁ rest hLength).symm
              (targetEquiv.symm (some remainder))).1.1.length = edge.1
        rw [hoffset, Nat.add_zero, congrArg List.length horiginalList,
          Nat.mod_eq_of_lt hedgeLt]
      exact get_eq_of_list_eq_of_val_eq edge _
        (htargetList.trans horiginalList.symm) hbackward.symm

/-- The concrete vertex renumbering implementing the displayed append swap. -/
noncomputable def ofAppend (y₀ y₁ : List (α × Bool)) (rest : LabellingScheme α)
    (hLength : 3 ≤ (y₀ ++ y₁).length) :
    Renumbering
      (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest)
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest) where
  permute := LabellingScheme.Permute.ofAppend y₀ y₁ rest hLength
  regionEquiv := appendRegionEquiv y₀ y₁ rest hLength
  edgeEquiv := appendEdgeEquiv y₀ y₁ rest hLength
  letter_eq := appendLetter_eq y₀ y₁ rest hLength

/-- The source and target occurrences of the concrete append-swap
renumbering have equal boundary lengths. -/
theorem ofAppend_region_length (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest)) :
    (((ofAppend y₀ y₁ rest hLength).regionEquiv.symm region).1.1.length) =
      region.1.1.length := by
  -- The `ofAppend` projection is the concrete append occurrence equivalence.
  exact appendRegion_length y₀ y₁ rest hLength region

/-- The edge equivalence of the concrete append-swap renumbering commutes with
cyclic successor. -/
theorem ofAppend_edgeEquiv_finRotate (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : Occurrence
      (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest))
    (edge : Fin
      (((ofAppend y₀ y₁ rest hLength).regionEquiv.symm region).1.1.length)) :
    (ofAppend y₀ y₁ rest hLength).edgeEquiv region (finRotate _ edge) =
      finRotate _ ((ofAppend y₀ y₁ rest hLength).edgeEquiv region edge) := by
  -- Reduce the two projections to the checked modular commutation theorem.
  exact appendEdgeEquiv_finRotate y₀ y₁ rest hLength region edge

/-- The distinguished original polygon occurrence maps to the distinguished swapped one. -/
theorem appendRegionEquiv_selected (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length) :
    appendRegionEquiv y₀ y₁ rest hLength
        ((consOccurrenceEquiv ⟨y₀ ++ y₁, hLength⟩ rest).symm none) =
      (consOccurrenceEquiv
        ⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ rest).symm none := by
  -- Both adjoining-occurrence equivalences send the distinguished occurrence to `none`.
  simp [appendRegionEquiv]

/-- Every occurrence belonging to the unchanged remainder is fixed by the append
occurrence equivalence. -/
theorem appendRegionEquiv_remainder (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (region : rest.Occurrence) :
    appendRegionEquiv y₀ y₁ rest hLength
        ((consOccurrenceEquiv ⟨y₀ ++ y₁, hLength⟩ rest).symm
          (some region)) =
      (consOccurrenceEquiv
        ⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ rest).symm
          (some region) := by
  -- The composite occurrence equivalence leaves every remainder occurrence in place.
  simp [appendRegionEquiv]

/-- On the selected polygon, the inverse edge map is addition by `y₀.length`
modulo the boundary length. -/
theorem appendEdgeBackward_selected (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length)
    (edge : Fin (y₁ ++ y₀).length) :
    (appendEdgeBackward y₀ y₁ rest hLength
      ((consOccurrenceEquiv
        ⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ rest).symm none)
      edge).1 = (edge + y₀.length) % (y₀ ++ y₁).length := by
  -- On the distinguished occurrence, the offset definition selects the cut length `y₀.length`.
  have hlength :
      ((consOccurrenceEquiv ⟨y₀ ++ y₁, hLength⟩ rest).symm none).1.1.length =
        (y₀ ++ y₁).length := by
    have hselected := @Multiset.consEquiv_symm_none (PolygonWord α)
      (Classical.decEq _) rest ⟨y₀ ++ y₁, hLength⟩
    exact congrArg
      (fun region : Occurrence (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest) ↦ region.1.1.length)
      hselected
  simp [appendEdgeBackward, appendEdgeOffset, appendRegionEquiv, hlength]

/-- The image of a polygon occurrence under a renumbering. -/
@[expose]
def mapOccurrence (renumbering : Renumbering before after)
    (region : before.Occurrence) : after.Occurrence :=
  renumbering.regionEquiv region

/-- Applying `mapOccurrence` is the forward map of the occurrence equivalence. -/
@[simp]
theorem mapOccurrence_eq (renumbering : Renumbering before after)
    (region : before.Occurrence) :
    renumbering.mapOccurrence region = renumbering.regionEquiv region := rfl

/-- The polygonal regions obtained by cyclically reindexing the selected polygon's edges. -/
@[expose]
def regions (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) : PolygonalRegions after where
  Point region := original.Point (renumbering.regionEquiv.symm region)
  topology region := original.topology (renumbering.regionEquiv.symm region)
  edge region edge t :=
    original.edge (renumbering.regionEquiv.symm region)
      ((renumbering.edgeEquiv region).symm edge) t

/-- A renumbered region uses the original edge at the inverse edge index and
the same affine parameter. -/
theorem regions_edge (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) (region : Occurrence after)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    (renumbering.regions original).edge region edge t =
      original.edge (renumbering.regionEquiv.symm region)
        ((renumbering.edgeEquiv region).symm edge) t := by
  -- This is the edge projection of the renumbered family.
  rfl

/-- The occurrence equivalence induces an equivalence of the disjoint unions of region points. -/
def sourceEquiv (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) :
    original.Source ≃ (renumbering.regions original).Source :=
  Equiv.sigmaCongr renumbering.regionEquiv fun region ↦
    Equiv.cast (congrArg original.Point (renumbering.regionEquiv.left_inv region).symm)

/-- Helper for Definition 76.6: the source equivalence induced by renumbering is
continuous. -/
theorem continuous_sourceEquiv (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) :
    Continuous (renumbering.sourceEquiv original) := by
  -- Check continuity componentwise in the disjoint-union topology.
  change @Continuous _ _ original.sourceTopology
    (renumbering.regions original).sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let target := renumbering.regionEquiv region
  have hregion := renumbering.regionEquiv.left_inv region
  have hcast := continuous_regionPointCast original hregion
  have hinclusion :
      @Continuous ((renumbering.regions original).Point target)
        (renumbering.regions original).Source
        ((renumbering.regions original).topology target)
        (renumbering.regions original).sourceTopology (Sigma.mk target) :=
    continuous_iSup_rng (i := target) (f := Sigma.mk target)
      (continuous_coinduced_rng (f := Sigma.mk target))
  dsimp [sourceEquiv, Equiv.sigmaCongr]
  exact @Continuous.comp
    (original.Point region) ((renumbering.regions original).Point target)
    (renumbering.regions original).Source (original.topology region)
    ((renumbering.regions original).topology target)
    (renumbering.regions original).sourceTopology _ _ hinclusion hcast

/-- Helper for Definition 76.6: the inverse source equivalence induced by renumbering is
continuous. -/
theorem continuous_sourceEquiv_symm (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) :
    Continuous (renumbering.sourceEquiv original).symm := by
  -- On each target summand the inverse is the inclusion of its original component.
  change @Continuous _ _ (renumbering.regions original).sourceTopology
    original.sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let source := renumbering.regionEquiv.symm region
  letI : TopologicalSpace (original.Point source) := original.topology source
  have hinclusion : Continuous
      (Sigma.mk source : original.Point source → original.Source) :=
    continuous_iSup_rng (i := source) (f := Sigma.mk source)
      (continuous_coinduced_rng (f := Sigma.mk source))
  have hinverse :
      (renumbering.sourceEquiv original).symm ∘ Sigma.mk region =
        (Sigma.mk source : original.Point source → original.Source) := by
    funext point
    dsimp only [Function.comp_apply]
    dsimp [regions, source] at point
    apply (renumbering.sourceEquiv original).injective
    rw [(renumbering.sourceEquiv original).apply_symm_apply]
    apply Sigma.ext
    · exact renumbering.regionEquiv.apply_symm_apply region |>.symm
    · exact (cast_heq _ _).symm
  rw [hinverse]
  exact hinclusion

/-- The source equivalence induced by a renumbering preserves the disjoint-union topologies. -/
theorem sourceEquiv_isOpen_iff (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after)
    (s : Set (renumbering.regions original).Source) :
    IsOpen (renumbering.sourceEquiv original ⁻¹' s) ↔ IsOpen s := by
  constructor
  · intro hopen
    -- Pull the preimage back along the continuous inverse and cancel the equivalence.
    have hpreimage :
        (renumbering.sourceEquiv original).symm ⁻¹'
            (renumbering.sourceEquiv original ⁻¹' s) = s := by
      ext point
      simp only [Set.mem_preimage, Equiv.apply_symm_apply]
    rw [← hpreimage]
    exact (renumbering.continuous_sourceEquiv_symm original).isOpen_preimage _ hopen
  · intro hopen
    exact (renumbering.continuous_sourceEquiv original).isOpen_preimage _ hopen

/-- The renumbering equivalence is a homeomorphism of the disjoint unions of region points. -/
def sourceHomeomorph (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) :
    original.Source ≃ₜ (renumbering.regions original).Source :=
  (renumbering.sourceEquiv original).toHomeomorph
    (renumbering.sourceEquiv_isOpen_iff original)

/-- The inverse renumbering source homeomorphism has the same underlying
function as the inverse source equivalence. -/
theorem sourceHomeomorph_symm_apply
    (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after)
    (x : (renumbering.regions original).Source) :
    (renumbering.sourceHomeomorph original).symm x =
      (renumbering.sourceEquiv original).symm x := by
  -- `toHomeomorph` retains both functions of the source equivalence.
  rfl

/-- Helper for Definition 76.6: the renumbering source equivalence carries each original
boundary point to the corresponding reindexed boundary point. -/
theorem sourceEquiv_edge (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) (region : Occurrence before)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    renumbering.sourceEquiv original ⟨region, original.edge region edge t⟩ =
      ⟨renumbering.regionEquiv region,
        (renumbering.regions original).edge (renumbering.regionEquiv region)
          (renumbering.edgeEquiv (renumbering.regionEquiv region)
            (Fin.cast
              (congrArg (fun r : Occurrence before ↦ r.1.1.length)
                (renumbering.regionEquiv.left_inv region)).symm edge)) t⟩ := by
  -- Compare the sigma components, then cancel the inverse occurrence and edge equivalences.
  apply Sigma.ext
  · rfl
  · have hregion := renumbering.regionEquiv.left_inv region
    let sourceEdge := Fin.cast
      (congrArg (fun r : Occurrence before ↦ r.1.1.length) hregion).symm edge
    have hsourceEdge : HEq sourceEdge edge :=
      (Fin.heq_ext_iff
        (congrArg (fun r : Occurrence before ↦ r.1.1.length) hregion)).mpr rfl
    have hindex :
        (⟨renumbering.regionEquiv.symm (renumbering.regionEquiv region),
            (renumbering.edgeEquiv (renumbering.regionEquiv region)).symm
              (renumbering.edgeEquiv (renumbering.regionEquiv region) sourceEdge)⟩ :
          (r : Occurrence before) × Fin r.1.1.length) = ⟨region, edge⟩ := by
      apply Sigma.ext hregion
      exact (heq_of_eq
        ((renumbering.edgeEquiv (renumbering.regionEquiv region)).symm_apply_apply
          sourceEdge)).trans hsourceEdge
    have hedge := congr_arg_heq
      (fun p : (r : Occurrence before) × Fin r.1.1.length ↦
        original.edge p.1 p.2 t) hindex
    dsimp [sourceEquiv, Equiv.sigmaCongr, regions, sourceEdge]
    exact (cast_heq _ _).trans hedge.symm

/-- Helper for Definition 76.6: pulling a renumbered boundary point back through the
source equivalence recovers its original occurrence, edge index, and parameter. -/
theorem sourceEquiv_symm_edge (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) (region : Occurrence after)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    (renumbering.sourceEquiv original).symm
        ⟨region, (renumbering.regions original).edge region edge t⟩ =
      ⟨renumbering.regionEquiv.symm region,
        original.edge (renumbering.regionEquiv.symm region)
          ((renumbering.edgeEquiv region).symm edge) t⟩ := by
  -- Apply the forward equivalence and normalize the copied edge projection.
  apply (renumbering.sourceEquiv original).injective
  rw [(renumbering.sourceEquiv original).apply_symm_apply]
  apply Sigma.ext
  · exact renumbering.regionEquiv.apply_symm_apply region |>.symm
  · dsimp [sourceEquiv, Equiv.sigmaCongr, regions]
    exact (cast_heq _ _).symm

/-- Helper for Definition 76.6: lookup at a forward-reindexed edge recovers the original
boundary letter. -/
theorem sourceLetter_eq (renumbering : Renumbering before after)
    (region : Occurrence before) (edge : Fin region.1.1.length) :
    (renumbering.regionEquiv region).1.1.get
        (renumbering.edgeEquiv (renumbering.regionEquiv region)
          (Fin.cast
            (congrArg (fun r : Occurrence before ↦ r.1.1.length)
              (renumbering.regionEquiv.left_inv region)).symm edge)) =
      region.1.1.get edge := by
  -- Use `letter_eq`, then cancel the inverse occurrence and edge equivalences together.
  rw [renumbering.letter_eq]
  have hregion := renumbering.regionEquiv.left_inv region
  let sourceEdge := Fin.cast
    (congrArg (fun r : Occurrence before ↦ r.1.1.length) hregion).symm edge
  have hsourceEdge : HEq sourceEdge edge :=
    (Fin.heq_ext_iff
      (congrArg (fun r : Occurrence before ↦ r.1.1.length) hregion)).mpr rfl
  have hboundary :
      (⟨renumbering.regionEquiv.symm (renumbering.regionEquiv region),
          (renumbering.edgeEquiv (renumbering.regionEquiv region)).symm
            (renumbering.edgeEquiv (renumbering.regionEquiv region) sourceEdge)⟩ :
        (r : Occurrence before) × Fin r.1.1.length) = ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    exact (heq_of_eq
      ((renumbering.edgeEquiv (renumbering.regionEquiv region)).symm_apply_apply
        sourceEdge)).trans hsourceEdge
  exact congrArg
    (fun p : (r : Occurrence before) × Fin r.1.1.length ↦ p.1.1.1.get p.2)
    hboundary

/-- Cyclic edge reindexing preserves and reflects direct labelled-edge pairings. -/
theorem edgeRelated_iff (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after)
    (x y : original.Source) :
    original.EdgeRelated x y ↔
      (renumbering.regions original).EdgeRelated (renumbering.sourceEquiv original x)
        (renumbering.sourceEquiv original y) := by
  rw [edgeRelated_iff_exists_boundaryData, edgeRelated_iff_exists_boundaryData]
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let mapped₁ := renumbering.regionEquiv region₁
    let mapped₂ := renumbering.regionEquiv region₂
    let mappedEdge₁ := renumbering.edgeEquiv mapped₁
      (Fin.cast
        (congrArg (fun r : Occurrence before ↦ r.1.1.length)
          (renumbering.regionEquiv.left_inv region₁)).symm edge₁)
    let mappedEdge₂ := renumbering.edgeEquiv mapped₂
      (Fin.cast
        (congrArg (fun r : Occurrence before ↦ r.1.1.length)
          (renumbering.regionEquiv.left_inv region₂)).symm edge₂)
    refine ⟨mapped₁, mapped₂, mappedEdge₁, mappedEdge₂, t, ?_, ?_, ?_⟩
    · -- Forward-reindexed boundary letters are the original signed letters.
      simpa only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂,
        renumbering.sourceLetter_eq] using hlabel
    · -- The source equivalence computes on the first original boundary point.
      rw [hx, renumbering.sourceEquiv_edge]
    · -- It computes on the second point and preserves the orientation comparison.
      rw [hy, renumbering.sourceEquiv_edge]
      dsimp only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂]
      simp only [renumbering.sourceLetter_eq]
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let source₁ := renumbering.regionEquiv.symm region₁
    let source₂ := renumbering.regionEquiv.symm region₂
    let sourceEdge₁ := (renumbering.edgeEquiv region₁).symm edge₁
    let sourceEdge₂ := (renumbering.edgeEquiv region₂).symm edge₂
    refine ⟨source₁, source₂, sourceEdge₁, sourceEdge₂, t, ?_, ?_, ?_⟩
    · -- The structure's letter equation identifies each target letter with its source letter.
      simpa only [source₁, source₂, sourceEdge₁, sourceEdge₂,
        renumbering.letter_eq] using hlabel
    · -- Pull the first target boundary point back through the source equivalence.
      have hx' := congrArg (renumbering.sourceEquiv original).symm hx
      simpa only [Equiv.symm_apply_apply, renumbering.sourceEquiv_symm_edge] using hx'
    · -- Pull back the second point and rewrite its unchanged signed letters.
      have hy' := congrArg (renumbering.sourceEquiv original).symm hy
      simpa only [Equiv.symm_apply_apply, renumbering.sourceEquiv_symm_edge,
        renumbering.letter_eq] using hy'

/-- Cyclic edge reindexing preserves and reflects the generated identification relation. -/
theorem identified_iff (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after)
    (x y : original.Source) :
    original.Identified.r x y ↔
      (renumbering.regions original).Identified.r (renumbering.sourceEquiv original x)
        (renumbering.sourceEquiv original y) := by
  -- Lift the direct-relation comparison through the generated equivalence relation.
  rw [identified_iff_generatedEdgeRelated, identified_iff_generatedEdgeRelated]
  exact (eqvGen_equiv_iff (renumbering.sourceEquiv original)
    (fun first second ↦ (renumbering.edgeRelated_iff original first second).symm)
    x y).symm

/-- The source equivalence descends to an equivalence of quotient realizations. -/
def realizationEquiv (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) :
    Quotient original.Identified ≃ Quotient (renumbering.regions original).Identified :=
  Quotient.congr (renumbering.sourceEquiv original) (renumbering.identified_iff original)

/-- The quotient equivalence induced by a renumbering preserves the quotient topologies. -/
theorem realizationEquiv_isOpen_iff (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after)
    (s : Set (Quotient (renumbering.regions original).Identified)) :
    IsOpen (renumbering.realizationEquiv original ⁻¹' s) ↔ IsOpen s := by
  -- The canonical quotient homeomorphism has the displayed realization equivalence underneath.
  exact (Homeomorph.Quotient.congr (renumbering.sourceHomeomorph original)
    (renumbering.identified_iff original)).isOpen_preimage

/-- Renumbering a polygon's vertices induces a homeomorphism of quotient realizations. -/
def realizationHomeomorph (original : PolygonalRegions.{u, v} before)
    (renumbering : Renumbering before after) :
    Quotient original.Identified ≃ₜ Quotient (renumbering.regions original).Identified :=
  (renumbering.realizationEquiv original).toHomeomorph
    (renumbering.realizationEquiv_isOpen_iff original)


end Renumbering

end LabellingScheme.PolygonalRegions
