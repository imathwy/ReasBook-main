import Mathlib
import StacksProject_2024.Chap10.Lemma_10_13_3

-- Two-slot insertion and deletion helpers for Lemma 10.13.4.

open scoped TensorProduct
open PiTensorProduct exteriorPower

section

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
variable (n : ℕ) (M : Type) [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M]

/-- Helper for Lemma 10.13.4: an ordered pair of tensor slots forces the ambient tensor degree to
be at least `2`. -/
lemma two_le_of_tensorSlotPair {n : ℕ} (p : TensorSlotPair n) : 2 ≤ n := by
  -- An increasing pair of slots needs room for at least two indices.
  rcases p with ⟨⟨i, j⟩, hij⟩
  omega

/-- Helper for Lemma 10.13.4: the left distinguished slot in the auxiliary two-slot insertion
model. -/
abbrev leftTensorSlot {n : ℕ} (p : TensorSlotPair (n + 2)) : Fin (n + 2) :=
  p.1.1

/-- Helper for Lemma 10.13.4: the right distinguished slot in the auxiliary two-slot insertion
model. -/
abbrev rightTensorSlot {n : ℕ} (p : TensorSlotPair (n + 2)) : Fin (n + 2) :=
  p.1.2

/-- Helper for Lemma 10.13.4: after deleting the left distinguished slot, the right one becomes a
slot of the remaining `n + 1` indices. -/
abbrev leftTensorSlotCast {n : ℕ} (p : TensorSlotPair (n + 2)) : Fin (n + 1) :=
  (leftTensorSlot p).castLT (Fin.val_lt_last (Fin.ne_last_of_lt p.2))

/-- Helper for Lemma 10.13.4: the explicit auxiliary tuple obtained by inserting two entries into
chosen tensor slots before reindexing back to degree `n`. -/
def insertTwoTensorEntriesAux {n : ℕ} (p : TensorSlotPair (n + 2)) (x y : M)
    (m : Fin n → M) :
    Fin (n + 2) → M :=
  Fin.insertNth (leftTensorSlot p) x
    (Fin.insertNth ((leftTensorSlotCast p).predAbove (rightTensorSlot p)) y m)

/-- Helper for Lemma 10.13.4: reindex an ordered pair of slots in `Fin n` as an ordered pair of
slots in `Fin ((n - 2) + 2)`. -/
def castTwoSlotsEq {n : ℕ} (p : TensorSlotPair n) : n = (n - 2) + 2 :=
  (Nat.sub_add_cancel (two_le_of_tensorSlotPair p)).symm

/-- Helper for Lemma 10.13.4: the order relation on a tensor-slot pair is preserved by the
canonical reindexing to degree `(n - 2) + 2`. -/
lemma castTwoSlots_lt {n : ℕ} (p : TensorSlotPair n) :
    finCongr (castTwoSlotsEq p) p.1.1 < finCongr (castTwoSlotsEq p) p.1.2 := by
  -- Reindexing along an equality of finite types does not change the underlying slot order.
  simpa using p.2

/-- Helper for Lemma 10.13.4: the ordered pair of distinguished slots reindexed to the auxiliary
degree `(n - 2) + 2`. -/
def castTwoSlots {n : ℕ} (p : TensorSlotPair n) : TensorSlotPair (n - 2 + 2) :=
  let e : Fin n ≃ Fin ((n - 2) + 2) := finCongr (castTwoSlotsEq p)
  ⟨⟨e p.1.1, e p.1.2⟩, castTwoSlots_lt p⟩

/-- Helper for Lemma 10.13.4: the public insertion operation is definitionally the auxiliary
two-slot insertion followed by the harmless tensor-degree reindexing. -/
lemma insertTwoTensorEntries_eq_aux
    (p : TensorSlotPair n) (x y : M) (m : Fin (n - 2) → M) :
    insertTwoTensorEntries n p x y m =
      insertTwoTensorEntriesAux (M := M) (castTwoSlots p) x y m ∘ Fin.cast (castTwoSlotsEq p) := by
  -- This is exactly the unfolded definition of `insertTwoTensorEntries`.
  rfl

/-- Helper for Lemma 10.13.4: after deleting the left distinguished slot, reinserting the
remaining deleted position recovers the right distinguished slot. -/
lemma rightTensorSlot_eq_left_succAbove_predAbove {n : ℕ}
    (p : TensorSlotPair (n + 2)) :
    rightTensorSlot p =
      (leftTensorSlot p).succAbove
        ((leftTensorSlotCast p).predAbove (rightTensorSlot p)) := by
  -- The right slot survives deletion of the left slot, so reinserting that deleted position
  -- recovers the original right coordinate.
  symm
  have hne :
      rightTensorSlot p ≠ (leftTensorSlotCast p).castSucc := by
    simpa [leftTensorSlot, leftTensorSlotCast, rightTensorSlot] using
      (ne_of_lt p.2).symm
  simpa [leftTensorSlot, leftTensorSlotCast, rightTensorSlot] using
    (Fin.succAbove_predAbove (p := leftTensorSlotCast p)
      (i := rightTensorSlot p) hne)

/-- Helper for Lemma 10.13.4: delete the two distinguished tensor slots used by
`insertTwoTensorEntriesAux`, keeping the remaining entries in their original order. -/
def deleteTwoTensorEntriesAux {n : ℕ} (p : TensorSlotPair (n + 2))
    (v : Fin (n + 2) → M) : Fin n → M :=
  ((leftTensorSlotCast p).predAbove (rightTensorSlot p)).removeNth
    ((leftTensorSlot p).removeNth v)

/-- Helper for Lemma 10.13.4: deleting the two distinguished slots and then reinserting the
original entries recovers the starting tensor family. -/
lemma insertTwoTensorEntriesAux_deleteTwoTensorEntriesAux {n : ℕ}
    (p : TensorSlotPair (n + 2)) (v : Fin (n + 2) → M) :
    insertTwoTensorEntriesAux (M := M) p (v (leftTensorSlot p)) (v (rightTensorSlot p))
      (deleteTwoTensorEntriesAux (M := M) p v) = v := by
  let q : Fin (n + 1) := (leftTensorSlotCast p).predAbove (rightTensorSlot p)
  have hslot :
      rightTensorSlot p = (leftTensorSlot p).succAbove q := by
    -- The right distinguished slot is exactly the `succAbove` image of the deleted right index.
    simpa [q] using rightTensorSlot_eq_left_succAbove_predAbove (p := p)
  have hinner :
      Fin.insertNth q (v (rightTensorSlot p))
          (q.removeNth ((leftTensorSlot p).removeNth v)) =
        (leftTensorSlot p).removeNth v := by
    -- Reinserting the right distinguished entry undoes the second deletion.
    rw [show v (rightTensorSlot p) = ((leftTensorSlot p).removeNth v) q by
      simpa [Fin.removeNth_apply, hslot]]
    exact Fin.insertNth_self_removeNth q ((leftTensorSlot p).removeNth v)
  -- A second `insertNth_self_removeNth` restores the deleted left distinguished entry.
  calc
    insertTwoTensorEntriesAux (M := M) p (v (leftTensorSlot p)) (v (rightTensorSlot p))
        (deleteTwoTensorEntriesAux (M := M) p v)
      = Fin.insertNth (leftTensorSlot p) (v (leftTensorSlot p))
          (Fin.insertNth q (v (rightTensorSlot p))
            (q.removeNth ((leftTensorSlot p).removeNth v))) := by
          rfl
    _ = Fin.insertNth (leftTensorSlot p) (v (leftTensorSlot p))
          ((leftTensorSlot p).removeNth v) := by rw [hinner]
    _ = v := Fin.insertNth_self_removeNth (leftTensorSlot p) v

/-- Helper for Lemma 10.13.4: delete the two distinguished tensor slots from an arbitrary
`Fin n`-indexed tensor family using the same normalization as `insertTwoTensorEntries`. -/
def deleteTwoTensorEntries (n : ℕ)
    (p : TensorSlotPair n) (v : Fin n → M) : Fin (n - 2) → M :=
  deleteTwoTensorEntriesAux (M := M) (castTwoSlots p) (v ∘ Fin.cast (castTwoSlotsEq p).symm)

/-- Helper for Lemma 10.13.4: the explicit delete-two-slots adapter is inverse to
`insertTwoTensorEntries` on arbitrary tensor families. -/
lemma insertTwoTensorEntries_deleteTwoTensorEntries
    (n : ℕ) (p : TensorSlotPair n) (v : Fin n → M) :
    insertTwoTensorEntries n p (v p.1.1) (v p.1.2)
      (deleteTwoTensorEntries (M := M) n p v) = v := by
  -- Transport the auxiliary delete/reinsert identity across the harmless reindexing built into
  -- `insertTwoTensorEntries`.
  ext k
  simpa [insertTwoTensorEntries, deleteTwoTensorEntries, Function.comp] using
    congrFun
      (insertTwoTensorEntriesAux_deleteTwoTensorEntriesAux (M := M) (p := castTwoSlots p)
        (v := v ∘ Fin.cast (castTwoSlotsEq p).symm))
      (Fin.cast (castTwoSlotsEq p) k)

/-- Helper for Lemma 10.13.4: the canonical cast used to compare degree `n` with
`(n - 2) + 2` is injective. -/
lemma castTwoSlotsEq_cast_injective (p : TensorSlotPair n) :
    Function.Injective (Fin.cast (castTwoSlotsEq p).symm) := by
  -- Equality of the cast images is definitional equality of the original indices.
  intro i j hij
  simpa using hij

/-- Helper for Lemma 10.13.4: deleting the two chosen tensor slots is unchanged by updating the
left distinguished slot before deletion. -/
lemma deleteTwoTensorEntries_update_left
    (p : TensorSlotPair n) (v : Fin n → M) (x : M) :
    deleteTwoTensorEntries (M := M) n p (Function.update v p.1.1 x) =
      deleteTwoTensorEntries (M := M) n p v := by
  let p' : TensorSlotPair ((n - 2) + 2) := castTwoSlots p
  let e : n = (n - 2) + 2 := castTwoSlotsEq p
  have hupdate :
      (Function.update v p.1.1 x) ∘ Fin.cast e.symm =
        Function.update (v ∘ Fin.cast e.symm) (leftTensorSlot p') x := by
    -- Transport the updated tensor family to the auxiliary indexing model before deleting slots.
    ext i
    by_cases hi : i = leftTensorSlot p'
    · subst hi
      simp [p', castTwoSlots, leftTensorSlot]
    · have hcast : Fin.cast e.symm i ≠ p.1.1 := by
        intro h
        apply hi
        have := congrArg (Fin.cast e) h
        simpa [p', e, castTwoSlots, leftTensorSlot] using this
      simp [Function.update, hi, hcast]
  -- After transport, the left-slot update disappears under the first `removeNth`.
  rw [deleteTwoTensorEntries, deleteTwoTensorEntriesAux, hupdate, Fin.removeNth_update,
    deleteTwoTensorEntries]
  rfl

/-- Helper for Lemma 10.13.4: deleting the two chosen tensor slots is unchanged by updating the
right distinguished slot before deletion. -/
lemma deleteTwoTensorEntries_update_right
    (p : TensorSlotPair n) (v : Fin n → M) (x : M) :
    deleteTwoTensorEntries (M := M) n p (Function.update v p.1.2 x) =
      deleteTwoTensorEntries (M := M) n p v := by
  let p' : TensorSlotPair ((n - 2) + 2) := castTwoSlots p
  let e : n = (n - 2) + 2 := castTwoSlotsEq p
  let q : Fin ((n - 2) + 1) :=
    (leftTensorSlotCast p').predAbove (rightTensorSlot p')
  have hslot :
      rightTensorSlot p' = (leftTensorSlot p').succAbove q := by
    -- The right distinguished slot survives the first deletion as the `succAbove` image of `q`.
    simpa [q] using rightTensorSlot_eq_left_succAbove_predAbove (p := p')
  have hpred :
      (leftTensorSlotCast p').predAbove ((leftTensorSlot p').succAbove q) = q := by
    -- Deleting the left distinguished slot and reinserting it recovers the surviving right index.
    simpa [q, leftTensorSlot, leftTensorSlotCast] using
      (Fin.predAbove_succAbove (leftTensorSlotCast p') q)
  have hupdate :
      (Function.update v p.1.2 x) ∘ Fin.cast e.symm =
        Function.update (v ∘ Fin.cast e.symm) (rightTensorSlot p') x := by
    -- Transport the right-slot update to the auxiliary indexing model before deleting slots.
    ext i
    by_cases hi : i = rightTensorSlot p'
    · subst hi
      simp [p', castTwoSlots, rightTensorSlot]
    · have hcast : Fin.cast e.symm i ≠ p.1.2 := by
        intro h
        apply hi
        have := congrArg (Fin.cast e) h
        simpa [p', e, castTwoSlots, rightTensorSlot] using this
      simp [Function.update, hi, hcast]
  -- Route correction: move the right-slot update through the first deletion, then the second
  -- deletion erases the resulting update on the residual index `q`.
  rw [deleteTwoTensorEntries, deleteTwoTensorEntriesAux, hupdate, hslot,
    Fin.removeNth_update_succAbove, hpred, Fin.removeNth_update, deleteTwoTensorEntries]
  rfl

/-- Helper for Lemma 10.13.4: updating the left distinguished slot of the inserted tensor family
just replaces the left inserted entry. -/
lemma insertTwoTensorEntries_update_left
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y y' z : M) :
    Function.update (insertTwoTensorEntries n p y z m) p.1.1 y' =
      insertTwoTensorEntries n p y' z m := by
  let p' : TensorSlotPair ((n - 2) + 2) := castTwoSlots p
  let e : n = (n - 2) + 2 := castTwoSlotsEq p
  have htransport :
      Function.update ((insertTwoTensorEntriesAux (M := M) p' y z m) ∘ Fin.cast e) p.1.1 y' =
        (Function.update (insertTwoTensorEntriesAux (M := M) p' y z m)
          (leftTensorSlot p') y') ∘ Fin.cast e := by
    -- Reindex the left-slot update to the explicit nested `insertNth` model.
    ext i
    by_cases hi : i = p.1.1
    · subst hi
      simp [p', castTwoSlots, leftTensorSlot]
    · have hcast : Fin.cast e i ≠ leftTensorSlot p' := by
        intro h
        apply hi
        have := congrArg (Fin.cast e.symm) h
        simpa [p', e, castTwoSlots, leftTensorSlot] using this
      simp [Function.update, hi, hcast]
  have haux :
      Function.update (insertTwoTensorEntriesAux (M := M) p' y z m)
          (leftTensorSlot p') y' =
        insertTwoTensorEntriesAux (M := M) p' y' z m := by
    -- In the auxiliary model the left distinguished entry is the outer `insertNth` slot.
    simp [insertTwoTensorEntriesAux]
  -- Transport the left-slot update to the auxiliary model and simplify there.
  calc
    Function.update (insertTwoTensorEntries n p y z m) p.1.1 y'
      = Function.update ((insertTwoTensorEntriesAux (M := M) p' y z m) ∘ Fin.cast e) p.1.1 y' := by
          rw [insertTwoTensorEntries_eq_aux]
    _ = (Function.update (insertTwoTensorEntriesAux (M := M) p' y z m)
          (leftTensorSlot p') y') ∘ Fin.cast e := htransport
    _ = insertTwoTensorEntries n p y' z m := by
          rw [haux, insertTwoTensorEntries_eq_aux]

/-- Helper for Lemma 10.13.4: updating the right distinguished slot of the inserted tensor family
just replaces the right inserted entry. -/
lemma insertTwoTensorEntries_update_right
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y z z' : M) :
    Function.update (insertTwoTensorEntries n p y z m) p.1.2 z' =
      insertTwoTensorEntries n p y z' m := by
  let p' : TensorSlotPair ((n - 2) + 2) := castTwoSlots p
  let e : n = (n - 2) + 2 := castTwoSlotsEq p
  let q : Fin ((n - 2) + 1) :=
    (leftTensorSlotCast p').predAbove (rightTensorSlot p')
  have hslot :
      rightTensorSlot p' = (leftTensorSlot p').succAbove q := by
    -- The right distinguished slot is the `succAbove` image of the remaining deleted index.
    simpa [q] using rightTensorSlot_eq_left_succAbove_predAbove (p := p')
  have htransport :
      Function.update ((insertTwoTensorEntriesAux (M := M) p' y z m) ∘ Fin.cast e) p.1.2 z' =
        (Function.update (insertTwoTensorEntriesAux (M := M) p' y z m)
          (rightTensorSlot p') z') ∘ Fin.cast e := by
    -- Reindex the right-slot update to the explicit nested `insertNth` model.
    ext i
    by_cases hi : i = p.1.2
    · subst hi
      simp [p', castTwoSlots, rightTensorSlot]
    · have hcast : Fin.cast e i ≠ rightTensorSlot p' := by
        intro h
        apply hi
        have := congrArg (Fin.cast e.symm) h
        simpa [p', e, castTwoSlots, rightTensorSlot] using this
      simp [Function.update, hi, hcast]
  have haux :
      Function.update (insertTwoTensorEntriesAux (M := M) p' y z m)
          (rightTensorSlot p') z' =
        insertTwoTensorEntriesAux (M := M) p' y z' m := by
    -- In the auxiliary model the right distinguished entry is the inner `insertNth` slot.
    rw [hslot, insertTwoTensorEntriesAux, ← Fin.insertNth_update, Fin.update_insertNth]
    rfl
  -- Transport the right-slot update to the auxiliary model and simplify there.
  calc
    Function.update (insertTwoTensorEntries n p y z m) p.1.2 z'
      = Function.update ((insertTwoTensorEntriesAux (M := M) p' y z m) ∘ Fin.cast e) p.1.2 z' := by
          rw [insertTwoTensorEntries_eq_aux]
    _ = (Function.update (insertTwoTensorEntriesAux (M := M) p' y z m)
          (rightTensorSlot p') z') ∘ Fin.cast e := htransport
    _ = insertTwoTensorEntries n p y z' m := by
          rw [haux, insertTwoTensorEntries_eq_aux]

/-- Helper for Lemma 10.13.4: evaluating the inserted tensor family at the left distinguished
slot recovers the left inserted entry. -/
lemma insertTwoTensorEntries_left_value
    (p : TensorSlotPair n) (y z : M) (m : Fin (n - 2) → M) :
    insertTwoTensorEntries n p y z m p.1.1 = y := by
  -- Route correction: evaluate the already proved left-slot update identity at the left slot.
  have h :=
    congrFun
      (insertTwoTensorEntries_update_left (M := M) (n := n) (p := p)
        (m := m) (y := y) (y' := y) (z := z))
      p.1.1
  simpa [Function.update] using h.symm

/-- Helper for Lemma 10.13.4: evaluating the inserted tensor family at the right distinguished
slot recovers the right inserted entry. -/
lemma insertTwoTensorEntries_right_value
    (p : TensorSlotPair n) (y z : M) (m : Fin (n - 2) → M) :
    insertTwoTensorEntries n p y z m p.1.2 = z := by
  -- Route correction: evaluate the already proved right-slot update identity at the right slot.
  have h :=
    congrFun
      (insertTwoTensorEntries_update_right (M := M) (n := n) (p := p)
        (m := m) (y := y) (z := z) (z' := z))
      p.1.2
  simpa [Function.update] using h.symm

/-- Helper for Lemma 10.13.4: scaling the left inserted entry scales the resulting pure tensor. -/
lemma tprod_insertTwoTensorEntries_left_smul
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y z : M) (b : B) :
    tprod B (insertTwoTensorEntries n p (b • y) z m) =
      b • tprod B (insertTwoTensorEntries n p y z m) := by
  -- Normalize the public insertion API to the explicit nested `Fin.insertNth` model.
  rw [insertTwoTensorEntries_eq_aux, insertTwoTensorEntries_eq_aux]
  have haux :
      tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) (b • y) z m) =
        b • tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y z m) := by
    -- In the auxiliary model, the left inserted entry is exactly the outer `insertNth` slot.
    simpa [insertTwoTensorEntriesAux] using
      (MultilinearMap.map_insertNth_smul
        (f := (tprod B : MultilinearMap B (fun _ : Fin ((n - 2) + 2) ↦ M)
          (⨂[B]^((n - 2) + 2) M)))
        (p := leftTensorSlot (castTwoSlots p))
        (m := Fin.insertNth
          ((leftTensorSlotCast (castTwoSlots p)).predAbove (rightTensorSlot (castTwoSlots p))) z m)
        (c := b) (x := y))
  -- Transport the auxiliary equality back across the harmless tensor-degree cast.
  simpa [Function.comp, TensorPower.cast_tprod] using
    congrArg (TensorPower.cast B M (castTwoSlotsEq p).symm) haux

/-- Helper for Lemma 10.13.4: scaling the right inserted entry scales the resulting pure tensor. -/
lemma tprod_insertTwoTensorEntries_right_smul
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y z : M) (b : B) :
    tprod B (insertTwoTensorEntries n p y (b • z) m) =
      b • tprod B (insertTwoTensorEntries n p y z m) := by
  -- Normalize the public insertion API to the explicit nested `Fin.insertNth` model.
  rw [insertTwoTensorEntries_eq_aux, insertTwoTensorEntries_eq_aux]
  have haux :
      tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y (b • z) m) =
        b • tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y z m) := by
    let q : Fin ((n - 2) + 1) :=
      (leftTensorSlotCast (castTwoSlots p)).predAbove (rightTensorSlot (castTwoSlots p))
    -- After fixing the left slot, the right inserted entry becomes the distinguished slot of the
    -- curried multilinear map.
    simpa [insertTwoTensorEntriesAux, q] using
      (MultilinearMap.map_insertNth_smul
        (f := ((tprod B :
          MultilinearMap B (fun _ : Fin ((n - 2) + 2) ↦ M) (⨂[B]^((n - 2) + 2) M)).curryMid
            (leftTensorSlot (castTwoSlots p)) y))
        (p := q) (m := m) (c := b) (x := z))
  -- Transport the auxiliary equality back across the harmless tensor-degree cast.
  simpa [Function.comp, TensorPower.cast_tprod] using
    congrArg (TensorPower.cast B M (castTwoSlotsEq p).symm) haux

/-- Helper for Lemma 10.13.4: adding in the left inserted slot expands linearly on pure tensors
over `B`. -/
lemma tprod_insertTwoTensorEntries_left_add
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y₁ y₂ z : M) :
    tprod B (insertTwoTensorEntries n p (y₁ + y₂) z m) =
      tprod B (insertTwoTensorEntries n p y₁ z m) +
        tprod B (insertTwoTensorEntries n p y₂ z m) := by
  -- Normalize the public insertion API to the explicit nested `Fin.insertNth` model.
  rw [insertTwoTensorEntries_eq_aux, insertTwoTensorEntries_eq_aux, insertTwoTensorEntries_eq_aux]
  have haux :
      tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) (y₁ + y₂) z m) =
        tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y₁ z m) +
          tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y₂ z m) := by
    -- In the auxiliary model, additivity in the left inserted slot is exactly
    -- `MultilinearMap.map_insertNth_add`.
    simpa [insertTwoTensorEntriesAux] using
      (MultilinearMap.map_insertNth_add
        (f := (tprod B : MultilinearMap B (fun _ : Fin ((n - 2) + 2) ↦ M)
          (⨂[B]^((n - 2) + 2) M)))
        (p := leftTensorSlot (castTwoSlots p))
        (m := Fin.insertNth
          ((leftTensorSlotCast (castTwoSlots p)).predAbove (rightTensorSlot (castTwoSlots p))) z m)
        (x := y₁) (y := y₂))
  -- Transport the auxiliary equality back across the harmless tensor-degree cast.
  simpa [Function.comp, TensorPower.cast_tprod] using
    congrArg (TensorPower.cast B M (castTwoSlotsEq p).symm) haux

/-- Helper for Lemma 10.13.4: adding in the right inserted slot expands linearly on pure tensors
over `B`. -/
lemma tprod_insertTwoTensorEntries_right_add
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y z₁ z₂ : M) :
    tprod B (insertTwoTensorEntries n p y (z₁ + z₂) m) =
      tprod B (insertTwoTensorEntries n p y z₁ m) +
        tprod B (insertTwoTensorEntries n p y z₂ m) := by
  -- Normalize the public insertion API to the explicit nested `Fin.insertNth` model.
  rw [insertTwoTensorEntries_eq_aux, insertTwoTensorEntries_eq_aux, insertTwoTensorEntries_eq_aux]
  have haux :
      tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y (z₁ + z₂) m) =
        tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y z₁ m) +
          tprod B (insertTwoTensorEntriesAux (M := M) (castTwoSlots p) y z₂ m) := by
    let q : Fin ((n - 2) + 1) :=
      (leftTensorSlotCast (castTwoSlots p)).predAbove (rightTensorSlot (castTwoSlots p))
    -- After fixing the left slot, additivity in the right inserted slot is additivity for the
    -- curried multilinear map at the distinguished index `q`.
    simpa [insertTwoTensorEntriesAux, q] using
      (MultilinearMap.map_insertNth_add
        (f := ((tprod B :
          MultilinearMap B (fun _ : Fin ((n - 2) + 2) ↦ M) (⨂[B]^((n - 2) + 2) M)).curryMid
            (leftTensorSlot (castTwoSlots p)) y))
        (p := q) (m := m) (x := z₁) (y := z₂))
  -- Transport the auxiliary equality back across the harmless tensor-degree cast.
  simpa [Function.comp, TensorPower.cast_tprod] using
    congrArg (TensorPower.cast B M (castTwoSlotsEq p).symm) haux

end
