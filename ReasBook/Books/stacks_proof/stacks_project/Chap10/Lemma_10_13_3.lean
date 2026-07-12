import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PiTensorProduct exteriorPower

universe u v

section

variable {R : Type} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- A strictly increasing pair of tensor slots in degree `n`. -/
abbrev TensorSlotPair (n : ℕ) :=
  { pq : Fin n × Fin n // pq.1 < pq.2 }

/-- The left slot of a `TensorSlotPair`. -/
private abbrev leftTensorSlot {n : ℕ} (p : TensorSlotPair (n + 2)) : Fin (n + 2) :=
  p.1.1

/-- The right slot of a `TensorSlotPair`. -/
private abbrev rightTensorSlot {n : ℕ} (p : TensorSlotPair (n + 2)) : Fin (n + 2) :=
  p.1.2

/-- The left slot, viewed inside `Fin (n + 1)`, so that `Fin.predAbove` may remove it from
`Fin (n + 2)`. -/
private abbrev leftTensorSlotCast {n : ℕ} (p : TensorSlotPair (n + 2)) : Fin (n + 1) :=
  (leftTensorSlot p).castLT (Fin.val_lt_last (Fin.ne_last_of_lt p.2))

/-- Insert two distinguished entries into a pure tensor in slots `j₁ < j₂`. -/
private def insertTwoTensorEntriesAux {n : ℕ} (p : TensorSlotPair (n + 2)) (x y : M)
    (m : Fin n → M) :
    Fin (n + 2) → M :=
  Fin.insertNth (leftTensorSlot p) x
    (Fin.insertNth ((leftTensorSlotCast p).predAbove (rightTensorSlot p)) y m)

/-- The multilinear map sending a pure tensor in degree `n` to the pure tensor in degree `n + 2`
obtained by inserting fixed entries in a chosen pair of slots. -/
private noncomputable def two_slot_tensor_multilinear (n : ℕ) (p : TensorSlotPair (n + 2))
    (x y : M) :
    MultilinearMap R (fun _ : Fin n ↦ M) (⨂[R]^(n + 2) M) :=
  let t : MultilinearMap R (fun _ : Fin (n + 2) ↦ M) (⨂[R]^(n + 2) M) := tprod R
  let q : Fin (n + 1) := (leftTensorSlotCast p).predAbove (rightTensorSlot p)
  ((((t.curryMid (leftTensorSlot p)) x).curryMid q) y)

/-- The linear map on tensor powers obtained by inserting two fixed entries in chosen slots. -/
private noncomputable def two_slot_tensor_map (n : ℕ) (p : TensorSlotPair (n + 2)) (x y : M) :
    ⨂[R]^n M →ₗ[R] ⨂[R]^(n + 2) M :=
  lift (two_slot_tensor_multilinear n p x y)

-- Proof sketch: unwind the two successive `curryMid` operations and the universal property of the
-- tensor power; this identifies the multilinear map with the pure tensor obtained by inserting
-- `x` and `y` into the chosen slots.
/-- The two-slot insertion map sends a pure tensor to the pure tensor with the chosen entries
inserted into the prescribed slots. -/
private lemma two_slot_tensor_map_apply_tprod {n : ℕ} (p : TensorSlotPair (n + 2)) (x y : M)
    (m : Fin n → M) :
    two_slot_tensor_map n p x y (tprod R m) =
      tprod R (insertTwoTensorEntriesAux p x y m) := by
  -- Unwinding the lift reduces the claim to the defining action of the two successive
  -- `curryMid` insertions on a pure tensor.
  rw [two_slot_tensor_map, PiTensorProduct.lift.tprod]
  rfl

/-- An ordered pair of tensor slots forces the ambient tensor degree to be at least `2`. -/
private lemma two_le_of_orderedTensorSlotPair {n : ℕ}
    (p : TensorSlotPair n) : 2 ≤ n := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  omega

/-- Reindex an ordered pair of slots in `Fin n` as an ordered pair of slots in
`Fin ((n - 2) + 2)`. -/
private abbrev castTwoSlotsEq {n : ℕ}
    (p : TensorSlotPair n) : n = (n - 2) + 2 :=
  (Nat.sub_add_cancel (two_le_of_orderedTensorSlotPair p)).symm

/-- Reindex an ordered pair of slots in `Fin n` as an ordered pair of slots in
`Fin ((n - 2) + 2)`. -/
private lemma castTwoSlots_lt {n : ℕ}
    (p : TensorSlotPair n) :
    finCongr (castTwoSlotsEq p) p.1.1 < finCongr (castTwoSlotsEq p) p.1.2 := by
  -- Reindexing along an equality of finite types preserves the original slot order.
  simpa using p.2

/-- Reindex an ordered pair of slots in `Fin n` as an ordered pair of slots in
`Fin ((n - 2) + 2)`. -/
private def castTwoSlots {n : ℕ}
    (p : TensorSlotPair n) : TensorSlotPair (n - 2 + 2) :=
  let e : Fin n ≃ Fin ((n - 2) + 2) := finCongr (castTwoSlotsEq p)
  ⟨⟨e p.1.1, e p.1.2⟩, castTwoSlots_lt p⟩

/-- Insert two chosen entries into a pure tensor of degree `n - 2` in an ordered pair of slots of
degree `n`. This is the explicit tensor-indexing operation appearing in
Lemma 10.13.3. -/
def insertTwoTensorEntries (n : ℕ)
    (p : TensorSlotPair n) (x y : M) (m : Fin (n - 2) → M) :
    Fin n → M :=
  insertTwoTensorEntriesAux (castTwoSlots p) x y m ∘ Fin.cast (castTwoSlotsEq p)

/-- Helper for Lemma 10.13.3: delete the two distinguished tensor slots used by
`insertTwoTensorEntriesAux`, keeping the remaining entries in their original order. -/
private def deleteTwoTensorEntriesAux {n : ℕ} (p : TensorSlotPair (n + 2))
    (v : Fin (n + 2) → M) : Fin n → M :=
  ((leftTensorSlotCast p).predAbove (rightTensorSlot p)).removeNth
    ((leftTensorSlot p).removeNth v)

/-- Helper for Lemma 10.13.3: after deleting the left distinguished slot, reinserting the
remaining deleted position recovers the right distinguished slot. -/
private lemma rightTensorSlot_eq_left_succAbove_predAbove {n : ℕ}
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

/-- Helper for Lemma 10.13.3: deleting the two distinguished slots and then reinserting the
original entries recovers the starting tensor family. -/
private lemma insertTwoTensorEntriesAux_deleteTwoTensorEntriesAux {n : ℕ}
    (p : TensorSlotPair (n + 2)) (v : Fin (n + 2) → M) :
    insertTwoTensorEntriesAux p (v (leftTensorSlot p)) (v (rightTensorSlot p))
      (deleteTwoTensorEntriesAux p v) = v := by
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
    insertTwoTensorEntriesAux p (v (leftTensorSlot p)) (v (rightTensorSlot p))
        (deleteTwoTensorEntriesAux p v)
      = Fin.insertNth (leftTensorSlot p) (v (leftTensorSlot p))
          (Fin.insertNth q (v (rightTensorSlot p))
            (q.removeNth ((leftTensorSlot p).removeNth v))) := by
          rfl
    _ = Fin.insertNth (leftTensorSlot p) (v (leftTensorSlot p))
          ((leftTensorSlot p).removeNth v) := by rw [hinner]
    _ = v := Fin.insertNth_self_removeNth (leftTensorSlot p) v

/-- Helper for Lemma 10.13.3: delete the two distinguished tensor slots from an arbitrary
`Fin n`-indexed tensor family using the same normalization as `insertTwoTensorEntries`. -/
private def deleteTwoTensorEntries (n : ℕ)
    (p : TensorSlotPair n) (v : Fin n → M) : Fin (n - 2) → M :=
  deleteTwoTensorEntriesAux (castTwoSlots p) (v ∘ Fin.cast (castTwoSlotsEq p).symm)

/-- Helper for Lemma 10.13.3: the explicit delete-two-slots adapter is inverse to
`insertTwoTensorEntries` on arbitrary tensor families. -/
private lemma insertTwoTensorEntries_deleteTwoTensorEntries
    (n : ℕ) (p : TensorSlotPair n) (v : Fin n → M) :
    insertTwoTensorEntries n p (v p.1.1) (v p.1.2)
      (deleteTwoTensorEntries n p v) = v := by
  -- Transport the auxiliary delete/reinsert identity across the harmless reindexing built into
  -- `insertTwoTensorEntries`.
  ext k
  simpa [insertTwoTensorEntries, deleteTwoTensorEntries, Function.comp] using
    congrFun
      (insertTwoTensorEntriesAux_deleteTwoTensorEntriesAux (p := castTwoSlots p)
        (v := v ∘ Fin.cast (castTwoSlotsEq p).symm))
      (Fin.cast (castTwoSlotsEq p) k)

/-- The two-slot insertion map in degree `n`, obtained by inserting two fixed entries into a pure
tensor in the chosen ordered pair of slots. -/
private noncomputable def twoSlotTensorMap (n : ℕ)
    (p : TensorSlotPair n) (x y : M) :
    ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M :=
  (TensorPower.cast R M (castTwoSlotsEq p).symm).toLinearMap.comp
    (two_slot_tensor_map (n - 2) (castTwoSlots p) x y)

/-- The two-slot insertion map sends a pure tensor to the pure tensor with the chosen entries
inserted into the prescribed slots. -/
private theorem twoSlotTensorMap_apply_tprod (n : ℕ)
    (p : TensorSlotPair n) (x y : M) (m : Fin (n - 2) → M) :
    twoSlotTensorMap n p x y (tprod R m) =
      tprod R (insertTwoTensorEntries n p x y m) := by
  -- Evaluate the auxiliary insertion map first, then transport the pure tensor across the
  -- canonical reindexing of the tensor power.
  rw [twoSlotTensorMap, LinearMap.comp_apply, two_slot_tensor_map_apply_tprod]
  -- The transport theorem for tensor powers already produces the required reindexed pure tensor.
  simpa [insertTwoTensorEntries, Function.comp] using
    (TensorPower.cast_tprod (R := R) (M := M) (h := (castTwoSlotsEq p).symm)
      (a := insertTwoTensorEntriesAux (castTwoSlots p) x y m))

/-- Helper for Lemma 10.13.3: the auxiliary two-slot multilinear insertion is additive in the
left distinguished entry. -/
private theorem two_slot_tensor_multilinear_add_left {n : ℕ}
    (p : TensorSlotPair (n + 2)) (x₁ x₂ y : M) :
    two_slot_tensor_multilinear (R := R) n p (x₁ + x₂) y =
      two_slot_tensor_multilinear (R := R) n p x₁ y +
        two_slot_tensor_multilinear (R := R) n p x₂ y := by
  ext m
  -- The left distinguished slot is a genuine multilinear variable, so addition in that slot
  -- expands by `map_insertNth_add`.
  dsimp [two_slot_tensor_multilinear]
  rw [MultilinearMap.map_insertNth_add]

/-- Helper for Lemma 10.13.3: the auxiliary two-slot multilinear insertion is additive in the
right distinguished entry. -/
private theorem two_slot_tensor_multilinear_add_right {n : ℕ}
    (p : TensorSlotPair (n + 2)) (x y₁ y₂ : M) :
    two_slot_tensor_multilinear (R := R) n p x (y₁ + y₂) =
      two_slot_tensor_multilinear (R := R) n p x y₁ +
        two_slot_tensor_multilinear (R := R) n p x y₂ := by
  let t : MultilinearMap R (fun _ : Fin (n + 2) ↦ M) (⨂[R]^(n + 2) M) := tprod R
  let q : Fin (n + 1) := (leftTensorSlotCast p).predAbove (rightTensorSlot p)
  ext m
  -- After currying out the left slot, the right distinguished slot is still multilinear.
  change (((t.curryMid (leftTensorSlot p)) x) (q.insertNth (y₁ + y₂) m)) =
      ((t.curryMid (leftTensorSlot p)) x) (q.insertNth y₁ m) +
        ((t.curryMid (leftTensorSlot p)) x) (q.insertNth y₂ m)
  rw [MultilinearMap.map_insertNth_add]

/-- Helper for Lemma 10.13.3: the auxiliary two-slot multilinear insertion is linear in the left
distinguished entry with respect to scalar multiplication. -/
private theorem two_slot_tensor_multilinear_smul_left {n : ℕ}
    (p : TensorSlotPair (n + 2)) (r : R) (x y : M) :
    two_slot_tensor_multilinear (R := R) n p (r • x) y =
      r • two_slot_tensor_multilinear (R := R) n p x y := by
  ext m
  -- Scalar multiplication in the left distinguished slot factors out of the multilinear map.
  dsimp [two_slot_tensor_multilinear]
  rw [MultilinearMap.map_insertNth_smul]

/-- Helper for Lemma 10.13.3: the auxiliary two-slot multilinear insertion is linear in the right
distinguished entry with respect to scalar multiplication. -/
private theorem two_slot_tensor_multilinear_smul_right {n : ℕ}
    (p : TensorSlotPair (n + 2)) (r : R) (x y : M) :
    two_slot_tensor_multilinear (R := R) n p x (r • y) =
      r • two_slot_tensor_multilinear (R := R) n p x y := by
  let t : MultilinearMap R (fun _ : Fin (n + 2) ↦ M) (⨂[R]^(n + 2) M) := tprod R
  let q : Fin (n + 1) := (leftTensorSlotCast p).predAbove (rightTensorSlot p)
  ext m
  -- After currying out the left slot, scalar multiplication in the right slot still factors out.
  change (((t.curryMid (leftTensorSlot p)) x) (q.insertNth (r • y) m)) =
      r • ((t.curryMid (leftTensorSlot p)) x) (q.insertNth y m)
  rw [MultilinearMap.map_insertNth_smul]

/-- Helper for Lemma 10.13.3: postcomposing the inserted pure tensor by any linear map preserves
additivity in the left distinguished slot. -/
private theorem linearMap_insertTwoTensorEntries_add_left
    {N : Type*} [AddCommGroup N] [Module R N]
    (q : ⨂[R]^n M →ₗ[R] N) (p : TensorSlotPair n)
    (y₁ y₂ z : M) (m : Fin (n - 2) → M) :
    q (tprod R (insertTwoTensorEntries n p (y₁ + y₂) z m)) =
      q (tprod R (insertTwoTensorEntries n p y₁ z m)) +
        q (tprod R (insertTwoTensorEntries n p y₂ z m)) := by
  let c : ⨂[R]^(n - 2 + 2) M →ₗ[R] ⨂[R]^n M :=
    (TensorPower.cast R M (castTwoSlotsEq p).symm).toLinearMap
  have haux :
      c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) (y₁ + y₂) z
          (tprod R m)) =
        c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y₁ z
            (tprod R m)) +
          c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y₂ z
            (tprod R m)) := by
    have haux₀ :
        two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) (y₁ + y₂) z
            (tprod R m) =
          two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y₁ z
              (tprod R m) +
            two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y₂ z
              (tprod R m) := by
      -- The auxiliary tensor insertion map is additive in the left distinguished entry.
      simp [two_slot_tensor_map, PiTensorProduct.lift.tprod,
        two_slot_tensor_multilinear_add_left (R := R) (M := M) (p := castTwoSlots p)]
    -- First expand the auxiliary insertion map in the left slot, then transport across the cast.
    simpa [LinearMap.map_add] using congrArg c haux₀
  -- The displayed tensor-insertion formula is exactly `twoSlotTensorMap_apply_tprod`.
  rw [← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p (y₁ + y₂) z m,
    ← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y₁ z m,
    ← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y₂ z m]
  simpa [twoSlotTensorMap, c, LinearMap.comp_apply, LinearMap.map_add] using congrArg q haux

/-- Helper for Lemma 10.13.3: postcomposing the inserted pure tensor by any linear map preserves
additivity in the right distinguished slot. -/
private theorem linearMap_insertTwoTensorEntries_add_right
    {N : Type*} [AddCommGroup N] [Module R N]
    (q : ⨂[R]^n M →ₗ[R] N) (p : TensorSlotPair n)
    (y z₁ z₂ : M) (m : Fin (n - 2) → M) :
    q (tprod R (insertTwoTensorEntries n p y (z₁ + z₂) m)) =
      q (tprod R (insertTwoTensorEntries n p y z₁ m)) +
        q (tprod R (insertTwoTensorEntries n p y z₂ m)) := by
  let c : ⨂[R]^(n - 2 + 2) M →ₗ[R] ⨂[R]^n M :=
    (TensorPower.cast R M (castTwoSlotsEq p).symm).toLinearMap
  have haux :
      c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y (z₁ + z₂)
          (tprod R m)) =
        c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z₁
            (tprod R m)) +
          c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z₂
            (tprod R m)) := by
    have haux₀ :
        two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y (z₁ + z₂)
            (tprod R m) =
          two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z₁
              (tprod R m) +
            two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z₂
              (tprod R m) := by
      -- The auxiliary tensor insertion map is additive in the right distinguished entry.
      simp [two_slot_tensor_map, PiTensorProduct.lift.tprod,
        two_slot_tensor_multilinear_add_right (R := R) (M := M) (p := castTwoSlots p)]
    -- The same transport argument works for the right slot after currying out the left one.
    simpa [LinearMap.map_add] using congrArg c haux₀
  rw [← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y (z₁ + z₂) m,
    ← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y z₁ m,
    ← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y z₂ m]
  simpa [twoSlotTensorMap, c, LinearMap.comp_apply, LinearMap.map_add] using congrArg q haux

/-- Helper for Lemma 10.13.3: postcomposing the inserted pure tensor by any linear map preserves
scalar multiplication in the left distinguished slot. -/
private theorem linearMap_insertTwoTensorEntries_smul_left
    {N : Type*} [AddCommGroup N] [Module R N]
    (q : ⨂[R]^n M →ₗ[R] N) (p : TensorSlotPair n)
    (r : R) (y z : M) (m : Fin (n - 2) → M) :
    q (tprod R (insertTwoTensorEntries n p (r • y) z m)) =
      r • q (tprod R (insertTwoTensorEntries n p y z m)) := by
  let c : ⨂[R]^(n - 2 + 2) M →ₗ[R] ⨂[R]^n M :=
    (TensorPower.cast R M (castTwoSlotsEq p).symm).toLinearMap
  have haux :
      c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) (r • y) z
          (tprod R m)) =
        r • c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z
          (tprod R m)) := by
    have haux₀ :
        two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) (r • y) z
            (tprod R m) =
          r • two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z
            (tprod R m) := by
      -- The auxiliary tensor insertion map is linear in the left distinguished entry.
      simp [two_slot_tensor_map, PiTensorProduct.lift.tprod,
        two_slot_tensor_multilinear_smul_left (R := R) (M := M) (p := castTwoSlots p)]
    -- Linearity in the left slot survives the tensor-power cast unchanged.
    simpa [LinearMap.map_smul] using congrArg c haux₀
  rw [← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p (r • y) z m,
    ← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y z m]
  simpa [twoSlotTensorMap, c, LinearMap.comp_apply, LinearMap.map_smul] using congrArg q haux

/-- Helper for Lemma 10.13.3: postcomposing the inserted pure tensor by any linear map preserves
scalar multiplication in the right distinguished slot. -/
private theorem linearMap_insertTwoTensorEntries_smul_right
    {N : Type*} [AddCommGroup N] [Module R N]
    (q : ⨂[R]^n M →ₗ[R] N) (p : TensorSlotPair n)
    (y z : M) (r : R) (m : Fin (n - 2) → M) :
    q (tprod R (insertTwoTensorEntries n p y (r • z) m)) =
      r • q (tprod R (insertTwoTensorEntries n p y z m)) := by
  let c : ⨂[R]^(n - 2 + 2) M →ₗ[R] ⨂[R]^n M :=
    (TensorPower.cast R M (castTwoSlotsEq p).symm).toLinearMap
  have haux :
      c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y (r • z)
          (tprod R m)) =
        r • c (two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z
          (tprod R m)) := by
    have haux₀ :
        two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y (r • z)
            (tprod R m) =
          r • two_slot_tensor_map (R := R) (M := M) (n := n - 2) (castTwoSlots p) y z
            (tprod R m) := by
      -- The auxiliary tensor insertion map is linear in the right distinguished entry.
      simp [two_slot_tensor_map, PiTensorProduct.lift.tprod,
        two_slot_tensor_multilinear_smul_right (R := R) (M := M) (p := castTwoSlots p)]
    -- The same transport argument applies to scalar multiplication in the right slot.
    simpa [LinearMap.map_smul] using congrArg c haux₀
  rw [← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y (r • z) m,
    ← twoSlotTensorMap_apply_tprod (R := R) (M := M) n p y z m]
  simpa [twoSlotTensorMap, c, LinearMap.comp_apply, LinearMap.map_smul] using congrArg q haux

section FamilyRelations

variable {I : Type v} (n : ℕ) (x : I → M)

local notation "ExteriorRelationSource" =>
  (((TensorSlotPair n × I × I) →₀ ⨂[R]^(n - 2) M) ×
    ((TensorSlotPair n × I) →₀ ⨂[R]^(n - 2) M))

local notation "SymmetricRelationSource" =>
  ((TensorSlotPair n × I × I) →₀ ⨂[R]^(n - 2) M)

/-- Helper for Lemma 10.13.3: if a linear map kills every single summand of a finitely supported
linear combination, then it kills the whole `Finsupp.lsum`. -/
private theorem comp_lsum_eq_zero_of_single_eq_zero
    {α : Type*} {N₁ : Type*} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module R N₂]
    {N₃ : Type*} [AddCommGroup N₃] [Module R N₃]
    (f : α → N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (h : ∀ a z, g (f a z) = 0) :
    g.comp (Finsupp.lsum R f) = 0 := by
  apply LinearMap.ext
  intro l
  change g (Finsupp.lsum R f l) = 0
  -- Reduce the direct-sum aggregation to the single-summand vanishing hypothesis.
  refine Finsupp.induction_linear l ?_ ?_ ?_
  · simp
  · intro l₁ l₂ hl₁ hl₂
    rw [(Finsupp.lsum R f).map_add, LinearMap.map_add, hl₁, hl₂, add_zero]
  · intro a z
    simpa [Finsupp.lsum_single] using h a z

/-- Helper for Lemma 10.13.3: quotient classes of pure tensors still span any quotient of the
degree-`n` tensor power. -/
private theorem tensor_quotient_mkQ_tprod_span_top
    (Q : Submodule R (⨂[R]^n M)) :
    Submodule.span R (Set.range (Q.mkQ ∘ tprod R)) = ⊤ := by
  -- The quotient map is surjective, so the image of the standard spanning family still spans.
  calc
    Submodule.span R (Set.range (Q.mkQ ∘ tprod R)) =
        Submodule.map Q.mkQ (Submodule.span R (Set.range (tprod R : (Fin n → M) → ⨂[R]^n M))) := by
          rw [Set.range_comp, Submodule.map_span]
    _ = Submodule.map Q.mkQ ⊤ := by
          rw [PiTensorProduct.span_tprod_eq_top (R := R) (s := fun _ : Fin n ↦ M)]
    _ = ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]

/-- For the exterior-power presentation, the skew-symmetry relation attached to two entries of a
family and two slots. -/
private noncomputable def exteriorSwapRelationMapOfFamily :
    (TensorSlotPair n × I × I) → ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M
  | ⟨p, i₁, i₂⟩ =>
      twoSlotTensorMap n p (x i₁) (x i₂) +
        twoSlotTensorMap n p (x i₂) (x i₁)

/-- For the exterior-power presentation, the repeated-entry relation attached to one entry of a
family and two slots. -/
private noncomputable def exteriorRepeatRelationMapOfFamily :
    (TensorSlotPair n × I) → ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M
  | ⟨p, i⟩ => twoSlotTensorMap n p (x i) (x i)

/-- On pure tensors, the skew-symmetry relation attached to a family is the sum of the two
corresponding slot-insertion tensors. -/
private theorem exteriorSwapRelationMapOfFamily_apply_tprod
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    exteriorSwapRelationMapOfFamily n x (p, i₁, i₂) (tprod R m) =
      tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) +
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := by
  -- The family relation is defined as the sum of the two ordered slot insertions.
  simp [exteriorSwapRelationMapOfFamily, twoSlotTensorMap_apply_tprod]

/-- On pure tensors, the repeated-entry relation attached to a family inserts the same entry into
the two chosen slots. -/
private theorem exteriorRepeatRelationMapOfFamily_apply_tprod
    (p : TensorSlotPair n) (i : I)
    (m : Fin (n - 2) → M) :
    exteriorRepeatRelationMapOfFamily n x (p, i) (tprod R m) =
      tprod R (insertTwoTensorEntries n p (x i) (x i) m) := by
  -- The repeated-entry relation is a single insertion map with the same generator in both slots.
  simp [exteriorRepeatRelationMapOfFamily, twoSlotTensorMap_apply_tprod]

/-- The family-level relation map used in Stacks Project, Lemma 10.13.3 (1). If `x` generates
`M`, then the exactness theorem below identifies its cokernel with `⋀[R]^n M`. -/
noncomputable def exteriorRelationMapOfFamily : ExteriorRelationSource →ₗ[R] ⨂[R]^n M :=
  let swapRelations := Finsupp.lsum R (fun a ↦ exteriorSwapRelationMapOfFamily n x a)
  let repeatRelations := Finsupp.lsum R (fun a ↦ exteriorRepeatRelationMapOfFamily n x a)
  swapRelations.comp (LinearMap.fst R _ _) + repeatRelations.comp (LinearMap.snd R _ _)

/-- The exterior relation map restricts on a generator of the first direct-sum factor to the
corresponding skew-symmetry relation. -/
private theorem exteriorRelationMapOfFamily_fst_single_apply
    (a : TensorSlotPair n × I × I) (z : ⨂[R]^(n - 2) M) :
    exteriorRelationMapOfFamily n x (Finsupp.single a z, 0) =
      exteriorSwapRelationMapOfFamily n x a z := by
  -- On the first direct-sum generator only the skew-symmetry summand survives.
  simp [exteriorRelationMapOfFamily]

/-- The exterior relation map restricts on a generator of the second direct-sum factor to the
corresponding repeated-entry relation. -/
private theorem exteriorRelationMapOfFamily_snd_single_apply
    (a : TensorSlotPair n × I) (z : ⨂[R]^(n - 2) M) :
    exteriorRelationMapOfFamily n x (0, Finsupp.single a z) =
      exteriorRepeatRelationMapOfFamily n x a z := by
  -- On the second direct-sum generator only the repeated-entry summand survives.
  simp [exteriorRelationMapOfFamily]

/-- On a pure-tensor generator of the first direct-sum factor, the exterior relation map is the
sum of the two skew-symmetry tensors. This is the explicit left-map formula from
Lemma 10.13.3 (1). -/
theorem exteriorRelationMapOfFamily_fst_single_tprod
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    exteriorRelationMapOfFamily n x
        (Finsupp.single (p, i₁, i₂) (tprod R m), 0) =
      tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) +
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := by
  -- Combine the direct-sum restriction with the pure-tensor evaluation of the skew relation.
  rw [exteriorRelationMapOfFamily_fst_single_apply]
  exact exteriorSwapRelationMapOfFamily_apply_tprod n x p i₁ i₂ m

/-- On a pure-tensor generator of the second direct-sum factor, the exterior relation map inserts
the same family entry twice. This is the repeated-entry formula from Lemma 10.13.3 (1). -/
theorem exteriorRelationMapOfFamily_snd_single_tprod
    (p : TensorSlotPair n) (i : I)
    (m : Fin (n - 2) → M) :
    exteriorRelationMapOfFamily n x
        (0, Finsupp.single (p, i) (tprod R m)) =
      tprod R (insertTwoTensorEntries n p (x i) (x i) m) := by
  -- Combine the direct-sum restriction with the pure-tensor evaluation of the repeat relation.
  rw [exteriorRelationMapOfFamily_snd_single_apply]
  exact exteriorRepeatRelationMapOfFamily_apply_tprod n x p i m

/-- For the symmetric-power presentation, the commutator relation attached to two entries of a
family and two slots. -/
private noncomputable def symmetricCommutatorRelationMapOfFamily :
    (TensorSlotPair n × I × I) → ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M
  | ⟨p, i₁, i₂⟩ =>
      twoSlotTensorMap n p (x i₁) (x i₂) -
        twoSlotTensorMap n p (x i₂) (x i₁)

/-- On pure tensors, the symmetric commutator relation is the difference of the two slot-insertion
tensors. -/
private theorem symmetricCommutatorRelationMapOfFamily_apply_tprod
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    symmetricCommutatorRelationMapOfFamily n x (p, i₁, i₂) (tprod R m) =
      tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) -
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := by
  -- The symmetric relation is defined as the commutator of the two ordered slot insertions.
  simp [symmetricCommutatorRelationMapOfFamily, twoSlotTensorMap_apply_tprod]

/-- The family-level relation map used in Stacks Project, Lemma 10.13.3 (2). If `x` generates
`M`, then the exactness theorem below identifies its cokernel with `Sym[R]^n M`. -/
noncomputable def symmetricRelationMapOfFamily :
    SymmetricRelationSource →ₗ[R] ⨂[R]^n M :=
  Finsupp.lsum R (fun a ↦ symmetricCommutatorRelationMapOfFamily n x a)

/-- The symmetric relation map restricts on a direct-sum generator to the corresponding
commutator relation. -/
private theorem symmetricRelationMapOfFamily_single_apply
    (a : TensorSlotPair n × I × I) (z : ⨂[R]^(n - 2) M) :
    symmetricRelationMapOfFamily n x (Finsupp.single a z) =
      symmetricCommutatorRelationMapOfFamily n x a z := by
  -- The `lsum` defining the symmetric relation map picks out the unique chosen generator.
  simp [symmetricRelationMapOfFamily]

/-- On a pure-tensor generator, the symmetric relation map is the difference of the two
slot-insertion tensors. This is the explicit left-map formula from Lemma 10.13.3 (2). -/
theorem symmetricRelationMapOfFamily_single_tprod
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    symmetricRelationMapOfFamily n x
        (Finsupp.single (p, i₁, i₂) (tprod R m)) =
      tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) -
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := by
  -- Reduce to the commutator relation and then evaluate it on the pure tensor generator.
  rw [symmetricRelationMapOfFamily_single_apply]
  exact symmetricCommutatorRelationMapOfFamily_apply_tprod n x p i₁ i₂ m

/-- Helper for Lemma 10.13.3: in the quotient by the displayed exterior family relations, each
generator skew-symmetry relation already vanishes. -/
private theorem exteriorRelationQuotient_fst_single_tprod_eq_zero
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
        (PiTensorProduct.tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) +
          PiTensorProduct.tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m)) = 0 := by
  -- Rewrite the displayed relation as a literal image of `exteriorRelationMapOfFamily`,
  -- then apply the quotient relation `mkQ z = 0` for elements of the defining range.
  rw [← exteriorRelationMapOfFamily_fst_single_tprod (n := n) (x := x) p i₁ i₂ m,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨(Finsupp.single (p, i₁, i₂) (tprod R m), 0), rfl⟩

/-- Helper for Lemma 10.13.3: in the quotient by the displayed exterior family relations, each
generator repeated-entry relation already vanishes. -/
private theorem exteriorRelationQuotient_snd_single_tprod_eq_zero
    (p : TensorSlotPair n) (i : I)
    (m : Fin (n - 2) → M) :
    (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
        (tprod R (insertTwoTensorEntries n p (x i) (x i) m)) = 0 := by
  -- Rewrite the repeated-entry tensor as the value of the displayed relation map on a
  -- direct-sum generator, so it dies in the quotient by construction.
  rw [← exteriorRelationMapOfFamily_snd_single_tprod (n := n) (x := x) p i m,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨(0, Finsupp.single (p, i) (tprod R m)), rfl⟩

/-- Helper for Lemma 10.13.3: in the quotient by the displayed symmetric family relations, each
generator commutator relation already vanishes. -/
private theorem symmetricRelationQuotient_single_tprod_eq_zero
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ
        (PiTensorProduct.tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) -
          PiTensorProduct.tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m)) = 0 := by
  -- The symmetric quotient is defined by these commutator generators, so each displayed
  -- pure-tensor commutator becomes zero after passing to the quotient.
  rw [← symmetricRelationMapOfFamily_single_tprod (n := n) (x := x) p i₁ i₂ m,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨Finsupp.single (p, i₁, i₂) (tprod R m), rfl⟩

/-- Helper for Lemma 10.13.3: after inserting the same entry twice, the two distinguished slots of
the resulting tensor family agree. -/
private lemma insertTwoTensorEntries_left_value
    (p : TensorSlotPair n) (y : M) (m : Fin (n - 2) → M) :
    insertTwoTensorEntries n p y y m p.1.1 = y := by
  -- Unfold the indexed insertion and read off the entry in the left distinguished slot.
  simp only [insertTwoTensorEntries, insertTwoTensorEntriesAux, Function.comp_apply]
  rw [show Fin.cast (castTwoSlotsEq p) p.1.1 = leftTensorSlot (castTwoSlots p) by rfl]
  simpa using
    (Fin.insertNth_apply_same
      (α := fun _ : Fin ((n - 2) + 2) ↦ M)
      (i := leftTensorSlot (castTwoSlots p)) (x := y)
      (p := ((leftTensorSlotCast (castTwoSlots p)).predAbove
        (rightTensorSlot (castTwoSlots p))).insertNth y m))

/-- Helper for Lemma 10.13.3: evaluating at the right distinguished slot reads off the second
inserted entry. -/
private lemma insertTwoTensorEntries_right_value
    (p : TensorSlotPair n) (y : M) (m : Fin (n - 2) → M) :
    insertTwoTensorEntries n p y y m p.1.2 = y := by
  -- The right distinguished slot is the `succAbove` image of its `predAbove` index.
  have hslot :
      rightTensorSlot (castTwoSlots p) =
        (leftTensorSlot (castTwoSlots p)).succAbove
          ((leftTensorSlotCast (castTwoSlots p)).predAbove
            (rightTensorSlot (castTwoSlots p))) := by
    symm
    have hne :
        rightTensorSlot (castTwoSlots p) ≠
          (leftTensorSlotCast (castTwoSlots p)).castSucc := by
      simpa [leftTensorSlot, leftTensorSlotCast, rightTensorSlot] using
        (ne_of_lt (castTwoSlots p).2).symm
    simpa [leftTensorSlot, leftTensorSlotCast, rightTensorSlot] using
      (Fin.succAbove_predAbove (p := leftTensorSlotCast (castTwoSlots p))
        (i := rightTensorSlot (castTwoSlots p)) hne)
  have hpred :
      (leftTensorSlotCast (castTwoSlots p)).predAbove
          ((leftTensorSlot (castTwoSlots p)).succAbove
            ((leftTensorSlotCast (castTwoSlots p)).predAbove
              (rightTensorSlot (castTwoSlots p)))) =
        (leftTensorSlotCast (castTwoSlots p)).predAbove
          (rightTensorSlot (castTwoSlots p)) := by
    simpa [leftTensorSlot, leftTensorSlotCast] using
      (Fin.predAbove_succAbove
        (leftTensorSlotCast (castTwoSlots p))
        ((leftTensorSlotCast (castTwoSlots p)).predAbove
          (rightTensorSlot (castTwoSlots p))))
  simp only [insertTwoTensorEntries, insertTwoTensorEntriesAux, Function.comp_apply]
  rw [show Fin.cast (castTwoSlotsEq p) p.1.2 = rightTensorSlot (castTwoSlots p) by rfl]
  rw [hslot, Fin.insertNth_apply_succAbove, hpred]
  simpa using
    (Fin.insertNth_apply_same
      (α := fun _ : Fin ((n - 2) + 1) ↦ M)
      (i := (leftTensorSlotCast (castTwoSlots p)).predAbove
        (rightTensorSlot (castTwoSlots p)))
      (x := y) (p := m))

/-- Helper for Lemma 10.13.3: after inserting the same entry twice, the two distinguished slots of
the resulting tensor family agree. -/
private lemma insertTwoTensorEntries_same_on_slots
    (p : TensorSlotPair n) (y : M) (m : Fin (n - 2) → M) :
    insertTwoTensorEntries n p y y m p.1.1 =
      insertTwoTensorEntries n p y y m p.1.2 := by
  -- Both distinguished coordinates evaluate to the repeated inserted entry.
  rw [insertTwoTensorEntries_left_value (n := n) p y m,
    insertTwoTensorEntries_right_value (n := n) p y m]

/-- Helper for Lemma 10.13.3: swapping the two inserted entries is the same as precomposing with
the transposition of the distinguished tensor slots. -/
private lemma insertTwoTensorEntriesAux_swap {n : ℕ}
    (p : TensorSlotPair (n + 2)) (x y : M) (m : Fin n → M) :
    insertTwoTensorEntriesAux p x y m =
      insertTwoTensorEntriesAux p y x m ∘ Equiv.swap p.1.1 p.1.2 := by
  let q : Fin (n + 1) := (leftTensorSlotCast p).predAbove (rightTensorSlot p)
  have hslot :
      rightTensorSlot p =
        (leftTensorSlot p).succAbove
          q := by
    -- The right distinguished slot is the `succAbove` image of the deleted right index.
    simpa [q] using rightTensorSlot_eq_left_succAbove_predAbove (p := p)
  have hi :
      insertTwoTensorEntriesAux p y x m (leftTensorSlot p) = y := by
    -- Evaluating the auxiliary insertion at the left distinguished slot reads off the left entry.
    simp [insertTwoTensorEntriesAux]
  have hj :
      insertTwoTensorEntriesAux p y x m (rightTensorSlot p) = x := by
    -- Evaluating at the right distinguished slot reads off the second inserted entry.
    rw [insertTwoTensorEntriesAux, hslot, Fin.insertNth_apply_succAbove]
    rw [show (leftTensorSlotCast p).predAbove ((leftTensorSlot p).succAbove q) = q by
      simpa [leftTensorSlot, leftTensorSlotCast] using
        (Fin.predAbove_succAbove (leftTensorSlotCast p) q)]
    exact
      (Fin.insertNth_apply_same
        (α := fun _ : Fin (n + 1) ↦ M) (i := q) (x := x) (p := m))
  have hright_update :
      Function.update (insertTwoTensorEntriesAux p y x m) (rightTensorSlot p) y =
        Fin.insertNth (leftTensorSlot p) y (Fin.insertNth q y m) := by
    -- Updating the right distinguished slot only changes the inner inserted entry.
    unfold insertTwoTensorEntriesAux
    rw [hslot, ← Fin.insertNth_update]
    rw [show (leftTensorSlotCast p).predAbove ((leftTensorSlot p).succAbove q) = q by
      simpa [leftTensorSlot, leftTensorSlotCast] using
        (Fin.predAbove_succAbove (leftTensorSlotCast p) q)]
    rw [Fin.update_insertNth]
  -- Rewriting the transposition as two point updates exposes the two inserted coordinates.
  rw [Equiv.comp_swap_eq_update, hi, hj]
  rw [hright_update, Fin.update_insertNth]
  simpa [insertTwoTensorEntriesAux, q]

/-- Helper for Lemma 10.13.3: swapping the two inserted entries is the same as precomposing with
the transposition of the chosen tensor slots. -/
private theorem insertTwoTensorEntries_swap
    (p : TensorSlotPair n) (x y : M) (m : Fin (n - 2) → M) :
    insertTwoTensorEntries n p x y m =
      insertTwoTensorEntries n p y x m ∘ Equiv.swap p.1.1 p.1.2 := by
  have hcast_swap (k : Fin n) :
      Equiv.swap (leftTensorSlot (castTwoSlots p)) (rightTensorSlot (castTwoSlots p))
          (Fin.cast (castTwoSlotsEq p) k) =
        Fin.cast (castTwoSlotsEq p) (Equiv.swap p.1.1 p.1.2 k) := by
    -- The casted transposition is the same transposition on the reindexed `Fin` type.
    apply Fin.ext
    by_cases hk₁ : k = p.1.1
    · subst hk₁
      simp [castTwoSlots, leftTensorSlot, rightTensorSlot]
    · by_cases hk₂ : k = p.1.2
      · subst hk₂
        simp [castTwoSlots, leftTensorSlot, rightTensorSlot]
      · have hk₁' :
            Fin.cast (castTwoSlotsEq p) k ≠ leftTensorSlot (castTwoSlots p) := by
          simpa [castTwoSlots, leftTensorSlot] using hk₁
        have hk₂' :
            Fin.cast (castTwoSlotsEq p) k ≠ rightTensorSlot (castTwoSlots p) := by
          simpa [castTwoSlots, rightTensorSlot] using hk₂
        simp [Equiv.swap_apply_def, hk₁, hk₂, castTwoSlots, leftTensorSlot,
          rightTensorSlot]
  ext k
  have haux :=
    congrFun
      (insertTwoTensorEntriesAux_swap (p := castTwoSlots p) x y m)
      (Fin.cast (castTwoSlotsEq p) k)
  -- Transport the auxiliary swap identity across the harmless `Fin.cast` reindexing.
  calc
    insertTwoTensorEntries n p x y m k
      = insertTwoTensorEntriesAux (castTwoSlots p) x y m (Fin.cast (castTwoSlotsEq p) k) := by
          rfl
    _ = insertTwoTensorEntriesAux (castTwoSlots p) y x m
          (Equiv.swap (leftTensorSlot (castTwoSlots p)) (rightTensorSlot (castTwoSlots p))
            (Fin.cast (castTwoSlotsEq p) k)) := haux
    _ = insertTwoTensorEntriesAux (castTwoSlots p) y x m
          (Fin.cast (castTwoSlotsEq p) (Equiv.swap p.1.1 p.1.2 k)) := by
            rw [hcast_swap]
    _ = (insertTwoTensorEntries n p y x m ∘ Equiv.swap p.1.1 p.1.2) k := by
          rfl

/-- Helper for Lemma 10.13.3: a pure tensor with two equal distinguished entries already lies in
the kernel of the canonical map to the exterior power. -/
private theorem repeated_insertTwoTensorEntries_mem_exterior_ker
    (p : TensorSlotPair n) (y : M) (m : Fin (n - 2) → M) :
    tprod R (insertTwoTensorEntries n p y y m) ∈
      LinearMap.ker
        (lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := by
  rw [LinearMap.mem_ker]
  -- The canonical tensor-power map evaluates pure tensors by `ιMulti`.
  rw [PiTensorProduct.lift.tprod]
  -- The two distinguished slots coincide, so alternation forces vanishing.
  exact (ιMulti R n).map_eq_zero_of_eq (insertTwoTensorEntries n p y y m)
    (insertTwoTensorEntries_same_on_slots (n := n) p y m)
    (ne_of_lt p.2)

/-- Helper for Lemma 10.13.3: the repeated-entry family relations are contained in the exterior
kernel even before using the spanning hypothesis on the generators. -/
private theorem exteriorRepeatRelationMapOfFamily_range_le_ker
    (p : TensorSlotPair n) (i : I) :
    LinearMap.range (exteriorRepeatRelationMapOfFamily n x (p, i)) ≤
      LinearMap.ker
        (lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := by
  rw [LinearMap.range_le_ker_iff]
  apply LinearMap.ext
  intro z
  -- It is enough to check the kernel statement on scaled pure tensors.
  refine PiTensorProduct.induction_on z ?_ ?_
  · intro r m
    -- The pure-tensor case is exactly the repeated-entry exterior relation.
    have hm :
        ((lift (ιMulti R n).toMultilinearMap :
            ⨂[R]^n M →ₗ[R] ⋀[R]^n M) ∘ₗ
          exteriorRepeatRelationMapOfFamily n x (p, i)) (tprod R m) = 0 := by
      -- Evaluate the repeated-entry relation on a pure tensor and use alternation.
      rw [LinearMap.comp_apply, exteriorRepeatRelationMapOfFamily_apply_tprod]
      exact LinearMap.mem_ker.mp
        (repeated_insertTwoTensorEntries_mem_exterior_ker (R := R) (n := n) p (x i) m)
    simpa [LinearMap.comp_apply, LinearMap.map_smul] using congrArg (fun t ↦ r • t) hm
  · intro a b ha hb
    simpa [LinearMap.comp_apply, LinearMap.map_add, ha, hb]

/-- Helper for Lemma 10.13.3: the sum of the two pure tensors obtained by swapping the two
distinguished inserted entries already vanishes in the exterior quotient. -/
private theorem swapped_insertTwoTensorEntries_mem_exterior_ker
    (p : TensorSlotPair n) (y₁ y₂ : M) (m : Fin (n - 2) → M) :
    tprod R (insertTwoTensorEntries n p y₁ y₂ m) +
      tprod R (insertTwoTensorEntries n p y₂ y₁ m) ∈
        LinearMap.ker
          (lift (ιMulti R n).toMultilinearMap :
            ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := by
  rw [LinearMap.mem_ker, LinearMap.map_add, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
  -- Rewrite the second tensor as the first tensor precomposed with the slot transposition.
  rw [insertTwoTensorEntries_swap (n := n) p y₂ y₁ m]
  -- Alternation makes the two swapped pure tensors cancel in the exterior power.
  simpa using
    (ιMulti R n).map_add_swap
      (v := insertTwoTensorEntries n p y₁ y₂ m) (i := p.1.1) (j := p.1.2) (ne_of_lt p.2)

/-- Helper for Lemma 10.13.3: the skew-symmetry family relations are contained in the exterior
kernel before any use of the spanning hypothesis. -/
private theorem exteriorSwapRelationMapOfFamily_range_le_ker
    (p : TensorSlotPair n) (i₁ i₂ : I) :
    LinearMap.range (exteriorSwapRelationMapOfFamily n x (p, i₁, i₂)) ≤
      LinearMap.ker
        (lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := by
  rw [LinearMap.range_le_ker_iff]
  apply LinearMap.ext
  intro z
  -- Reduce to pure tensors, where alternating swap-cancellation is explicit.
  refine PiTensorProduct.induction_on z ?_ ?_
  · intro r m
    have hm :
        ((lift (ιMulti R n).toMultilinearMap :
            ⨂[R]^n M →ₗ[R] ⋀[R]^n M) ∘ₗ
          exteriorSwapRelationMapOfFamily n x (p, i₁, i₂)) (tprod R m) = 0 := by
      rw [LinearMap.comp_apply, exteriorSwapRelationMapOfFamily_apply_tprod]
      exact LinearMap.mem_ker.mp
        (swapped_insertTwoTensorEntries_mem_exterior_ker
          (R := R) (n := n) p (x i₁) (x i₂) m)
    simpa [LinearMap.comp_apply, LinearMap.map_smul] using congrArg (fun t ↦ r • t) hm
  · intro a b ha hb
    simpa [LinearMap.comp_apply, LinearMap.map_add, ha, hb]

/-- Helper for Lemma 10.13.3: every displayed exterior family relation already maps to zero in
the canonical map from tensor power to exterior power. -/
private theorem exteriorRelationMapOfFamily_range_le_ker :
    LinearMap.range (exteriorRelationMapOfFamily n x) ≤
      LinearMap.ker
        (lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := by
  rw [LinearMap.range_le_ker_iff]
  let q : ⨂[R]^n M →ₗ[R] ⋀[R]^n M := lift (ιMulti R n).toMultilinearMap
  let swapRelations :
      ((TensorSlotPair n × I × I) →₀ ⨂[R]^(n - 2) M) →ₗ[R] ⨂[R]^n M :=
    Finsupp.lsum R (fun a ↦ exteriorSwapRelationMapOfFamily n x a)
  let repeatRelations :
      ((TensorSlotPair n × I) →₀ ⨂[R]^(n - 2) M) →ₗ[R] ⨂[R]^n M :=
    Finsupp.lsum R (fun a ↦ exteriorRepeatRelationMapOfFamily n x a)
  have hswap : q.comp swapRelations = 0 := by
    refine comp_lsum_eq_zero_of_single_eq_zero
      (f := fun a ↦ exteriorSwapRelationMapOfFamily n x a) (g := q) ?_
    intro a z
    rcases a with ⟨p, i₁, i₂⟩
    exact DFunLike.congr_fun
      ((LinearMap.range_le_ker_iff.mp
        (exteriorSwapRelationMapOfFamily_range_le_ker
          (R := R) (M := M) (n := n) (x := x) p i₁ i₂))) z
  have hrepeat : q.comp repeatRelations = 0 := by
    refine comp_lsum_eq_zero_of_single_eq_zero
      (f := fun a ↦ exteriorRepeatRelationMapOfFamily n x a) (g := q) ?_
    intro a z
    rcases a with ⟨p, i⟩
    exact DFunLike.congr_fun
      ((LinearMap.range_le_ker_iff.mp
        (exteriorRepeatRelationMapOfFamily_range_le_ker
          (R := R) (M := M) (n := n) (x := x) p i))) z
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  change q (swapRelations a + repeatRelations b) = 0
  rw [q.map_add]
  have hs : q (swapRelations a) = 0 := DFunLike.congr_fun hswap a
  have hr : q (repeatRelations b) = 0 := DFunLike.congr_fun hrepeat b
  simp [hs, hr]

/-- Helper for Lemma 10.13.3: each displayed symmetric commutator relation already lies in the
kernel of the canonical map to the symmetric tensor power. -/
private theorem symmetricCommutatorRelationMapOfFamily_range_le_ker
    (p : TensorSlotPair n) (i₁ i₂ : I) :
    LinearMap.range (symmetricCommutatorRelationMapOfFamily n x (p, i₁, i₂)) ≤
      LinearMap.ker (SymmetricPower.mk R (Fin n) M) := by
  rw [LinearMap.range_le_ker_iff]
  apply LinearMap.ext
  intro z
  -- Reduce to pure tensors, where the quotient only depends on the unordered pair of slots.
  refine PiTensorProduct.induction_on z ?_ ?_
  · intro r m
    have hm :
        ((SymmetricPower.mk R (Fin n) M) ∘ₗ
          symmetricCommutatorRelationMapOfFamily n x (p, i₁, i₂)) (tprod R m) = 0 := by
      rw [LinearMap.comp_apply, symmetricCommutatorRelationMapOfFamily_apply_tprod,
        LinearMap.map_sub]
      have hsym :
          SymmetricPower.mk R (Fin n) M
              (tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m)) =
            SymmetricPower.mk R (Fin n) M
              (tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m)) := by
        -- Rewrite the right tensor by the slot transposition and then use symmetry of `tprod`.
        rw [insertTwoTensorEntries_swap (n := n) p (x i₂) (x i₁) m]
        simpa [SymmetricPower.tprod] using
          (SymmetricPower.tprod_equiv (R := R) (ι := Fin n) (M := M)
            (e := Equiv.swap p.1.1 p.1.2)
            (f := insertTwoTensorEntries n p (x i₁) (x i₂) m)).symm
      simpa [hsym]
    simpa [LinearMap.comp_apply, LinearMap.map_smul] using congrArg (fun t ↦ r • t) hm
  · intro a b ha hb
    simpa [LinearMap.comp_apply, LinearMap.map_add, ha, hb]

/-- Helper for Lemma 10.13.3: every displayed symmetric family relation already maps to zero in
the canonical map from tensor power to symmetric power. -/
private theorem symmetricRelationMapOfFamily_range_le_ker :
    LinearMap.range (symmetricRelationMapOfFamily n x) ≤
      LinearMap.ker (SymmetricPower.mk R (Fin n) M) := by
  rw [LinearMap.range_le_ker_iff]
  let q : ⨂[R]^n M →ₗ[R] Sym[R]^n M := SymmetricPower.mk R (Fin n) M
  let commutatorRelations :
      ((TensorSlotPair n × I × I) →₀ ⨂[R]^(n - 2) M) →ₗ[R] ⨂[R]^n M :=
    Finsupp.lsum R (fun a ↦ symmetricCommutatorRelationMapOfFamily n x a)
  have hcomm : q.comp commutatorRelations = 0 := by
    refine comp_lsum_eq_zero_of_single_eq_zero
      (f := fun a ↦ symmetricCommutatorRelationMapOfFamily n x a) (g := q) ?_
    intro a z
    rcases a with ⟨p, i₁, i₂⟩
    exact DFunLike.congr_fun
      ((LinearMap.range_le_ker_iff.mp
        (symmetricCommutatorRelationMapOfFamily_range_le_ker
          (R := R) (M := M) (n := n) (x := x) p i₁ i₂))) z
  apply LinearMap.ext
  intro z
  change q (commutatorRelations z) = 0
  exact DFunLike.congr_fun hcomm z

/-- Helper for Lemma 10.13.3: in the quotient by the displayed exterior family relations, the sum
of the two tensors obtained by swapping the distinguished inserted entries vanishes for arbitrary
entries in the span of the chosen generators. -/
private theorem exteriorRelationQuotient_swap_sum_eq_zero_of_span
    (p : TensorSlotPair n) (m : Fin (n - 2) → M)
    {y₁ y₂ : M}
    (hy₁ : y₁ ∈ Submodule.span R (Set.range x))
    (hy₂ : y₂ ∈ Submodule.span R (Set.range x)) :
    (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
        (PiTensorProduct.tprod R (insertTwoTensorEntries n p y₁ y₂ m)) +
      (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
        (PiTensorProduct.tprod R (insertTwoTensorEntries n p y₂ y₁ m)) = 0 :=
by
  let Q : Submodule R (⨂[R]^n M) := LinearMap.range (exteriorRelationMapOfFamily n x)
  let qExt : ⨂[R]^n M →ₗ[R] (⨂[R]^n M) ⧸ Q := Q.mkQ
  let swapSum : M → M → (⨂[R]^n M) ⧸ Q := fun a b ↦
    qExt (tprod R (insertTwoTensorEntries n p a b m)) +
      qExt (tprod R (insertTwoTensorEntries n p b a m))
  change swapSum y₁ y₂ = 0
  -- The outer induction moves the right inserted entry across the chosen spanning family.
  refine Submodule.span_induction (p := fun y hy ↦ ∀ {z : M},
    z ∈ Submodule.span R (Set.range x) → swapSum z y = 0) ?_ ?_ ?_ ?_ hy₂ hy₁
  · intro y hy z hz
    rcases hy with ⟨i₂, rfl⟩
    -- For a fixed generator on the right, a second span induction handles the left slot.
    refine Submodule.span_induction (p := fun y hy ↦ swapSum y (x i₂) = 0) ?_ ?_ ?_ ?_ hz
    · intro y hy
      rcases hy with ⟨i₁, rfl⟩
      simpa [swapSum, qExt, Q] using
        exteriorRelationQuotient_fst_single_tprod_eq_zero (R := R) (M := M)
          (n := n) (x := x) p i₁ i₂ m
    · -- Zero in the left slot forces both pure tensors to vanish by multilinearity.
      change swapSum (0 : M) (x i₂) = 0
      calc
        swapSum (0 : M) (x i₂)
          = qExt (tprod R (insertTwoTensorEntries n p ((0 : R) • (0 : M)) (x i₂) m)) +
              qExt (tprod R (insertTwoTensorEntries n p (x i₂) ((0 : R) • (0 : M)) m)) := by
                  simp [swapSum]
        _ = (0 : R) • qExt (tprod R (insertTwoTensorEntries n p (0 : M) (x i₂) m)) +
              (0 : R) • qExt (tprod R (insertTwoTensorEntries n p (x i₂) (0 : M) m)) := by
                  rw [linearMap_insertTwoTensorEntries_smul_left (R := R) (M := M) (q := qExt) p
                        (0 : R) (0 : M) (x i₂) m,
                    linearMap_insertTwoTensorEntries_smul_right (R := R) (M := M) (q := qExt) p
                        (x i₂) (0 : M) (0 : R) m]
        _ = 0 := by simp
    · intro a b ha hb hza hzb
      -- The left-slot bilinearity packages the two induction hypotheses into one rewrite.
      calc
        swapSum (a + b) (x i₂)
          = swapSum a (x i₂) + swapSum b (x i₂) := by
              dsimp [swapSum]
              rw [linearMap_insertTwoTensorEntries_add_left (R := R) (M := M) (q := qExt) p
                    a b (x i₂) m,
                linearMap_insertTwoTensorEntries_add_right (R := R) (M := M) (q := qExt) p
                    (x i₂) a b m]
              abel
        _ = 0 := by rw [hza, hzb, add_zero]
    · intro r a ha hza
      -- Scalar compatibility in both inserted slots reduces the goal to the inductive case.
      calc
        swapSum (r • a) (x i₂)
          = r • swapSum a (x i₂) := by
              dsimp [swapSum]
              rw [linearMap_insertTwoTensorEntries_smul_left (R := R) (M := M) (q := qExt) p
                    r a (x i₂) m,
                linearMap_insertTwoTensorEntries_smul_right (R := R) (M := M) (q := qExt) p
                    (x i₂) a r m]
              simp [smul_add]
        _ = 0 := by rw [hza, smul_zero]
  · intro z hz
    -- Zero in the right slot vanishes by the corresponding right-slot multilinearity.
    change swapSum z (0 : M) = 0
    calc
      swapSum z (0 : M)
        = qExt (tprod R (insertTwoTensorEntries n p z ((0 : R) • (0 : M)) m)) +
            qExt (tprod R (insertTwoTensorEntries n p ((0 : R) • (0 : M)) z m)) := by
                simp [swapSum]
      _ = (0 : R) • qExt (tprod R (insertTwoTensorEntries n p z (0 : M) m)) +
            (0 : R) • qExt (tprod R (insertTwoTensorEntries n p (0 : M) z m)) := by
                rw [linearMap_insertTwoTensorEntries_smul_right (R := R) (M := M) (q := qExt) p
                      z (0 : M) (0 : R) m,
                  linearMap_insertTwoTensorEntries_smul_left (R := R) (M := M) (q := qExt) p
                      (0 : R) (0 : M) z m]
      _ = 0 := by simp
  · intro a b ha hb hza hzb z hz
    -- Additivity in the right slot turns the outer induction step into a sum of known zeros.
    calc
      swapSum z (a + b)
        = swapSum z a + swapSum z b := by
            dsimp [swapSum]
            rw [linearMap_insertTwoTensorEntries_add_right (R := R) (M := M) (q := qExt) p
                  z a b m,
              linearMap_insertTwoTensorEntries_add_left (R := R) (M := M) (q := qExt) p
                  a b z m]
            abel
      _ = 0 := by rw [hza hz, hzb hz, add_zero]
  · intro r a ha hza z hz
    -- The right-slot scalar rule gives the same reduction for scalar multiples.
    calc
      swapSum z (r • a)
        = r • swapSum z a := by
            dsimp [swapSum]
            rw [linearMap_insertTwoTensorEntries_smul_right (R := R) (M := M) (q := qExt) p
                  z a r m,
              linearMap_insertTwoTensorEntries_smul_left (R := R) (M := M) (q := qExt) p
                  r a z m]
            simp [smul_add]
      _ = 0 := by rw [hza hz, smul_zero]

/-- Helper for Lemma 10.13.3: in the quotient by the displayed exterior family relations, every
tensor with equal distinguished inserted entries vanishes once that repeated entry lies in the span
of the chosen generators. -/
private theorem exteriorRelationQuotient_repeated_eq_zero_of_span
    (p : TensorSlotPair n) (m : Fin (n - 2) → M)
    {y : M}
    (hy : y ∈ Submodule.span R (Set.range x)) :
    (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
        (PiTensorProduct.tprod R (insertTwoTensorEntries n p y y m)) = 0 :=
by
  let Q : Submodule R (⨂[R]^n M) := LinearMap.range (exteriorRelationMapOfFamily n x)
  let qExt : ⨂[R]^n M →ₗ[R] (⨂[R]^n M) ⧸ Q := Q.mkQ
  let repeated : M → (⨂[R]^n M) ⧸ Q := fun a ↦
    qExt (tprod R (insertTwoTensorEntries n p a a m))
  change repeated y = 0
  -- A single span induction on the repeated entry matches the source proof verbatim.
  refine Submodule.span_induction (p := fun a _ => repeated a = 0) ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨i, rfl⟩
    -- Generator repeated-entry relations vanish in the quotient by construction.
    simpa [repeated, qExt, Q] using
      exteriorRelationQuotient_snd_single_tprod_eq_zero (R := R) (M := M)
        (n := n) (x := x) p i m
  · -- Zero vanishes because the insertion map is linear in the left distinguished slot.
    change repeated (0 : M) = 0
    calc
      repeated (0 : M) =
          qExt (tprod R (insertTwoTensorEntries n p ((0 : R) • (0 : M)) (0 : M) m)) := by
            simp [repeated]
      _ = (0 : R) • qExt (tprod R (insertTwoTensorEntries n p (0 : M) (0 : M) m)) := by
            rw [linearMap_insertTwoTensorEntries_smul_left
              (R := R) (M := M) (q := qExt) p (0 : R) (0 : M) (0 : M) m]
      _ = 0 := by simp
  · intro a b ha hb hza hzb
    have hcross :
        qExt (tprod R (insertTwoTensorEntries n p a b m)) +
            qExt (tprod R (insertTwoTensorEntries n p b a m)) = 0 :=
      exteriorRelationQuotient_swap_sum_eq_zero_of_span
        (R := R) (M := M) (n := n) (x := x) p m ha hb
    -- Expanding the diagonal tensor `(a + b, a + b)` produces two diagonal terms and one
    -- cross-term pair, which cancels by the previously proved swap-sum lemma.
    calc
      repeated (a + b) =
          repeated a + repeated b +
            (qExt (tprod R (insertTwoTensorEntries n p a b m)) +
              qExt (tprod R (insertTwoTensorEntries n p b a m))) := by
            dsimp [repeated]
            rw [linearMap_insertTwoTensorEntries_add_left
              (R := R) (M := M) (q := qExt) p a b (a + b) m]
            rw [linearMap_insertTwoTensorEntries_add_right
              (R := R) (M := M) (q := qExt) p a a b m]
            rw [linearMap_insertTwoTensorEntries_add_right
              (R := R) (M := M) (q := qExt) p b a b m]
            abel
      _ = 0 := by
            rw [hza, hzb, hcross]
            simp
  · intro r a ha hza
    -- Scalar multiplication in each distinguished slot reduces to the inductive diagonal term.
    calc
      repeated (r • a) =
          r • (r • repeated a) := by
            dsimp [repeated]
            rw [linearMap_insertTwoTensorEntries_smul_left
              (R := R) (M := M) (q := qExt) p r a (r • a) m]
            rw [linearMap_insertTwoTensorEntries_smul_right
              (R := R) (M := M) (q := qExt) p a a r m]
      _ = 0 := by rw [hza, smul_zero, smul_zero]

/-- Helper for Lemma 10.13.3: the quotient pure-tensor map before imposing alternation on the
family of inputs. -/
private noncomputable def exteriorRelationQuotientMultilinear :
    MultilinearMap R (fun _ : Fin n ↦ M)
      ((⨂[R]^n M) ⧸
        (LinearMap.range (exteriorRelationMapOfFamily n x) : Submodule R (⨂[R]^n M))) :=
  ((LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ).compMultilinearMap (tprod R)

/-- Helper for Lemma 10.13.3: once the generators span `M`, the quotient pure-tensor map already
vanishes on tuples with two equal entries. -/
private theorem exteriorRelationQuotientMultilinear_map_eq_zero_of_eq
    (hx : Submodule.span R (Set.range x) = ⊤)
    (v : Fin n → M) (i j : Fin n) (hij : v i = v j) (hne : i ≠ j) :
    exteriorRelationQuotientMultilinear (R := R) (M := M) (n := n) (x := x) v = 0 := by
  rcases lt_or_gt_of_ne hne with hijlt | hijgt
  · let p : TensorSlotPair n := ⟨⟨i, j⟩, hijlt⟩
    have hy : v i ∈ Submodule.span R (Set.range x) := by
      rw [hx]
      simp
    have hv :
        insertTwoTensorEntries n p (v i) (v i) (deleteTwoTensorEntries n p v) = v := by
      simpa [p, hij] using
        (insertTwoTensorEntries_deleteTwoTensorEntries (n := n) (p := p) (v := v))
    have hrewrite :
        (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ (tprod R v) =
          (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
            (tprod R (insertTwoTensorEntries n p (v i) (v i) (deleteTwoTensorEntries n p v))) := by
      simpa using
        congrArg
          (fun w ↦ (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ (tprod R w))
          hv.symm
    -- Normalize the tuple to an inserted family with equal distinguished entries.
    calc
      exteriorRelationQuotientMultilinear (R := R) (M := M) (n := n) (x := x) v
        = (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ (tprod R v) := by
            rfl
      _ = (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
            (tprod R (insertTwoTensorEntries n p (v i) (v i) (deleteTwoTensorEntries n p v))) :=
              hrewrite
      _ = 0 := exteriorRelationQuotient_repeated_eq_zero_of_span
            (R := R) (M := M) (n := n) (x := x) p (deleteTwoTensorEntries n p v) hy
  · let p : TensorSlotPair n := ⟨⟨j, i⟩, hijgt⟩
    have hy : v j ∈ Submodule.span R (Set.range x) := by
      rw [hx]
      simp
    have hv :
        insertTwoTensorEntries n p (v j) (v j) (deleteTwoTensorEntries n p v) = v := by
      simpa [p, hij] using
        (insertTwoTensorEntries_deleteTwoTensorEntries (n := n) (p := p) (v := v))
    have hrewrite :
        (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ (tprod R v) =
          (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
            (tprod R (insertTwoTensorEntries n p (v j) (v j) (deleteTwoTensorEntries n p v))) := by
      simpa using
        congrArg
          (fun w ↦ (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ (tprod R w))
          hv.symm
    -- The opposite slot ordering uses the same delete/reinsert normalization.
    calc
      exteriorRelationQuotientMultilinear (R := R) (M := M) (n := n) (x := x) v
        = (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ (tprod R v) := by
            rfl
      _ = (LinearMap.range (exteriorRelationMapOfFamily n x)).mkQ
            (tprod R (insertTwoTensorEntries n p (v j) (v j) (deleteTwoTensorEntries n p v))) :=
              hrewrite
      _ = 0 := exteriorRelationQuotient_repeated_eq_zero_of_span
            (R := R) (M := M) (n := n) (x := x) p (deleteTwoTensorEntries n p v) hy

/-- Helper for Lemma 10.13.3: the quotient by the displayed exterior family relations already
carries the canonical alternating pure-tensor map. -/
private noncomputable def exteriorRelationQuotientAlternating
    (hx : Submodule.span R (Set.range x) = ⊤) :
    M [⋀^Fin n]→ₗ[R]
      ((⨂[R]^n M) ⧸
        (LinearMap.range (exteriorRelationMapOfFamily n x) : Submodule R (⨂[R]^n M))) :=
  { exteriorRelationQuotientMultilinear (R := R) (M := M) (n := n) (x := x) with
    map_eq_zero_of_eq' := fun v i j hij hne ↦
      exteriorRelationQuotientMultilinear_map_eq_zero_of_eq
        (R := R) (M := M) (n := n) (x := x) hx v i j hij hne }

-- Proof sketch: compare the presented relation map with the standard presentation of the exterior
-- power, use that the family `x` spans `M` to show the alternating relations generated by the
-- chosen tensors already generate the full kernel, and combine this with surjectivity of the
-- canonical quotient map.
/-- Canonical kernel/range form of Stacks Project, Lemma 10.13.3 (1): if
`x : I → M` spans `M`, then the kernel of the canonical quotient map `T^n(M) → ⋀^n M` is the
range of the swap and repetition relation map built from the generators `x`. -/
theorem generator_exterior_power_ker_eq_range (hx : Submodule.span R (Set.range x) = ⊤) :
    LinearMap.ker
        (lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) =
      LinearMap.range (exteriorRelationMapOfFamily n x) := by
  let Q : Submodule R (⨂[R]^n M) := LinearMap.range (exteriorRelationMapOfFamily n x)
  let qToExterior :
      (⨂[R]^n M) ⧸ Q →ₗ[R] ⋀[R]^n M :=
    Q.liftQ (lift (ιMulti R n).toMultilinearMap)
      (exteriorRelationMapOfFamily_range_le_ker (R := R) (M := M) (n := n) (x := x))
  let sectionMap :
      ⋀[R]^n M →ₗ[R] (⨂[R]^n M) ⧸ Q :=
    exteriorPower.alternatingMapLinearEquiv
      (exteriorRelationQuotientAlternating (R := R) (M := M) (n := n) (x := x) hx)
  have hsection :
      ∀ m : Fin n → M,
        sectionMap (ιMulti R n m) = Q.mkQ (tprod R m) := by
    intro m
    -- The universal property identifies the descended alternating map on pure wedges.
    simpa [sectionMap, exteriorRelationQuotientAlternating, exteriorRelationQuotientMultilinear, Q]
      using
        (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
          (R := R) (n := n)
          (f := exteriorRelationQuotientAlternating
            (R := R) (M := M) (n := n) (x := x) hx) m)
  have hqToExterior :
      qToExterior.comp Q.mkQ =
        (lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := by
    -- The quotient lift agrees with the original tensor-to-wedge map on representatives.
    simpa [qToExterior, Q] using
      (Submodule.liftQ_mkQ Q (lift (ιMulti R n).toMultilinearMap)
        (exteriorRelationMapOfFamily_range_le_ker (R := R) (M := M) (n := n) (x := x)))
  have hleft : sectionMap.comp qToExterior = LinearMap.id := by
    -- Quotient classes of pure tensors span, so the composite is determined on those generators.
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (tensor_quotient_mkQ_tprod_span_top (R := R) (M := M) (n := n) Q)]
    rintro ⟨_, ⟨m, rfl⟩⟩
    have hdesc := LinearMap.congr_fun hqToExterior (tprod R m)
    have hι :
        (lift (ιMulti R n).toMultilinearMap : ⨂[R]^n M →ₗ[R] ⋀[R]^n M) (tprod R m) =
          ιMulti R n m := by
      simpa using
        (PiTensorProduct.lift.tprod (R := R) (f := (ιMulti R n).toMultilinearMap) (m := m))
    calc
      sectionMap (qToExterior (Q.mkQ (tprod R m))) =
          sectionMap ((lift (ιMulti R n).toMultilinearMap) (tprod R m)) := by
            simpa [LinearMap.comp_apply] using congrArg sectionMap hdesc
      _ = sectionMap (ιMulti R n m) := by
            rw [hι]
      _ = Q.mkQ (tprod R m) := hsection m
      _ = LinearMap.id (Q.mkQ (tprod R m)) := by simp
  have hqToExterior_injective : Function.Injective qToExterior := by
    -- A left inverse on the quotient makes the descended comparison map injective.
    intro a b hab
    have hab' := congrArg sectionMap hab
    have ha : sectionMap (qToExterior a) = a := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft a
    have hb : sectionMap (qToExterior b) = b := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft b
    simpa [ha, hb] using hab'
  apply le_antisymm
  · intro z hz
    have hz' : qToExterior (Q.mkQ z) = 0 := by
      -- Passing a kernel element through the quotient comparison map still gives zero.
      simpa [qToExterior, Q] using LinearMap.mem_ker.mp hz
    have hmkQ : Q.mkQ z = 0 := hqToExterior_injective hz'
    -- The quotient class is zero exactly for elements of the defining relation submodule.
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmkQ
    exact hmkQ
  · exact exteriorRelationMapOfFamily_range_le_ker (R := R) (M := M) (n := n) (x := x)

/-- Lemma 10.13.3 (1): if `x : I → M` spans `M`, then the canonical quotient map
from `T^n(M)` to `⋀^n M` has kernel generated by the swap and repetition relations built from the
generators `x`; equivalently, these relation tensors form the left map in an exact sequence
ending in `⋀^n M → 0`. -/
@[stacks 00DP]
theorem generator_exterior_power_exact_sequence (hx : Submodule.span R (Set.range x) = ⊤) :
    Function.Exact (exteriorRelationMapOfFamily n x)
      (lift (ιMulti R n).toMultilinearMap) ∧
    Function.Surjective (lift (ιMulti R n).toMultilinearMap :
      ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := by
  refine ⟨LinearMap.exact_iff.mpr (generator_exterior_power_ker_eq_range n x hx), ?_⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← ιMulti_span R n M, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact ⟨tprod R m, by simp⟩

/-- Helper for Lemma 10.13.3: in the quotient by the displayed symmetric family relations, swapping
two distinguished inserted entries does not change the quotient class once both entries lie in the
span of the chosen generators. -/
private theorem symmetricRelationQuotient_swap_eq_of_span
    (p : TensorSlotPair n) (m : Fin (n - 2) → M)
    {y₁ y₂ : M}
    (hy₁ : y₁ ∈ Submodule.span R (Set.range x))
    (hy₂ : y₂ ∈ Submodule.span R (Set.range x)) :
    (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ
        (PiTensorProduct.tprod R (insertTwoTensorEntries n p y₁ y₂ m)) =
      (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ
        (PiTensorProduct.tprod R (insertTwoTensorEntries n p y₂ y₁ m)) := by
  let Q : Submodule R (⨂[R]^n M) := LinearMap.range (symmetricRelationMapOfFamily n x)
  let qSym : ⨂[R]^n M →ₗ[R] (⨂[R]^n M) ⧸ Q := Q.mkQ
  let swapDiff : M → M → (⨂[R]^n M) ⧸ Q := fun a b ↦
    qSym (tprod R (insertTwoTensorEntries n p a b m)) -
      qSym (tprod R (insertTwoTensorEntries n p b a m))
  apply sub_eq_zero.mp
  change swapDiff y₁ y₂ = 0
  -- The quotient commutator vanishes by the same two-step span induction as in the exterior case.
  refine Submodule.span_induction (p := fun y _ ↦ ∀ {z : M},
    z ∈ Submodule.span R (Set.range x) → swapDiff z y = 0) ?_ ?_ ?_ ?_ hy₂ hy₁
  · intro y hy z hz
    rcases hy with ⟨i₂, rfl⟩
    -- For a fixed generator on the right, a second span induction handles the left slot.
    refine Submodule.span_induction (p := fun y _ ↦ swapDiff y (x i₂) = 0) ?_ ?_ ?_ ?_ hz
    · intro y hy
      rcases hy with ⟨i₁, rfl⟩
      simpa [swapDiff, qSym, Q, LinearMap.map_sub] using
        symmetricRelationQuotient_single_tprod_eq_zero
          (R := R) (M := M) (n := n) (x := x) p i₁ i₂ m
    · -- Zero in the left slot kills both inserted tensors by multilinearity.
      change swapDiff (0 : M) (x i₂) = 0
      calc
        swapDiff (0 : M) (x i₂)
          = qSym (tprod R (insertTwoTensorEntries n p ((0 : R) • (0 : M)) (x i₂) m)) -
              qSym (tprod R (insertTwoTensorEntries n p (x i₂) ((0 : R) • (0 : M)) m)) := by
                  simp [swapDiff]
        _ = (0 : R) • qSym (tprod R (insertTwoTensorEntries n p (0 : M) (x i₂) m)) -
              (0 : R) • qSym (tprod R (insertTwoTensorEntries n p (x i₂) (0 : M) m)) := by
                  rw [linearMap_insertTwoTensorEntries_smul_left
                        (R := R) (M := M) (q := qSym) p (0 : R) (0 : M) (x i₂) m,
                    linearMap_insertTwoTensorEntries_smul_right
                        (R := R) (M := M) (q := qSym) p (x i₂) (0 : M) (0 : R) m]
        _ = 0 := by simp
    · intro a b ha hb hza hzb
      -- Additivity in the left slot packages the two inductive vanishings into one identity.
      calc
        swapDiff (a + b) (x i₂)
          = swapDiff a (x i₂) + swapDiff b (x i₂) := by
              dsimp [swapDiff]
              rw [linearMap_insertTwoTensorEntries_add_left
                    (R := R) (M := M) (q := qSym) p a b (x i₂) m,
                linearMap_insertTwoTensorEntries_add_right
                    (R := R) (M := M) (q := qSym) p (x i₂) a b m]
              abel
        _ = 0 := by rw [hza, hzb, add_zero]
    · intro r a ha hza
      -- Scalar compatibility in the two distinguished slots reduces to the inductive case.
      calc
        swapDiff (r • a) (x i₂)
          = r • swapDiff a (x i₂) := by
              dsimp [swapDiff]
              rw [linearMap_insertTwoTensorEntries_smul_left
                    (R := R) (M := M) (q := qSym) p r a (x i₂) m,
                linearMap_insertTwoTensorEntries_smul_right
                    (R := R) (M := M) (q := qSym) p (x i₂) a r m]
              simp [smul_sub]
        _ = 0 := by rw [hza, smul_zero]
  · intro z hz
    -- Zero in the right slot vanishes by the corresponding right-slot multilinearity.
    change swapDiff z (0 : M) = 0
    calc
      swapDiff z (0 : M)
        = qSym (tprod R (insertTwoTensorEntries n p z ((0 : R) • (0 : M)) m)) -
            qSym (tprod R (insertTwoTensorEntries n p ((0 : R) • (0 : M)) z m)) := by
                simp [swapDiff]
      _ = (0 : R) • qSym (tprod R (insertTwoTensorEntries n p z (0 : M) m)) -
            (0 : R) • qSym (tprod R (insertTwoTensorEntries n p (0 : M) z m)) := by
                rw [linearMap_insertTwoTensorEntries_smul_right
                      (R := R) (M := M) (q := qSym) p z (0 : M) (0 : R) m,
                  linearMap_insertTwoTensorEntries_smul_left
                      (R := R) (M := M) (q := qSym) p (0 : R) (0 : M) z m]
      _ = 0 := by simp
  · intro a b ha hb hza hzb z hz
    -- Additivity in the right slot turns the outer induction step into a sum of known zeros.
    calc
      swapDiff z (a + b)
        = swapDiff z a + swapDiff z b := by
            dsimp [swapDiff]
            rw [linearMap_insertTwoTensorEntries_add_right
                  (R := R) (M := M) (q := qSym) p z a b m,
              linearMap_insertTwoTensorEntries_add_left
                  (R := R) (M := M) (q := qSym) p a b z m]
            abel
      _ = 0 := by rw [hza hz, hzb hz, add_zero]
  · intro r a ha hza z hz
    -- The right-slot scalar rule gives the same reduction for scalar multiples.
    calc
      swapDiff z (r • a)
        = r • swapDiff z a := by
            dsimp [swapDiff]
            rw [linearMap_insertTwoTensorEntries_smul_right
                  (R := R) (M := M) (q := qSym) p z a r m,
              linearMap_insertTwoTensorEntries_smul_left
                  (R := R) (M := M) (q := qSym) p r a z m]
            simp [smul_sub]
      _ = 0 := by rw [hza hz, smul_zero]

/-- Helper for Lemma 10.13.3: once the generators span `M`, the quotient by the displayed
symmetric family relations is invariant under permuting the entries of a pure tensor. -/
private theorem symmetricRelationQuotient_tprod_eq_of_perm
    (hx : Submodule.span R (Set.range x) = ⊤)
    (e : Equiv.Perm (Fin n)) (v : Fin n → M) :
    (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ (tprod R (v ∘ e)) =
      (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ (tprod R v) := by
  let Q : Submodule R (⨂[R]^n M) := LinearMap.range (symmetricRelationMapOfFamily n x)
  let qSym : ⨂[R]^n M →ₗ[R] (⨂[R]^n M) ⧸ Q := Q.mkQ
  have hswap :
      ∀ (w : Fin n → M) {i j : Fin n}, i ≠ j →
        qSym (tprod R (w ∘ Equiv.swap i j)) = qSym (tprod R w) := by
    intro w i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hijgt
    · let p : TensorSlotPair n := ⟨⟨i, j⟩, hijlt⟩
      have hwi : w i ∈ Submodule.span R (Set.range x) := by
        rw [hx]
        simp
      have hwj : w j ∈ Submodule.span R (Set.range x) := by
        rw [hx]
        simp
      have hw :
          insertTwoTensorEntries n p (w i) (w j) (deleteTwoTensorEntries n p w) = w := by
        simpa [p] using
          insertTwoTensorEntries_deleteTwoTensorEntries (n := n) (p := p) (v := w)
      have hswapw :
          insertTwoTensorEntries n p (w j) (w i) (deleteTwoTensorEntries n p w) =
            w ∘ Equiv.swap i j := by
        calc
          insertTwoTensorEntries n p (w j) (w i) (deleteTwoTensorEntries n p w)
            = insertTwoTensorEntries n p (w i) (w j) (deleteTwoTensorEntries n p w) ∘
                Equiv.swap i j := by
                  simpa [p] using
                    insertTwoTensorEntries_swap (n := n) p (w j) (w i)
                      (deleteTwoTensorEntries n p w)
          _ = w ∘ Equiv.swap i j := by rw [hw]
      -- Normalize to the inserted-family presentation attached to the swapped pair of slots.
      calc
        qSym (tprod R (w ∘ Equiv.swap i j))
          = qSym (tprod R
              (insertTwoTensorEntries n p (w j) (w i) (deleteTwoTensorEntries n p w))) := by
                  rw [hswapw]
        _ = qSym (tprod R
              (insertTwoTensorEntries n p (w i) (w j) (deleteTwoTensorEntries n p w))) := by
                  symm
                  exact symmetricRelationQuotient_swap_eq_of_span
                    (R := R) (M := M) (n := n) (x := x) p (deleteTwoTensorEntries n p w)
                    hwi hwj
        _ = qSym (tprod R w) := by rw [hw]
    · let p : TensorSlotPair n := ⟨⟨j, i⟩, hijgt⟩
      have hwj : w j ∈ Submodule.span R (Set.range x) := by
        rw [hx]
        simp
      have hwi : w i ∈ Submodule.span R (Set.range x) := by
        rw [hx]
        simp
      have hw :
          insertTwoTensorEntries n p (w j) (w i) (deleteTwoTensorEntries n p w) = w := by
        simpa [p] using
          insertTwoTensorEntries_deleteTwoTensorEntries (n := n) (p := p) (v := w)
      have hswapw :
          insertTwoTensorEntries n p (w i) (w j) (deleteTwoTensorEntries n p w) =
            w ∘ Equiv.swap i j := by
        calc
          insertTwoTensorEntries n p (w i) (w j) (deleteTwoTensorEntries n p w)
            = insertTwoTensorEntries n p (w j) (w i) (deleteTwoTensorEntries n p w) ∘
                Equiv.swap j i := by
                  simpa [p] using
                    insertTwoTensorEntries_swap (n := n) p (w i) (w j)
                      (deleteTwoTensorEntries n p w)
          _ = w ∘ Equiv.swap i j := by
                rw [hw]
                simp [Equiv.swap_comm]
      -- The opposite slot order uses the same normalization because `swap i j = swap j i`.
      calc
        qSym (tprod R (w ∘ Equiv.swap i j))
          = qSym (tprod R
              (insertTwoTensorEntries n p (w i) (w j) (deleteTwoTensorEntries n p w))) := by
                  rw [hswapw]
        _ = qSym (tprod R
              (insertTwoTensorEntries n p (w j) (w i) (deleteTwoTensorEntries n p w))) := by
                  exact symmetricRelationQuotient_swap_eq_of_span
                    (R := R) (M := M) (n := n) (x := x) p (deleteTwoTensorEntries n p w)
                    hwi hwj
        _ = qSym (tprod R w) := by rw [hw]
  -- `swap_induction_on'` promotes transposition invariance to full permutation invariance.
  induction e using Equiv.Perm.swap_induction_on' with
  | one =>
      simp
  | mul_swap e i j hij he =>
      have hswap' :
          (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ
              (tprod R ((v ∘ e) ∘ Equiv.swap i j)) =
            (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ (tprod R (v ∘ e)) := by
        simpa [Q, qSym] using hswap (v ∘ e) hij
      have ht :
          (PiTensorProduct.tprod R) (v ∘ (e * Equiv.swap i j)) =
            (PiTensorProduct.tprod R) ((v ∘ e) ∘ Equiv.swap i j) := by
        simpa [Function.comp] using
          congrArg (PiTensorProduct.tprod R)
            (show v ∘ (e * Equiv.swap i j) = (v ∘ e) ∘ Equiv.swap i j by rfl)
      exact (congrArg ((LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ) ht).trans
        (hswap'.trans he)

/-- Helper for Lemma 10.13.3: the quotient map by the displayed symmetric family relations is
constant on the congruence generated by `SymmetricPower.Rel`. -/
private theorem symmetricRelationQuotient_eq_of_rel
    (hx : Submodule.span R (Set.range x) = ⊤)
    {u v : ⨂[R]^n M}
    (h : addConGen (SymmetricPower.Rel R (Fin n) M) u v) :
    (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ u =
      (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ v := by
  induction h with
  | of _ _ hrel =>
      cases hrel with
      | perm e m =>
          -- The generating relation is exactly permutation invariance on pure tensors.
          simpa [Function.comp_apply] using
            (symmetricRelationQuotient_tprod_eq_of_perm
              (R := R) (M := M) (n := n) (x := x) hx e m).symm
  | refl =>
      rfl
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ =>
      simpa [LinearMap.map_add] using congrArg₂ (· + ·) ih₁ ih₂

/-- Helper for Lemma 10.13.3: the additive congruence defining symmetric power is contained in the
kernel congruence of the quotient map by the displayed symmetric family relations. -/
private theorem symmetricRelationQuotient_rel_le_ker
    (hx : Submodule.span R (Set.range x) = ⊤) :
    addConGen (SymmetricPower.Rel R (Fin n) M) ≤
      AddCon.ker (((LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ).toAddMonoidHom) := by
  intro u v h
  exact symmetricRelationQuotient_eq_of_rel (R := R) (M := M) (n := n) (x := x) hx h

/-- Helper for Lemma 10.13.3: the additive comparison map from symmetric power to the quotient by
the displayed symmetric family relations, obtained by descending `mkQ`. -/
private noncomputable def symmetricRelationQuotientDescAddHom
    (hx : Submodule.span R (Set.range x) = ⊤) :
    Sym[R]^n M →+
      ((⨂[R]^n M) ⧸
        (LinearMap.range (symmetricRelationMapOfFamily n x) : Submodule R (⨂[R]^n M))) :=
  AddCon.lift (addConGen (SymmetricPower.Rel R (Fin n) M))
    (((LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ).toAddMonoidHom)
    (symmetricRelationQuotient_rel_le_ker (R := R) (M := M) (n := n) (x := x) hx)

/-- Helper for Lemma 10.13.3: the descended additive comparison map is still `R`-linear because
the raw quotient map `mkQ` is linear on tensor power. -/
private theorem symmetricRelationQuotientDescAddHom_map_smul
    (hx : Submodule.span R (Set.range x) = ⊤)
    (r : R) (z : Sym[R]^n M) :
    symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx (r • z) =
      r • symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx z := by
  -- The quotient is generated by tensor-power classes, so checking scalar compatibility on
  -- representatives suffices.
  refine AddCon.induction_on z ?_
  intro y
  change
    symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx
      (((r • y : ⨂[R]^n M) :
        (addConGen (SymmetricPower.Rel R (Fin n) M)).Quotient)) =
      r • symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx
        ((y : ⨂[R]^n M) :
          (addConGen (SymmetricPower.Rel R (Fin n) M)).Quotient)
  calc
    symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx
        (((r • y : ⨂[R]^n M) :
          (addConGen (SymmetricPower.Rel R (Fin n) M)).Quotient))
      = (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ (r • y) := by
          rfl
    _ = r • (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ y := by
          simpa using ((LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ).map_smul r y
    _ = r • symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx
          ((y : ⨂[R]^n M) :
            (addConGen (SymmetricPower.Rel R (Fin n) M)).Quotient) := by
          rfl

/-- Helper for Lemma 10.13.3: the quotient by the displayed symmetric family relations already
carries the canonical comparison map from `Sym[R]^n M`. -/
private noncomputable def symmetricRelationQuotientDesc
    (hx : Submodule.span R (Set.range x) = ⊤) :
    Sym[R]^n M →ₗ[R]
      ((⨂[R]^n M) ⧸
        (LinearMap.range (symmetricRelationMapOfFamily n x) : Submodule R (⨂[R]^n M))) :=
  { symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx with
    map_smul' := symmetricRelationQuotientDescAddHom_map_smul
      (R := R) (M := M) (n := n) (x := x) hx }

/-- Helper for Lemma 10.13.3: on pure symmetric tensors, the descended comparison map is exactly
the quotient class of the corresponding pure tensor in tensor power. -/
private theorem symmetricRelationQuotientDesc_tprod
    (hx : Submodule.span R (Set.range x) = ⊤)
    (m : Fin n → M) :
    symmetricRelationQuotientDesc (R := R) (M := M) (n := n) (x := x) hx
        (SymmetricPower.tprod R m) =
      (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ (tprod R m) := by
  -- The descended map was defined from `mkQ`, so the pure-tensor formula is immediate.
  change
    symmetricRelationQuotientDescAddHom (R := R) (M := M) (n := n) (x := x) hx
      (((tprod R m : ⨂[R]^n M) :
        (addConGen (SymmetricPower.Rel R (Fin n) M)).Quotient)) =
      (LinearMap.range (symmetricRelationMapOfFamily n x)).mkQ (tprod R m)
  rfl

-- Proof sketch: compare the presented relation map with the canonical quotient defining
-- `SymmetricPower.mk`, and use that the generators `x` span `M` to see that the listed commutator
-- relations already generate the kernel of the quotient map.
/-- Canonical kernel/range form of Stacks Project, Lemma 10.13.3 (2): if
`x : I → M` spans `M`, then the kernel of the canonical quotient map `T^n(M) → Sym[R]^n M` is
the range of the commutator relation map built from the generators `x`. -/
theorem generator_symmetric_power_ker_eq_range (hx : Submodule.span R (Set.range x) = ⊤) :
    LinearMap.ker (SymmetricPower.mk R (Fin n) M) =
      LinearMap.range (symmetricRelationMapOfFamily n x) := by
  let Q : Submodule R (⨂[R]^n M) := LinearMap.range (symmetricRelationMapOfFamily n x)
  let qToSym :
      (⨂[R]^n M) ⧸ Q →ₗ[R] Sym[R]^n M :=
    Q.liftQ (SymmetricPower.mk R (Fin n) M)
      (symmetricRelationMapOfFamily_range_le_ker (R := R) (M := M) (n := n) (x := x))
  let sectionMap :
      Sym[R]^n M →ₗ[R] (⨂[R]^n M) ⧸ Q :=
    symmetricRelationQuotientDesc (R := R) (M := M) (n := n) (x := x) hx
  have hsection :
      ∀ m : Fin n → M,
        sectionMap (SymmetricPower.tprod R m) = Q.mkQ (tprod R m) := by
    intro m
    -- The descended comparison map was built to agree with `mkQ` on pure tensors.
    simpa [sectionMap, Q] using
      symmetricRelationQuotientDesc_tprod (R := R) (M := M) (n := n) (x := x) hx m
  have hqToSym :
      qToSym.comp Q.mkQ = SymmetricPower.mk R (Fin n) M := by
    -- The quotient lift agrees with the original tensor-to-symmetric map on representatives.
    simpa [qToSym, Q] using
      (Submodule.liftQ_mkQ Q (SymmetricPower.mk R (Fin n) M)
        (symmetricRelationMapOfFamily_range_le_ker (R := R) (M := M) (n := n) (x := x)))
  have hleft : sectionMap.comp qToSym = LinearMap.id := by
    -- Quotient classes of pure tensors span, so the composite is determined on those generators.
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (tensor_quotient_mkQ_tprod_span_top (R := R) (M := M) (n := n) Q)]
    rintro ⟨_, ⟨m, rfl⟩⟩
    have hdesc := LinearMap.congr_fun hqToSym (tprod R m)
    calc
      sectionMap (qToSym (Q.mkQ (tprod R m))) =
          sectionMap ((SymmetricPower.mk R (Fin n) M) (tprod R m)) := by
            simpa [LinearMap.comp_apply] using congrArg sectionMap hdesc
      _ = sectionMap (SymmetricPower.tprod R m) := by
            simp [SymmetricPower.tprod]
      _ = Q.mkQ (tprod R m) := hsection m
      _ = LinearMap.id (Q.mkQ (tprod R m)) := by simp
  have hqToSym_injective : Function.Injective qToSym := by
    -- A left inverse on the quotient makes the descended comparison map injective.
    intro a b hab
    have hab' := congrArg sectionMap hab
    have ha : sectionMap (qToSym a) = a := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft a
    have hb : sectionMap (qToSym b) = b := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft b
    simpa [ha, hb] using hab'
  apply le_antisymm
  · intro z hz
    have hz' : qToSym (Q.mkQ z) = 0 := by
      -- Passing a kernel element through the quotient comparison map still gives zero.
      simpa [qToSym, Q] using LinearMap.mem_ker.mp hz
    have hmkQ : Q.mkQ z = 0 := hqToSym_injective hz'
    -- The quotient class is zero exactly for elements of the defining relation submodule.
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmkQ
    exact hmkQ
  · exact symmetricRelationMapOfFamily_range_le_ker (R := R) (M := M) (n := n) (x := x)

/-- Lemma 10.13.3 (2): if `x : I → M` spans `M`, then the canonical quotient map
from `T^n(M)` to the `n`th symmetric tensor power has kernel generated by the commutator relations
built from the generators `x`; equivalently, these relation tensors form the left map in an exact
sequence ending in `Sym[R]^n M → 0`. -/
@[stacks 00DP]
theorem generator_symmetric_power_exact_sequence (hx : Submodule.span R (Set.range x) = ⊤) :
    Function.Exact (symmetricRelationMapOfFamily n x)
      (SymmetricPower.mk R (Fin n) M) ∧
    Function.Surjective (SymmetricPower.mk R (Fin n) M) := by
  refine ⟨LinearMap.exact_iff.mpr (generator_symmetric_power_ker_eq_range n x hx), ?_⟩
  exact AddCon.mk'_surjective

end FamilyRelations

end
