import Mathlib
import stacks_project.Chap10.Lemma_10_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PiTensorProduct exteriorPower

section

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
variable (n : ℕ) (M : Type) [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M]

local instance exteriorPowerModule : Module A (⋀[B]^n M) :=
  Module.compHom _ (algebraMap A B)

local instance exteriorPowerIsScalarTower : IsScalarTower A B (⋀[B]^n M) :=
  IsScalarTower.of_compHom A B _

local instance tensorPowerOverBaseModule : Module A (⨂[B]^n M) := by
  infer_instance

local instance tensorPowerOverBaseIsScalarTower : IsScalarTower A B (⨂[B]^n M) := by
  infer_instance

/-- Helper for Lemma 10.13.4: the scalar-tower actions let us view the canonical `B`-linear map
from tensor power to exterior power as an `A`-linear map. -/
local instance tensorPowerToExteriorCompatibleSMul :
    LinearMap.CompatibleSMul (⨂[B]^n M) (⋀[B]^n M) A B where
  map_smul f a x := by
    -- Both `A`-actions are induced through `algebraMap A B`, so `B`-linearity is enough.
    simpa [Algebra.smul_def] using f.map_smul (algebraMap A B a) x

/-- Helper for Lemma 10.13.4: the canonical comparison map from the tensor power over `A` to the
tensor power over `B`, obtained by restricting the multilinear pure-tensor map along `A → B`. -/
noncomputable def tensorPowerRestrictScalarsToBase :
    (⨂[A]^n M) →ₗ[A] (⨂[B]^n M) :=
  lift ((tprod B : MultilinearMap B (fun _ : Fin n ↦ M) (⨂[B]^n M)).restrictScalars A)

/-- Helper for Lemma 10.13.4: the scalar-restriction comparison map preserves pure tensors. -/
@[simp] lemma tensorPowerRestrictScalarsToBase_tprod (m : Fin n → M) :
    tensorPowerRestrictScalarsToBase A B n M (tprod A m) = tprod B m := by
  -- The comparison map was defined by the universal property of the tensor power over `A`.
  simp [tensorPowerRestrictScalarsToBase]

/-- Helper for Lemma 10.13.4: in positive degree, every tensor over `B` comes from the tensor
power over `A` by absorbing the leading `B`-scalar into one chosen tensor slot. -/
lemma tensorPowerRestrictScalarsToBase_surjective (hn : 0 < n) :
    Function.Surjective (tensorPowerRestrictScalarsToBase A B n M) := by
  let i0 : Fin n := ⟨0, hn⟩
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod b m =>
      -- In positive degree, move the scalar `b` into the fixed slot `i0`.
      refine ⟨tprod A (Function.update m i0 (b • m i0)), ?_⟩
      rw [tensorPowerRestrictScalarsToBase_tprod]
      simpa [i0] using
        (tprod B : MultilinearMap B (fun _ : Fin n ↦ M) (⨂[B]^n M)).map_update_smul
          m i0 b (m i0)
  | add z₁ z₂ hz₁ hz₂ =>
      -- Surjectivity is stable under sums because the comparison map is linear.
      rcases hz₁ with ⟨x₁, rfl⟩
      rcases hz₂ with ⟨x₂, rfl⟩
      refine ⟨x₁ + x₂, by simp⟩

/-- Helper for Lemma 10.13.4: the canonical map to the exterior power factors through the tensor
power formed over `B`. -/
lemma tensorPowerToExterior_factor_tprod (m : Fin n → M) :
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) : (⨂[A]^n M) →ₗ[A] ⋀[B]^n M)
      (tprod A m) =
      (((lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B n M)) (tprod A m) := by
  -- Both sides evaluate pure tensors through the same alternating multilinear map over `B`.
  calc
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) : (⨂[A]^n M) →ₗ[A] ⋀[B]^n M)
        (tprod A m) =
      ((ιMulti B n).toMultilinearMap.restrictScalars A) m := by
        rw [PiTensorProduct.lift.tprod]
    _ = (ιMulti B n).toMultilinearMap m := rfl
    _ = (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M) (tprod B m) := by
        rw [PiTensorProduct.lift.tprod]
        rfl
    _ =
      (((lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B n M)) (tprod A m) := by
        simp [LinearMap.comp_apply, tensorPowerRestrictScalarsToBase_tprod]

/-- Helper for Lemma 10.13.4: the canonical map to the exterior power factors through the tensor
power formed over `B`. -/
lemma tensorPowerToExterior_factor :
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) : (⨂[A]^n M) →ₗ[A] ⋀[B]^n M) =
      ((lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B n M) := by
  -- Route correction: prove the factorization on pure tensors first, then invoke tensor-power
  -- induction to extend the pure-tensor computation across the whole tensor power.
  refine LinearMap.ext fun z ↦ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
      -- The factorization is already known on pure tensors, and both sides are linear.
      rw [map_smul, LinearMap.comp_apply, map_smul,
        tensorPowerToExterior_factor_tprod (A := A) (B := B) (n := n) (M := M)]
      rw [map_smul, LinearMap.comp_apply]
  | add x y hx hy =>
      -- The equality is stable under addition because both maps are linear.
      simp [hx, hy]

/-- Helper for Lemma 10.13.4: over `B`, every repeated-entry tensor lies in the kernel of the
canonical map to the exterior power. -/
lemma repeated_relation_mem_exterior_ker_over_B
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M) :
    tprod B (insertTwoTensorEntries n p y y m) ∈
      (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).ker := by
  -- Route correction: instead of unfolding the inserted tensor directly, realize it as one of the
  -- explicit generators already packaged in Lemma 10.13.3.
  have hker :
      (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).ker =
        LinearMap.range
          (exteriorRelationMapOfFamily (R := B) (n := n) (x := fun z : M ↦ z)) := by
    simpa [Set.range_id] using
      (generator_exterior_power_ker_eq_range (R := B) (M := M) (I := M)
        (n := n) (x := fun z : M ↦ z)
        (by simpa [Set.range_id] using
          (Submodule.span_univ (R := B) (s := (Set.univ : Set M)))))
  rw [hker]
  refine LinearMap.mem_range.mpr ?_
  refine ⟨(0, Finsupp.single (p, y) (tprod B m)), ?_⟩
  simpa using
    (exteriorRelationMapOfFamily_snd_single_tprod (R := B) (n := n)
      (x := fun z : M ↦ z) p y m)

/-- Helper for Lemma 10.13.4: after pulling back along the tensor-power comparison, the
repeated-entry generators already lie in the target kernel. -/
lemma repeated_relation_mem_target_ker
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M) :
    tprod A (insertTwoTensorEntries n p y y m) ∈
      (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
        (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker := by
  -- Factor the target map through the tensor power over `B`, then use the known kernel generator
  -- description from Lemma 10.13.3.
  rw [tensorPowerToExterior_factor (A := A) (B := B) (n := n) (M := M), LinearMap.mem_ker]
  simpa using
    (LinearMap.mem_ker.mp
      (repeated_relation_mem_exterior_ker_over_B (B := B) (n := n) (M := M) p m y))

/-- Helper for Lemma 10.13.4: the `A`-span of the repeated-entry generators is contained in the
kernel of the canonical map to the exterior power over `B`. -/
lemma repeated_relations_span_le_ker :
    Submodule.span A
      {x | ∃ (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M),
          x = tprod A (insertTwoTensorEntries n p y y m)} ≤
      (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
        (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker := by
  -- It suffices to check the claimed generators.
  rw [Submodule.span_le]
  rintro _ ⟨p, m, y, rfl⟩
  exact repeated_relation_mem_target_ker (A := A) (B := B) (n := n) (M := M) p m y

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

/-- Helper for Lemma 10.13.4: the repeated-entry pure tensors over `A` that appear in the
kernel description. -/
private def repeatedRelationSetOverA : Set (⨂[A]^n M) :=
  {x | ∃ (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M),
      x = tprod A (insertTwoTensorEntries n p y y m)}

/-- Helper for Lemma 10.13.4: the repeated-entry pure tensors over `B` that appear after passing
through the scalar-restriction comparison. -/
private def repeatedRelationSetOverB : Set (⨂[B]^n M) :=
  {x | ∃ (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M),
      x = tprod B (insertTwoTensorEntries n p y y m)}

/-- Helper for Lemma 10.13.4: the balancing relations obtained by moving a `B`-scalar between two
tensor slots. -/
private def balancingRelationSetOverA : Set (⨂[A]^n M) :=
  {x | ∃ (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y z : M) (b : B),
      x = tprod A (insertTwoTensorEntries n p (b • y) z m) -
        tprod A (insertTwoTensorEntries n p y (b • z) m)}

local notation "RepeatedRelationSetOverA" => repeatedRelationSetOverA (A := A) (n := n) (M := M)
local notation "RepeatedRelationSetOverB" => repeatedRelationSetOverB (B := B) (n := n) (M := M)
local notation "BalancingRelationSetOverA" =>
  balancingRelationSetOverA (A := A) (B := B) (n := n) (M := M)

/-- Helper for Lemma 10.13.4: over `B`, the swap relation is already an `A`-linear combination of
repeated-entry generators. -/
lemma swap_relation_mem_span_repeated_relations_over_B
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y z : M) :
    tprod B (insertTwoTensorEntries n p y z m) +
        tprod B (insertTwoTensorEntries n p z y m) ∈
      Submodule.span B RepeatedRelationSetOverB := by
  have hexpand :
      tprod B (insertTwoTensorEntries n p (y + z) (y + z) m) =
        tprod B (insertTwoTensorEntries n p y y m) +
          tprod B (insertTwoTensorEntries n p y z m) +
            (tprod B (insertTwoTensorEntries n p z y m) +
              tprod B (insertTwoTensorEntries n p z z m)) := by
    -- Expand successively in the left and right distinguished tensor slots.
    rw [tprod_insertTwoTensorEntries_left_add (B := B), tprod_insertTwoTensorEntries_right_add
      (B := B), tprod_insertTwoTensorEntries_right_add (B := B)]
  have hrewrite :
      tprod B (insertTwoTensorEntries n p y z m) +
          tprod B (insertTwoTensorEntries n p z y m) =
        tprod B (insertTwoTensorEntries n p (y + z) (y + z) m) -
          tprod B (insertTwoTensorEntries n p y y m) -
            tprod B (insertTwoTensorEntries n p z z m) := by
    rw [hexpand]
    abel
  -- Rewrite the swap relation as a linear combination of three repeated-entry generators.
  rw [hrewrite]
  refine sub_mem (sub_mem ?_ ?_) ?_
  · exact Submodule.subset_span ⟨p, m, y + z, rfl⟩
  · exact Submodule.subset_span ⟨p, m, y, rfl⟩
  · exact Submodule.subset_span ⟨p, m, z, rfl⟩

/-- Helper for Lemma 10.13.4: a first-factor generator of the Stacks Project relation map over
`B` already belongs to the repeated-entry span. -/
lemma exteriorRelationMapOfFamily_fst_single_mem_span_repeated_relations_over_B
    (a : TensorSlotPair n × M × M) (z : ⨂[B]^(n - 2) M) :
    exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w)
        (Finsupp.single a z, 0) ∈
      Submodule.span B RepeatedRelationSetOverB := by
  rcases a with ⟨p, y₁, y₂⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod b m =>
      -- Reduce the first direct-sum generator to the pure swap relation and then use linearity.
      have hbase :
          exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w)
              (Finsupp.single (p, y₁, y₂) (tprod B m), 0) ∈
            Submodule.span B RepeatedRelationSetOverB := by
        rw [exteriorRelationMapOfFamily_fst_single_tprod (R := B) (n := n)
          (x := fun w : M ↦ w) p y₁ y₂ m]
        exact swap_relation_mem_span_repeated_relations_over_B
          (B := B) (n := n) (M := M) p m y₁ y₂
      have hsmul :
          ((Finsupp.single (p, y₁, y₂) (b • tprod B m), 0) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) =
            b • ((Finsupp.single (p, y₁, y₂) (tprod B m), 0) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) := by
        ext <;> simp
      rw [hsmul, map_smul]
      exact Submodule.smul_mem _ _ hbase
  | add z₁ z₂ hz₁ hz₂ =>
      -- The first direct-sum source is linear in the tensor input.
      have hadd :
          ((Finsupp.single (p, y₁, y₂) (z₁ + z₂), 0) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) =
            ((Finsupp.single (p, y₁, y₂) z₁, 0) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) +
            ((Finsupp.single (p, y₁, y₂) z₂, 0) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) := by
        ext <;> simp
      rw [hadd, map_add]
      exact Submodule.add_mem _ hz₁ hz₂

/-- Helper for Lemma 10.13.4: a second-factor generator of the Stacks Project relation map over
`B` already belongs to the repeated-entry span. -/
lemma exteriorRelationMapOfFamily_snd_single_mem_span_repeated_relations_over_B
    (a : TensorSlotPair n × M) (z : ⨂[B]^(n - 2) M) :
    exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w)
        (0, Finsupp.single a z) ∈
      Submodule.span B RepeatedRelationSetOverB := by
  rcases a with ⟨p, y⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod b m =>
      -- Reduce the second direct-sum generator to the pure repeated-entry relation and use
      -- linearity.
      have hbase :
          exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w)
              (0, Finsupp.single (p, y) (tprod B m)) ∈
            Submodule.span B RepeatedRelationSetOverB := by
        rw [exteriorRelationMapOfFamily_snd_single_tprod (R := B) (n := n)
          (x := fun w : M ↦ w) p y m]
        exact Submodule.subset_span ⟨p, m, y, rfl⟩
      have hsmul :
          ((0, Finsupp.single (p, y) (b • tprod B m)) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) =
            b • ((0, Finsupp.single (p, y) (tprod B m)) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) := by
        ext <;> simp
      rw [hsmul, map_smul]
      exact Submodule.smul_mem _ _ hbase
  | add z₁ z₂ hz₁ hz₂ =>
      -- The second direct-sum source is linear in the tensor input as well.
      have hadd :
          ((0, Finsupp.single (p, y) (z₁ + z₂)) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) =
            ((0, Finsupp.single (p, y) z₁) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) +
            ((0, Finsupp.single (p, y) z₂) :
              (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
                ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) := by
        ext <;> simp
      rw [hadd, map_add]
      exact Submodule.add_mem _ hz₁ hz₂

/-- Helper for Lemma 10.13.4: the standard exterior relation map over `B` lands in the span of
repeated-entry tensors, so the skew-symmetry relations contribute no new generators. -/
lemma exteriorRelationMapOfFamily_mem_span_repeated_relations_over_B
    (z :
      (((TensorSlotPair n × M × M) →₀ ⨂[B]^(n - 2) M) ×
        ((TensorSlotPair n × M) →₀ ⨂[B]^(n - 2) M))) :
    exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) z ∈
      Submodule.span B RepeatedRelationSetOverB := by
  have hfst :
      exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (z.1, 0) ∈
        Submodule.span B RepeatedRelationSetOverB := by
    induction z.1 using Finsupp.induction_linear with
    | zero =>
        simpa [exteriorRelationMapOfFamily] using
          (Submodule.zero_mem (Submodule.span B RepeatedRelationSetOverB) :
            (0 : ⨂[B]^n M) ∈ Submodule.span B RepeatedRelationSetOverB)
    | add l₁ l₂ hl₁ hl₂ =>
        have hmap :
            exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (l₁ + l₂, 0) =
              exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (l₁, 0) +
                exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (l₂, 0) := by
          simpa using
            (LinearMap.map_add
              (exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w))
              (l₁, 0) (l₂, 0))
        rw [hmap]
        exact Submodule.add_mem _ hl₁ hl₂
    | single a t =>
        exact exteriorRelationMapOfFamily_fst_single_mem_span_repeated_relations_over_B
          (B := B) (n := n) (M := M) a t
  have hsnd :
      exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (0, z.2) ∈
        Submodule.span B RepeatedRelationSetOverB := by
    induction z.2 using Finsupp.induction_linear with
    | zero =>
        simpa [exteriorRelationMapOfFamily] using
          (Submodule.zero_mem (Submodule.span B RepeatedRelationSetOverB) :
            (0 : ⨂[B]^n M) ∈ Submodule.span B RepeatedRelationSetOverB)
    | add l₁ l₂ hl₁ hl₂ =>
        have hmap :
            exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (0, l₁ + l₂) =
              exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (0, l₁) +
                exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (0, l₂) := by
          simpa using
            (LinearMap.map_add
              (exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w))
              (0, l₁) (0, l₂))
        rw [hmap]
        exact Submodule.add_mem _ hl₁ hl₂
    | single a t =>
        exact exteriorRelationMapOfFamily_snd_single_mem_span_repeated_relations_over_B
          (B := B) (n := n) (M := M) a t
  have hsplit :
      exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) z =
        exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (z.1, 0) +
          exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (0, z.2) := by
    -- Split the direct-sum source into its two finitely supported components.
    calc
      exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) z
        = exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w)
            ((z.1, 0) + (0, z.2)) := by
              congr
              ext <;> simp
      _ = exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (z.1, 0) +
            exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w) (0, z.2) := by
              rw [map_add]
  rw [hsplit]
  exact Submodule.add_mem _ hfst hsnd

/-- Helper for Lemma 10.13.4: after restricting scalars from `B` to `A`, the kernel of the
canonical map from tensor power to exterior power over `B` is generated by the repeated-entry
relations. -/
lemma ker_tensorPowerToExterior_over_B_eq_span_repeated_relations :
    (((lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).restrictScalars A).ker :
      Submodule A (⨂[B]^n M)) =
      (Submodule.span B RepeatedRelationSetOverB).restrictScalars A := by
  have hkerB :
      LinearMap.ker (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M) =
        LinearMap.range
          (exteriorRelationMapOfFamily (R := B) (n := n) (x := fun w : M ↦ w)) := by
    -- Lemma 10.13.3 gives the kernel/range presentation once we observe that the identity family
    -- spans all of `M`.
    simpa [Set.range_id] using
      (generator_exterior_power_ker_eq_range (R := B) (M := M) (I := M)
        (n := n) (x := fun w : M ↦ w)
        (by simpa [Set.range_id] using
          (Submodule.span_univ (R := B) (s := (Set.univ : Set M)))))
  have hB :
      LinearMap.ker (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M) =
        Submodule.span B RepeatedRelationSetOverB := by
    refine le_antisymm ?_ ?_
    · rw [hkerB]
      rintro _ ⟨z, rfl⟩
      exact exteriorRelationMapOfFamily_mem_span_repeated_relations_over_B
        (B := B) (n := n) (M := M) z
    · rw [Submodule.span_le]
      rintro _ ⟨p, m, y, rfl⟩
      exact repeated_relation_mem_exterior_ker_over_B (B := B) (n := n) (M := M) p m y
  -- Restrict scalars on the over-`B` kernel description.
  change
    (LinearMap.ker (lift (ιMulti B n).toMultilinearMap :
      (⨂[B]^n M) →ₗ[B] ⋀[B]^n M)).restrictScalars A =
      (Submodule.span B RepeatedRelationSetOverB).restrictScalars A
  simpa [hB]

/-- Helper for Lemma 10.13.4: each textbook balancing generator already lies in the kernel of the
scalar-restriction comparison from tensor power over `A` to tensor power over `B`. -/
lemma balancing_relation_mem_tensorPowerRestrictScalarsToBase_ker
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y z : M) (b : B) :
    tprod A (insertTwoTensorEntries n p (b • y) z m) -
        tprod A (insertTwoTensorEntries n p y (b • z) m) ∈
      LinearMap.ker (tensorPowerRestrictScalarsToBase A B n M) := by
  -- Evaluate both pure tensors in `⨂[B]^n M`, then move the scalar to the same tensor slot.
  rw [LinearMap.mem_ker, map_sub, tensorPowerRestrictScalarsToBase_tprod,
    tensorPowerRestrictScalarsToBase_tprod,
    tprod_insertTwoTensorEntries_left_smul (B := B),
    tprod_insertTwoTensorEntries_right_smul (B := B)]
  simp

/-- Helper for Lemma 10.13.4: the `A`-span of the balancing generators lies in the comparison
kernel from tensor power over `A` to tensor power over `B`. -/
lemma balancing_relations_span_le_tensorPowerRestrictScalarsToBase_ker :
    Submodule.span A
      BalancingRelationSetOverA ≤
      LinearMap.ker (tensorPowerRestrictScalarsToBase A B n M) := by
  -- It suffices to check the balancing generators themselves.
  rw [Submodule.span_le]
  rintro _ ⟨p, m, y, z, b, rfl⟩
  exact balancing_relation_mem_tensorPowerRestrictScalarsToBase_ker
    (A := A) (B := B) (n := n) (M := M) p m y z b

/-- Helper for Lemma 10.13.4: modulo the balancing relations, a `B`-scalar can be moved from any
tensor slot to a fixed positive-degree slot. -/
lemma balancing_quotient_update_smul_eq_fixed_slot
    (hn : 0 < n) (i0 i : Fin n) (b : B) (m : Fin n → M) :
    let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
    S.mkQ (tprod A (Function.update m i (b • m i))) =
      S.mkQ (tprod A (Function.update m i0 (b • m i0))) := by
  let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
  rcases lt_trichotomy i i0 with hlt | rfl | hgt
  · let p : TensorSlotPair n := ⟨⟨i, i0⟩, hlt⟩
    let m' : Fin (n - 2) → M := deleteTwoTensorEntries (M := M) n p m
    have hm :
        insertTwoTensorEntries n p (m i) (m i0) m' = m := by
      -- Deleting the two distinguished slots and reinserting their original entries recovers `m`.
      simpa [m'] using
        insertTwoTensorEntries_deleteTwoTensorEntries (M := M) n p m
    have hleft :
        Function.update m i (b • m i) =
          insertTwoTensorEntries n p (b • m i) (m i0) m' := by
      -- After the normalization `m = insertTwoTensorEntries ...`, updating the left slot just
      -- replaces the left inserted entry.
      calc
        Function.update m i (b • m i) =
            Function.update (insertTwoTensorEntries n p (m i) (m i0) m') p.1.1 (b • m i) := by
              simpa [p, hm]
        _ = insertTwoTensorEntries n p (b • m i) (m i0) m' := by
              simpa [m'] using
                (insertTwoTensorEntries_update_left (M := M) (n := n) (p := p)
                  (m := m') (y := m i) (y' := b • m i) (z := m i0))
    have hright :
        Function.update m i0 (b • m i0) =
          insertTwoTensorEntries n p (m i) (b • m i0) m' := by
      -- The same normalization identifies the right-slot update with replacing the right
      -- inserted entry.
      calc
        Function.update m i0 (b • m i0) =
            Function.update (insertTwoTensorEntries n p (m i) (m i0) m') p.1.2 (b • m i0) := by
              simpa [p, hm]
        _ = insertTwoTensorEntries n p (m i) (b • m i0) m' := by
              simpa [m'] using
                (insertTwoTensorEntries_update_right (M := M) (n := n) (p := p)
                  (m := m') (y := m i) (z := m i0) (z' := b • m i0))
    have hrel :
        tprod A (Function.update m i (b • m i)) -
            tprod A (Function.update m i0 (b • m i0)) ∈ S := by
      -- The two normalized tensors differ by one textbook balancing generator.
      rw [hleft, hright]
      exact Submodule.subset_span ⟨p, m', m i, m i0, b, rfl⟩
    exact (Submodule.Quotient.eq S).2 hrel
  · rfl
  · let p : TensorSlotPair n := ⟨⟨i0, i⟩, hgt⟩
    let m' : Fin (n - 2) → M := deleteTwoTensorEntries (M := M) n p m
    have hm :
        insertTwoTensorEntries n p (m i0) (m i) m' = m := by
      -- Deleting the ordered pair `(i0,i)` and reinserting its entries also recovers `m`.
      simpa [m'] using
        insertTwoTensorEntries_deleteTwoTensorEntries (M := M) n p m
    have hi0 :
        Function.update m i0 (b • m i0) =
          insertTwoTensorEntries n p (b • m i0) (m i) m' := by
      -- In this ordering, the fixed slot `i0` is the left distinguished slot.
      calc
        Function.update m i0 (b • m i0) =
            Function.update (insertTwoTensorEntries n p (m i0) (m i) m') p.1.1 (b • m i0) := by
              simpa [p, hm]
        _ = insertTwoTensorEntries n p (b • m i0) (m i) m' := by
              simpa [m'] using
                (insertTwoTensorEntries_update_left (M := M) (n := n) (p := p)
                  (m := m') (y := m i0) (y' := b • m i0) (z := m i))
    have hi :
        Function.update m i (b • m i) =
          insertTwoTensorEntries n p (m i0) (b • m i) m' := by
      -- The moving slot `i` is now the right distinguished slot.
      calc
        Function.update m i (b • m i) =
            Function.update (insertTwoTensorEntries n p (m i0) (m i) m') p.1.2 (b • m i) := by
              simpa [p, hm]
        _ = insertTwoTensorEntries n p (m i0) (b • m i) m' := by
              simpa [m'] using
                (insertTwoTensorEntries_update_right (M := M) (n := n) (p := p)
                  (m := m') (y := m i0) (z := m i) (z' := b • m i))
    have hrel :
        tprod A (Function.update m i0 (b • m i0)) -
            tprod A (Function.update m i (b • m i)) ∈ S := by
      -- With the ordered pair `(i0,i)`, the balancing generator appears in the opposite
      -- orientation.
      rw [hi0, hi]
      exact Submodule.subset_span ⟨p, m', m i0, m i, b, rfl⟩
    have hrel' :
        tprod A (Function.update m i (b • m i)) -
            tprod A (Function.update m i0 (b • m i0)) ∈ S := by
      -- Negating that generator reverses the quotient equality to the required orientation.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (Submodule.neg_mem S hrel)
    exact (Submodule.Quotient.eq S).2 hrel'

/-- Helper for Lemma 10.13.4: scaling one fixed tensor slot defines an `A`-linear endomorphism of
the tensor power over `A`. -/
noncomputable def fixed_slot_tensor_endomorphism
    (i0 : Fin n) (b : B) : (⨂[A]^n M) →ₗ[A] (⨂[A]^n M) :=
  PiTensorProduct.map
    (Function.update (fun _ ↦ (LinearMap.id : M →ₗ[A] M)) i0 (b • (LinearMap.id : M →ₗ[A] M)))

/-- Helper for Lemma 10.13.4: the fixed-slot endomorphism scales the chosen coordinate of a pure
tensor and leaves every other slot unchanged. -/
@[simp] lemma fixed_slot_tensor_endomorphism_tprod
    (i0 : Fin n) (b : B) (m : Fin n → M) :
    fixed_slot_tensor_endomorphism (A := A) (B := B) (n := n) (M := M) i0 b (tprod A m) =
      tprod A (Function.update m i0 (b • m i0)) := by
  -- `PiTensorProduct.map` computes on pure tensors by applying the chosen linear map in each slot.
  rw [fixed_slot_tensor_endomorphism, PiTensorProduct.map_tprod]
  congr 1
  ext i
  by_cases hi : i = i0
  · subst hi
    simp [Function.update]
  · simp [Function.update, hi]

/-- Helper for Lemma 10.13.4: the fixed-slot endomorphism preserves the balancing-relation span,
so it descends to the balancing quotient. -/
lemma fixed_slot_action_preserves_balancing_span
    (hn : 0 < n) (i0 : Fin n) (b : B) :
    let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
    S ≤ Submodule.comap (fixed_slot_tensor_endomorphism (A := A) (B := B) (n := n) (M := M) i0 b)
      S := by
  -- TODO: source-faithful quotient-step. Move the fixed-slot scalar back to a distinguished slot,
  -- identify the image as a balancing generator again, and conclude by quotient equality.
  sorry

/-- Helper for Lemma 10.13.4: the fixed-slot endomorphism descends to the balancing quotient. -/
noncomputable def fixed_slot_balancing_quotient_endomorphism
    (hn : 0 < n) (i0 : Fin n) (b : B) :
    let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
    (⨂[A]^n M) ⧸ S →ₗ[A] (⨂[A]^n M) ⧸ S :=
  let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
  S.mapQ S
    (fixed_slot_tensor_endomorphism (A := A) (B := B) (n := n) (M := M) i0 b)
    (fixed_slot_action_preserves_balancing_span (A := A) (B := B) (n := n) (M := M) hn i0 b)

/-- Helper for Lemma 10.13.4: on pure tensors, the descended fixed-slot quotient endomorphism is
still given by scaling the chosen tensor slot. -/
@[simp] lemma fixed_slot_balancing_quotient_endomorphism_tprod
    (hn : 0 < n) (i0 : Fin n) (b : B) (m : Fin n → M) :
    let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 b (S.mkQ (tprod A m)) =
      S.mkQ (tprod A (Function.update m i0 (b • m i0))) := by
  let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
  -- The descended map is computed by `Submodule.mapQ_apply` on the chosen pure tensor.
  simp [fixed_slot_balancing_quotient_endomorphism,
    fixed_slot_tensor_endomorphism_tprod]

/-- Helper for Lemma 10.13.4: the balancing relations span the kernel submodule used for the
stage-one quotient comparison. -/
private abbrev balancing_relation_span : Submodule A (⨂[A]^n M) :=
  Submodule.span A BalancingRelationSetOverA

/-- Helper for Lemma 10.13.4: quotienting the tensor power over `A` by the balancing relations
produces the stage-one comparison object. -/
private abbrev balancing_quotient :=
  (⨂[A]^n M) ⧸ balancing_relation_span (A := A) (B := B) (n := n) (M := M)

/-- Helper for Lemma 10.13.4: quotient classes of pure tensors still span the balancing quotient. -/
lemma balancing_quotient_mkQ_tprod_span_top :
    Submodule.span A
      (Set.range
        (fun m : Fin n → M ↦
          (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m))) = ⊤ := by
  -- The quotient map is surjective, so the quotient classes of pure tensors still span.
  calc
    Submodule.span A
        (Set.range
          (fun m : Fin n → M ↦
            (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m))) =
      Submodule.map
        (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
        (Submodule.span A (Set.range (tprod A : (Fin n → M) → ⨂[A]^n M))) := by
          rw [show
              (Set.range
                (fun m : Fin n → M ↦
                  (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
                    (tprod A m))) =
                Set.range
                  ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ ∘
                    (tprod A : (Fin n → M) → ⨂[A]^n M)) by
                rfl]
          rw [Set.range_comp, Submodule.map_span]
    _ = Submodule.map
        (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ ⊤ := by
          rw [PiTensorProduct.span_tprod_eq_top (R := A) (s := fun _ : Fin n ↦ M)]
    _ = ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]

/-- Helper for Lemma 10.13.4: two endomorphisms of the balancing quotient agree once they agree
on all quotient classes of pure tensors. -/
lemma balancing_quotient_endomorphism_ext_on_tprod
    (f g : Module.End A (balancing_quotient (A := A) (B := B) (n := n) (M := M)))
    (hfg : ∀ m : Fin n → M,
      f ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) =
        g ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m))) :
    f = g := by
  -- Quotient classes of pure tensors span the balancing quotient, so agreement there is enough.
  rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
    (balancing_quotient_mkQ_tprod_span_top (A := A) (B := B) (n := n) (M := M))]
  rintro ⟨_, ⟨m, rfl⟩⟩
  exact hfg m

/-- Helper for Lemma 10.13.4: the distinguished-slot quotient endomorphism is the identity at
scalar `1`. -/
lemma balancing_quotient_to_moduleEnd_map_one (hn : 0 < n) :
    let i0 : Fin n := ⟨0, hn⟩
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 1 =
      (1 : Module.End A (balancing_quotient (A := A) (B := B) (n := n) (M := M))) := by
  let i0 : Fin n := ⟨0, hn⟩
  -- Both endomorphisms agree on quotient classes of pure tensors, so spanning closes the proof.
  apply balancing_quotient_endomorphism_ext_on_tprod (A := A) (B := B) (n := n) (M := M)
  intro m
  calc
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 1
        ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m))
      = (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
          (tprod A (Function.update m i0 (1 • m i0))) := by
            simpa [i0] using
              (fixed_slot_balancing_quotient_endomorphism_tprod (A := A) (B := B) (n := n)
                (M := M) hn i0 1 m)
    _ = (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m) := by
          simp
    _ = (1 : Module.End A (balancing_quotient (A := A) (B := B) (n := n) (M := M)))
          ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) := by
          simp

/-- Helper for Lemma 10.13.4: the distinguished-slot quotient endomorphism is zero at scalar
`0`. -/
lemma balancing_quotient_to_moduleEnd_map_zero (hn : 0 < n) :
    let i0 : Fin n := ⟨0, hn⟩
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 0 =
      (0 : Module.End A (balancing_quotient (A := A) (B := B) (n := n) (M := M))) := by
  let i0 : Fin n := ⟨0, hn⟩
  -- A zero tensor slot kills the pure tensor, so the descended endomorphism vanishes on generators.
  apply balancing_quotient_endomorphism_ext_on_tprod (A := A) (B := B) (n := n) (M := M)
  intro m
  have hzero :
      tprod A (Function.update m i0 (0 : M)) = 0 := by
    simpa using
      ((tprod A : MultilinearMap A (fun _ : Fin n ↦ M) (⨂[A]^n M)).map_update_zero m i0)
  calc
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 0
        ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m))
      = (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
          (tprod A (Function.update m i0 (0 : M))) := by
            simpa [i0] using
              (fixed_slot_balancing_quotient_endomorphism_tprod (A := A) (B := B) (n := n)
                (M := M) hn i0 0 m)
    _ = 0 := by
          simp [hzero]
    _ = (0 : Module.End A (balancing_quotient (A := A) (B := B) (n := n) (M := M)))
          ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) := by
          simp

/-- Helper for Lemma 10.13.4: the distinguished-slot quotient endomorphisms are additive in the
scalar parameter. -/
lemma balancing_quotient_to_moduleEnd_map_add (hn : 0 < n) (b c : B) :
    let i0 : Fin n := ⟨0, hn⟩
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 (b + c) =
      fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 b +
      fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 c := by
  let i0 : Fin n := ⟨0, hn⟩
  -- Quotient classes of pure tensors span, so it is enough to compute both sides there.
  apply balancing_quotient_endomorphism_ext_on_tprod (A := A) (B := B) (n := n) (M := M)
  intro m
  calc
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 (b + c)
        ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) =
      (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
        (tprod A (Function.update m i0 ((b + c) • m i0))) := by
          simpa [i0] using
            (fixed_slot_balancing_quotient_endomorphism_tprod (A := A) (B := B) (n := n)
              (M := M) hn i0 (b + c) m)
    _ =
      (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
          (tprod A (Function.update m i0 (b • m i0))) +
        (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
          (tprod A (Function.update m i0 (c • m i0))) := by
          simpa [add_smul, map_add] using
            congrArg
              ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ)
              ((tprod A : MultilinearMap A (fun _ : Fin n ↦ M) (⨂[A]^n M)).map_update_add
                m i0 (b • m i0) (c • m i0))
    _ =
      fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 b
          ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) +
        fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 c
          ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) := by
          rw [fixed_slot_balancing_quotient_endomorphism_tprod,
            fixed_slot_balancing_quotient_endomorphism_tprod]
    _ =
      (fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 b +
        fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 c)
        ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) := by
          simp

/-- Helper for Lemma 10.13.4: the distinguished-slot quotient endomorphisms multiply according to
the scalar parameter. -/
lemma balancing_quotient_to_moduleEnd_map_mul (hn : 0 < n) (b c : B) :
    let i0 : Fin n := ⟨0, hn⟩
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 (b * c) =
      fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 b *
      fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 c := by
  let i0 : Fin n := ⟨0, hn⟩
  -- Quotient classes of pure tensors span, so multiplicativity reduces to the fixed-slot formula.
  apply balancing_quotient_endomorphism_ext_on_tprod (A := A) (B := B) (n := n) (M := M)
  intro m
  calc
    fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 (b * c)
        ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) =
      (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
        (tprod A (Function.update m i0 ((b * c) • m i0))) := by
          simpa [i0] using
            (fixed_slot_balancing_quotient_endomorphism_tprod (A := A) (B := B) (n := n)
              (M := M) hn i0 (b * c) m)
    _ =
      fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 b
          ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
            (tprod A (Function.update m i0 (c • m i0)))) := by
          simpa [i0, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            (fixed_slot_balancing_quotient_endomorphism_tprod (A := A) (B := B) (n := n)
              (M := M) hn i0 b (Function.update m i0 (c • m i0))).symm
    _ =
      fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 b
          (fixed_slot_balancing_quotient_endomorphism
            (A := A) (B := B) (n := n) (M := M) hn i0 c
            ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m))) := by
          simpa [i0] using
            congrArg
              (fixed_slot_balancing_quotient_endomorphism
                (A := A) (B := B) (n := n) (M := M) hn i0 b)
              (fixed_slot_balancing_quotient_endomorphism_tprod (A := A) (B := B) (n := n)
                (M := M) hn i0 c m).symm
    _ =
      (fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 b *
        fixed_slot_balancing_quotient_endomorphism
          (A := A) (B := B) (n := n) (M := M) hn i0 c)
        ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) := by
          rfl

/-- Helper for Lemma 10.13.4: the distinguished-slot quotient endomorphisms package into the ring
action of `B` on the balancing quotient. -/
noncomputable def balancing_quotient_to_moduleEnd (hn : 0 < n) :
    B →+* Module.End A (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
  let i0 : Fin n := ⟨0, hn⟩
  { toFun := fun b ↦
      fixed_slot_balancing_quotient_endomorphism
        (A := A) (B := B) (n := n) (M := M) hn i0 b
    map_one' := balancing_quotient_to_moduleEnd_map_one
      (A := A) (B := B) (n := n) (M := M) hn
    map_mul' := balancing_quotient_to_moduleEnd_map_mul
      (A := A) (B := B) (n := n) (M := M) hn
    map_zero' := balancing_quotient_to_moduleEnd_map_zero
      (A := A) (B := B) (n := n) (M := M) hn
    map_add' := balancing_quotient_to_moduleEnd_map_add
      (A := A) (B := B) (n := n) (M := M) hn }

/-- Helper for Lemma 10.13.4: the balancing quotient inherits a `B`-module structure from the
distinguished-slot ring action. -/
noncomputable instance balancing_quotient_module (hn : 0 < n) :
    Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
  Module.compHom _ (balancing_quotient_to_moduleEnd (A := A) (B := B) (n := n) (M := M) hn)

/-- Helper for Lemma 10.13.4: under the induced `B`-action, scalar multiplication on the
balancing quotient is evaluation of the distinguished-slot endomorphism. -/
lemma balancing_quotient_smul_def (hn : 0 < n) (b : B)
    (q : balancing_quotient (A := A) (B := B) (n := n) (M := M)) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    b • q =
      balancing_quotient_to_moduleEnd (A := A) (B := B) (n := n) (M := M) hn b q := by
  -- `Module.compHom` acts through the endomorphism ring by evaluation.
  rfl

/-- Helper for Lemma 10.13.4: the induced `B`-action on the balancing quotient scales a pure
tensor class by updating the distinguished tensor slot. -/
lemma balancing_quotient_smul_mkQ_tprod (hn : 0 < n) (b : B) (m : Fin n → M) :
    let i0 : Fin n := ⟨0, hn⟩
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    b • ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) =
      (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
        (tprod A (Function.update m i0 (b • m i0))) := by
  -- TODO: rewrite the induced `B`-action through `balancing_quotient_smul_def` and apply the
  -- pure-tensor formula for `fixed_slot_balancing_quotient_endomorphism`.
  sorry

/-- Helper for Lemma 10.13.4: the quotient pure-tensor map is additive in each tensor slot for
the induced `B`-module structure. -/
lemma balancing_quotient_tprod_map_update_add (hn : 0 < n)
    (m : Fin n → M) (i : Fin n) (x y : M) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
        (tprod A (Function.update m i (x + y))) =
      (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
          (tprod A (Function.update m i x)) +
        (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
          (tprod A (Function.update m i y)) := by
  -- Additivity comes directly from multilinearity of `tprod`.
  simpa [map_add] using
    congrArg
      ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ)
      ((tprod A : MultilinearMap A (fun _ : Fin n ↦ M) (⨂[A]^n M)).map_update_add m i x y)

/-- Helper for Lemma 10.13.4: the quotient pure-tensor map is `B`-linear in each tensor slot for
the induced `B`-module structure. -/
lemma balancing_quotient_tprod_map_update_smul (hn : 0 < n)
    (m : Fin n → M) (i : Fin n) (b : B) (x : M) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
        (tprod A (Function.update m i (b • x))) =
      b •
        (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
          (tprod A (Function.update m i x)) := by
  -- TODO: source-faithful slot-moving step. Move the scalar to the distinguished slot in the
  -- quotient, then read that distinguished slot as the induced `B`-action.
  sorry

/-- Helper for Lemma 10.13.4: the pure-tensor quotient map is `B`-multilinear once the balancing
quotient is endowed with the induced `B`-module structure. -/
noncomputable def balancing_quotient_tprod (hn : 0 < n) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    MultilinearMap B (fun _ : Fin n ↦ M)
      (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
  -- TODO: package the quotient pure-tensor map as a `B`-multilinear map once the induced
  -- quotient `B`-action is restored.
  sorry

/-- Helper for Lemma 10.13.4: the full displayed family of generators is contained in the target
kernel. This is the easy direction of the main equality. -/
lemma span_relations_le_target_ker :
    Submodule.span A
      {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA} ≤
      (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
        (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker := by
  rw [Submodule.span_le]
  rintro x (⟨p, m, y, rfl⟩ | ⟨p, m, y, z, b, rfl⟩)
  · exact repeated_relation_mem_target_ker (A := A) (B := B) (n := n) (M := M) p m y
  · have hker :
        LinearMap.ker (tensorPowerRestrictScalarsToBase A B n M) ≤
          (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
            (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker := by
      -- The target map factors through `tensorPowerRestrictScalarsToBase`, so the balancing
      -- generators stay in the target kernel.
      intro w hw
      rw [tensorPowerToExterior_factor (A := A) (B := B) (n := n) (M := M), LinearMap.mem_ker]
      simp [LinearMap.mem_ker.mp hw]
    exact hker <|
      balancing_relation_mem_tensorPowerRestrictScalarsToBase_ker
        (A := A) (B := B) (n := n) (M := M) p m y z b

/-- Helper for Lemma 10.13.4: the displayed relation span is the sum of the repeated-entry span
and the balancing-relation span. -/
lemma span_relations_eq_sup :
    Submodule.span A
      {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA} =
      Submodule.span A RepeatedRelationSetOverA ⊔
        Submodule.span A BalancingRelationSetOverA := by
  -- Rewrite the displayed predicate as a union of the two generator families.
  change Submodule.span A (RepeatedRelationSetOverA ∪ BalancingRelationSetOverA) =
    Submodule.span A RepeatedRelationSetOverA ⊔
      Submodule.span A BalancingRelationSetOverA
  rw [Submodule.span_union]

/-- Helper for Lemma 10.13.4: mapping the repeated-entry span across the scalar-restriction
comparison recovers exactly the repeated-entry span over `B`. -/
lemma repeated_relations_span_map_eq_over_B :
    Submodule.map (tensorPowerRestrictScalarsToBase A B n M)
      (Submodule.span A RepeatedRelationSetOverA) =
      Submodule.span A RepeatedRelationSetOverB := by
  -- The comparison map sends each displayed repeated-entry pure tensor to the same family over `B`.
  rw [Submodule.map_span]
  congr with x
  constructor
  · rintro ⟨u, ⟨p, m, y, rfl⟩, rfl⟩
    exact ⟨p, m, y, by simp [tensorPowerRestrictScalarsToBase_tprod]⟩
  · rintro ⟨p, m, y, rfl⟩
    refine ⟨tprod A (insertTwoTensorEntries n p y y m), ?_, ?_⟩
    · exact ⟨p, m, y, rfl⟩
    · simp [tensorPowerRestrictScalarsToBase_tprod]

/-- Helper for Lemma 10.13.4: the balancing-relation span maps to zero under the scalar-restriction
comparison. -/
lemma map_balancing_relations_span_eq_bot :
    Submodule.map (tensorPowerRestrictScalarsToBase A B n M)
      (Submodule.span A BalancingRelationSetOverA) = ⊥ := by
  refine le_antisymm ?_ bot_le
  -- Every balancing generator is already in the comparison kernel, so its image vanishes.
  rw [LinearMap.map_span_le]
  intro x hx
  rw [Submodule.mem_bot]
  exact LinearMap.mem_ker.mp <|
    balancing_relations_span_le_tensorPowerRestrictScalarsToBase_ker
      (A := A) (B := B) (n := n) (M := M) (Submodule.subset_span hx)

/-- Helper for Lemma 10.13.4: in degree `1`, the scalar-restriction comparison identifies with
the identity map on `M` under the singleton tensor-power equivalences. -/
lemma tensorPowerRestrictScalarsToBase_one_subsingleton :
    ((((PiTensorProduct.subsingletonEquiv
          (R := B) (s := fun _ : Fin 1 ↦ M) (0 : Fin 1)).toLinearMap).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B 1 M)) =
      (PiTensorProduct.subsingletonEquiv
        (R := A) (s := fun _ : Fin 1 ↦ M) (0 : Fin 1)).toLinearMap := by
  -- Compare both sides on pure tensors, then extend by tensor-power induction.
  refine LinearMap.ext fun z ↦ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
      -- On a singleton pure tensor, both maps simply recover the unique tensor entry.
      simp [tensorPowerRestrictScalarsToBase_tprod]
  | add x y hx hy =>
      -- The comparison remains stable under addition because all maps here are linear.
      rw [LinearMap.comp_apply, map_add, map_add]
      simpa [LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy

/-- Helper for Lemma 10.13.4: in degree `1`, the scalar-restriction comparison has trivial
kernel. -/
lemma ker_tensorPowerRestrictScalarsToBase_eq_bot_one :
    LinearMap.ker (tensorPowerRestrictScalarsToBase A B 1 M) = ⊥ := by
  -- Identify both degree-one tensor powers with `M` itself and use the comparison computed above.
  refine le_antisymm ?_ bot_le
  intro z hz
  rw [Submodule.mem_bot]
  rw [LinearMap.mem_ker] at hz
  let eA : (⨂[A]^1 M) ≃ₗ[A] M :=
    PiTensorProduct.subsingletonEquiv (R := A) (s := fun _ : Fin 1 ↦ M) (0 : Fin 1)
  let eB : (⨂[B]^1 M) ≃ₗ[B] M :=
    PiTensorProduct.subsingletonEquiv (R := B) (s := fun _ : Fin 1 ↦ M) (0 : Fin 1)
  have hcompz :
      (((eB.toLinearMap).restrictScalars A).comp (tensorPowerRestrictScalarsToBase A B 1 M)) z =
        eA z := by
    -- Evaluate the already proved comparison of the degree-one maps at the chosen tensor.
    simpa [eA, eB] using
      LinearMap.congr_fun
        (tensorPowerRestrictScalarsToBase_one_subsingleton (A := A) (B := B) (M := M)) z
  have hz' : eA z = 0 := by
    -- The kernel hypothesis forces the left-hand side of the comparison to vanish.
    simpa [LinearMap.comp_apply, hz] using hcompz.symm
  exact eA.injective <| by simpa [eA] using hz'

/-- Helper for Lemma 10.13.4: in degree `1`, there are no balancing generators because there is
no ordered pair of distinct tensor slots. -/
lemma span_balancing_relations_eq_bot_one :
    Submodule.span A
      ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y z : M) (b : B),
          x = tprod A (insertTwoTensorEntries 1 p (b • y) z m) -
            tprod A (insertTwoTensorEntries 1 p y (b • z) m)} : Set (⨂[A]^1 M)) = ⊥ := by
  have hempty :
      ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y z : M) (b : B),
          x = tprod A (insertTwoTensorEntries 1 p (b • y) z m) -
            tprod A (insertTwoTensorEntries 1 p y (b • z) m)} : Set (⨂[A]^1 M)) = ∅ := by
    -- A balancing generator needs two distinct tensor slots, but `TensorSlotPair 1` is empty.
    ext x
    simp [TensorSlotPair]
  rw [hempty, Submodule.span_empty]

/-- Helper for Lemma 10.13.4: in degree `1`, there are no repeated-entry generators over `B`
because there is no ordered pair of distinct tensor slots. -/
lemma span_repeated_relations_over_B_eq_bot_one :
    Submodule.span B
      ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y : M),
          x = tprod B (insertTwoTensorEntries 1 p y y m)} : Set (⨂[B]^1 M)) = ⊥ := by
  have hempty :
      ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y : M),
          x = tprod B (insertTwoTensorEntries 1 p y y m)} : Set (⨂[B]^1 M)) = ∅ := by
    -- A repeated-entry generator also needs two distinct tensor slots, so degree `1` has none.
    ext x
    simp [TensorSlotPair]
  rw [hempty, Submodule.span_empty]

/-- Helper for Lemma 10.13.4: in degree `1`, the full displayed relation family is empty, so its
span is trivial. -/
lemma span_relations_eq_bot_one :
    Submodule.span A
      ({x | x ∈
          ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y : M),
              x = tprod A (insertTwoTensorEntries 1 p y y m)} : Set (⨂[A]^1 M)) ∨
            x ∈
              ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y z : M) (b : B),
                  x = tprod A (insertTwoTensorEntries 1 p (b • y) z m) -
                    tprod A (insertTwoTensorEntries 1 p y (b • z) m)} :
                Set (⨂[A]^1 M))}) = ⊥ := by
  have hempty :
      ({x | x ∈
          ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y : M),
              x = tprod A (insertTwoTensorEntries 1 p y y m)} : Set (⨂[A]^1 M)) ∨
            x ∈
              ({x | ∃ (p : TensorSlotPair 1) (m : Fin (1 - 2) → M) (y z : M) (b : B),
                  x = tprod A (insertTwoTensorEntries 1 p (b • y) z m) -
                    tprod A (insertTwoTensorEntries 1 p y (b • z) m)} :
                Set (⨂[A]^1 M))}) = ∅ := by
    -- Both displayed generator families are empty because `TensorSlotPair 1` is empty.
    ext x
    simp [TensorSlotPair]
  rw [hempty, Submodule.span_empty]

/-- Helper for Lemma 10.13.4: the scalar-restriction comparison kernel is exactly the span of the
balancing relations from the source proof. -/
lemma ker_tensorPowerRestrictScalarsToBase_eq_span_balancing_relations (hn : 0 < n) :
    LinearMap.ker (tensorPowerRestrictScalarsToBase A B n M) =
      Submodule.span A BalancingRelationSetOverA := by
  -- TODO: source-faithful stage-one quotient/section argument. Descend
  -- `tensorPowerRestrictScalarsToBase`, build the quotient section from `balancing_quotient_tprod`,
  -- and deduce injectivity from the pure-tensor spanning family.
  sorry

/-- Helper for Lemma 10.13.4: the stage-one quotient comparison from the balancing quotient to the
tensor power over `B`, obtained by descending `tensorPowerRestrictScalarsToBase`. -/
noncomputable def balancing_quotient_to_tensorPowerOverB (hn : 0 < n) :
    balancing_quotient (A := A) (B := B) (n := n) (M := M) →ₗ[A] (⨂[B]^n M) :=
  let Q : Submodule A (⨂[A]^n M) := balancing_relation_span (A := A) (B := B) (n := n) (M := M)
  Q.liftQ (tensorPowerRestrictScalarsToBase A B n M)
    (balancing_relations_span_le_tensorPowerRestrictScalarsToBase_ker
      (A := A) (B := B) (n := n) (M := M))

/-- Helper for Lemma 10.13.4: the stage-one section map from tensor power over `B` back to the
balancing quotient, defined by the quotient pure-tensor multilinear map. -/
noncomputable def tensorPowerOverB_to_balancing_quotient (hn : 0 < n) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    (⨂[B]^n M) →ₗ[B] balancing_quotient (A := A) (B := B) (n := n) (M := M) :=
  let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
    balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
  lift (balancing_quotient_tprod (A := A) (B := B) (n := n) (M := M) hn)

/-- Helper for Lemma 10.13.4: the descended stage-one comparison agrees with the raw comparison on
quotient classes of pure tensors. -/
@[simp] lemma balancing_quotient_to_tensorPowerOverB_mkQ_tprod
    (hn : 0 < n) (m : Fin n → M) :
    balancing_quotient_to_tensorPowerOverB (A := A) (B := B) (n := n) (M := M) hn
      ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m)) =
      tprod B m := by
  -- The descended comparison is the quotient lift of `tensorPowerRestrictScalarsToBase`.
  simp [balancing_quotient_to_tensorPowerOverB, tensorPowerRestrictScalarsToBase_tprod]

/-- Helper for Lemma 10.13.4: the stage-one section sends a pure tensor over `B` to the
corresponding quotient class over `A`. -/
@[simp] lemma tensorPowerOverB_to_balancing_quotient_tprod
    (hn : 0 < n) (m : Fin n → M) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    tensorPowerOverB_to_balancing_quotient (A := A) (B := B) (n := n) (M := M) hn (tprod B m) =
      (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m) := by
  -- TODO: evaluate the lifted quotient multilinear map on pure tensors after the quotient
  -- `B`-module structure is stabilized.
  sorry

/-- Helper for Lemma 10.13.4: the quotient comparison identifies a `B`-scalar multiple of a pure
quotient tensor class with the corresponding scalar multiple of the pure tensor over `B`. -/
lemma balancing_quotient_to_tensorPowerOverB_smul_mkQ_tprod
    (hn : 0 < n) (b : B) (m : Fin n → M) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    balancing_quotient_to_tensorPowerOverB (A := A) (B := B) (n := n) (M := M) hn
      (b • ((balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ (tprod A m))) =
      b • tprod B m := by
  -- TODO: descend the quotient `B`-action to tensor power over `B` via the pure-tensor formulas
  -- for `balancing_quotient_smul_mkQ_tprod` and `balancing_quotient_to_tensorPowerOverB_mkQ_tprod`.
  sorry

/-- Helper for Lemma 10.13.4: composing the stage-one section with
`tensorPowerRestrictScalarsToBase` recovers the raw quotient map `mkQ`. -/
lemma tensorPowerOverB_to_balancing_quotient_comp_tensorPowerRestrictScalarsToBase
    (hn : 0 < n) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    let _ : IsScalarTower A B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      by
        -- TODO: restore the induced scalar tower on the balancing quotient.
        sorry
    let _ : LinearMap.CompatibleSMul (⨂[B]^n M)
        (balancing_quotient (A := A) (B := B) (n := n) (M := M)) A B :=
      by
        -- TODO: reinstall the quotient `CompatibleSMul` witness for the stage-one section map.
        sorry
    ((tensorPowerOverB_to_balancing_quotient (A := A) (B := B) (n := n) (M := M) hn).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B n M) =
      (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ := by
  -- TODO: compare the two `A`-linear maps on pure tensors once
  -- `tensorPowerOverB_to_balancing_quotient_tprod` is restored, then extend by tensor-power induction.
  sorry

/-- Helper for Lemma 10.13.4: descending `tensorPowerRestrictScalarsToBase` and then applying the
quotient map `mkQ` recovers the original comparison map on representatives. -/
lemma balancing_quotient_to_tensorPowerOverB_comp_mkQ (hn : 0 < n) :
    (balancing_quotient_to_tensorPowerOverB (A := A) (B := B) (n := n) (M := M) hn).comp
        (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ =
      tensorPowerRestrictScalarsToBase A B n M := by
  -- TODO: recover the descended comparison from `liftQ_mkQ` once the stage-one quotient package is restored.
  sorry

/-- Helper for Lemma 10.13.4: the stage-one comparison retraction is the identity on tensor power
over `B`. -/
lemma balancing_quotient_to_tensorPowerOverB_comp_tensorPowerOverB_to_balancing_quotient
    (hn : 0 < n) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    let _ : IsScalarTower A B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      by
        -- TODO: restore the induced scalar tower on the balancing quotient.
        sorry
    let _ : LinearMap.CompatibleSMul (⨂[B]^n M)
        (balancing_quotient (A := A) (B := B) (n := n) (M := M)) A B :=
      by
        -- TODO: reinstall the quotient `CompatibleSMul` witness for the stage-one retraction.
        sorry
    (balancing_quotient_to_tensorPowerOverB (A := A) (B := B) (n := n) (M := M) hn).comp
        ((tensorPowerOverB_to_balancing_quotient (A := A) (B := B) (n := n) (M := M) hn).restrictScalars A) =
      LinearMap.id := by
  -- TODO: prove the retraction on pure tensors over `B` after restoring the section/tensor
  -- pure-tensor formulas, then extend by tensor-power induction.
  sorry

/-- Helper for Lemma 10.13.4: the quotient-stage comparison identifies the `mkQ`-image of the
displayed relation span with the balancing-quotient image of the repeated-entry span over `B`. -/
lemma mkQ_map_span_relations_eq_tensorPowerOverB_to_balancing_quotient_map_span_repeated_over_B
    (hn : 0 < n) :
    let _ : Module B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      balancing_quotient_module (A := A) (B := B) (n := n) (M := M) hn
    let _ : IsScalarTower A B (balancing_quotient (A := A) (B := B) (n := n) (M := M)) :=
      by
        -- TODO: restore the induced scalar tower on the balancing quotient.
        sorry
    Submodule.map
        (balancing_relation_span (A := A) (B := B) (n := n) (M := M)).mkQ
        (Submodule.span A
          {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA}) =
      (Submodule.map
          (tensorPowerOverB_to_balancing_quotient
            (A := A) (B := B) (n := n) (M := M) hn)
          (Submodule.span B RepeatedRelationSetOverB)).restrictScalars A := by
  -- Route correction: this is the remaining quotient-stage step from the source proof.
  -- TODO: identify the `mkQ`-image of the displayed relation span with the balancing-quotient
  -- repeated-relation submodule by constructing the quotient repeated-relation map and comparing
  -- its range on pure-tensor generators.
  sorry

/-- Helper for Lemma 10.13.4: the image of the full displayed relation span under the
scalar-restriction comparison is exactly the `A`-span of the repeated-entry generators over `B`;
the balancing generators contribute only the zero image. -/
lemma tensorPowerRestrictScalarsToBase_map_span_relations_eq_span_repeated_over_A :
    Submodule.map (tensorPowerRestrictScalarsToBase A B n M)
      (Submodule.span A
        {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA}) =
      Submodule.span A RepeatedRelationSetOverB := by
  -- Split the source span into repeated and balancing parts, then map each piece separately.
  rw [span_relations_eq_sup (A := A) (B := B) (n := n) (M := M), Submodule.map_sup,
    repeated_relations_span_map_eq_over_B (A := A) (B := B) (n := n) (M := M),
    map_balancing_relations_span_eq_bot (A := A) (B := B) (n := n) (M := M), sup_bot_eq]

/-- Helper for Lemma 10.13.4: the full displayed relation span maps into the restricted
`B`-submodule generated by the repeated-entry tensors. -/
lemma tensorPowerRestrictScalarsToBase_map_span_relations_le_span_repeated_over_B :
    Submodule.map (tensorPowerRestrictScalarsToBase A B n M)
      (Submodule.span A
        {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA}) ≤
      (Submodule.span B RepeatedRelationSetOverB).restrictScalars A := by
  -- The image was computed exactly as the `A`-span of repeated generators, and that always lies
  -- in the restricted `B`-span on the same generating set.
  rw [tensorPowerRestrictScalarsToBase_map_span_relations_eq_span_repeated_over_A
    (A := A) (B := B) (n := n) (M := M)]
  exact Submodule.span_le_restrictScalars A B RepeatedRelationSetOverB

/-- Helper for Lemma 10.13.4: in positive degree, the image of the full displayed relation span is
the restricted `B`-span of the repeated-entry generators. -/
lemma tensorPowerRestrictScalarsToBase_map_target_ker_eq_span_repeated_over_B
    (hn : 0 < n) :
    Submodule.map (tensorPowerRestrictScalarsToBase A B n M)
      ((lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
        (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker) =
      (Submodule.span B RepeatedRelationSetOverB).restrictScalars A := by
  -- Factor the target kernel through the tensor power over `B`, then use surjectivity of the
  -- scalar-restriction comparison to map that comap back onto the over-`B` kernel.
  rw [tensorPowerToExterior_factor (A := A) (B := B) (n := n) (M := M), LinearMap.ker_comp,
    ker_tensorPowerToExterior_over_B_eq_span_repeated_relations (A := A) (B := B) (n := n)
      (M := M)]
  exact Submodule.map_comap_eq_of_surjective
    (tensorPowerRestrictScalarsToBase_surjective (A := A) (B := B) (n := n) (M := M) hn) _

/-- Helper for Lemma 10.13.4: in positive degree, the image of the full displayed relation span is
the restricted `B`-span of the repeated-entry generators. -/
lemma tensorPowerRestrictScalarsToBase_map_span_relations_eq_span_repeated_over_B
    (hn : 0 < n) :
    Submodule.map (tensorPowerRestrictScalarsToBase A B n M)
      (Submodule.span A
        {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA}) =
      (Submodule.span B RepeatedRelationSetOverB).restrictScalars A := by
  -- TODO: after the quotient-stage image comparison is restored, rewrite the factorization
  -- through the balancing quotient and collapse the composite by the stage-one retraction.
  sorry

/-- Helper for Lemma 10.13.4: once the positive-degree comparison kernel is known, the pullback of
the restricted `B`-span of repeated-entry relations is exactly the displayed `A`-span of repeated
and balancing generators. -/
lemma tensorPowerRestrictScalarsToBase_comap_span_repeated_over_B_eq_span_relations
    (hn : 0 < n) :
    Submodule.comap (tensorPowerRestrictScalarsToBase A B n M)
      ((Submodule.span B RepeatedRelationSetOverB).restrictScalars A) =
      Submodule.span A
        {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA} := by
  have hker :
      LinearMap.ker (tensorPowerRestrictScalarsToBase A B n M) ≤
        Submodule.span A
          {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA} := by
    -- The stage-one kernel is exactly the balancing span, and those generators are part of the
    -- full displayed relation family.
    rw [ker_tensorPowerRestrictScalarsToBase_eq_span_balancing_relations
      (A := A) (B := B) (n := n) (M := M) hn]
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span (Or.inr hx)
  -- Pull back the computed image of the full relation span; the kernel condition makes the
  -- standard `comap_map_eq_self` identity apply.
  rw [← tensorPowerRestrictScalarsToBase_map_span_relations_eq_span_repeated_over_B
    (A := A) (B := B) (n := n) (M := M) hn]
  exact Submodule.comap_map_eq_self hker

/-- Helper for Lemma 10.13.4: after factoring through the tensor power over `B`, the target kernel
is the pullback of the corrected over-`B` repeated-relation span. -/
lemma target_ker_eq_comap_span_repeated_over_B :
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
      (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker =
      Submodule.comap (tensorPowerRestrictScalarsToBase A B n M)
        ((Submodule.span B RepeatedRelationSetOverB).restrictScalars A) := by
  -- Rewrite the target map as a composition and then substitute the corrected over-`B` kernel
  -- description.
  rw [tensorPowerToExterior_factor (A := A) (B := B) (n := n) (M := M), LinearMap.ker_comp,
    ker_tensorPowerToExterior_over_B_eq_span_repeated_relations (A := A) (B := B) (n := n)
      (M := M)]

/-- Lemma 10.13.4: for `n > 0`, the kernel of the canonical `A`-linear map from the `n`th tensor
power of `M` over `A` to the `n`th exterior power of `M` over `B` is generated by pure tensors
with two equal entries and by the differences obtained by moving a scalar `b : B` across one chosen
pair of tensor slots. We express these generators using the tensor-slot insertion API from
Lemma 10.13.3. -/
-- Proof sketch: use the standard presentation of `⋀[B]^n M` by alternating relations over `B`,
-- compose it with the universal property of `⨂[A]^n M`, and identify the induced kernel with the
-- `A`-span of the repeated-entry relations and the extra `B`-balancing relations.
lemma ker_tensorPowerToExteriorPower_eq_span_relations (hn : 0 < n) :
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) : (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker =
      Submodule.span A
        {x | x ∈ RepeatedRelationSetOverA ∨ x ∈ BalancingRelationSetOverA} := by
  -- The kernel of the target map is the pullback of the corrected over-`B` repeated-relation
  -- span, and the remaining pullback calculation is isolated in the dedicated comparison lemma.
  rw [target_ker_eq_comap_span_repeated_over_B (A := A) (B := B) (n := n) (M := M)]
  exact tensorPowerRestrictScalarsToBase_comap_span_repeated_over_B_eq_span_relations
    (A := A) (B := B) (n := n) (M := M) hn

end
