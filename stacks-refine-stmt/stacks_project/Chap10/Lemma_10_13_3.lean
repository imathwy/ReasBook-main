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
      tprod R (insertTwoTensorEntriesAux p x y m) := sorry

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
    finCongr (castTwoSlotsEq p) p.1.1 < finCongr (castTwoSlotsEq p) p.1.2 := sorry

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
      tprod R (insertTwoTensorEntries n p x y m) := sorry

section FamilyRelations

variable {I : Type v} (n : ℕ) (x : I → M)

local notation "ExteriorRelationSource" =>
  (((TensorSlotPair n × I × I) →₀ ⨂[R]^(n - 2) M) ×
    ((TensorSlotPair n × I) →₀ ⨂[R]^(n - 2) M))

local notation "SymmetricRelationSource" =>
  ((TensorSlotPair n × I × I) →₀ ⨂[R]^(n - 2) M)

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
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := sorry

/-- On pure tensors, the repeated-entry relation attached to a family inserts the same entry into
the two chosen slots. -/
private theorem exteriorRepeatRelationMapOfFamily_apply_tprod
    (p : TensorSlotPair n) (i : I)
    (m : Fin (n - 2) → M) :
    exteriorRepeatRelationMapOfFamily n x (p, i) (tprod R m) =
      tprod R (insertTwoTensorEntries n p (x i) (x i) m) := sorry

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
      exteriorSwapRelationMapOfFamily n x a z := sorry

/-- The exterior relation map restricts on a generator of the second direct-sum factor to the
corresponding repeated-entry relation. -/
private theorem exteriorRelationMapOfFamily_snd_single_apply
    (a : TensorSlotPair n × I) (z : ⨂[R]^(n - 2) M) :
    exteriorRelationMapOfFamily n x (0, Finsupp.single a z) =
      exteriorRepeatRelationMapOfFamily n x a z := sorry

/-- On a pure-tensor generator of the first direct-sum factor, the exterior relation map is the
sum of the two skew-symmetry tensors. This is the explicit left-map formula from
Lemma 10.13.3 (1). -/
theorem exteriorRelationMapOfFamily_fst_single_tprod
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    exteriorRelationMapOfFamily n x
        (Finsupp.single (p, i₁, i₂) (tprod R m), 0) =
      tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) +
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := sorry

/-- On a pure-tensor generator of the second direct-sum factor, the exterior relation map inserts
the same family entry twice. This is the repeated-entry formula from Lemma 10.13.3 (1). -/
theorem exteriorRelationMapOfFamily_snd_single_tprod
    (p : TensorSlotPair n) (i : I)
    (m : Fin (n - 2) → M) :
    exteriorRelationMapOfFamily n x
        (0, Finsupp.single (p, i) (tprod R m)) =
      tprod R (insertTwoTensorEntries n p (x i) (x i) m) := sorry

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
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := sorry

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
      symmetricCommutatorRelationMapOfFamily n x a z := sorry

/-- On a pure-tensor generator, the symmetric relation map is the difference of the two
slot-insertion tensors. This is the explicit left-map formula from Lemma 10.13.3 (2). -/
theorem symmetricRelationMapOfFamily_single_tprod
    (p : TensorSlotPair n) (i₁ i₂ : I)
    (m : Fin (n - 2) → M) :
    symmetricRelationMapOfFamily n x
        (Finsupp.single (p, i₁, i₂) (tprod R m)) =
      tprod R (insertTwoTensorEntries n p (x i₁) (x i₂) m) -
        tprod R (insertTwoTensorEntries n p (x i₂) (x i₁) m) := sorry

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
      LinearMap.range (exteriorRelationMapOfFamily n x) := sorry

/-- Lemma 10.13.3 (1): if `x : I → M` spans `M`, then the canonical quotient map
from `T^n(M)` to `⋀^n M` has kernel generated by the swap and repetition relations built from the
generators `x`; equivalently, these relation tensors form the left map in an exact sequence
ending in `⋀^n M → 0`. -/
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

-- Proof sketch: compare the presented relation map with the canonical quotient defining
-- `SymmetricPower.mk`, and use that the generators `x` span `M` to see that the listed commutator
-- relations already generate the kernel of the quotient map.
/-- Canonical kernel/range form of Stacks Project, Lemma 10.13.3 (2): if
`x : I → M` spans `M`, then the kernel of the canonical quotient map `T^n(M) → Sym[R]^n M` is
the range of the commutator relation map built from the generators `x`. -/
theorem generator_symmetric_power_ker_eq_range (hx : Submodule.span R (Set.range x) = ⊤) :
    LinearMap.ker (SymmetricPower.mk R (Fin n) M) =
      LinearMap.range (symmetricRelationMapOfFamily n x) := sorry

/-- Lemma 10.13.3 (2): if `x : I → M` spans `M`, then the canonical quotient map
from `T^n(M)` to the `n`th symmetric tensor power has kernel generated by the commutator relations
built from the generators `x`; equivalently, these relation tensors form the left map in an exact
sequence ending in `Sym[R]^n M → 0`. -/
theorem generator_symmetric_power_exact_sequence (hx : Submodule.span R (Set.range x) = ⊤) :
    Function.Exact (symmetricRelationMapOfFamily n x)
      (SymmetricPower.mk R (Fin n) M) ∧
    Function.Surjective (SymmetricPower.mk R (Fin n) M) := by
  refine ⟨LinearMap.exact_iff.mpr (generator_symmetric_power_ker_eq_range n x hx), ?_⟩
  exact AddCon.mk'_surjective

end FamilyRelations

end
