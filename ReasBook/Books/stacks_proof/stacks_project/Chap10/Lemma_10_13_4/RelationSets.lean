import StacksProject_2024.Chap10.Lemma_10_13_4.TensorComparison
import StacksProject_2024.Chap10.Lemma_10_13_4.TensorSlotInsertion

-- Relation-set and balancing-quotient setup helpers for Lemma 10.13.4.

open scoped TensorProduct
open PiTensorProduct exteriorPower

section

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
variable (n : ℕ) (M : Type) [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M]

local instance relationSetsExteriorPowerModule : Module A (⋀[B]^n M) :=
  Module.compHom _ (algebraMap A B)

local instance relationSetsExteriorPowerIsScalarTower : IsScalarTower A B (⋀[B]^n M) :=
  IsScalarTower.of_compHom A B _

local instance relationSetsTensorPowerOverBaseModule : Module A (⨂[B]^n M) := by
  infer_instance

local instance relationSetsTensorPowerOverBaseIsScalarTower : IsScalarTower A B (⨂[B]^n M) := by
  infer_instance

/-- Helper for Lemma 10.13.4: the scalar-tower actions let us view the canonical `B`-linear map
from tensor power to exterior power as an `A`-linear map. -/
local instance relationSetsTensorPowerToExteriorCompatibleSMul :
    LinearMap.CompatibleSMul (⨂[B]^n M) (⋀[B]^n M) A B where
  map_smul f a x := by
    -- Both `A`-actions are induced through `algebraMap A B`, so `B`-linearity is enough.
    simpa [Algebra.smul_def] using f.map_smul (algebraMap A B a) x

/-- Helper for Lemma 10.13.4: the repeated-entry pure tensors over `A` that appear in the
kernel description. -/
def repeatedRelationSetOverA : Set (⨂[A]^n M) :=
  {x | ∃ (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M),
      x = tprod A (insertTwoTensorEntries n p y y m)}

/-- Helper for Lemma 10.13.4: the repeated-entry pure tensors over `B` that appear after passing
through the scalar-restriction comparison. -/
def repeatedRelationSetOverB : Set (⨂[B]^n M) :=
  {x | ∃ (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M),
      x = tprod B (insertTwoTensorEntries n p y y m)}

/-- Helper for Lemma 10.13.4: the balancing relations obtained by moving a `B`-scalar between two
tensor slots. -/
def balancingRelationSetOverA : Set (⨂[A]^n M) :=
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
        simp [exteriorRelationMapOfFamily]
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
        simp [exteriorRelationMapOfFamily]
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

omit [Module A M] [IsScalarTower A B M] in
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
        (by
          have hrange : Set.range (fun w : M ↦ w) = Set.univ := by
            ext w
            simp
          rw [hrange]
          exact Submodule.span_univ (R := B) (M := M)))
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
  exact congrArg (fun S : Submodule B (⨂[B]^n M) => S.restrictScalars A) hB

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

omit [Algebra A B] [IsScalarTower A B M] in
/-- Helper for Lemma 10.13.4: modulo the balancing relations, a `B`-scalar can be moved from any
tensor slot to a fixed positive-degree slot. -/
lemma balancing_quotient_update_smul_eq_fixed_slot
    (_hn : 0 < n) (i0 i : Fin n) (b : B) (m : Fin n → M) :
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
              simp [p, hm]
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
              simp [p, hm]
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
              simp [p, hm]
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
              simp [p, hm]
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

/-- Helper for Lemma 10.13.4: the scalar-restriction comparison sends the repeated-entry span over
`A` onto the repeated-entry span over `B`. -/
lemma tensorPowerRestrictScalarsToBase_repeated_generator
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M) :
    tensorPowerRestrictScalarsToBase A B n M (tprod A (insertTwoTensorEntries n p y y m)) =
      tprod B (insertTwoTensorEntries n p y y m) := by
  -- The comparison map was defined to preserve pure tensors.
  simp [tensorPowerRestrictScalarsToBase_tprod]

/-- Helper for Lemma 10.13.4: the scalar-restriction comparison sends the repeated-entry span over
`A` into the repeated-entry span over `B`. -/
theorem map_tensorPowerRestrictScalarsToBase_spanRepeated_le :
    Submodule.map (tensorPowerRestrictScalarsToBase A B n M)
        (Submodule.span A RepeatedRelationSetOverA) ≤
      (Submodule.span B RepeatedRelationSetOverB).restrictScalars A := by
  -- It suffices to check the repeated pure-tensor generators.
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro _ ⟨p, m, y, rfl⟩
  have hy :
      tprod B (insertTwoTensorEntries n p y y m) ∈
        Submodule.span B RepeatedRelationSetOverB := by
    exact Submodule.subset_span ⟨p, m, y, rfl⟩
  simpa [tensorPowerRestrictScalarsToBase_repeated_generator
      (A := A) (B := B) (n := n) (M := M) p m y] using hy

/-- Helper for Lemma 10.13.4: the repeated and balancing spans over `A` are contained in the
pullback of the repeated-entry span over `B`. -/
theorem repeated_sup_balancing_le_comap_tensorPowerRestrictScalarsToBase :
    Submodule.span A RepeatedRelationSetOverA ⊔
        Submodule.span A BalancingRelationSetOverA ≤
      Submodule.comap (tensorPowerRestrictScalarsToBase A B n M)
        ((Submodule.span B RepeatedRelationSetOverB).restrictScalars A) := by
  let repeatedA : Submodule A (⨂[A]^n M) := Submodule.span A RepeatedRelationSetOverA
  let S : Submodule A (⨂[A]^n M) := Submodule.span A BalancingRelationSetOverA
  let comparisonMap : (⨂[A]^n M) →ₗ[A] (⨂[B]^n M) := tensorPowerRestrictScalarsToBase A B n M
  have hkerLe :
      S ≤ LinearMap.ker comparisonMap := by
    simpa [S, comparisonMap] using
      balancing_relations_span_le_tensorPowerRestrictScalarsToBase_ker
        (A := A) (B := B) (n := n) (M := M)
  have hmapRepeated :
      Submodule.map comparisonMap repeatedA ≤
        (Submodule.span B RepeatedRelationSetOverB).restrictScalars A := by
    simpa [repeatedA, comparisonMap] using
      map_tensorPowerRestrictScalarsToBase_spanRepeated_le
        (A := A) (B := B) (n := n) (M := M)
  refine sup_le ?_ ?_
  · exact (Submodule.map_le_iff_le_comap).1 hmapRepeated
  · intro x hx
    rw [Submodule.mem_comap]
    have hxker : comparisonMap x = 0 := by
      exact LinearMap.mem_ker.mp (hkerLe hx)
    rw [hxker]
    exact Submodule.zero_mem _

end
