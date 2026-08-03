module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Real.Basic
public import Topology_Munkres_2000.Book.Exercise_19_7.EventuallyZero

import Mathlib.Algebra.FiniteSupport.Basic

public section

namespace RealSequence

/-- The subgroup of real sequences supported at the coordinate `n`. -/
@[expose]
def coordinate (n : ℕ) : AddSubgroup (ℕ → ℝ) :=
  (AddMonoidHom.single (fun _ : ℕ ↦ ℝ) n).range

/-- The eventually-zero real sequences, as an additive subgroup. -/
@[expose]
def finiteSupport : AddSubgroup (ℕ → ℝ) where
  carrier := eventuallyZeroRealSequences
  zero_mem' := mem_eventuallyZeroRealSequences.mpr Function.hasFiniteSupport_zero
  add_mem' := by
    intro x y hx hy
    apply mem_eventuallyZeroRealSequences.mpr
    exact ((mem_eventuallyZeroRealSequences.mp hx).union
      (mem_eventuallyZeroRealSequences.mp hy)).subset (Function.support_add x y)
  neg_mem' := by
    intro x hx
    apply mem_eventuallyZeroRealSequences.mpr
    change (Function.support (-x)).Finite
    rw [Function.support_neg]
    exact mem_eventuallyZeroRealSequences.mp hx

/-- The carrier of `finiteSupport` is the earlier set of eventually-zero real sequences. -/
@[simp]
theorem coe_finiteSupport :
    (finiteSupport : Set (ℕ → ℝ)) = eventuallyZeroRealSequences := rfl

/-- A real sequence belongs to `finiteSupport` exactly when it is eventually zero. -/
@[simp]
theorem mem_finiteSupport {x : ℕ → ℝ} :
    x ∈ finiteSupport ↔ x ∈ eventuallyZeroRealSequences := Iff.rfl

/-- The `n`th coordinate subgroup viewed inside `finiteSupport`. -/
def finiteSupportCoordinate (n : ℕ) : AddSubgroup finiteSupport :=
  (coordinate n).comap finiteSupport.subtype

/- Example 67.1 (1): Real sequences form an abelian group under coordinate-wise addition. -/
#check (inferInstance : AddCommGroup (ℕ → ℝ))

/-- The second assertion of Example 67.1: the `n`th coordinate subgroup is canonically
isomorphic to `ℝ`. -/
@[expose]
def coordinateEquiv (n : ℕ) : ℝ ≃+ coordinate n where
  toFun x := ⟨Pi.single n x, ⟨x, rfl⟩⟩
  invFun x := x.1 n
  left_inv x := by simp
  right_inv x := by
    rcases x with ⟨f, x, rfl⟩
    ext i
    simp [Pi.single_apply]
  map_add' x y := by
    ext i
    simp only [Pi.single_apply]
    split <;> simp_all

@[simp]
theorem coordinateEquiv_apply (n : ℕ) (x : ℝ) :
    (coordinateEquiv n x).1 = Pi.single n x := rfl

@[simp]
theorem coordinateEquiv_symm_apply (n : ℕ) (x : coordinate n) :
    (coordinateEquiv n).symm x = x.1 n := rfl

/-- Helper for Example 67.1: a sequence in one coordinate subgroup vanishes away from that
coordinate. -/
private lemma apply_eq_zero_of_mem_coordinate {f : ℕ → ℝ} {n i : ℕ}
    (hf : f ∈ coordinate n) (hi : i ≠ n) : f i = 0 := by
  -- Unpack the range description and evaluate the resulting coordinate spike.
  rcases hf with ⟨x, rfl⟩
  simp only [AddMonoidHom.single_apply, Pi.single_apply, hi, ↓reduceIte]

/-- Helper for Example 67.1: the function underlying a `Finsupp` lies in the supremum of the
coordinate subgroups. -/
private lemma coeFinsupp_mem_iSup_coordinate (f : ℕ →₀ ℝ) :
    (f : ℕ → ℝ) ∈ ⨆ n, coordinate n := by
  classical
  -- Build the membership from the zero function and one coordinate spike at a time.
  induction f using Finsupp.induction with
  | zero => exact AddSubgroup.zero_mem _
  | single_add n x f _ _ ih =>
      rw [Finsupp.coe_add, Finsupp.single_eq_pi_single]
      exact AddSubgroup.add_mem _ (le_iSup (fun k ↦ coordinate k) n ⟨x, rfl⟩) ih

/-- The third assertion of Example 67.1: the coordinate subgroups generate the finitely supported
sequences. -/
theorem iSup_coordinate : (⨆ n, coordinate n) = finiteSupport := by
  apply le_antisymm
  · -- Every coordinate spike has singleton support, so the generated subgroup is finitely
    -- supported.
    refine iSup_le fun n f hf ↦ ?_
    rcases hf with ⟨x, rfl⟩
    apply mem_eventuallyZeroRealSequences.mpr
    exact (Set.finite_singleton n).subset Pi.support_single_subset
  · -- Replace an eventually-zero function by its canonical `Finsupp` and use the helper above.
    intro f hf
    have hSupport : (Function.support f).Finite :=
      mem_eventuallyZeroRealSequences.mp hf
    simpa only [Finsupp.ofSupportFinite_coe] using
      coeFinsupp_mem_iSup_coordinate (Finsupp.ofSupportFinite f hSupport)

/-- Helper for Example 67.1: the coordinate subgroups inside `finiteSupport` are independent. -/
private lemma iSupIndep_finiteSupportCoordinate :
    iSupIndep finiteSupportCoordinate := by
  classical
  -- Transport to integer submodules, where finite zero-sums characterize independence.
  rw [← iSupIndep_map_orderIso_iff
    (AddSubgroup.toIntSubmodule : AddSubgroup finiteSupport ≃o Submodule ℤ finiteSupport)]
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  -- Evaluating the zero-sum at `i` isolates its `i`th summand, since all others vanish there.
  have hZeroCoe : ((0 : finiteSupport) : ℕ → ℝ) = 0 := rfl
  have hFunctionSum : (∑ j ∈ s, (v j : ℕ → ℝ)) = 0 := by
    simpa only [AddSubmonoidClass.coe_finsetSum, hZeroCoe] using
      congrArg (fun x : finiteSupport ↦ (x : ℕ → ℝ)) hsum
  have hEval : (∑ j ∈ s, (v j : ℕ → ℝ) i) = 0 := by
    simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun hFunctionSum i
  have hDiagonal : (v i : ℕ → ℝ) i = 0 := by
    rw [Finset.sum_eq_single i] at hEval
    · exact hEval
    · intro j hj hji
      exact apply_eq_zero_of_mem_coordinate (hv j hj) hji.symm
    · exact fun hNotMem ↦ (hNotMem hi).elim
  -- The diagonal coordinate is zero by the sum, and every off-diagonal coordinate is zero by
  -- membership in the `i`th coordinate subgroup.
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k
    exact hDiagonal
  · exact apply_eq_zero_of_mem_coordinate (hv i hi) hki

/-- Helper for Example 67.1: inclusion into all real sequences maps each restricted coordinate
subgroup back to the corresponding ambient coordinate subgroup. -/
private lemma map_finiteSupportCoordinate (n : ℕ) :
    (finiteSupportCoordinate n).map finiteSupport.subtype = coordinate n := by
  -- Generation shows that every ambient coordinate subgroup lies in `finiteSupport`.
  simpa only [finiteSupportCoordinate, AddSubgroup.comap_subtype] using
    AddSubgroup.map_addSubgroupOf_eq_of_le
    ((le_iSup (fun k ↦ coordinate k) n).trans_eq iSup_coordinate)

/-- Helper for Example 67.1: the restricted coordinate subgroups generate all of
`finiteSupport`. -/
private lemma iSup_finiteSupportCoordinate :
    (⨆ n, finiteSupportCoordinate n) = ⊤ := by
  -- Membership can be checked after the injective inclusion; after mapping, generation is exactly
  -- `iSup_coordinate`.
  apply top_unique
  intro x _
  apply (AddSubgroup.mem_map_iff_mem finiteSupport.subtype_injective).mp
  rw [AddSubgroup.map_iSup]
  simp_rw [map_finiteSupportCoordinate]
  rw [iSup_coordinate]
  exact x.property

/-- Example 67.1 (4): The finitely supported sequences are the internal direct sum of the
coordinate subgroups. -/
theorem isInternal_coordinate : DirectSum.IsInternal finiteSupportCoordinate := by
  -- Transport independence and generation to integer submodules, then use mathlib's canonical
  -- internal-direct-sum constructor.
  have hIndependent :
      iSupIndep (AddSubgroup.toIntSubmodule ∘ finiteSupportCoordinate) :=
    (iSupIndep_map_orderIso_iff
      (AddSubgroup.toIntSubmodule : AddSubgroup finiteSupport ≃o Submodule ℤ finiteSupport)).mpr
        iSupIndep_finiteSupportCoordinate
  have hSpanning :
      (⨆ n, (AddSubgroup.toIntSubmodule ∘ finiteSupportCoordinate) n) = ⊤ := by
    have hMapped := congrArg
      (AddSubgroup.toIntSubmodule : AddSubgroup finiteSupport → Submodule ℤ finiteSupport)
      iSup_finiteSupportCoordinate
    rw [OrderIso.map_iSup, OrderIso.map_top] at hMapped
    have hFamily : (fun n ↦ (finiteSupportCoordinate n).toIntSubmodule) =
        AddSubgroup.toIntSubmodule ∘ finiteSupportCoordinate := rfl
    rw [← hFamily]
    exact hMapped
  have hInternal :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndependent hSpanning
  have hInternalAdd : DirectSum.IsInternal
      (fun n ↦ ((AddSubgroup.toIntSubmodule ∘ finiteSupportCoordinate) n).toAddSubgroup) :=
    hInternal
  -- Returning each integer submodule to an additive subgroup recovers the original family.
  simpa only [Function.comp_apply, AddSubgroup.toIntSubmodule_toAddSubgroup] using hInternalAdd

end RealSequence
