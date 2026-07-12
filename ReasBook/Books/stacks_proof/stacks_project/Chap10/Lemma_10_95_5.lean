import Mathlib
import StacksProject_2024.Chap10.Lemma_10_95_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule

universe u v w x

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {I : Type x}

/-- Helper for Lemma 10.95.5: base change of a countably generated submodule is countably
generated. -/
lemma countablyGenerated_baseChange {P : Submodule R M}
    (hP : P.CountablyGenerated) :
    (P.baseChange S).CountablyGenerated := by
  rcases (Submodule.countablyGenerated_iff (P := P)).mp hP with ⟨s, hs, hspan⟩
  -- Rewrite the base change of a span as the span of the pure tensors `1 ⊗ m`.
  refine (Submodule.countablyGenerated_iff (P := P.baseChange S)).2 ?_
  refine ⟨((TensorProduct.mk R S M) 1) '' s, hs.image _, ?_⟩
  rw [← hspan, Submodule.baseChange_span]

/-- Helper for Lemma 10.95.5: a countable supremum of countably generated submodules is still
countably generated. -/
lemma countablyGenerated_iSup_of_countable {α : Sort*} [Countable α]
    (A : α → Submodule R M) (hA : ∀ a, (A a).CountablyGenerated) :
    (⨆ a, A a).CountablyGenerated := by
  let spanning : α → Set M := fun a ↦
    Classical.choose ((Submodule.countablyGenerated_iff (P := A a)).mp (hA a))
  have hspanning_countable : ∀ a, (spanning a).Countable := by
    intro a
    exact (Classical.choose_spec ((Submodule.countablyGenerated_iff (P := A a)).mp (hA a))).1
  have hspanning_eq : ∀ a, Submodule.span R (spanning a) = A a := by
    intro a
    exact (Classical.choose_spec ((Submodule.countablyGenerated_iff (P := A a)).mp (hA a))).2
  let U : Set M := ⋃ a, spanning a
  have hU_countable : U.Countable := by
    -- A countable union of countable spanning sets stays countable.
    simpa [U] using Set.countable_iUnion hspanning_countable
  -- The supremum is the span of the union of all chosen spanning sets.
  refine (Submodule.countablyGenerated_iff (P := ⨆ a, A a)).2 ⟨U, hU_countable, ?_⟩
  calc
    Submodule.span R U = ⨆ a, Submodule.span R (spanning a) := by
      simpa [U] using (Submodule.span_iUnion (R := R) (s := spanning))
    _ = ⨆ a, A a := by
      simp [hspanning_eq]

/-- Helper for Lemma 10.95.5: the supremum of two countably generated submodules is countably
generated. -/
lemma countablyGenerated_sup {P P' : Submodule R M}
    (hP : P.CountablyGenerated) (hP' : P'.CountablyGenerated) :
    (P ⊔ P').CountablyGenerated := by
  rcases (Submodule.countablyGenerated_iff (P := P)).mp hP with ⟨s, hs, hspan⟩
  rcases (Submodule.countablyGenerated_iff (P := P')).mp hP' with ⟨t, ht, htspan⟩
  -- A union of two countable spanning sets spans the supremum.
  refine (Submodule.countablyGenerated_iff (P := P ⊔ P')).2 ?_
  refine ⟨s ∪ t, hs.union ht, ?_⟩
  calc
    Submodule.span R (s ∪ t) = Submodule.span R s ⊔ Submodule.span R t := by
      rw [Submodule.span_union]
    _ = P ⊔ P' := by
      rw [hspan, htspan]

/-- Helper for Lemma 10.95.5: a countably generated submodule of the internal direct sum is
contained in the sum of a countable subfamily of summands. -/
lemma exists_countable_subfamily_le_of_countablyGenerated
    (Q : I → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q)
    (hQtop : iSup Q = ⊤)
    {P : Submodule S (S ⊗[R] M)}
    (hP : P.CountablyGenerated) :
    ∃ J : Set I, J.Countable ∧ P ≤ ⨆ i : J, Q i.1 := by
  classical
  let hInternal : DirectSum.IsInternal Q :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hQindep hQtop
  let _ : DirectSum.Decomposition Q :=
    DirectSum.IsInternal.chooseDecomposition (ℳ := Q) hInternal
  rcases (Submodule.countablyGenerated_iff (P := P)).mp hP with ⟨t, ht, hspan⟩
  let support : t → Finset I := fun y ↦ (DirectSum.decompose Q y.1).support
  let J : Set I := ⋃ y : t, (support y : Set I)
  have hJ : J.Countable := by
    -- Countably many finite supports still give a countable union of indices.
    let _ : Countable t := ht.to_subtype
    simpa [J, support] using Set.countable_iUnion (fun y : t ↦ Finset.countable_toSet (support y))
  refine ⟨J, hJ, ?_⟩
  rw [← hspan]
  refine Submodule.span_le.2 ?_
  intro y hy
  let y' : t := ⟨y, hy⟩
  -- Expand a generator into finitely many direct-sum components, all indexed inside `J`.
  rw [← DirectSum.sum_support_decompose Q y]
  refine Submodule.sum_mem _ ?_
  intro i hi
  have hiJ : i ∈ J := by
    exact Set.mem_iUnion.2 ⟨y', hi⟩
  exact Submodule.mem_iSup_of_mem ⟨i, hiJ⟩ (DirectSum.decompose Q y i).2

-- Proof sketch: start with `N'_0 = N` and inductively enlarge to countably generated submodules
-- `N'_ℓ` so that each next base change contains every summand `Q i` that meets the current image.
-- Apply Lemma `10.95.4` to the countable sum of those summands at each step, then take the union
-- over the countable iteration to obtain `N'` and the corresponding subset `I'`.
/-- Lemma 10.95.5: if `S ⊗[R] M` is the sum of an independent family of countably generated
`S`-submodules `Q i`, equivalently an internal direct-sum decomposition by countably generated
summands, then every countably generated `R`-submodule `N` of `M` is contained in a countably
generated `R`-submodule whose base change is the sum of a subfamily of the `Q i`. This is the
canonical Lean form of the statement that the image of `N' ⊗_R S → M ⊗_R S` is `⨁_{i ∈ I'} Q i`.
-/
@[stacks 05A8]
theorem exists_countablyGenerated_supermodule_with_baseChange_eq_iSup_subfamily
    (Q : I → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q)
    (hQtop : iSup Q = ⊤)
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    {N : Submodule R M}
    (hN : N.CountablyGenerated) :
    ∃ (N' : Submodule R M) (_ : N ≤ N') (_ : N'.CountablyGenerated) (I' : Set I),
      N'.baseChange S = ⨆ i : I', Q i.1 := by
  classical
  let Stage := { P : Submodule R M // P.CountablyGenerated }
  have hsucc :
      ∀ A : Stage, ∃ B : Stage, A.1 ≤ B.1 ∧
        ∃ J : Set I, J.Countable ∧
          A.1.baseChange S ≤ ⨆ i : J, Q i.1 ∧
          (⨆ i : J, Q i.1) ≤ B.1.baseChange S := by
    intro A
    rcases exists_countable_subfamily_le_of_countablyGenerated
        (Q := Q) hQindep hQtop
        (P := A.1.baseChange S)
        (countablyGenerated_baseChange (R := R) (S := S) (M := M) A.2) with
      ⟨J, hJ, hAJ⟩
    let _ : Countable J := hJ.to_subtype
    have hQJcg : (⨆ i : J, Q i.1).CountablyGenerated := by
      -- The chosen subfamily is countably generated because both the index set and summands are.
      exact countablyGenerated_iSup_of_countable
        (R := S) (M := S ⊗[R] M) (A := fun i : J ↦ Q i.1) (fun i ↦ hQcg i.1)
    rcases exists_countablyGenerated_submodule_whose_baseChange_contains
        (R := R) (S := S) (M := M) (Q := ⨆ i : J, Q i.1) hQJcg with
      ⟨P, hPcg, hJP⟩
    refine ⟨⟨A.1 ⊔ P, countablyGenerated_sup (R := R) (M := M) A.2 hPcg⟩, le_sup_left, ?_⟩
    -- Enlarge by `P` so the next stage base change contains the whole touched subfamily.
    refine ⟨J, hJ, hAJ, ?_⟩
    exact hJP.trans (baseChange_mono (R := R) (S := S) (M := M) le_sup_right)
  let next : Stage → Stage := fun A ↦ Classical.choose (hsucc A)
  have hnext_le : ∀ A : Stage, A.1 ≤ (next A).1 := by
    intro A
    exact (Classical.choose_spec (hsucc A)).1
  have hnext_data :
      ∀ A : Stage,
        ∃ J : Set I, J.Countable ∧
          A.1.baseChange S ≤ ⨆ i : J, Q i.1 ∧
          (⨆ i : J, Q i.1) ≤ (next A).1.baseChange S := by
    intro A
    exact (Classical.choose_spec (hsucc A)).2
  let Jnext : Stage → Set I := fun A ↦ Classical.choose (hnext_data A)
  have hJnext_countable : ∀ A : Stage, (Jnext A).Countable := by
    intro A
    exact (Classical.choose_spec (hnext_data A)).1
  have hJnext_base_le :
      ∀ A : Stage, A.1.baseChange S ≤ ⨆ i : Jnext A, Q i.1 := by
    intro A
    exact (Classical.choose_spec (hnext_data A)).2.1
  have hJnext_fill :
      ∀ A : Stage, (⨆ i : Jnext A, Q i.1) ≤ (next A).1.baseChange S := by
    intro A
    exact (Classical.choose_spec (hnext_data A)).2.2
  let NSeq : ℕ → Stage := Nat.rec ⟨N, hN⟩ fun _ A ↦ next A
  let NSub : ℕ → Submodule R M := fun n ↦ (NSeq n).1
  let JSeq : ℕ → Set I := fun n ↦ Jnext (NSeq n)
  have hNSub_cg : ∀ n, (NSub n).CountablyGenerated := by
    intro n
    exact (NSeq n).2
  have hNSub_succ : ∀ n, NSub n ≤ NSub (n + 1) := by
    intro n
    simpa [NSub, NSeq] using hnext_le (NSeq n)
  have hNSub_mono : Monotone NSub := monotone_nat_of_le_succ hNSub_succ
  have hstage_base_le : ∀ n, (NSub n).baseChange S ≤ ⨆ i : JSeq n, Q i.1 := by
    intro n
    simpa [NSub, JSeq] using hJnext_base_le (NSeq n)
  have hstage_fill : ∀ n, (⨆ i : JSeq n, Q i.1) ≤ (NSub (n + 1)).baseChange S := by
    intro n
    simpa [NSub, JSeq, NSeq] using hJnext_fill (NSeq n)
  let NChain : ℕ →o Submodule R M :=
    { toFun := NSub
      monotone' := hNSub_mono }
  let N' : Submodule R M := ⨆ n, NSub n
  let I' : Set I := ⋃ n, JSeq n
  have hN_le : N ≤ N' := by
    -- The initial submodule is the zeroth stage of the recursive construction.
    simpa [N', NSub, NSeq] using (le_iSup NSub 0)
  have hN'cg : N'.CountablyGenerated := by
    -- Countable generation survives the countable union of the increasing stages.
    exact countablyGenerated_iSup_of_countable (R := R) (M := M) NSub hNSub_cg
  have hbase_le : N'.baseChange S ≤ ⨆ i : I', Q i.1 := by
    rw [Submodule.baseChange_eq_span (A := S)]
    refine Submodule.span_le.2 ?_
    intro z hz
    rcases hz with ⟨m, hm, rfl⟩
    have hm_stage : ∃ n, m ∈ NSub n := by
      simpa [N', NChain] using (Submodule.mem_iSup_of_chain NChain m).mp hm
    rcases hm_stage with ⟨n, hmN⟩
    have hmem_stage : (1 : S) ⊗ₜ[R] m ∈ (NSub n).baseChange S := by
      exact Submodule.tmul_mem_baseChange_of_mem (R := R) (A := S) (1 : S) hmN
    have hmem_subfamily : (1 : S) ⊗ₜ[R] m ∈ ⨆ i : JSeq n, Q i.1 := by
      exact hstage_base_le n hmem_stage
    have hsubfamily_le : (⨆ i : JSeq n, Q i.1) ≤ ⨆ i : I', Q i.1 := by
      refine iSup_le fun i ↦ ?_
      exact le_iSup_of_le ⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩ le_rfl
    exact hsubfamily_le hmem_subfamily
  have hbase_ge : (⨆ i : I', Q i.1) ≤ N'.baseChange S := by
    refine iSup_le ?_
    intro i
    rcases Set.mem_iUnion.1 i.2 with ⟨n, hin⟩
    have hi_subfamily : Q i.1 ≤ ⨆ j : JSeq n, Q j.1 := by
      exact le_iSup_of_le ⟨i.1, hin⟩ le_rfl
    have hi_stage : Q i.1 ≤ (NSub (n + 1)).baseChange S := by
      exact hi_subfamily.trans (hstage_fill n)
    have hstage_to_limit : (NSub (n + 1)).baseChange S ≤ N'.baseChange S := by
      exact baseChange_mono (R := R) (S := S) (M := M) (le_iSup NSub (n + 1))
    exact hi_stage.trans hstage_to_limit
  refine ⟨N', hN_le, hN'cg, I', ?_⟩
  -- The recursive closure is exactly the sum of the accumulated touched summands.
  exact le_antisymm hbase_le hbase_ge

end
