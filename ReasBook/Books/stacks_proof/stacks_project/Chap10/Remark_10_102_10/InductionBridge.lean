import stacks_proof.stacks_project.Chap10.Proposition_10_102_9
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import stacks_proof.stacks_project.Chap10.Lemma_10_72_5
import stacks_proof.stacks_project.Chap10.Lemma_10_74_1

-- Theorem-local support for `Remark_10_102_10`.

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open RingTheory
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

namespace FiniteFreeComplex

/-- Helper for Remark 10.102.10: the induction measure is the total positive-degree rank. -/
def positiveRankSum (C : _root_.FiniteFreeComplex R e) : ℕ :=
  ∑ j : Fin e, C.rank j.succ

/-- Helper for Remark 10.102.10: the threshold property for the unit rank-minor ideals of a
bounded finite free complex. -/
def HasThreshold (C : _root_.FiniteFreeComplex R e) : Prop :=
  ∃ j : Fin (e + 1),
    ∀ i : Fin e,
      I(C.diffAt i) = ⊤ ↔ j ≤ i.castSucc

/-- Helper for Remark 10.102.10: in a local ring, if no displayed matrix entry is a unit, then
every displayed entry lies in the maximal ideal. -/
lemma diffEntry_mem_maximal_of_no_unit
    (C : _root_.FiniteFreeComplex R e)
    (hnoUnit :
      ¬ ∃ i : Fin e, ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
          IsUnit (C.diffEntry i a b))
    (i : Fin e) (a : Fin (C.rank i.succ)) (b : Fin (C.rank i.castSucc)) :
    C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R := by
  -- Proof comment: outside the maximal ideal every element is a unit, so the local no-unit
  -- hypothesis forces every displayed entry into `maximalIdeal R`.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  exact hnoUnit ⟨i, a, b, hunit⟩

/-- Helper for Remark 10.102.10: exactness at a positive degree of a chain complex of modules is
the ordinary exactness of the adjacent linear maps. -/
lemma exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  have hsucc : k + 1 + 1 = k + 2 := by
    omega
  have hpred : k + 1 - 1 = k := by
    omega
  -- Proof comment: rewrite `ExactAt` to the concrete three-term row around degree `k + 1`.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  simpa [HomologicalComplex.sc'] using
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (K.sc' (k + 2) (k + 1) k))

/-- Helper for Remark 10.102.10: splitting off a unit entry lowers the total positive-degree
rank by one. -/
lemma positiveRankSum_splitRank_lt_of_unit_entry
    (C C' : _root_.FiniteFreeComplex R e) (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
        IsUnit (C.diffEntry i a b))
    (hsplit : C'.rank = FiniteFreeComplex.splitRank C.rank i) :
    positiveRankSum (R := R) C' < positiveRankSum (R := R) C := by
  obtain ⟨a, b, _⟩ := hunit
  have hi_pos : 0 < C.rank i.succ := by
    -- Proof comment: the chosen row index witnesses that the source rank is positive.
    exact lt_of_le_of_lt (Nat.zero_le a.1) a.2
  -- Proof comment: the split rank agrees away from degree `i + 1`, and drops by one there.
  refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [hsplit, FiniteFreeComplex.splitRank]
    by_cases hji : j = i
    · subst hji
      simp
    · by_cases hcast : j.succ = i.castSucc
      · simp [hji, hcast]
      · simp [hji, hcast]
  · have hpred : C.rank i.succ - 1 < C.rank i.succ := by
      -- Proof comment: the positive source rank loses exactly one basis vector in the split.
      simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hi_pos)
    simpa [hsplit, FiniteFreeComplex.splitRank] using hpred

/-- Helper for Remark 10.102.10: exactness of a biproduct row implies exactness of the first
summand row. -/
lemma exactAt_fst_of_biprod_exactAt
    {K L : ChainComplex (ModuleCat R) ℕ} {j : ℕ}
    (hj : 1 ≤ j)
    (h : (biprod K L).ExactAt j) :
    K.ExactAt j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  rw [hmid] at h ⊢
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      (biprod K L) (k + 2) (k + 1) k (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      K (k + 2) (k + 1) k (by simp) (by simp)]
  intro A x₂ hx₂
  -- Proof comment: insert the cycle into the left summand, use exactness there, and project back.
  have hx₂' :
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k = 0 := by
    have hcomm := (biprod.inl : K ⟶ biprod K L).comm (k + 1) k
    calc
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k =
          x₂ ≫ (K.d (k + 1) k ≫ (biprod.inl : K ⟶ biprod K L).f k) := by
            simpa [Category.assoc] using congrArg (fun m ↦ x₂ ≫ m) hcomm
      _ = (x₂ ≫ K.d (k + 1) k) ≫ (biprod.inl : K ⟶ biprod K L).f k := by
            simp [Category.assoc]
      _ = 0 := by
            simp [hx₂]
  obtain ⟨A', π, hπ, y₁, hy₁⟩ := h (x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1)) hx₂'
  refine ⟨A', π, hπ, y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2), ?_⟩
  calc
    π ≫ x₂ = π ≫ x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simp [Category.assoc]
    _ = y₁ ≫ (biprod K L).d (k + 2) (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simpa [Category.assoc] using congrArg
            (fun m ↦ m ≫ (biprod.fst : biprod K L ⟶ K).f (k + 1)) hy₁
    _ = y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2) ≫ K.d (k + 2) (k + 1) := by
          have hcomm := (biprod.fst : biprod K L ⟶ K).comm (k + 2) (k + 1)
          simpa [Category.assoc] using congrArg (fun m ↦ y₁ ≫ m) hcomm.symm
    _ = (y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2)) ≫ K.d (k + 2) (k + 1) := by
          simp [Category.assoc]

/-- Helper for Remark 10.102.10: exactness in positive degrees descends across a split
`identityDiskComplex` summand. -/
lemma exactInPositiveDegrees_of_biprod_identityDisk
    {C C' : _root_.FiniteFreeComplex R e} {i : Fin e}
    (eiso : C.toChainComplex ≅
      biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    C.ExactInPositiveDegrees → C'.ExactInPositiveDegrees := by
  intro hExact j hj hje
  -- Proof comment: transport exactness to the split model and project to the reduced summand.
  have hbiprod :
      (biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)).ExactAt j := by
    exact (hExact j hj hje).of_iso eiso
  exact exactAt_fst_of_biprod_exactAt (R := R) hj hbiprod
/-- Helper for Remark 10.102.10: a degreewise equivalence of the predicates
`I(C.diffAt i) = ⊤` transports a threshold witness from one finite free complex to another. -/
lemma hasThreshold_of_rankMinorIdeal_eq_top_iff
    {C D : _root_.FiniteFreeComplex R e}
    (hiff : ∀ i : Fin e, I(C.diffAt i) = ⊤ ↔ I(D.diffAt i) = ⊤)
    (hthreshold : HasThreshold (R := R) C) :
    HasThreshold (R := R) D := by
  rcases hthreshold with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro i
  -- Proof comment: reuse the same cutoff index and rewrite the displayed top-ideal predicate
  -- through the supplied degreewise equivalence.
  simpa using (hiff i).symm.trans (hj i)

end FiniteFreeComplex



end
