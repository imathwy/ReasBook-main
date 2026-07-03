import Mathlib
import StacksProject_2024.Chap10.Situation_10_102_1
import StacksProject_2024.Chap10.Lemma_10_102_3
import StacksProject_2024.Chap10.Definition_10_102_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open CategoryTheory CategoryTheory.Limits LinearMap

variable {R : Type u} [CommRing R]
variable {e : ℕ}

namespace FiniteFreeComplex

variable (C : _root_.FiniteFreeComplex R e)

private abbrev adjacentLeftIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1, by omega⟩

private abbrev adjacentRightIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1 + 1, by omega⟩

private abbrev adjacentMiddleIndex (i : Fin (e - 1)) : Fin (e + 1) :=
  ⟨i.1 + 1, by omega⟩

/-- Helper for Lemma 10.102.6: the induction measure is the total positive-degree rank. -/
private def positiveRankSum (C : FiniteFreeComplex R e) : ℕ :=
  ∑ j : Fin e, C.rank j.succ

/-- Helper for Lemma 10.102.6: if the total positive-degree rank vanishes, then each positive
displayed rank vanishes. -/
private theorem rank_succ_eq_zero_of_positiveRankSum_eq_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (j : Fin e) :
    C.rank j.succ = 0 := by
  -- The rank in degree `j + 1` is one nonnegative summand in the total positive-degree rank sum.
  have hle : C.rank j.succ ≤ positiveRankSum (R := R) C := by
    simpa [positiveRankSum] using
      (Finset.single_le_sum
        (f := fun k : Fin e ↦ C.rank k.succ)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j))
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Helper for Lemma 10.102.6: an alternating sum and its tail recover the head term. -/
private theorem alternatingSum_cons_add_tail_eq_head (a : ℤ) :
    ∀ l : List ℤ, List.alternatingSum (a :: l) + List.alternatingSum l = a
  | [] => by
      -- With empty tail the alternating sum is just the head term.
      simp [List.alternatingSum]
  | [b] => by
      -- With a singleton tail the two displayed terms cancel directly.
      simp [List.alternatingSum]
  | b :: c :: t => by
      -- Peel off the first cancelling pair and recurse on the shorter tail.
      have ih : List.alternatingSum (c :: t) + List.alternatingSum t = c :=
        alternatingSum_cons_add_tail_eq_head c t
      simp [List.alternatingSum] at ih ⊢
      linarith

/-- Helper for Lemma 10.102.6: consecutive alternating tails add back up to the middle rank. -/
private theorem adjacent_alternatingRank_add_eq_rank (C : _root_.FiniteFreeComplex R e)
    (i : Fin (e - 1)) :
    C.alternatingRank (adjacentLeftIndex i) + C.alternatingRank (adjacentRightIndex i) =
      C.rank (adjacentMiddleIndex i) := by
  let tail : List ℤ :=
    List.ofFn fun k : Fin (e - (i.1 + 1)) ↦
      (C.rank ⟨i.1 + 2 + k.1, by omega⟩ : ℤ)
  have hleft_length : e - i.1 = (e - (i.1 + 1)) + 1 := by
    omega
  have hleft_list :
      List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
        (C.rank (adjacentMiddleIndex i) : ℤ) :: tail := by
    -- Split the left list into its first entry and the remaining tail.
    have hsucc_eq :
        List.ofFn
            (fun k : Fin ((e - (i.1 + 1)) + 1) ↦
              (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
          (C.rank (adjacentMiddleIndex i) : ℤ) ::
            List.ofFn
              (fun k : Fin (e - (i.1 + 1)) ↦
                (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) := by
      rw [List.ofFn_succ]
      simp [adjacentMiddleIndex]
    have htail_eq :
        List.ofFn
            (fun k : Fin (e - (i.1 + 1)) ↦
              (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) = tail := by
      apply congrArg List.ofFn
      funext k
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    calc
      List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) =
          List.ofFn
            (fun k : Fin ((e - (i.1 + 1)) + 1) ↦
              (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ)) := by
            simpa [hleft_length]
      _ = (C.rank (adjacentMiddleIndex i) : ℤ) ::
            List.ofFn
              (fun k : Fin (e - (i.1 + 1)) ↦
                (C.rank ⟨i.1 + 1 + k.succ.1, by omega⟩ : ℤ)) := hsucc_eq
      _ = (C.rank (adjacentMiddleIndex i) : ℤ) :: tail := by
            rw [htail_eq]
  have hleft :
      C.alternatingRank (adjacentLeftIndex i) =
        List.alternatingSum ((C.rank (adjacentMiddleIndex i) : ℤ) :: tail) := by
    -- Rewrite the left alternating tail through the explicit head-tail list identity.
    change
      List.alternatingSum
          (List.ofFn (fun k : Fin (e - i.1) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ))) =
        List.alternatingSum ((C.rank (adjacentMiddleIndex i) : ℤ) :: tail)
    simpa using congrArg List.alternatingSum hleft_list
  have hright :
      C.alternatingRank (adjacentRightIndex i) =
        List.alternatingSum tail := by
    -- The right alternating tail is definitionally the tail list introduced above.
    change
      List.alternatingSum
          (List.ofFn (fun k : Fin (e - (i.1 + 1)) ↦
            (C.rank ⟨i.1 + 2 + k.1, by omega⟩ : ℤ))) =
        List.alternatingSum tail
    rfl
  -- Apply the elementary alternating-sum identity to the head-tail decomposition.
  rw [hleft, hright]
  simpa [tail] using
    alternatingSum_cons_add_tail_eq_head (a := (C.rank (adjacentMiddleIndex i) : ℤ)) tail

/-- Helper for Lemma 10.102.6: a zero standard finite free module must have rank `0` over a
nontrivial ring. -/
private theorem rank_eq_zero_of_isZero_standard_module [Nontrivial R] (n : ℕ)
    (hzero : CategoryTheory.Limits.IsZero (ModuleCat.of R (Fin n → R))) :
    n = 0 := by
  by_contra hn
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  let i : Fin n := ⟨0, hpos⟩
  letI : Subsingleton (Fin n → R) := ModuleCat.subsingleton_of_isZero hzero
  -- Evaluate the unique equality between `Pi.single i 1` and `0` in coordinate `i`.
  have hsingle : (Pi.single i (1 : R) : Fin n → R) = 0 := Subsingleton.elim _ _
  have hone_zero : (1 : R) = 0 := by
    simpa [Pi.single_apply, i] using congrArg (fun f : Fin n → R ↦ f i) hsingle
  exact one_ne_zero hone_zero

/-- Helper for Lemma 10.102.6: if `R^n` is identified with a biproduct `R^a ⊞ R^b`, then the
displayed rank is `n = a + b`. -/
private theorem rank_eq_add_of_iso_biprod_standard_module [Nontrivial R]
    (n a b : ℕ)
    (e : ModuleCat.of R (Fin n → R) ≅
      (ModuleCat.of R (Fin a → R) ⊞ ModuleCat.of R (Fin b → R))) :
    n = a + b := by
  -- Convert the categorical biproduct isomorphism to a linear equivalence with the standard
  -- product model, then apply invariant basis number to compare the finite free ranks.
  let eprod : (Fin n → R) ≃ₗ[R] (Fin a → R) × (Fin b → R) :=
    e.toLinearEquiv.trans (ModuleCat.biprodIsoProd _ _).toLinearEquiv
  let esum : (Fin n → R) ≃ₗ[R] (Fin (a + b) → R) :=
    eprod.trans <|
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).symm.trans <|
        (LinearEquiv.piCongrLeft R (fun _ : Fin a ⊕ Fin b ↦ R) finSumFinEquiv.symm).symm
  exact InvariantBasisNumber.eq_of_fin_equiv esum

/-- Helper for Lemma 10.102.6: every positive exterior power of the zero map vanishes. -/
private theorem exteriorPower_map_zero_eq_zero {m n r : ℕ} (hr : 0 < r) :
    exteriorPower.map r (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = 0 := by
  -- Route correction: prove vanishing on the spanning `ιMulti` generators instead of unfolding
  -- the exterior-power presentation by hand.
  ext v
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
  -- After one exterior factor, the induced alternating family already starts with `0`.
  simp

/-- Helper for Lemma 10.102.6: the zero map has exterior rank `0`. -/
private theorem exteriorRank_zero_eq_zero {m n : ℕ} :
    exteriorRank (0 : (Fin m → R) →ₗ[R] (Fin n → R)) = 0 := by
  classical
  letI :
      DecidablePred
        (fun r ↦ exteriorPower.map r (0 : (Fin m → R) →ₗ[R] (Fin n → R)) ≠ 0) :=
    Classical.decPred _
  -- Positive exterior powers of `0` vanish, so `Nat.findGreatest` can only return `0`.
  unfold LinearMap.exteriorRank
  rw [Nat.findGreatest_eq_zero_iff]
  intro r hr hk
  simp [exteriorPower_map_zero_eq_zero (R := R) (m := m) (n := n) hr]

/-- Helper for Lemma 10.102.6: the rank-minor ideal of the zero map is the unit ideal because the
only `0 × 0` minor is `1`. -/
private theorem rankMinorIdeal_zero_eq_top {m n : ℕ} :
    I((0 : (Fin m → R) →ₗ[R] (Fin n → R))) = ⊤ := by
  -- Unfold to size-`0` minors and use the convention `I₀ = R`.
  rw [LinearMap.rankMinorIdeal, exteriorRank_zero_eq_zero (R := R) (m := m) (n := n)]
  simp [Matrix.minorIdeal]

/-- Helper for Lemma 10.102.6: changing coordinates on the source and target by linear
automorphisms does not change the exterior rank. -/
private theorem exteriorRank_eq_of_conj {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    exteriorRank (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) =
      exteriorRank φ := by
  have hpred :
      (fun r ↦
        exteriorPower.map r
            (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ≠
          0) =
        fun r ↦ exteriorPower.map r φ ≠ 0 := by
    funext r
    apply propext
    constructor
    · intro hconj
      intro hφ
      apply hconj
      -- Expand the conjugated exterior-power map and rewrite the middle factor to `0`.
      calc
        exteriorPower.map r (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) =
            exteriorPower.map r eTarget.toLinearMap ∘ₗ
              exteriorPower.map r φ ∘ₗ exteriorPower.map r eSource.symm.toLinearMap := by
              simp [exteriorPower.map_comp]
        _ = 0 := by
              simp [hφ]
    · intro hφ
      intro hconj
      apply hφ
      have hrecover :
          φ =
            eTarget.symm.toLinearMap.comp
              ((eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)).comp
                eSource.toLinearMap) := by
        -- Cancelling the inverse coordinate changes recovers the original map.
        ext x
        simp
      have hmaprecover :
          exteriorPower.map r φ =
            exteriorPower.map r eTarget.symm.toLinearMap ∘ₗ
              exteriorPower.map r
                (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ∘ₗ
              exteriorPower.map r eSource.toLinearMap := by
        -- Apply the exterior-power functor to the recovered map and expand the compositions.
        have hmap := congrArg (exteriorPower.map r) hrecover
        simpa [exteriorPower.map_comp] using hmap
      -- Compose on the left and right by the inverse coordinate changes to recover `φ`.
      calc
        exteriorPower.map r φ =
            exteriorPower.map r eTarget.symm.toLinearMap ∘ₗ
              exteriorPower.map r
                (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ∘ₗ
              exteriorPower.map r eSource.toLinearMap := hmaprecover
        _ = 0 := by
              simp [hconj]
  -- The search bound `min m n` is unchanged, so `Nat.findGreatest` sees the same predicate.
  unfold LinearMap.exteriorRank
  rw [hpred]

/-- Helper for Lemma 10.102.6: transposing a matrix does not change the fixed-size minor ideal,
because transposed minors have the same determinants. -/
private theorem minorIdeal_transpose_eq {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (r : ℕ) (A : Matrix ι κ R) :
    Matrix.minorIdeal r A.transpose = Matrix.minorIdeal r A := by
  refine le_antisymm ?_ ?_
  · -- Every generator on the transpose side is the transpose of a generator on the original side.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hsub :
        A.transpose.submatrix e₁ e₂ = (A.submatrix e₂ e₁).transpose := by
      ext i j
      rfl
    change Matrix.det (A.transpose.submatrix e₁ e₂) ∈ Matrix.minorIdeal r A
    rw [hsub, Matrix.det_transpose]
    exact Matrix.det_submatrix_mem_minorIdeal r A e₂ e₁
  · -- The same generator-wise transpose argument works in the opposite direction.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hsub :
        A.submatrix e₁ e₂ = (A.transpose.submatrix e₂ e₁).transpose := by
      ext i j
      rfl
    change Matrix.det (A.submatrix e₁ e₂) ∈ Matrix.minorIdeal r A.transpose
    rw [hsub, Matrix.det_transpose]
    exact Matrix.det_submatrix_mem_minorIdeal r A.transpose e₂ e₁

/-- Helper for Lemma 10.102.6: right multiplication by a square matrix does not enlarge a fixed
minor ideal. -/
private theorem minorIdeal_mul_right_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (r : ℕ) (A : Matrix ι κ R) (C : Matrix κ κ R) :
    Matrix.minorIdeal r (A * C) ≤ Matrix.minorIdeal r A := by
  -- Route correction: reduce right multiplication to the proved left-multiplication statement by
  -- transposing, apply the left-hand lemma there, and transpose back.
  have hleft :
      Matrix.minorIdeal r ((A * C).transpose) ≤ Matrix.minorIdeal r A.transpose := by
    simpa [Matrix.transpose_mul] using
      (Matrix.minorIdeal_mul_left_le (R := R) (r := r) C.transpose A.transpose)
  calc
    Matrix.minorIdeal r (A * C) = Matrix.minorIdeal r ((A * C).transpose) := by
      symm
      exact minorIdeal_transpose_eq (r := r) (A := A * C)
    _ ≤ Matrix.minorIdeal r A.transpose := hleft
    _ = Matrix.minorIdeal r A := minorIdeal_transpose_eq (r := r) (A := A)

/-- Helper for Lemma 10.102.6: if all positive displayed ranks vanish, then the displayed
alternating rank is `0`. -/
private theorem alternatingRank_eq_zero_of_positiveRankSum_eq_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (i : Fin e) :
    C.alternatingRank i = 0 := by
  -- Every entry in the alternating tail lies in a positive degree, hence has rank `0`.
  unfold _root_.FiniteFreeComplex.alternatingRank
  change
    List.alternatingSum
        (List.ofFn (fun k : Fin (e - i) ↦ (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ))) = 0
  have hentry :
      ∀ k : Fin (e - i),
        (C.rank ⟨i.1 + 1 + k.1, by omega⟩ : ℤ) = 0 := by
    intro k
    let j : Fin e := ⟨i.1 + k.1, by omega⟩
    have hj : C.rank j.succ = 0 :=
      rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero j
    simpa [j, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      congrArg (fun n : ℕ ↦ (n : ℤ)) hj
  have hzero_list : (List.replicate (e - i) (0 : ℤ)).alternatingSum = 0 := by
    -- The alternating sum of a list of zeros is zero.
    let hzero_replicate : ∀ n : ℕ, (List.replicate n (0 : ℤ)).alternatingSum = 0 :=
      Nat.twoStepInduction
        (by simp [List.alternatingSum])
        (by simp [List.alternatingSum])
        (fun n ih _ ↦ by
          simp [List.replicate, List.alternatingSum, ih])
    simpa using hzero_replicate (e - i)
  simpa [hentry] using hzero_list

/-- Helper for Lemma 10.102.6: if all positive displayed ranks vanish, then every displayed
differential is the zero map because its source module is zero. -/
private theorem diffAt_eq_zero_of_positiveRankSum_eq_zero
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (i : Fin e) :
    C.diffAt i = 0 := by
  have hrank : C.rank i.succ = 0 :=
    rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
  letI : Subsingleton (C.term i.succ) := by
    simpa [FiniteFreeComplex.term, hrank] using (inferInstance : Subsingleton (Fin 0 → R))
  -- With a subsingleton source, every vector is `0`, so the linear map is pointwise zero.
  apply LinearMap.ext
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  simp

/-- Helper for Lemma 10.102.6: at the top displayed differential, the alternating tail has only
one term, so it is exactly the top displayed rank. -/
private theorem alternatingRank_last_eq_rank_top
    (C : FiniteFreeComplex R (e + 1)) :
    C.alternatingRank (Fin.last e) = C.rank ⟨e + 1, by omega⟩ := by
  -- The last alternating tail consists of the single top-degree rank.
  unfold _root_.FiniteFreeComplex.alternatingRank
  simp
  congr

/-- Helper for Lemma 10.102.6: the source descending count is determined by the adjacent-rank
recurrence together with the top boundary value. -/
private theorem alternatingRank_eq_of_profile_recurrence
    (C : FiniteFreeComplex R e)
    (r : Fin e → ℕ)
    (hrec : ∀ j : Fin (e - 1),
      (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
        C.rank (adjacentMiddleIndex j))
    (htop : ∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩)
    (i : Fin e) :
    (r i : ℤ) = C.alternatingRank i := by
  cases e with
  | zero =>
      exact Fin.elim0 i
  | succ e =>
      -- Descend from the top index: both the profile counts and alternating ranks satisfy the
      -- same adjacent recurrence, so equality propagates one degree at a time.
      induction i using Fin.reverseInduction with
      | last =>
          calc
            (r (Fin.last e) : ℤ) = C.rank ⟨e + 1, by omega⟩ := htop (Nat.succ_pos _)
            _ = C.alternatingRank (Fin.last e) := by
                  symm
                  exact alternatingRank_last_eq_rank_top (C := C)
      | cast j ih =>
          -- Route correction: use the source recurrence `r_i + r_{i + 1} = n_i` directly, rather
          -- than the abandoned identity-disk peel.
          have hr :
              (r (Fin.castSucc j) : ℤ) + r j.succ = C.rank (adjacentMiddleIndex j) :=
            hrec j
          have halt :
              C.alternatingRank (Fin.castSucc j) + C.alternatingRank j.succ =
                C.rank (adjacentMiddleIndex j) :=
            adjacent_alternatingRank_add_eq_rank (C := C) j
          linarith

/-- Helper for Lemma 10.102.6: exactness in a positive degree of a chain complex of modules is
exactness of the two consecutive differentials as linear maps. -/
private theorem exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  have hsucc : k + 1 + 1 = k + 2 := by
    omega
  have hpred : k + 1 - 1 = k := by
    omega
  -- Rewrite `ExactAt` through the explicit three-term short complex around `k + 1`.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  -- For `ModuleCat`, categorical exactness is exactly `Function.Exact`.
  simpa [HomologicalComplex.sc'] using
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (K.sc' (k + 2) (k + 1) k))

/-- Helper for Lemma 10.102.6: if the middle term is zero, the corresponding positive-degree row
is exact. -/
private theorem exactAt_of_isZero_middle
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j)
    (hzero : CategoryTheory.Limits.IsZero (K.X j)) :
    K.ExactAt j := by
  -- Rewrite to linear-map exactness, then note that every map into the zero middle term is
  -- automatically surjective.
  rw [exactAt_iff_function_exact (R := R) (K := K) hj]
  have hnext : (K.d j (j - 1)).hom = 0 := by
    simpa using congrArg ModuleCat.Hom.hom (hzero.eq_of_src (K.d j (j - 1)) 0)
  rw [hnext]
  letI : Subsingleton (K.X j) := ModuleCat.subsingleton_of_isZero hzero
  exact (LinearMap.exact_zero_iff_surjective
    (R := R) (P := K.X (j - 1)) ((K.d (j + 1) j).hom)).2 <|
    Function.surjective_to_subsingleton _

/-- Helper for Lemma 10.102.6: the degree-zero single complex is exact in every positive degree. -/
private theorem exactAt_single₀
    (n j : ℕ) (hj : 1 ≤ j) :
    (((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))).ExactAt j) := by
  -- Every positive degree of `single₀` is zero, so the middle term of the row vanishes.
  exact exactAt_of_isZero_middle (R := R)
    (((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R)))) hj
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of R (Fin n → R)) j (by omega))

/-- Helper for Lemma 10.102.6: the standard free module on `Fin (a + b)` identifies with the
binary biproduct of the standard free modules on `Fin a` and `Fin b`. -/
private noncomputable def standard_module_sum_iso_biprod (a b : ℕ) :
    ModuleCat.of R (Fin (a + b) → R) ≅
      (ModuleCat.of R (Fin a → R) ⊞ ModuleCat.of R (Fin b → R)) :=
  ((LinearEquiv.piCongrLeft R (fun _ : Fin a ⊕ Fin b ↦ R) finSumFinEquiv.symm).toModuleIso) ≪≫
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd (ModuleCat.of R (Fin a → R)) (ModuleCat.of R (Fin b → R))).symm

/-- Helper for Lemma 10.102.6: the standard free module on the empty finite set is a zero
object. -/
private theorem standard_zero_module_isZero :
    CategoryTheory.Limits.IsZero (ModuleCat.of R (Fin 0 → R)) := by
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R))

/-- Helper for Lemma 10.102.6: the displayed zero-by-zero biproduct is a zero object. -/
private theorem standard_zero_biprod_isZero :
    CategoryTheory.Limits.IsZero
      ((ModuleCat.of R (Fin 0 → R) ⊞ ModuleCat.of R (Fin 0 → R)) : ModuleCat R) := by
  exact CategoryTheory.Limits.IsZero.of_iso
    (standard_zero_module_isZero (R := R))
    (standard_module_sum_iso_biprod (R := R) 0 0).symm

/-- Helper for Lemma 10.102.6: any zero term can be identified with the standard zero-by-zero
biproduct. -/
private noncomputable def zero_term_iso_standard_biprod {X : ModuleCat R}
    (hzero : CategoryTheory.Limits.IsZero X) :
    X ≅ ((ModuleCat.of R (Fin 0 → R) ⊞ ModuleCat.of R (Fin 0 → R)) : ModuleCat R) :=
  hzero.iso (standard_zero_biprod_isZero (R := R))

/-- Helper for Lemma 10.102.6: a sequence supported in one degree records the basis-count profile
from the source proof. -/
private def supported_rank_sequence (n s : ℕ) : ℕ → ℕ :=
  fun j ↦ if j = s then n else 0

/-- Helper for Lemma 10.102.6: the standard projection shape in the split-basis profile is the
map from the right source summand to the left target summand. -/
private abbrev standard_biprod_projection (r : ℕ → ℕ) (j : ℕ) :
    (ModuleCat.of R (Fin (r (j + 2)) → R) ⊞
        ModuleCat.of R (Fin (r (j + 1)) → R)) ⟶
      (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
        ModuleCat.of R (Fin (r j) → R)) :=
  (biprod.snd : _ ⟶ ModuleCat.of R (Fin (r (j + 1)) → R)) ≫
    (biprod.inl :
      ModuleCat.of R (Fin (r (j + 1)) → R) ⟶
        (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
          ModuleCat.of R (Fin (r j) → R)))

/-- Helper for Lemma 10.102.6: the chain-level split-basis profile used to model a direct sum of
trivial complexes in categorical biproduct coordinates. -/
private structure BiprodProjectionProfile (K : ChainComplex (ModuleCat R) ℕ) where
  r : ℕ → ℕ
  coord :
    ∀ j : ℕ,
      K.X j ≅
        (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
          ModuleCat.of R (Fin (r j) → R))
  differential :
    ∀ j : ℕ,
      (coord (j + 1)).inv ≫ K.d (j + 1) j ≫ (coord j).hom =
        standard_biprod_projection (R := R) r j

/-- Helper for Lemma 10.102.6: in degree `0`, the `single₀` generator identifies with the
supported biproduct coordinate model `0 ⊞ R^n`. -/
private theorem biprodProjectionProfile_single₀_coord_exists
    (n j : ℕ) :
    Nonempty
      ((((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))).X j) ≅
        ((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 1)) → R)) ⊞
          ModuleCat.of R (Fin ((supported_rank_sequence n 0) j) → R))) := by
  by_cases hj : j = 0
  · -- In degree `0`, the supported sequence records `n` basis vectors in the second summand.
    subst hj
    let e₀ : ModuleCat.of R (Fin n → R) ≅ ModuleCat.of R (Fin (0 + n) → R) :=
      (LinearEquiv.piCongrLeft R (fun _ : Fin (0 + n) ↦ R)
        (finCongr (Nat.zero_add n)).symm).toModuleIso
    change Nonempty
      ((ModuleCat.of R (Fin n → R)) ≅
        ((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (0 + 1)) → R)) ⊞
          ModuleCat.of R (Fin ((supported_rank_sequence n 0) 0) → R)))
    refine ⟨?_⟩
    simpa [supported_rank_sequence] using
      (e₀ ≪≫ standard_module_sum_iso_biprod (R := R) 0 n)
  · -- Every positive degree is zero, so its coordinate model is the zero-by-zero biproduct.
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hzeroj : (supported_rank_sequence n 0) j = 0 := by
      simp [supported_rank_sequence, hj]
    refine ⟨?_⟩
    -- Positive degrees of `single₀` are zero, so the chosen coordinate model is the standard
    -- zero biproduct.
    simpa [ChainComplex.single₀, supported_rank_sequence, hzeroj] using
      zero_term_iso_standard_biprod (R := R)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          (ModuleCat.of R (Fin n → R)) j (by omega))

/-- Helper for Lemma 10.102.6: choose the supported coordinate isomorphism for the `single₀`
generator. -/
private noncomputable def biprodProjectionProfile_single₀_coord
    (n j : ℕ) :
    (((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))).X j) ≅
      ((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 1)) → R)) ⊞
        ModuleCat.of R (Fin ((supported_rank_sequence n 0) j) → R)) :=
  Classical.choice (biprodProjectionProfile_single₀_coord_exists (R := R) n j)

/-- Helper for Lemma 10.102.6: every positive-degree source coordinate in the `single₀` profile is
the standard zero biproduct. -/
private theorem biprodProjectionProfile_single₀_source_isZero (n j : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 2)) → R)) ⊞
          ModuleCat.of R (Fin ((supported_rank_sequence n 0) (j + 1)) → R)) :
        ModuleCat R) := by
  -- Both supported counts vanish away from degree `0`, so the source coordinate is the zero
  -- biproduct.
  simpa [supported_rank_sequence] using standard_zero_biprod_isZero (R := R)

/-- Helper for Lemma 10.102.6: the `single₀` profile has the required standard-projection
normal form because every positive-degree source coordinate is zero. -/
private theorem biprodProjectionProfile_single₀_differential
    (n j : ℕ) :
    (biprodProjectionProfile_single₀_coord (R := R) n (j + 1)).inv ≫
        (((ChainComplex.single₀ (ModuleCat R)).obj
              (ModuleCat.of R (Fin n → R))).d (j + 1) j) ≫
        (biprodProjectionProfile_single₀_coord (R := R) n j).hom =
      standard_biprod_projection (R := R) (supported_rank_sequence n 0) j := by
  -- Both composites have zero source, so the source-faithful normal form is forced by
  -- uniqueness of morphisms out of the zero object.
  exact
    (biprodProjectionProfile_single₀_source_isZero (R := R) n j).eq_of_src _ _

/-- Helper for Lemma 10.102.6: package the `single₀` generator with its supported coordinate
profile. -/
private noncomputable def biprodProjectionProfile_single₀ (n : ℕ) :
    BiprodProjectionProfile (R := R)
      ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))) :=
  { r := supported_rank_sequence n 0
    coord := biprodProjectionProfile_single₀_coord (R := R) n
    differential := biprodProjectionProfile_single₀_differential (R := R) n }

/-- Helper for Lemma 10.102.6: the local public model of `identityDiskComplex` with the same
support and differential formulas as in Lemma `10.102.2`. -/
private def local_identityDiskRank {e : ℕ} (i : Fin e) (j : ℕ) : ℕ :=
  if j = i.1 + 1 ∨ j = i.1 then 1 else 0

/-- Helper for Lemma 10.102.6: the matrix of the local identity-disk differential. -/
private def local_identityDiskMatrix {e : ℕ} (i : Fin e) (j : ℕ) :
    Matrix (Fin (local_identityDiskRank i (j + 1)))
      (Fin (local_identityDiskRank i j)) R :=
  fun _ _ ↦ if j = i.1 then 1 else 0

/-- Helper for Lemma 10.102.6: the local identity-disk differential written through the standard
matrix model. -/
private abbrev local_identityDiskDifferential {e : ℕ} (i : Fin e) (j : ℕ) :
    ModuleCat.of R (Fin (local_identityDiskRank i (j + 1)) → R) ⟶
      ModuleCat.of R (Fin (local_identityDiskRank i j) → R) :=
  ModuleCat.ofHom ((local_identityDiskMatrix (R := R) i j).toLinearMapRight')

/-- Helper for Lemma 10.102.6: away from the supported degree, the local identity-disk
differential vanishes. -/
private theorem local_identityDiskDifferential_eq_zero_of_ne {e : ℕ}
    (i : Fin e) {j : ℕ} (hj : j ≠ i.1) :
    local_identityDiskDifferential (R := R) i j =
      (0 :
        ModuleCat.of R (Fin (local_identityDiskRank i (j + 1)) → R) ⟶
          ModuleCat.of R (Fin (local_identityDiskRank i j) → R)) := by
  have hMatrix :
      local_identityDiskMatrix (R := R) i j =
        (0 :
          Matrix (Fin (local_identityDiskRank i (j + 1)))
            (Fin (local_identityDiskRank i j)) R) := by
    ext a b
    simp [local_identityDiskMatrix, hj]
  let M0 :
      Matrix (Fin (local_identityDiskRank i (j + 1)))
        (Fin (local_identityDiskRank i j)) R := 0
  have hLinear :
      M0.toLinearMapRight' =
        (0 :
          (Fin (local_identityDiskRank i (j + 1)) → R) →ₗ[R]
            Fin (local_identityDiskRank i j) → R) := by
    ext x y
    simp [M0]
  rw [local_identityDiskDifferential, hMatrix]
  change ModuleCat.ofHom (M0.toLinearMapRight') = 0
  rw [hLinear]
  rfl

/-- Helper for Lemma 10.102.6: the remaining source-faithful blocker is to extract, from a direct
sum decomposition into trivial complexes, the split-basis profile whose counts satisfy the source
recurrence and whose differentials become standard projections in those coordinates. -/
private theorem exists_standard_projection_profile_of_positiveRankSum_eq_zero
    [Nontrivial R]
    (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0) :
    ∃ r : Fin e → ℕ,
      (∀ j : Fin (e - 1),
        (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
          C.rank (adjacentMiddleIndex j)) ∧
      (∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩) ∧
      (∀ i : Fin e, (exteriorRank (C.diffAt i) : ℤ) = r i) ∧
      (∀ i : Fin e, I(C.diffAt i) = ⊤) := by
  refine ⟨fun _ ↦ 0, ?_, ?_, ?_, ?_⟩
  · intro j
    -- Every positive displayed rank vanishes, so the adjacent middle rank is `0`.
    have hmid :
        C.rank (adjacentMiddleIndex j) = 0 := by
      simpa [adjacentLeftIndex, adjacentMiddleIndex] using
        rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero
          (adjacentLeftIndex j)
    simpa [hmid]
  · intro h
    -- The top displayed rank also vanishes in the zero positive-rank branch.
    have htop :
        C.rank ⟨e, by omega⟩ = 0 := by
      let j : Fin e := ⟨e - 1, by omega⟩
      have hj : C.rank j.succ = 0 :=
        rank_succ_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero j
      have hj' : C.rank ⟨e - 1 + 1, by omega⟩ = 0 := by
        simpa [j] using hj
      have hs : e - 1 + 1 = e := by
        omega
      simpa [hs] using hj'
    simpa [htop]
  · intro i
    -- With zero positive-degree source, every displayed differential is the zero map.
    have hdiff :
        C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, exteriorRank_zero_eq_zero (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)]
  · intro i
    -- The zero differential has unit rank-minor ideal by the size-`0` minor convention.
    have hdiff :
        C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, rankMinorIdeal_zero_eq_top (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)]

/-- Helper for Lemma 10.102.6: the remaining source-faithful blocker is to extract, from a direct
sum decomposition into trivial complexes, the split-basis profile whose counts satisfy the source
recurrence and whose differentials become standard projections in those coordinates. -/
private theorem exists_standard_projection_profile_of_isDirectSumOfTrivialComplexes
    [Nontrivial R]
    (C : FiniteFreeComplex R e)
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex) :
    ∃ r : Fin e → ℕ,
      (∀ j : Fin (e - 1),
        (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
          C.rank (adjacentMiddleIndex j)) ∧
      (∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩) ∧
      (∀ i : Fin e, (exteriorRank (C.diffAt i) : ℤ) = r i) ∧
      (∀ i : Fin e, I(C.diffAt i) = ⊤) := by
  by_cases hzero : positiveRankSum (R := R) C = 0
  · -- The zero positive-rank branch is already complete without using the decomposition.
    exact exists_standard_projection_profile_of_positiveRankSum_eq_zero
      (R := R) (C := C) hzero
  · -- Route correction: the open frontier is now only the genuinely positive-rank decomposition.
    -- The source proof counts basis vectors globally in a split basis coming from `hC`, then
    -- reads each differential as a standard projection.
    have hsingle_exact :
        ∀ n j : ℕ, 1 ≤ j →
          (((ChainComplex.single₀ (ModuleCat R)).obj
              (ModuleCat.of R (Fin n → R))).ExactAt j) :=
      fun n j hj ↦ exactAt_single₀ (R := R) n j hj
    -- The zero branch is handled above; the remaining frontier is the source-faithful
    -- split-basis/profile extraction for the positive-rank disk, identity-disk, biproduct, and
    -- transport steps. The numeric bookkeeping from a degreewise block decomposition back to the
    -- displayed ranks is already isolated in `rank_eq_add_of_iso_biprod_standard_module`.
    -- TODO: recurse on `hC`, construct the single-sequence block profile `C_j ≅ R^{r_{j + 1}} ⊞
    -- R^{r_j}` with differential `(x, y) ↦ (y, 0)` in the positive-rank branch, and then read
    -- off the recurrence, exterior ranks, and unit minors from that profile.
    sorry

-- Proof sketch: identify the complex with a split exact sum of two-term identity complexes. In
-- that model each differential is a projection onto a free summand of rank equal to the relevant
-- alternating sum, adjacent projection ranks add to the rank of the middle term, and the maximal
-- minors include a unit so the associated ideal is the unit ideal.
/-- Lemma 10.102.6: if the bounded finite free complex is isomorphic to a direct sum of trivial
two-term complexes, then each differential has the expected alternating rank formula, adjacent
differential ranks add to the rank of the middle term, and each ideal `I(φ_i)` is the unit ideal.
-/
theorem exteriorRank_diffAt_eq_alternatingRankFormula_of_isDirectSumOfTrivialComplexes
    [Nontrivial R]
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin e) :
    (exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i := by
  by_cases hzero : positiveRankSum (R := R) C = 0
  · -- Base case: every positive-degree term has rank `0`, so both sides are `0`.
    have hdiff : C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    have halt : C.alternatingRank i = 0 :=
      alternatingRank_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, exteriorRank_zero_eq_zero (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc), halt]
    norm_num
  · -- Route correction: use the source split-basis profile rather than the abandoned peel route.
    obtain ⟨r, hrec, htop, hexterior, -⟩ :=
      exists_standard_projection_profile_of_isDirectSumOfTrivialComplexes (C := C) hC
    calc
      (exteriorRank (C.diffAt i) : ℤ) = r i := hexterior i
      _ = C.alternatingRank i :=
        alternatingRank_eq_of_profile_recurrence (C := C) r hrec htop i

/-- In the direct-sum-of-trivial-complexes situation, adjacent differential ranks add up to the
rank of the middle term. The index `i` corresponds to the consecutive differentials
`C_{i + 2} → C_{i + 1} → C_i`. -/
theorem adjacent_differential_exteriorRank_add_eq
    [Nontrivial R]
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin (e - 1)) :
    exteriorRank (C.diffAt (adjacentLeftIndex i)) +
        exteriorRank (C.diffAt (adjacentRightIndex i)) =
      C.rank (adjacentMiddleIndex i) := by
  -- Rewrite both exterior ranks using the main rank formula, then telescope the two alternating
  -- tails to the middle rank.
  have hsum :
      (exteriorRank (C.diffAt (adjacentLeftIndex i)) : ℤ) +
          exteriorRank (C.diffAt (adjacentRightIndex i)) =
        C.rank (adjacentMiddleIndex i) := by
    rw [exteriorRank_diffAt_eq_alternatingRankFormula_of_isDirectSumOfTrivialComplexes
          (C := C) hC (adjacentLeftIndex i)]
    rw [exteriorRank_diffAt_eq_alternatingRankFormula_of_isDirectSumOfTrivialComplexes
          (C := C) hC (adjacentRightIndex i)]
    exact adjacent_alternatingRank_add_eq_rank (C := C) i
  exact_mod_cast hsum

/-- In the direct-sum-of-trivial-complexes situation, the rank-minor ideal of every differential
is the unit ideal. -/
theorem rankMinorIdeal_diffAt_eq_top_of_isDirectSumOfTrivialComplexes
    [Nontrivial R]
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin e) :
    I(C.diffAt i) = ⊤ := by
  by_cases hzero : positiveRankSum (R := R) C = 0
  · -- Base case: the differential is the zero map, whose rank-minor ideal is `⊤`.
    have hdiff : C.diffAt i = 0 :=
      diffAt_eq_zero_of_positiveRankSum_eq_zero (R := R) (C := C) hzero i
    rw [hdiff, rankMinorIdeal_zero_eq_top (R := R) (m := C.rank i.succ) (n := C.rank i.castSucc)]
  · -- Route correction: the same split-basis profile carries the obvious unit minor.
    obtain ⟨-, -, -, -, hminor⟩ :=
      exists_standard_projection_profile_of_isDirectSumOfTrivialComplexes (C := C) hC
    exact hminor i

end FiniteFreeComplex

end
