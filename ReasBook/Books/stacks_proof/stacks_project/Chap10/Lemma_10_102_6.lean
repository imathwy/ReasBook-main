import Mathlib
import StacksProject_2024.Chap10.Situation_10_102_1
import StacksProject_2024.Chap10.Lemma_10_102_2.BiproductBlock
import StacksProject_2024.Chap10.Definition_10_102_5
import StacksProject_2024.Chap10.IsDirectSumOfTrivialComplexes

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
      simp [Nat.add_left_comm, Nat.add_comm]
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
    · intro hconj hφ
      apply hconj
      -- Expand the conjugated exterior-power map and rewrite the middle factor to `0`.
      calc
        exteriorPower.map r (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) =
            exteriorPower.map r eTarget.toLinearMap ∘ₗ
              exteriorPower.map r φ ∘ₗ exteriorPower.map r eSource.symm.toLinearMap := by
              simp [exteriorPower.map_comp]
        _ = 0 := by
              simp [hφ]
    · intro hφ hconj
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
    (r : ℕ) (A : Matrix ι κ R) :
    Matrix.minorIdeal r A.transpose = Matrix.minorIdeal r A := by
  classical
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
    [Fintype κ]
    (r : ℕ) (A : Matrix ι κ R) (C : Matrix κ κ R) :
    Matrix.minorIdeal r (A * C) ≤ Matrix.minorIdeal r A := by
  classical
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

/-- Helper for Chap10 Lemma 10 102 6: changing standard coordinates on the source and target
does not change the rank-minor ideal. -/
private theorem rankMinorIdeal_eq_of_linearEquiv_conj {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    I(eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) = I(φ) := by
  classical
  let f : (Fin m → R) →ₗ[R] (Fin n → R) :=
    eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)
  let r := exteriorRank φ
  let sourceBasis := Pi.basisFun R (Fin m)
  let targetBasis := Pi.basisFun R (Fin n)
  have hrank : exteriorRank f = r := by
    -- First align the fixed minor size with the already-proved exterior-rank conjugation lemma.
    simpa [f, r] using
      exteriorRank_eq_of_conj (R := R) φ eSource eTarget
  have hf_matrix :
      LinearMap.toMatrix sourceBasis targetBasis f =
        LinearMap.toMatrix targetBasis targetBasis eTarget.toLinearMap *
          (LinearMap.toMatrix sourceBasis targetBasis φ *
            LinearMap.toMatrix sourceBasis sourceBasis eSource.symm.toLinearMap) := by
    -- Expand the conjugated linear map as left and right matrix multiplication.
    have hleft_matrix :=
      LinearMap.toMatrix_comp sourceBasis targetBasis targetBasis eTarget.toLinearMap
        (φ.comp eSource.symm.toLinearMap)
    have hright_matrix :=
      LinearMap.toMatrix_comp sourceBasis sourceBasis targetBasis φ eSource.symm.toLinearMap
    calc
      LinearMap.toMatrix sourceBasis targetBasis f =
          LinearMap.toMatrix targetBasis targetBasis eTarget.toLinearMap *
            LinearMap.toMatrix sourceBasis targetBasis (φ.comp eSource.symm.toLinearMap) := by
            simpa [f] using hleft_matrix
      _ = LinearMap.toMatrix targetBasis targetBasis eTarget.toLinearMap *
            (LinearMap.toMatrix sourceBasis targetBasis φ *
              LinearMap.toMatrix sourceBasis sourceBasis eSource.symm.toLinearMap) := by
            rw [hright_matrix]
  have hleft :
      Matrix.minorIdeal r (LinearMap.toMatrix sourceBasis targetBasis f) ≤
        Matrix.minorIdeal r (LinearMap.toMatrix sourceBasis targetBasis φ) := by
    -- Left multiplication and right multiplication by square change-of-basis matrices cannot
    -- enlarge fixed-size minor ideals.
    rw [hf_matrix]
    calc
      Matrix.minorIdeal r
          (LinearMap.toMatrix targetBasis targetBasis eTarget.toLinearMap *
            (LinearMap.toMatrix sourceBasis targetBasis φ *
              LinearMap.toMatrix sourceBasis sourceBasis eSource.symm.toLinearMap)) ≤
          Matrix.minorIdeal r
            (LinearMap.toMatrix sourceBasis targetBasis φ *
              LinearMap.toMatrix sourceBasis sourceBasis eSource.symm.toLinearMap) := by
            exact Matrix.minorIdeal_mul_left_le (R := R) (r := r)
              (LinearMap.toMatrix targetBasis targetBasis eTarget.toLinearMap)
              (LinearMap.toMatrix sourceBasis targetBasis φ *
                LinearMap.toMatrix sourceBasis sourceBasis eSource.symm.toLinearMap)
      _ ≤ Matrix.minorIdeal r (LinearMap.toMatrix sourceBasis targetBasis φ) := by
            exact minorIdeal_mul_right_le (R := R) (r := r)
              (LinearMap.toMatrix sourceBasis targetBasis φ)
              (LinearMap.toMatrix sourceBasis sourceBasis eSource.symm.toLinearMap)
  have hrecover :
      φ = eTarget.symm.toLinearMap.comp (f.comp eSource.toLinearMap) := by
    -- Compose the conjugated map with the inverse coordinate changes to recover `φ`.
    ext x
    simp [f]
  have hφ_matrix :
      LinearMap.toMatrix sourceBasis targetBasis φ =
        LinearMap.toMatrix targetBasis targetBasis eTarget.symm.toLinearMap *
          (LinearMap.toMatrix sourceBasis targetBasis f *
            LinearMap.toMatrix sourceBasis sourceBasis eSource.toLinearMap) := by
    -- The recovered expression gives the reverse minor-ideal inclusion.
    rw [hrecover]
    have hleft_matrix :=
      LinearMap.toMatrix_comp sourceBasis targetBasis targetBasis eTarget.symm.toLinearMap
        (f.comp eSource.toLinearMap)
    have hright_matrix :=
      LinearMap.toMatrix_comp sourceBasis sourceBasis targetBasis f eSource.toLinearMap
    calc
      LinearMap.toMatrix sourceBasis targetBasis
          (eTarget.symm.toLinearMap.comp (f.comp eSource.toLinearMap)) =
          LinearMap.toMatrix targetBasis targetBasis eTarget.symm.toLinearMap *
            LinearMap.toMatrix sourceBasis targetBasis (f.comp eSource.toLinearMap) := by
            simpa using hleft_matrix
      _ = LinearMap.toMatrix targetBasis targetBasis eTarget.symm.toLinearMap *
            (LinearMap.toMatrix sourceBasis targetBasis f *
              LinearMap.toMatrix sourceBasis sourceBasis eSource.toLinearMap) := by
            rw [hright_matrix]
  have hright :
      Matrix.minorIdeal r (LinearMap.toMatrix sourceBasis targetBasis φ) ≤
        Matrix.minorIdeal r (LinearMap.toMatrix sourceBasis targetBasis f) := by
    -- Apply the same two multiplication bounds after recovering `φ` from the conjugated map.
    rw [hφ_matrix]
    calc
      Matrix.minorIdeal r
          (LinearMap.toMatrix targetBasis targetBasis eTarget.symm.toLinearMap *
            (LinearMap.toMatrix sourceBasis targetBasis f *
              LinearMap.toMatrix sourceBasis sourceBasis eSource.toLinearMap)) ≤
          Matrix.minorIdeal r
            (LinearMap.toMatrix sourceBasis targetBasis f *
              LinearMap.toMatrix sourceBasis sourceBasis eSource.toLinearMap) := by
            exact Matrix.minorIdeal_mul_left_le (R := R) (r := r)
              (LinearMap.toMatrix targetBasis targetBasis eTarget.symm.toLinearMap)
              (LinearMap.toMatrix sourceBasis targetBasis f *
                LinearMap.toMatrix sourceBasis sourceBasis eSource.toLinearMap)
      _ ≤ Matrix.minorIdeal r (LinearMap.toMatrix sourceBasis targetBasis f) := by
            exact minorIdeal_mul_right_le (R := R) (r := r)
              (LinearMap.toMatrix sourceBasis targetBasis f)
              (LinearMap.toMatrix sourceBasis sourceBasis eSource.toLinearMap)
  -- Rewrite both `I` terms to the same minor size and compare the two coordinate matrices.
  rw [LinearMap.rankMinorIdeal, LinearMap.rankMinorIdeal, hrank]
  exact le_antisymm hleft hright

/-- Helper for Chap10 Lemma 10 102 6: exterior rank is invariant under source and target linear
equivalences, even when the finite index sizes are syntactically different. -/
private theorem exteriorRank_eq_of_linearEquiv_conj [Nontrivial R] {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R)) :
    exteriorRank (eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) =
      exteriorRank φ := by
  -- Invariant basis number first identifies the syntactic finite ranks; the same-size
  -- coordinate-invariance lemma then applies directly.
  have hm : m' = m := InvariantBasisNumber.eq_of_fin_equiv eSource
  have hn : n = n' := InvariantBasisNumber.eq_of_fin_equiv eTarget
  cases hm
  cases hn
  simpa using
    exteriorRank_eq_of_conj (R := R) φ eSource.symm eTarget

/-- Helper for Chap10 Lemma 10 102 6: the rank-minor ideal is invariant under source and target
linear equivalences, even when the finite index sizes are syntactically different. -/
private theorem rankMinorIdeal_eq_of_linearEquiv_conj' [Nontrivial R] {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R)) :
    I(eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) = I(φ) := by
  -- Reduce the syntactically different dimensions by invariant basis number, then reuse the
  -- same-size minor-ideal invariance.
  have hm : m' = m := InvariantBasisNumber.eq_of_fin_equiv eSource
  have hn : n = n' := InvariantBasisNumber.eq_of_fin_equiv eTarget
  cases hm
  cases hn
  simpa using
    rankMinorIdeal_eq_of_linearEquiv_conj (R := R) φ eSource.symm eTarget

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
        (by simp)
        (by simp)
        (fun n ih _ ↦ by
          simp [List.replicate, ih])
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

/-- Helper for Lemma 10.102.6: if the left summand is zero, projection to the right summand and
inclusion back compose to the identity on the biproduct. -/
private theorem biprod_snd_comp_inr_of_isZero_left {X Y : ModuleCat R}
    (hX : CategoryTheory.Limits.IsZero X) :
    (biprod.snd : X ⊞ Y ⟶ Y) ≫ (biprod.inr : Y ⟶ X ⊞ Y) = 𝟙 (X ⊞ Y) := by
  -- The standard total decomposition loses its left summand because the left projection targets a
  -- zero object.
  have hfst : (biprod.fst : X ⊞ Y ⟶ X) = 0 := hX.eq_of_tgt _ _
  calc
    (biprod.snd : X ⊞ Y ⟶ Y) ≫ (biprod.inr : Y ⟶ X ⊞ Y) =
        (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) +
          (biprod.snd : X ⊞ Y ⟶ Y) ≫ (biprod.inr : Y ⟶ X ⊞ Y) := by
          rw [hfst]
          simp
    _ = 𝟙 (X ⊞ Y) := by
          rw [biprod.total]

/-- Helper for Lemma 10.102.6: the right inclusion followed by the right projection is the
identity. -/
private theorem biprod_inr_comp_snd {X Y : ModuleCat R} :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y := by
  -- This is one of the defining biproduct projection identities.
  simp

/-- Helper for Lemma 10.102.6: if the right summand is zero, projection to the left summand and
inclusion back compose to the identity on the biproduct. -/
private theorem biprod_fst_comp_inl_of_isZero_right {X Y : ModuleCat R}
    (hY : CategoryTheory.Limits.IsZero Y) :
    (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) = 𝟙 (X ⊞ Y) := by
  -- The standard total decomposition loses its right summand because the right projection targets a
  -- zero object.
  have hsnd : (biprod.snd : X ⊞ Y ⟶ Y) = 0 := hY.eq_of_tgt _ _
  calc
    (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) =
        (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) +
          (biprod.snd : X ⊞ Y ⟶ Y) ≫ (biprod.inr : Y ⟶ X ⊞ Y) := by
          rw [hsnd]
          simp
    _ = 𝟙 (X ⊞ Y) := by
          rw [biprod.total]

/-- Helper for Lemma 10.102.6: the left inclusion followed by the left projection is the identity.
-/
private theorem biprod_inl_comp_fst {X Y : ModuleCat R} :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X := by
  -- This is one of the defining biproduct projection identities.
  simp

/-- Helper for Lemma 10.102.6: a biproduct with zero left summand is canonically the right
summand. -/
private noncomputable def biprodRightIsoOfLeftIsZero {X Y : ModuleCat R}
    (hX : CategoryTheory.Limits.IsZero X) :
    X ⊞ Y ≅ Y :=
  { hom := biprod.snd
    inv := biprod.inr
    hom_inv_id := biprod_snd_comp_inr_of_isZero_left (R := R) hX
    inv_hom_id := biprod_inr_comp_snd (R := R) }

/-- Helper for Lemma 10.102.6: a biproduct with zero right summand is canonically the left
summand. -/
private noncomputable def biprodLeftIsoOfRightIsZero {X Y : ModuleCat R}
    (hY : CategoryTheory.Limits.IsZero Y) :
    X ⊞ Y ≅ X :=
  { hom := biprod.fst
    inv := biprod.inl
    hom_inv_id := biprod_fst_comp_inl_of_isZero_right (R := R) hY
    inv_hom_id := biprod_inl_comp_fst (R := R) }

/-- Helper for Lemma 10.102.6: a sequence supported in one degree records the basis-count profile
from the source proof. -/
private def supported_rank_sequence (n s : ℕ) : ℕ → ℕ :=
  fun j ↦ if j = s then n else 0

/-- Helper for Chap10 Lemma 10 102 6: the supported rank sequence takes the displayed value at
its support. -/
private theorem supported_rank_sequence_self (n s : ℕ) :
    supported_rank_sequence n s s = n := by
  -- The defining support test is true at the support index.
  simp [supported_rank_sequence]

/-- Helper for Chap10 Lemma 10 102 6: the supported rank sequence vanishes away from its support.
-/
private theorem supported_rank_sequence_eq_zero_of_ne {n s j : ℕ} (hj : j ≠ s) :
    supported_rank_sequence n s j = 0 := by
  -- Away from the support, the defining support test is false.
  simp [supported_rank_sequence, hj]

/-- Helper for Lemma 10.102.6: the standard projection shape in the split-basis profile is the
map from the right source summand to the left target summand. -/
private noncomputable abbrev standard_biprod_projection (r : ℕ → ℕ) (j : ℕ) :
    (ModuleCat.of R (Fin (r (j + 2)) → R) ⊞
        ModuleCat.of R (Fin (r (j + 1)) → R)) ⟶
      (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
        ModuleCat.of R (Fin (r j) → R)) :=
  (biprod.snd : _ ⟶ ModuleCat.of R (Fin (r (j + 1)) → R)) ≫
    (biprod.inl :
      ModuleCat.of R (Fin (r (j + 1)) → R) ⟶
        (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
          ModuleCat.of R (Fin (r j) → R)))

/-- Helper for Chap10 Lemma 10 102 6: the projection from the right block of `R^(a + b)` to
`R^b` exists with its coordinate formula. -/
private theorem rightProjectionLinear_exists (a b : ℕ) :
    ∃ f : (Fin (a + b) → R) →ₗ[R] (Fin b → R),
      ∀ x k, f x k = x (Fin.natAdd a k) := by
  -- Package the coordinate projection as a linear map; the chosen definition below stays
  -- proof-free.
  let f : (Fin (a + b) → R) →ₗ[R] (Fin b → R) :=
    { toFun := fun x k ↦ x (Fin.natAdd a k)
      map_add' := by
        intro x y
        ext k
        simp
      map_smul' := by
        intro r x
        ext k
        simp }
  exact ⟨f, by intro x k; rfl⟩

/-- Helper for Chap10 Lemma 10 102 6: the projection from `R^(a + b)` onto its right `R^b`
block. -/
private noncomputable def rightProjectionLinear (a b : ℕ) :
    (Fin (a + b) → R) →ₗ[R] (Fin b → R) :=
  Classical.choose (rightProjectionLinear_exists (R := R) a b)

/-- Helper for Chap10 Lemma 10 102 6: coordinate formula for the right-block projection. -/
private theorem rightProjectionLinear_apply (a b : ℕ) (x : Fin (a + b) → R) (k : Fin b) :
    rightProjectionLinear (R := R) a b x k = x (Fin.natAdd a k) :=
  Classical.choose_spec (rightProjectionLinear_exists (R := R) a b) x k

/-- Helper for Chap10 Lemma 10 102 6: the inclusion of `R^b` into the left block of
`R^(b + c)` exists with its coordinate formula. -/
private theorem leftInclusionLinear_exists (b c : ℕ) :
    ∃ f : (Fin b → R) →ₗ[R] (Fin (b + c) → R),
      ∀ x k, f x k = if h : k.1 < b then x (Fin.castLT k h) else 0 := by
  -- Package extension by zero into the target's first block.
  let f : (Fin b → R) →ₗ[R] (Fin (b + c) → R) :=
    { toFun := fun x k ↦ if h : k.1 < b then x (Fin.castLT k h) else 0
      map_add' := by
        intro x y
        ext k
        by_cases h : k.1 < b <;> simp [h]
      map_smul' := by
        intro r x
        ext k
        by_cases h : k.1 < b <;> simp [h] }
  exact ⟨f, by intro x k; rfl⟩

/-- Helper for Chap10 Lemma 10 102 6: the inclusion of `R^b` as the left block of
`R^(b + c)`. -/
private noncomputable def leftInclusionLinear (b c : ℕ) :
    (Fin b → R) →ₗ[R] (Fin (b + c) → R) :=
  Classical.choose (leftInclusionLinear_exists (R := R) b c)

/-- Helper for Chap10 Lemma 10 102 6: coordinate formula for the left-block inclusion. -/
private theorem leftInclusionLinear_apply (b c : ℕ) (x : Fin b → R) (k : Fin (b + c)) :
    leftInclusionLinear (R := R) b c x k =
      if h : k.1 < b then x (Fin.castLT k h) else 0 :=
  Classical.choose_spec (leftInclusionLinear_exists (R := R) b c) x k

/-- Helper for Chap10 Lemma 10 102 6: the standard split projection
`R^(a + b) → R^(b + c)` exists with formula `(x, y) ↦ (y, 0)`. -/
private theorem standardProjectionLinear_exists (a b c : ℕ) :
    ∃ f : (Fin (a + b) → R) →ₗ[R] (Fin (b + c) → R),
      ∀ x k, f x k = if h : k.1 < b then x (Fin.natAdd a (Fin.castLT k h)) else 0 := by
  -- Package the block projection in standard coordinates; downstream proofs consume only the
  -- coordinate formula.
  let f : (Fin (a + b) → R) →ₗ[R] (Fin (b + c) → R) :=
    { toFun := fun x k ↦ if h : k.1 < b then x (Fin.natAdd a (Fin.castLT k h)) else 0
      map_add' := by
        intro x y
        ext k
        by_cases h : k.1 < b <;> simp [h]
      map_smul' := by
        intro r x
        ext k
        by_cases h : k.1 < b <;> simp [h] }
  exact ⟨f, by intro x k; rfl⟩

/-- Helper for Chap10 Lemma 10 102 6: the standard split projection
`R^(a + b) → R^(b + c)`. -/
private noncomputable def standardProjectionLinear (a b c : ℕ) :
    (Fin (a + b) → R) →ₗ[R] (Fin (b + c) → R) :=
  Classical.choose (standardProjectionLinear_exists (R := R) a b c)

/-- Helper for Chap10 Lemma 10 102 6: coordinate formula for the standard split projection. -/
private theorem standardProjectionLinear_apply (a b c : ℕ) (x : Fin (a + b) → R)
    (k : Fin (b + c)) :
    standardProjectionLinear (R := R) a b c x k =
      if h : k.1 < b then x (Fin.natAdd a (Fin.castLT k h)) else 0 :=
  Classical.choose_spec (standardProjectionLinear_exists (R := R) a b c) x k

/-- Helper for Chap10 Lemma 10 102 6: the standard split projection factors through the middle
block `R^b`. -/
private theorem standardProjectionLinear_eq_comp (a b c : ℕ) :
    standardProjectionLinear (R := R) a b c =
      (leftInclusionLinear (R := R) b c).comp (rightProjectionLinear (R := R) a b) := by
  -- Compare both maps coordinatewise in the target block decomposition.
  apply LinearMap.ext
  intro x
  ext k
  rw [standardProjectionLinear_apply, LinearMap.comp_apply, leftInclusionLinear_apply]
  by_cases h : k.1 < b <;> simp [h, rightProjectionLinear_apply]

/-- Helper for Chap10 Lemma 10 102 6: the right-block projection is surjective. -/
private theorem rightProjectionLinear_surjective (a b : ℕ) :
    Function.Surjective (rightProjectionLinear (R := R) a b) := by
  -- Extend a vector on `R^b` by zero outside the right block of `R^(a + b)`.
  intro y
  refine ⟨fun k ↦ Fin.addCases (fun _ : Fin a ↦ 0) y k, ?_⟩
  ext k
  rw [rightProjectionLinear_apply]
  simp

/-- Helper for Chap10 Lemma 10 102 6: the projection from `R^(b + c)` onto its left block exists
with its coordinate formula. -/
private theorem leftProjectionLinear_exists (b c : ℕ) :
    ∃ f : (Fin (b + c) → R) →ₗ[R] (Fin b → R),
      ∀ x k, f x k = x (Fin.castAdd c k) := by
  -- Package the left-block projection as a linear map for use as a retraction.
  let f : (Fin (b + c) → R) →ₗ[R] (Fin b → R) :=
    { toFun := fun x k ↦ x (Fin.castAdd c k)
      map_add' := by
        intro x y
        ext k
        simp
      map_smul' := by
        intro r x
        ext k
        simp }
  exact ⟨f, by intro x k; rfl⟩

/-- Helper for Chap10 Lemma 10 102 6: the projection from `R^(b + c)` onto its left block. -/
private noncomputable def leftProjectionLinear (b c : ℕ) :
    (Fin (b + c) → R) →ₗ[R] (Fin b → R) :=
  Classical.choose (leftProjectionLinear_exists (R := R) b c)

/-- Helper for Chap10 Lemma 10 102 6: coordinate formula for the left-block projection. -/
private theorem leftProjectionLinear_apply (b c : ℕ) (x : Fin (b + c) → R) (k : Fin b) :
    leftProjectionLinear (R := R) b c x k = x (Fin.castAdd c k) :=
  Classical.choose_spec (leftProjectionLinear_exists (R := R) b c) x k

/-- Helper for Chap10 Lemma 10 102 6: the left-block inclusion has the left-block projection as
a retraction. -/
private theorem leftInclusionLinear_retraction (b c : ℕ) :
    (leftProjectionLinear (R := R) b c).comp (leftInclusionLinear (R := R) b c) =
      LinearMap.id := by
  -- Projecting the included first block recovers the original vector.
  apply LinearMap.ext
  intro x
  ext k
  rw [LinearMap.comp_apply, leftProjectionLinear_apply, leftInclusionLinear_apply]
  simp

/-- Helper for Chap10 Lemma 10 102 6: exterior powers of the right-block projection vanish above
the size of the block. -/
private theorem exteriorPower_map_rightProjection_eq_zero_of_lt [Nontrivial R]
    {a b r : ℕ} (hbr : b < r) :
    exteriorPower.map r (rightProjectionLinear (R := R) a b) = 0 := by
  -- The target exterior power is finite free of rank `choose b r = 0`, hence is a subsingleton.
  have hfin : Module.finrank R (⋀[R]^r (Fin b → R)) = 0 := by
    rw [exteriorPower.finrank_eq]
    simpa using Nat.choose_eq_zero_of_lt hbr
  haveI : Subsingleton (⋀[R]^r (Fin b → R)) :=
    (Module.finrank_eq_zero_iff_of_free R (⋀[R]^r (Fin b → R))).mp hfin
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- Helper for Chap10 Lemma 10 102 6: exterior powers of the standard split projection vanish
above the middle block rank. -/
private theorem exteriorPower_map_standardProjection_eq_zero_of_lt [Nontrivial R]
    {a b c r : ℕ} (hbr : b < r) :
    exteriorPower.map r (standardProjectionLinear (R := R) a b c) = 0 := by
  -- Factor through `R^b`, where the exterior power already vanishes.
  rw [standardProjectionLinear_eq_comp, exteriorPower.map_comp,
    exteriorPower_map_rightProjection_eq_zero_of_lt (R := R) (a := a) (b := b) hbr]
  apply LinearMap.ext
  intro x
  simp

/-- Helper for Chap10 Lemma 10 102 6: the exterior power in degree `b` of the standard split
projection is nonzero. -/
private theorem exteriorPower_map_standardProjection_ne_zero [Nontrivial R]
    (a b c : ℕ) :
    exteriorPower.map b (standardProjectionLinear (R := R) a b c) ≠ 0 := by
  -- The projection is surjective on `⋀^b` and the inclusion is injective on `⋀^b`; since
  -- `⋀^b R^b` has rank one, the composite cannot be the zero map.
  rw [standardProjectionLinear_eq_comp, exteriorPower.map_comp]
  intro hzero
  have hfin : Module.finrank R (⋀[R]^b (Fin b → R)) = 1 := by
    rw [exteriorPower.finrank_eq]
    simp
  haveI : Nontrivial (⋀[R]^b (Fin b → R)) :=
    Module.nontrivial_of_finrank_pos (R := R) (M := ⋀[R]^b (Fin b → R))
      (by rw [hfin]; norm_num)
  obtain ⟨y, hy⟩ := exists_ne (0 : ⋀[R]^b (Fin b → R))
  obtain ⟨x, hx⟩ :=
    exteriorPower.map_surjective (n := b) (rightProjectionLinear_surjective (R := R) a b) y
  have hinj : Function.Injective (exteriorPower.map b (leftInclusionLinear (R := R) b c)) :=
    exteriorPower.map_injective (n := b) (leftProjectionLinear (R := R) b c)
      (leftInclusionLinear_retraction (R := R) b c)
  have hcomp :
      exteriorPower.map b (leftInclusionLinear (R := R) b c)
          (exteriorPower.map b (rightProjectionLinear (R := R) a b) x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f x) hzero
  have hleft_y_zero :
      exteriorPower.map b (leftInclusionLinear (R := R) b c) y = 0 := by
    simpa [hx] using hcomp
  exact hy (hinj (by simpa using hleft_y_zero))

/-- Helper for Chap10 Lemma 10 102 6: the standard split projection has exterior rank exactly
the middle block rank. -/
private theorem standardProjectionLinear_exteriorRank [Nontrivial R]
    (a b c : ℕ) :
    exteriorRank (standardProjectionLinear (R := R) a b c) = b := by
  classical
  letI :
      DecidablePred
        (fun r ↦ exteriorPower.map r (standardProjectionLinear (R := R) a b c) ≠ 0) :=
    Classical.decPred _
  -- `findGreatest` is forced to be `b`: degree `b` is nonzero and all larger exterior powers
  -- vanish by the factorization through `R^b`.
  unfold LinearMap.exteriorRank
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, ?_, ?_⟩
  · intro _
    exact exteriorPower_map_standardProjection_ne_zero (R := R) a b c
  · intro n hbn _ hn
    exact hn (exteriorPower_map_standardProjection_eq_zero_of_lt (R := R) (a := a) (b := b)
      (c := c) hbn)

/-- Helper for Chap10 Lemma 10 102 6: the identity `b × b` minor is visible in the matrix of the
standard split projection. -/
private theorem standardProjectionLinear_submatrix_eq_one (a b c : ℕ) :
    (LinearMap.toMatrix (Pi.basisFun R (Fin (a + b))) (Pi.basisFun R (Fin (b + c)))
      (standardProjectionLinear (R := R) a b c)).submatrix
        (Fin.castAdd c) (Fin.natAdd a) = 1 := by
  -- Select the first `b` target rows and the right `b` source columns.
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.submatrix_apply, LinearMap.toMatrix_apply]
    simp [standardProjectionLinear_apply]
  · rw [Matrix.submatrix_apply, Matrix.one_apply, LinearMap.toMatrix_apply]
    simp [standardProjectionLinear_apply, hij]

/-- Helper for Chap10 Lemma 10 102 6: the standard split projection has unit rank-minor ideal. -/
private theorem standardProjectionLinear_rankMinorIdeal_eq_top [Nontrivial R]
    (a b c : ℕ) :
    I(standardProjectionLinear (R := R) a b c) = ⊤ := by
  -- Once the exterior rank is `b`, the displayed identity minor contributes `1` to the minor
  -- ideal.
  rw [LinearMap.rankMinorIdeal, standardProjectionLinear_exteriorRank (R := R) a b c]
  apply (Ideal.eq_top_iff_one _).2
  let A := LinearMap.toMatrix (Pi.basisFun R (Fin (a + b))) (Pi.basisFun R (Fin (b + c)))
      (standardProjectionLinear (R := R) a b c)
  have hdet : (A.submatrix (Fin.castAddEmb c) (Fin.natAddEmb a)).det = (1 : R) := by
    have hsub := standardProjectionLinear_submatrix_eq_one (R := R) a b c
    simpa [A, Fin.coe_castAddEmb, Fin.natAddEmb_apply] using congrArg Matrix.det hsub
  rw [← hdet]
  exact Matrix.det_submatrix_mem_minorIdeal b A (Fin.castAddEmb c) (Fin.natAddEmb a)

/-- Helper for Chap10 Lemma 10 102 6: bundled exterior-rank and rank-minor computation for the
standard split projection. -/
private theorem standardProjectionLinear_exteriorRank_rankMinorIdeal [Nontrivial R]
    (a b c : ℕ) :
    exteriorRank (standardProjectionLinear (R := R) a b c) = b ∧
      I(standardProjectionLinear (R := R) a b c) = ⊤ := by
  -- This is the linear-algebra computation consumed by any future split-profile transport.
  exact ⟨standardProjectionLinear_exteriorRank (R := R) a b c,
    standardProjectionLinear_rankMinorIdeal_eq_top (R := R) a b c⟩

/-- Helper for Chap10 Lemma 10 102 6: the right projection after the standard sum isomorphism
is the coordinate right-block projection. -/
private theorem standardModuleSumIsoBiprod_hom_comp_snd (a b : ℕ) :
    (standard_module_sum_iso_biprod (R := R) a b).hom ≫
        (biprod.snd :
          ((ModuleCat.of R (Fin a → R)) ⊞ (ModuleCat.of R (Fin b → R))) ⟶
            ModuleCat.of R (Fin b → R)) =
      ModuleCat.ofHom (rightProjectionLinear (R := R) a b) := by
  -- Push the categorical projection through the product comparison, then compare coordinates.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  ext k
  -- After the product comparison, the right summand is indexed by `Fin.natAdd`.
  have hk : finSumFinEquiv (Sum.inr k) = Fin.natAdd a k := by
    apply Equiv.injective finSumFinEquiv.symm
    simpa using (finSumFinEquiv_symm_apply_natAdd (m := a) (n := b) k)
  simp [standard_module_sum_iso_biprod, rightProjectionLinear_apply,
    LinearEquiv.piCongrLeft, hk]

/-- Helper for Chap10 Lemma 10 102 6: the left inclusion before the inverse standard sum
isomorphism is the coordinate left-block inclusion. -/
private theorem biprod_inl_comp_standardModuleSumIsoBiprod_inv (b c : ℕ) :
    (biprod.inl :
        ModuleCat.of R (Fin b → R) ⟶
          ((ModuleCat.of R (Fin b → R)) ⊞ (ModuleCat.of R (Fin c → R)))) ≫
        (standard_module_sum_iso_biprod (R := R) b c).inv =
      ModuleCat.ofHom (leftInclusionLinear (R := R) b c) := by
  -- Push the categorical inclusion through the product comparison, then compare coordinates.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  ext k
  have hprod :
      (((ModuleCat.biprodIsoProd
            (ModuleCat.of R (Fin b → R))
            (ModuleCat.of R (Fin c → R))).hom).hom
          ((biprod.inl :
              ModuleCat.of R (Fin b → R) ⟶
                ((ModuleCat.of R (Fin b → R)) ⊞ (ModuleCat.of R (Fin c → R)))).hom x)) =
        (x, 0) := by
    exact biprodIsoProd_hom_inl_apply (R := R)
      (ModuleCat.of R (Fin b → R)) (ModuleCat.of R (Fin c → R)) x
  -- The inverse sum coordinates split according to whether the target index lies in the left
  -- block or the right block.
  by_cases h : k.1 < b
  · have hk : finSumFinEquiv.symm k = Sum.inl (Fin.castLT k h) := by
      apply Equiv.injective finSumFinEquiv
      ext
      simp [Fin.castAdd, Fin.castLT]
    simp [standard_module_sum_iso_biprod, leftInclusionLinear_apply, hprod,
      LinearEquiv.piCongrLeft, hk, h]
  · let kc : Fin c := ⟨k.1 - b, by omega⟩
    have hk : finSumFinEquiv.symm k = Sum.inr kc := by
      apply Equiv.injective finSumFinEquiv
      ext
      simp [kc]
      omega
    simp [standard_module_sum_iso_biprod, leftInclusionLinear_apply, hprod,
      LinearEquiv.piCongrLeft, hk, h]
    rfl

/-- Helper for Chap10 Lemma 10 102 6: after the standard finite-free sum coordinates, the
categorical biproduct projection is the standard split projection. -/
private theorem standardBiprodProjection_hom_eq_standardProjectionLinear
    (r : ℕ → ℕ) (j : ℕ) :
    (((standard_module_sum_iso_biprod (R := R) (r (j + 2)) (r (j + 1))).hom ≫
          standard_biprod_projection (R := R) r j ≫
        (standard_module_sum_iso_biprod (R := R) (r (j + 1)) (r j)).inv).hom) =
      standardProjectionLinear (R := R) (r (j + 2)) (r (j + 1)) (r j) := by
  -- The standard sum isomorphisms identify the categorical projection with the coordinate
  -- formula `(x, y) ↦ (y, 0)`.
  have hmorph :
      (standard_module_sum_iso_biprod (R := R) (r (j + 2)) (r (j + 1))).hom ≫
          standard_biprod_projection (R := R) r j ≫
        (standard_module_sum_iso_biprod (R := R) (r (j + 1)) (r j)).inv =
        ModuleCat.ofHom
          (standardProjectionLinear (R := R) (r (j + 2)) (r (j + 1)) (r j)) := by
    calc
      (standard_module_sum_iso_biprod (R := R) (r (j + 2)) (r (j + 1))).hom ≫
            standard_biprod_projection (R := R) r j ≫
          (standard_module_sum_iso_biprod (R := R) (r (j + 1)) (r j)).inv =
          ((standard_module_sum_iso_biprod (R := R) (r (j + 2)) (r (j + 1))).hom ≫
              (biprod.snd :
                ((ModuleCat.of R (Fin (r (j + 2)) → R)) ⊞
                    (ModuleCat.of R (Fin (r (j + 1)) → R))) ⟶
                  ModuleCat.of R (Fin (r (j + 1)) → R))) ≫
            (biprod.inl :
              ModuleCat.of R (Fin (r (j + 1)) → R) ⟶
                ((ModuleCat.of R (Fin (r (j + 1)) → R)) ⊞
                  (ModuleCat.of R (Fin (r j) → R)))) ≫
            (standard_module_sum_iso_biprod (R := R) (r (j + 1)) (r j)).inv := by
              simp [standard_biprod_projection, Category.assoc]
      _ = ModuleCat.ofHom (rightProjectionLinear (R := R) (r (j + 2)) (r (j + 1))) ≫
            (biprod.inl :
              ModuleCat.of R (Fin (r (j + 1)) → R) ⟶
                ((ModuleCat.of R (Fin (r (j + 1)) → R)) ⊞
                  (ModuleCat.of R (Fin (r j) → R)))) ≫
            (standard_module_sum_iso_biprod (R := R) (r (j + 1)) (r j)).inv := by
              rw [standardModuleSumIsoBiprod_hom_comp_snd]
      _ = ModuleCat.ofHom (rightProjectionLinear (R := R) (r (j + 2)) (r (j + 1))) ≫
            ModuleCat.ofHom (leftInclusionLinear (R := R) (r (j + 1)) (r j)) := by
              rw [biprod_inl_comp_standardModuleSumIsoBiprod_inv]
      _ = ModuleCat.ofHom
            (standardProjectionLinear (R := R) (r (j + 2)) (r (j + 1)) (r j)) := by
              apply ModuleCat.hom_ext
              rw [standardProjectionLinear_eq_comp]
              rfl
  simpa using congrArg ModuleCat.Hom.hom hmorph

/-- Helper for Chap10 Lemma 10 102 6: if the middle block in the standard split projection has
rank zero, then the projection factors through a zero module and is the zero morphism. -/
private theorem standard_biprod_projection_eq_zero_of_middle_count_eq_zero
    {r : ℕ → ℕ} {j : ℕ} (hmid : r (j + 1) = 0) :
    standard_biprod_projection (R := R) r j = 0 := by
  -- The projection lands in the middle block, and that block is a zero object by hypothesis.
  unfold standard_biprod_projection
  have hzero :
      CategoryTheory.Limits.IsZero (ModuleCat.of R (Fin (r (j + 1)) → R)) := by
    simpa [hmid] using standard_zero_module_isZero (R := R)
  have hsnd :
      (biprod.snd :
        ((ModuleCat.of R (Fin (r (j + 2)) → R)) ⊞
          ModuleCat.of R (Fin (r (j + 1)) → R)) ⟶
        ModuleCat.of R (Fin (r (j + 1)) → R)) = 0 :=
    hzero.eq_of_tgt _ _
  rw [hsnd]
  simp

/-- Helper for Chap10 Lemma 10 102 6: interchange the two middle factors in a biproduct of two
biproducts. -/
private noncomputable def biprodInterchange {𝒞 : Type*} [Category 𝒞] [HasZeroMorphisms 𝒞]
    [HasBinaryBiproducts 𝒞] (A B C D : 𝒞) :
    (A ⊞ B) ⊞ (C ⊞ D) ≅ (A ⊞ C) ⊞ (B ⊞ D) :=
  (biprod.associator A B (C ⊞ D)) ≪≫
    biprod.mapIso (Iso.refl A)
      ((biprod.associator B C D).symm ≪≫
        biprod.mapIso (biprod.braiding B C) (Iso.refl D) ≪≫
        biprod.associator C B D) ≪≫
    (biprod.associator A C (B ⊞ D)).symm

/-- Helper for Chap10 Lemma 10 102 6: after interchanging four biproduct factors, the two
component projection maps combine to the projection onto the middle pair. -/
private theorem biprodInterchange_projection {𝒞 : Type*} [Category 𝒞] [HasZeroMorphisms 𝒞]
    [HasBinaryBiproducts 𝒞] (A B C D E F : 𝒞) :
    (biprodInterchange A B C D).inv ≫
        biprod.map
          ((biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inl : B ⟶ B ⊞ E))
          ((biprod.snd : C ⊞ D ⟶ D) ≫ (biprod.inl : D ⟶ D ⊞ F)) ≫
        (biprodInterchange B E D F).hom =
      (biprod.snd : (A ⊞ C) ⊞ (B ⊞ D) ⟶ B ⊞ D) ≫
        (biprod.inl : B ⊞ D ⟶ (B ⊞ D) ⊞ (E ⊞ F)) := by
  -- The statement is purely biproduct bookkeeping.
  dsimp [biprodInterchange]
  ext <;> simp [Category.assoc]

/-- Helper for Chap10 Lemma 10 102 6: adding two split projection profiles again gives the
standard split projection after the canonical four-summand interchange. -/
private theorem standard_biprod_projection_add (r s : ℕ → ℕ) (j : ℕ) :
    biprod.map
      (standard_module_sum_iso_biprod (R := R) (r (j + 2)) (s (j + 2))).hom
      (standard_module_sum_iso_biprod (R := R) (r (j + 1)) (s (j + 1))).hom ≫
      (biprodInterchange
        (ModuleCat.of R (Fin (r (j + 2)) → R))
        (ModuleCat.of R (Fin (r (j + 1)) → R))
        (ModuleCat.of R (Fin (s (j + 2)) → R))
        (ModuleCat.of R (Fin (s (j + 1)) → R))).inv ≫
      biprod.map (standard_biprod_projection (R := R) r j)
        (standard_biprod_projection (R := R) s j) ≫
      (biprodInterchange
        (ModuleCat.of R (Fin (r (j + 1)) → R))
        (ModuleCat.of R (Fin (r j) → R))
        (ModuleCat.of R (Fin (s (j + 1)) → R))
        (ModuleCat.of R (Fin (s j) → R))).hom ≫
      biprod.map
        (standard_module_sum_iso_biprod (R := R) (r (j + 1)) (s (j + 1))).inv
        (standard_module_sum_iso_biprod (R := R) (r j) (s j)).inv =
    standard_biprod_projection (R := R) (fun k ↦ r k + s k) j := by
  -- First combine the two component projections through the interchange, then cancel the middle
  -- standard-sum coordinate isomorphism.
  let A := ModuleCat.of R (Fin (r (j + 2)) → R)
  let B := ModuleCat.of R (Fin (r (j + 1)) → R)
  let C := ModuleCat.of R (Fin (s (j + 2)) → R)
  let D := ModuleCat.of R (Fin (s (j + 1)) → R)
  let E := ModuleCat.of R (Fin (r j) → R)
  let F := ModuleCat.of R (Fin (s j) → R)
  let sourceSum := standard_module_sum_iso_biprod (R := R) (r (j + 2)) (s (j + 2))
  let middleSum := standard_module_sum_iso_biprod (R := R) (r (j + 1)) (s (j + 1))
  let targetSum := standard_module_sum_iso_biprod (R := R) (r j) (s j)
  unfold standard_biprod_projection
  simp only
  change
    biprod.map sourceSum.hom middleSum.hom ≫ (biprodInterchange A B C D).inv ≫
        biprod.map
          ((biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inl : B ⟶ B ⊞ E))
          ((biprod.snd : C ⊞ D ⟶ D) ≫ (biprod.inl : D ⟶ D ⊞ F)) ≫
        (biprodInterchange B E D F).hom ≫
        biprod.map middleSum.inv targetSum.inv =
      (biprod.snd :
          (ModuleCat.of R (Fin (r (j + 2) + s (j + 2)) → R) ⊞
            ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R)) ⟶
            ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R)) ≫
        (biprod.inl :
          ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R) ⟶
            (ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R) ⊞
              ModuleCat.of R (Fin (r j + s j) → R)))
  calc
    biprod.map sourceSum.hom middleSum.hom ≫ (biprodInterchange A B C D).inv ≫
        biprod.map
          ((biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inl : B ⟶ B ⊞ E))
          ((biprod.snd : C ⊞ D ⟶ D) ≫ (biprod.inl : D ⟶ D ⊞ F)) ≫
        (biprodInterchange B E D F).hom ≫
        biprod.map middleSum.inv targetSum.inv =
      biprod.map sourceSum.hom middleSum.hom ≫
        ((biprodInterchange A B C D).inv ≫
          biprod.map
            ((biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inl : B ⟶ B ⊞ E))
            ((biprod.snd : C ⊞ D ⟶ D) ≫ (biprod.inl : D ⟶ D ⊞ F)) ≫
          (biprodInterchange B E D F).hom) ≫
        biprod.map middleSum.inv targetSum.inv := by
          simp only [Category.assoc]
    _ = biprod.map sourceSum.hom middleSum.hom ≫
        ((biprod.snd : (A ⊞ C) ⊞ (B ⊞ D) ⟶ B ⊞ D) ≫
          (biprod.inl : B ⊞ D ⟶ (B ⊞ D) ⊞ (E ⊞ F))) ≫
        biprod.map middleSum.inv targetSum.inv := by
          rw [biprodInterchange_projection]
    _ = (biprod.snd :
          (ModuleCat.of R (Fin (r (j + 2) + s (j + 2)) → R) ⊞
            ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R)) ⟶
            ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R)) ≫
        (biprod.inl :
          ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R) ⟶
            (ModuleCat.of R (Fin (r (j + 1) + s (j + 1)) → R) ⊞
              ModuleCat.of R (Fin (r j + s j) → R))) := by
          simp [A, B, C, D, E, F, sourceSum, middleSum, targetSum, Category.assoc]

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

/-- Helper for Chap10 Lemma 10 102 6: transport a split-basis profile coordinate across a
chain-complex isomorphism. -/
private noncomputable def biprodProjectionProfileOfIsoCoord
    {K L : ChainComplex (ModuleCat R) ℕ}
    (P : BiprodProjectionProfile (R := R) K) (e : K ≅ L) (j : ℕ) :
    L.X j ≅
      (ModuleCat.of R (Fin (P.r (j + 1)) → R) ⊞
        ModuleCat.of R (Fin (P.r j) → R)) :=
  (HomologicalComplex.Hom.isoApp e j).symm ≪≫ P.coord j

/-- Helper for Chap10 Lemma 10 102 6: the transported profile keeps the same standard
projection differential normal form. -/
private theorem biprodProjectionProfileOfIso_differential
    {K L : ChainComplex (ModuleCat R) ℕ}
    (P : BiprodProjectionProfile (R := R) K) (e : K ≅ L) (j : ℕ) :
    (biprodProjectionProfileOfIsoCoord (R := R) P e (j + 1)).inv ≫ L.d (j + 1) j ≫
        (biprodProjectionProfileOfIsoCoord (R := R) P e j).hom =
      standard_biprod_projection (R := R) P.r j := by
  -- Move the `L` differential through the chain isomorphism, then cancel the inverse component.
  dsimp [biprodProjectionProfileOfIsoCoord]
  exact
    calc
      (P.coord (j + 1)).inv ≫ e.hom.f (j + 1) ≫ L.d (j + 1) j ≫ e.inv.f j ≫
          (P.coord j).hom =
        (P.coord (j + 1)).inv ≫ K.d (j + 1) j ≫ e.hom.f j ≫ e.inv.f j ≫
          (P.coord j).hom := by
          have hcomm := e.hom.comm (j + 1) j
          simpa [Category.assoc] using
            congrArg
              (fun m ↦ (P.coord (j + 1)).inv ≫ m ≫ e.inv.f j ≫ (P.coord j).hom)
              hcomm
      _ = (P.coord (j + 1)).inv ≫ K.d (j + 1) j ≫ (P.coord j).hom := by
          have hcancel : e.hom.f j ≫ e.inv.f j = 𝟙 (K.X j) := by
            exact HomologicalComplex.congr_hom e.hom_inv_id j
          simpa only [Category.assoc, Category.comp_id] using
            congrArg
              (fun m ↦ (P.coord (j + 1)).inv ≫ K.d (j + 1) j ≫ m ≫ (P.coord j).hom)
              hcancel
      _ = standard_biprod_projection (R := R) P.r j := by
          simpa [Nat.add_assoc] using P.differential j

/-- Helper for Chap10 Lemma 10 102 6: a split-basis profile is invariant under isomorphism of
chain complexes. -/
private noncomputable def BiprodProjectionProfile.ofIso
    {K L : ChainComplex (ModuleCat R) ℕ}
    (P : BiprodProjectionProfile (R := R) K) (e : K ≅ L) :
    BiprodProjectionProfile (R := R) L :=
  { r := P.r
    coord := biprodProjectionProfileOfIsoCoord (R := R) P e
    differential := biprodProjectionProfileOfIso_differential (R := R) P e }

/-- Helper for Chap10 Lemma 10 102 6: a split-basis profile reads the displayed rank as the sum
of the two adjacent profile counts. -/
private theorem biprodProjectionProfile_rank_eq_add [Nontrivial R]
    (C : FiniteFreeComplex R e) (P : BiprodProjectionProfile (R := R) C.toChainComplex)
    (j : Fin (e + 1)) :
    C.rank j = P.r (j.1 + 1) + P.r j.1 := by
  -- Compare the chosen finite-free coordinate for `C_j` with the profile coordinate for `C_j`.
  exact rank_eq_add_of_iso_biprod_standard_module (R := R)
    (C.rank j) (P.r (j.1 + 1)) (P.r j.1)
    ((C.termIso j).symm ≪≫ P.coord j.1)

/-- Helper for Chap10 Lemma 10 102 6: the first profile count above the bounded complex is zero.
-/
private theorem biprodProjectionProfile_top_count_eq_zero [Nontrivial R]
    (C : FiniteFreeComplex R e) (P : BiprodProjectionProfile (R := R) C.toChainComplex) :
    P.r (e + 1) = 0 := by
  -- The degree `e + 1` term of `C` is zero, while the profile identifies it with
  -- `R^(r(e+2)+r(e+1))`.
  have hstd :
      CategoryTheory.Limits.IsZero
        (ModuleCat.of R (Fin (P.r (e + 2) + P.r (e + 1)) → R)) := by
    exact CategoryTheory.Limits.IsZero.of_iso
      (C.isZero_toChainComplex_X (e + 1) (by omega))
      ((P.coord (e + 1)) ≪≫
        (standard_module_sum_iso_biprod (R := R) (P.r (e + 2)) (P.r (e + 1))).symm).symm
  have hsum : P.r (e + 2) + P.r (e + 1) = 0 :=
    rank_eq_zero_of_isZero_standard_module (R := R) _ hstd
  omega

/-- Helper for Chap10 Lemma 10 102 6: an existing split-basis profile supplies the displayed
rank recurrence and the top boundary count. -/
private theorem exists_rank_counts_of_biprodProjectionProfile [Nontrivial R]
    (C : FiniteFreeComplex R e) (P : BiprodProjectionProfile (R := R) C.toChainComplex) :
    ∃ r : Fin e → ℕ,
      (∀ j : Fin (e - 1),
        (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
          C.rank (adjacentMiddleIndex j)) ∧
      (∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩) := by
  refine ⟨fun i ↦ P.r (i.1 + 1), ?_, ?_⟩
  · intro j
    -- The middle displayed term has profile counts `r_{j+2}` and `r_{j+1}`.
    have hrank :
        C.rank (adjacentMiddleIndex j) =
          P.r (j.1 + 2) + P.r (j.1 + 1) := by
      simpa [adjacentMiddleIndex, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        biprodProjectionProfile_rank_eq_add (R := R) (C := C) P (adjacentMiddleIndex j)
    rw [hrank]
    norm_num
    ring
  · intro h
    -- In the top degree the count above the complex is zero, so the top rank is the last count.
    have hrank :
        C.rank ⟨e, by omega⟩ = P.r (e + 1) + P.r e := by
      simpa using
        biprodProjectionProfile_rank_eq_add (R := R) (C := C) P ⟨e, by omega⟩
    have htop : P.r (e + 1) = 0 :=
      biprodProjectionProfile_top_count_eq_zero (R := R) (C := C) P
    rw [hrank, htop]
    have hidx : e - 1 + 1 = e := by
      omega
    simpa [hidx]

/-- Helper for Chap10 Lemma 10 102 6: conjugating the displayed linear differential back through
the chosen finite-free term coordinates recovers the underlying chain differential. -/
private theorem termIso_hom_comp_diffAt_comp_termIso_inv
    (C : FiniteFreeComplex R e) (i : Fin e) :
    (C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i) ≫
        (C.termIso i.castSucc).inv =
      C.toChainComplex.d (i.1 + 1) i.1 := by
  -- The definition of `diffAt` is exactly this coordinate conjugation; the two isomorphism
  -- cancellation laws expose the original chain-complex differential.
  dsimp [FiniteFreeComplex.diffAt, FiniteFreeComplex.differential,
    FiniteFreeComplex.termIsoAt]
  change (C.termIso i.succ).hom ≫
      ((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
        (C.termIso i.castSucc).hom) ≫
      (C.termIso i.castSucc).inv =
    C.toChainComplex.d (i.1 + 1) i.1
  simp [Category.assoc]

/-- Helper for Chap10 Lemma 10 102 6: a split-biproduct profile makes each displayed
differential a standard split projection after changing finite-free coordinates. -/
private theorem biprodProjectionProfile_diffAt_exteriorRank_rankMinorIdeal [Nontrivial R]
    (C : FiniteFreeComplex R e) (P : BiprodProjectionProfile (R := R) C.toChainComplex)
    (i : Fin e) :
    exteriorRank (C.diffAt i) = P.r (i.1 + 1) ∧ I(C.diffAt i) = ⊤ := by
  -- The profile coordinate ranks identify the source and target dimensions of `C.diffAt i`.
  let a := P.r (i.1 + 2)
  let b := P.r (i.1 + 1)
  let c := P.r i.1
  have hb : b = P.r (i.1 + 1) := rfl
  let sourceIso :
      ModuleCat.of R (Fin (C.rank i.succ) → R) ≅ ModuleCat.of R (Fin (a + b) → R) :=
    (C.termIso i.succ).symm ≪≫ P.coord (i.1 + 1) ≪≫
      (standard_module_sum_iso_biprod (R := R) a b).symm
  let targetIso :
      ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅ ModuleCat.of R (Fin (b + c) → R) :=
    (C.termIso i.castSucc).symm ≪≫ P.coord i.1 ≪≫
      (standard_module_sum_iso_biprod (R := R) b c).symm
  have hmorph :
      sourceIso.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ targetIso.hom =
        ModuleCat.ofHom (standardProjectionLinear (R := R) a b c) := by
    -- Expand the displayed differential, cancel the `C.termIso` coordinates, then consume the
    -- profile normal form and the standard biproduct-projection bridge.
    calc
      sourceIso.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ targetIso.hom =
          (standard_module_sum_iso_biprod (R := R) a b).hom ≫
            (P.coord (i.1 + 1)).inv ≫
            ((C.termIso i.succ).hom ≫ ModuleCat.ofHom (C.diffAt i) ≫
              (C.termIso i.castSucc).inv) ≫
            (P.coord i.1).hom ≫
            (standard_module_sum_iso_biprod (R := R) b c).inv := by
            simp [sourceIso, targetIso, Category.assoc]
      _ = (standard_module_sum_iso_biprod (R := R) a b).hom ≫
            (P.coord (i.1 + 1)).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
            (P.coord i.1).hom ≫
            (standard_module_sum_iso_biprod (R := R) b c).inv := by
            simpa only [Category.assoc] using
              congrArg
                (fun f ↦ (standard_module_sum_iso_biprod (R := R) a b).hom ≫
                  (P.coord (i.1 + 1)).inv ≫ f ≫ (P.coord i.1).hom ≫
                  (standard_module_sum_iso_biprod (R := R) b c).inv)
                (termIso_hom_comp_diffAt_comp_termIso_inv (R := R) C i)
      _ = (standard_module_sum_iso_biprod (R := R) a b).hom ≫
            standard_biprod_projection (R := R) P.r i.1 ≫
            (standard_module_sum_iso_biprod (R := R) b c).inv := by
            simpa only [Category.assoc] using
              congrArg
                (fun f ↦ (standard_module_sum_iso_biprod (R := R) a b).hom ≫ f ≫
                  (standard_module_sum_iso_biprod (R := R) b c).inv)
                (P.differential i.1)
      _ = ModuleCat.ofHom (standardProjectionLinear (R := R) a b c) := by
            apply ModuleCat.hom_ext
            simpa [a, b, c] using
              standardBiprodProjection_hom_eq_standardProjectionLinear (R := R) P.r i.1
  have hlinear :
      targetIso.toLinearEquiv.toLinearMap.comp
          ((C.diffAt i).comp sourceIso.toLinearEquiv.symm.toLinearMap) =
        standardProjectionLinear (R := R) a b c := by
    -- Read the morphism equality as the corresponding equality of linear maps.
    simpa [LinearMap.comp_assoc] using congrArg ModuleCat.Hom.hom hmorph
  have hstandard := standardProjectionLinear_exteriorRank_rankMinorIdeal (R := R) a b c
  constructor
  · -- Exterior rank is invariant under the two coordinate automorphisms.
    have hconj :=
      exteriorRank_eq_of_linearEquiv_conj (R := R) (φ := C.diffAt i)
        sourceIso.toLinearEquiv.symm targetIso.toLinearEquiv
    rw [hlinear] at hconj
    exact hconj.symm.trans (hstandard.1.trans hb)
  · -- The rank-minor ideal is invariant under the same coordinate automorphisms.
    have hconj :=
      rankMinorIdeal_eq_of_linearEquiv_conj' (R := R) (φ := C.diffAt i)
        sourceIso.toLinearEquiv.symm targetIso.toLinearEquiv
    rw [hlinear] at hconj
    exact hconj.symm.trans hstandard.2

/-- Helper for Chap10 Lemma 10 102 6: an existing split-biproduct profile supplies exactly the
standard projection profile data needed by the final finite-free statement. -/
private theorem exists_standard_projection_profile_of_biprodProjectionProfile [Nontrivial R]
    (C : FiniteFreeComplex R e) (P : BiprodProjectionProfile (R := R) C.toChainComplex) :
    ∃ r : Fin e → ℕ,
      (∀ j : Fin (e - 1),
        (r (adjacentLeftIndex j) : ℤ) + r (adjacentRightIndex j) =
          C.rank (adjacentMiddleIndex j)) ∧
      (∀ h : 0 < e, (r ⟨e - 1, by omega⟩ : ℤ) = C.rank ⟨e, by omega⟩) ∧
      (∀ i : Fin e, (exteriorRank (C.diffAt i) : ℤ) = r i) ∧
      (∀ i : Fin e, I(C.diffAt i) = ⊤) := by
  refine ⟨fun i ↦ P.r (i.1 + 1), ?_, ?_, ?_, ?_⟩
  · intro j
    -- The middle displayed term has profile counts `r_{j+2}` and `r_{j+1}`.
    have hrank :
        C.rank (adjacentMiddleIndex j) =
          P.r (j.1 + 2) + P.r (j.1 + 1) := by
      simpa [adjacentMiddleIndex, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        biprodProjectionProfile_rank_eq_add (R := R) (C := C) P (adjacentMiddleIndex j)
    rw [hrank]
    norm_num
    ring
  · intro h
    -- In the top degree the count above the complex is zero, so the top rank is the last count.
    have hrank :
        C.rank ⟨e, by omega⟩ = P.r (e + 1) + P.r e := by
      simpa using
        biprodProjectionProfile_rank_eq_add (R := R) (C := C) P ⟨e, by omega⟩
    have htop : P.r (e + 1) = 0 :=
      biprodProjectionProfile_top_count_eq_zero (R := R) (C := C) P
    rw [hrank, htop]
    have hidx : e - 1 + 1 = e := by
      omega
    simpa [hidx]
  · intro i
    -- The profile count in degree `i + 1` is the exterior rank of the displayed differential.
    have h := (biprodProjectionProfile_diffAt_exteriorRank_rankMinorIdeal
      (R := R) (C := C) P i).1
    simpa using congrArg (fun n : ℕ ↦ (n : ℤ)) h
  · intro i
    -- The standard split projection has a unit rank-minor ideal, and this survives transport.
    exact (biprodProjectionProfile_diffAt_exteriorRank_rankMinorIdeal
      (R := R) (C := C) P i).2

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
    have hzero :
        CategoryTheory.Limits.IsZero
          ((((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R))).X j)) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        (ModuleCat.of R (Fin n → R)) j (by omega)
    have hsucc_count : (supported_rank_sequence n 0) (j + 1) = 0 := by
      simp [supported_rank_sequence]
    have hj_count : (supported_rank_sequence n 0) j = 0 := by
      simp [supported_rank_sequence, hj]
    -- Both supported counts vanish away from degree `0`, so the zero-term isomorphism already
    -- has the required target after simplifying the profile sequence.
    refine ⟨?_⟩
    rw [hsucc_count, hj_count]
    exact zero_term_iso_standard_biprod (R := R) hzero

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

/-- Helper for Chap10 Lemma 10 102 6: an already constructed `single₀` profile gives the
corresponding nonempty split-biproduct profile. -/
private theorem nonempty_biprodProjectionProfile_single₀ (n : ℕ) :
    Nonempty
      (BiprodProjectionProfile (R := R)
        ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (Fin n → R)))) := by
  -- The supported coordinate model above is exactly the profile needed for the generator case.
  exact ⟨biprodProjectionProfile_single₀ (R := R) n⟩

/-- Helper for Chap10 Lemma 10 102 6: nonempty split-biproduct profiles transport across chain
complex isomorphisms. -/
private theorem nonempty_biprodProjectionProfile_ofIso
    {K L : ChainComplex (ModuleCat R) ℕ}
    (hK : Nonempty (BiprodProjectionProfile (R := R) K)) (e : K ≅ L) :
    Nonempty (BiprodProjectionProfile (R := R) L) := by
  -- Choose a profile on the source and move its coordinates through the chain isomorphism.
  obtain ⟨P⟩ := hK
  exact ⟨BiprodProjectionProfile.ofIso (R := R) P e⟩

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

/-- Helper for Lemma 10.102.6: the source term of `identityDiskComplex` is the rank-one
standard module. -/
private theorem identityDiskComplex_source_X_eq {e : ℕ} (i : Fin e) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).X (i.1 + 1) =
      ModuleCat.of R (Fin 1 → R) := by
  -- Unfold the explicit chain-complex model at the supported source degree.
  rw [FiniteFreeComplex.identityDiskComplex, ChainComplex.of_x,
    FiniteFreeComplex.identityDiskRank_succ]

/-- Helper for Lemma 10.102.6: the target term of `identityDiskComplex` is the rank-one
standard module. -/
private theorem identityDiskComplex_target_X_eq {e : ℕ} (i : Fin e) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).X i.1 =
      ModuleCat.of R (Fin 1 → R) := by
  -- Unfold the explicit chain-complex model at the supported target degree.
  rw [FiniteFreeComplex.identityDiskComplex, ChainComplex.of_x,
    FiniteFreeComplex.identityDiskRank_castSucc]

/-- Helper for Chap10 Lemma 10 102 6: the supported identity-disk matrix differential is the
identity on the rank-one standard module, up to the rank equalities. -/
private theorem identityDiskDifferential_heq_id {e : ℕ} (i : Fin e) :
    FiniteFreeComplex.identityDiskDifferential (R := R) i i.1 ≍
      𝟙 (ModuleCat.of R (Fin 1 → R)) := by
  -- Expose the supported matrix and check its only coordinate.
  change ModuleCat.ofHom
      (Matrix.toLinearMapRight' (FiniteFreeComplex.identityDiskMatrix (R := R) i i.1)) ≍
    𝟙 (ModuleCat.of R (Fin 1 → R))
  unfold FiniteFreeComplex.identityDiskMatrix FiniteFreeComplex.identityDiskRank
  rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
  apply heq_of_eq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  ext j
  fin_cases j
  simp [Matrix.toLinearMapRight'_apply, Matrix.vecMul, dotProduct]

/-- Helper for Chap10 Lemma 10 102 6: after identifying the two supported terms with the
rank-one standard module, the identity-disk differential is the identity map. -/
private theorem identityDiskComplex_eqToHom_symm_comp_d {e : ℕ} (i : Fin e) :
    eqToHom (identityDiskComplex_source_X_eq (R := R) i).symm ≫
        (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 =
      eqToHom (identityDiskComplex_target_X_eq (R := R) i).symm := by
  have hd_heq : (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≍
      𝟙 (ModuleCat.of R (Fin 1 → R)) := by
    -- Unfold only the chain-complex wrapper, then reuse the matrix computation.
    simpa [FiniteFreeComplex.identityDiskComplex, ChainComplex.of_d] using
      identityDiskDifferential_heq_id (R := R) (i := i)
  -- The two object identifications turn the heterogeneous identity into an equality of
  -- transported morphisms.
  rw [CategoryTheory.eqToHom_comp_iff]
  exact (CategoryTheory.conj_eqToHom_iff_heq
    ((FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1)
    (𝟙 (ModuleCat.of R (Fin 1 → R)))
    (identityDiskComplex_source_X_eq (R := R) i)
    (identityDiskComplex_target_X_eq (R := R) i)).2 hd_heq

/-- Helper for Chap10 Lemma 10 102 6: the supported identity-disk differential preserves the
right biproduct projection after the source and target rank-one identifications. -/
private theorem biprod_snd_identityDiskComplex_supported {e : ℕ} {X : ModuleCat R}
    (i : Fin e) :
    (biprod.snd : X ⊞ ModuleCat.of R (Fin 1 → R) ⟶ ModuleCat.of R (Fin 1 → R)) ≫
        eqToHom (identityDiskComplex_source_X_eq (R := R) i).symm ≫
          (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫
            eqToHom (identityDiskComplex_target_X_eq (R := R) i) =
      (biprod.snd : X ⊞ ModuleCat.of R (Fin 1 → R) ⟶ ModuleCat.of R (Fin 1 → R)) := by
  -- Reassociate only the inner transported differential and then cancel the target transport.
  rw [← Category.assoc
    (eqToHom (identityDiskComplex_source_X_eq (R := R) i).symm)
    ((FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1)
    (eqToHom (identityDiskComplex_target_X_eq (R := R) i))]
  rw [identityDiskComplex_eqToHom_symm_comp_d]
  simp

/-- Helper for Chap10 Lemma 10 102 6: the supported identity-disk component is unchanged if the
rank-one summand is written by an equal object. -/
private theorem biprod_snd_identityDiskComplex_supported_of_eq {e : ℕ} {X Y : ModuleCat R}
    (i : Fin e) (hY : ModuleCat.of R (Fin 1 → R) = Y) :
    (biprod.snd : X ⊞ Y ⟶ Y) ≫
        eqToHom hY.symm ≫
          eqToHom (identityDiskComplex_source_X_eq (R := R) i).symm ≫
            (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≫
              eqToHom (identityDiskComplex_target_X_eq (R := R) i) ≫
                eqToHom hY =
      (biprod.snd : X ⊞ Y ⟶ Y) := by
  -- Reduce to the rank-one spelling used by the transported-differential computation.
  subst hY
  simpa using biprod_snd_identityDiskComplex_supported (R := R) (X := X) i

/-- Helper for Chap10 Lemma 10 102 6: after the objectwise biproduct comparison, the differential
of a binary biproduct complex is the biproduct map of the two summand differentials. -/
private theorem biprodXIso_differential_hom
    {K L : ChainComplex (ModuleCat R) ℕ} (j : ℕ) :
    ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom =
      (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
        biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
  -- Compare the two maps after projecting to the two explicit summands of the objectwise
  -- biproduct; each component is the chain-map square for the corresponding projection.
  apply biprod.hom_ext
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.fst =
        ((biprod K L).d (j + 1) j) ≫ (biprod.fst : biprod K L ⟶ K).f j := by
          rw [HomologicalComplex.biprodXIso_hom_fst]
      _ = (biprod.fst : biprod K L ⟶ K).f (j + 1) ≫ K.d (j + 1) j := by
          simpa [Category.assoc] using
            ((biprod.fst : biprod K L ⟶ K).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
            biprod.fst ≫ K.d (j + 1) j := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ m ≫ K.d (j + 1) j)
              (HomologicalComplex.biprodXIso_hom_fst K L (j + 1)).symm
      _ =
        (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.fst := by
          simp
  · calc
      ((biprod K L).d (j + 1) j) ≫ (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.snd =
        ((biprod K L).d (j + 1) j) ≫ (biprod.snd : biprod K L ⟶ L).f j := by
          rw [HomologicalComplex.biprodXIso_hom_snd]
      _ = (biprod.snd : biprod K L ⟶ L).f (j + 1) ≫ L.d (j + 1) j := by
          simpa [Category.assoc] using
            ((biprod.snd : biprod K L ⟶ L).comm (j + 1) j).symm
      _ = (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
            biprod.snd ≫ L.d (j + 1) j := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ m ≫ L.d (j + 1) j)
              (HomologicalComplex.biprodXIso_hom_snd K L (j + 1)).symm
      _ =
        (HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫ biprod.snd := by
          simp

/-- Helper for Chap10 Lemma 10 102 6: the two-term identity complex has a split-biproduct
projection profile supported in degrees `i + 1` and `i`. -/
private theorem nonempty_biprodProjectionProfile_doubleIdentity (i n : ℕ) :
    Nonempty
      (BiprodProjectionProfile (R := R)
        (HomologicalComplex.double
          (𝟙 (ModuleCat.of R (Fin n → R)))
          (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl))) := by
  -- The profile uses `0 ⊞ R^n` in degree `i + 1`, `R^n ⊞ 0` in degree `i`, and the
  -- zero-by-zero coordinate model everywhere else.
  let K : ChainComplex (ModuleCat R) ℕ :=
    HomologicalComplex.double
      (𝟙 (ModuleCat.of R (Fin n → R)))
      (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
  let coord :
      ∀ j : ℕ,
        K.X j ≅
          (ModuleCat.of R (Fin ((supported_rank_sequence n (i + 1)) (j + 1)) → R) ⊞
            ModuleCat.of R (Fin ((supported_rank_sequence n (i + 1)) j) → R)) := by
    intro j
    by_cases hsrc : j = i + 1
    · subst j
      have hleft : (supported_rank_sequence n (i + 1)) (i + 1 + 1) = 0 := by
        apply supported_rank_sequence_eq_zero_of_ne
        omega
      have hright : (supported_rank_sequence n (i + 1)) (i + 1) = n :=
        supported_rank_sequence_self n (i + 1)
      have hleftZero :
          CategoryTheory.Limits.IsZero
            (ModuleCat.of R (Fin ((supported_rank_sequence n (i + 1)) (i + 1 + 1)) → R)) := by
        simpa [hleft] using standard_zero_module_isZero (R := R)
      have hrightObj :
          ModuleCat.of R (Fin n → R) =
            ModuleCat.of R (Fin ((supported_rank_sequence n (i + 1)) (i + 1)) → R) := by
        rw [hright]
      exact
        (HomologicalComplex.doubleXIso₀
          (𝟙 (ModuleCat.of R (Fin n → R)))
          (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl) ≪≫
            eqToIso hrightObj ≪≫
            (biprodRightIsoOfLeftIsZero (R := R) hleftZero).symm)
    · by_cases htgt : j = i
      · subst j
        have hleft : (supported_rank_sequence n (i + 1)) (i + 1) = n :=
          supported_rank_sequence_self n (i + 1)
        have hright : (supported_rank_sequence n (i + 1)) i = 0 := by
          apply supported_rank_sequence_eq_zero_of_ne
          omega
        have hleftObj :
            ModuleCat.of R (Fin n → R) =
              ModuleCat.of R (Fin ((supported_rank_sequence n (i + 1)) (i + 1)) → R) := by
          rw [hleft]
        have hrightZero :
            CategoryTheory.Limits.IsZero
              (ModuleCat.of R (Fin ((supported_rank_sequence n (i + 1)) i) → R)) := by
          simpa [hright] using standard_zero_module_isZero (R := R)
        exact
          (HomologicalComplex.doubleXIso₁
            (𝟙 (ModuleCat.of R (Fin n → R)))
            (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
            (by omega) ≪≫
              eqToIso hleftObj ≪≫
              (biprodLeftIsoOfRightIsZero (R := R) hrightZero).symm)
      · have hzero : CategoryTheory.Limits.IsZero (K.X j) := by
          simpa [K] using
            HomologicalComplex.isZero_double_X
              (𝟙 (ModuleCat.of R (Fin n → R)))
              (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl) j hsrc htgt
        have hsucc_count : (supported_rank_sequence n (i + 1)) (j + 1) = 0 := by
          apply supported_rank_sequence_eq_zero_of_ne
          omega
        have hj_count : (supported_rank_sequence n (i + 1)) j = 0 := by
          apply supported_rank_sequence_eq_zero_of_ne
          exact hsrc
        rw [hsucc_count, hj_count]
        exact zero_term_iso_standard_biprod (R := R) hzero
  refine ⟨{ r := supported_rank_sequence n (i + 1), coord := coord, differential := ?_ }⟩
  intro j
  -- Off the supported differential, both sides have a zero source or the standard middle count is
  -- zero; the only real coordinate computation is the degree `i` identity map.
  by_cases hj : j = i
  · subst hj
    dsimp [coord, K]
    have hne : j + 1 ≠ j := by
      omega
    rw [HomologicalComplex.double_d
      (f := 𝟙 (ModuleCat.of R (Fin n → R)))
      (hi₀₁ := show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) hne]
    apply biprod.hom_ext
    · simp [supported_rank_sequence, standard_biprod_projection, biprodRightIsoOfLeftIsZero,
        biprodLeftIsoOfRightIsZero, Category.assoc]
    · simp [supported_rank_sequence, standard_biprod_projection, biprodRightIsoOfLeftIsZero,
        biprodLeftIsoOfRightIsZero, Category.assoc]
  · have hmid : (supported_rank_sequence n (i + 1)) (j + 1) = 0 := by
      apply supported_rank_sequence_eq_zero_of_ne
      omega
    have hstd :
        standard_biprod_projection (R := R) (supported_rank_sequence n (i + 1)) j = 0 :=
      standard_biprod_projection_eq_zero_of_middle_count_eq_zero (R := R) hmid
    have hdiff : K.d (j + 1) j = 0 := by
      simpa [K] using
        HomologicalComplex.double_d_eq_zero₁
          (𝟙 (ModuleCat.of R (Fin n → R)))
          (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl) (j + 1) j hj
    rw [hdiff, hstd]
    simp

/-- Helper for Chap10 Lemma 10 102 6: the project identity disk has the same split-biproduct
projection profile as the rank-one two-term identity complex. -/
private theorem nonempty_biprodProjectionProfile_identityDiskComplex {e : ℕ} (i : Fin e) :
    Nonempty
      (BiprodProjectionProfile (R := R)
        (FiniteFreeComplex.identityDiskComplex (R := R) i)) := by
  -- Use the same supported `0 ⊞ R` / `R ⊞ 0` coordinate profile as for the two-term
  -- double-identity complex.
  let K : ChainComplex (ModuleCat R) ℕ := FiniteFreeComplex.identityDiskComplex (R := R) i
  let coord :
      ∀ j : ℕ,
        K.X j ≅
          (ModuleCat.of R (Fin ((supported_rank_sequence 1 (i.1 + 1)) (j + 1)) → R) ⊞
            ModuleCat.of R (Fin ((supported_rank_sequence 1 (i.1 + 1)) j) → R)) := by
    intro j
    by_cases hsrc : j = i.1 + 1
    · subst j
      have hleft : (supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1 + 1) = 0 := by
        apply supported_rank_sequence_eq_zero_of_ne
        omega
      have hright : (supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1) = 1 :=
        supported_rank_sequence_self 1 (i.1 + 1)
      have hleftZero :
          CategoryTheory.Limits.IsZero
            (ModuleCat.of R (Fin ((supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1 + 1)) → R)) := by
        simpa [hleft] using standard_zero_module_isZero (R := R)
      have hrightObj :
          ModuleCat.of R (Fin 1 → R) =
            ModuleCat.of R (Fin ((supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1)) → R) := by
        rw [hright]
      exact
        (eqToIso (identityDiskComplex_source_X_eq (R := R) i) ≪≫
          eqToIso hrightObj ≪≫
          (biprodRightIsoOfLeftIsZero (R := R) hleftZero).symm)
    · by_cases htgt : j = i.1
      · subst j
        have hleft : (supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1) = 1 :=
          supported_rank_sequence_self 1 (i.1 + 1)
        have hright : (supported_rank_sequence 1 (i.1 + 1)) i.1 = 0 := by
          apply supported_rank_sequence_eq_zero_of_ne
          omega
        have hleftObj :
            ModuleCat.of R (Fin 1 → R) =
              ModuleCat.of R (Fin ((supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1)) → R) := by
          rw [hleft]
        have hrightZero :
            CategoryTheory.Limits.IsZero
              (ModuleCat.of R (Fin ((supported_rank_sequence 1 (i.1 + 1)) i.1) → R)) := by
          simpa [hright] using standard_zero_module_isZero (R := R)
        exact
          (eqToIso (identityDiskComplex_target_X_eq (R := R) i) ≪≫
            eqToIso hleftObj ≪≫
            (biprodLeftIsoOfRightIsZero (R := R) hrightZero).symm)
      · have hzero : CategoryTheory.Limits.IsZero (K.X j) := by
          simpa [K] using
            FiniteFreeComplex.identityDiskComplex_X_isZero_of_ne_support (R := R) (i := i)
              (j := j) hsrc htgt
        have hsucc_count : (supported_rank_sequence 1 (i.1 + 1)) (j + 1) = 0 := by
          apply supported_rank_sequence_eq_zero_of_ne
          omega
        have hj_count : (supported_rank_sequence 1 (i.1 + 1)) j = 0 := by
          apply supported_rank_sequence_eq_zero_of_ne
          exact hsrc
        rw [hsucc_count, hj_count]
        exact zero_term_iso_standard_biprod (R := R) hzero
  refine ⟨{ r := supported_rank_sequence 1 (i.1 + 1), coord := coord, differential := ?_ }⟩
  intro j
  by_cases hj : j = i.1
  · subst j
    dsimp [coord, K]
    apply biprod.hom_ext
    · -- The nonzero component is exactly the supported identity-disk differential.
      have hrightObj :
          ModuleCat.of R (Fin 1 → R) =
            ModuleCat.of R
              (Fin ((supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1)) → R) := by
        rw [supported_rank_sequence_self]
      simpa [supported_rank_sequence, standard_biprod_projection, biprodRightIsoOfLeftIsZero,
        biprodLeftIsoOfRightIsZero, Category.assoc] using
        (biprod_snd_identityDiskComplex_supported_of_eq
          (R := R)
          (X := ModuleCat.of R
            (Fin ((supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1 + 1)) → R))
          (Y := ModuleCat.of R
            (Fin ((supported_rank_sequence 1 (i.1 + 1)) (i.1 + 1)) → R))
          i hrightObj)
    · simp [supported_rank_sequence, standard_biprod_projection, biprodRightIsoOfLeftIsZero,
        biprodLeftIsoOfRightIsZero, Category.assoc, FiniteFreeComplex.identityDiskComplex,
        ChainComplex.of_d, FiniteFreeComplex.identityDiskDifferential]
  · have hmid : (supported_rank_sequence 1 (i.1 + 1)) (j + 1) = 0 := by
      apply supported_rank_sequence_eq_zero_of_ne
      omega
    have hstd :
        standard_biprod_projection (R := R) (supported_rank_sequence 1 (i.1 + 1)) j = 0 :=
      standard_biprod_projection_eq_zero_of_middle_count_eq_zero (R := R) hmid
    have hdiff : K.d (j + 1) j = 0 := by
      simpa [K, FiniteFreeComplex.identityDiskComplex, ChainComplex.of_d] using
        FiniteFreeComplex.identityDiskDifferential_eq_zero_of_ne (R := R) (i := i) hj
    rw [hdiff, hstd]
    simp

/-- Helper for Chap10 Lemma 10 102 6: split-biproduct projection profiles are closed under
binary biproducts of chain complexes. -/
private theorem nonempty_biprodProjectionProfile_biprod
    {K L : ChainComplex (ModuleCat R) ℕ}
    (hK : Nonempty (BiprodProjectionProfile (R := R) K))
    (hL : Nonempty (BiprodProjectionProfile (R := R) L)) :
    Nonempty (BiprodProjectionProfile (R := R) (biprod K L)) := by
  -- Combine the two rank sequences, then shuffle the four coordinate summands so the middle
  -- blocks stay adjacent.
  obtain ⟨P⟩ := hK
  obtain ⟨Q⟩ := hL
  let r : ℕ → ℕ := fun j ↦ P.r j + Q.r j
  let coord :
      ∀ j : ℕ,
        (biprod K L).X j ≅
          (ModuleCat.of R (Fin (r (j + 1)) → R) ⊞
            ModuleCat.of R (Fin (r j) → R)) := fun j ↦
    (HomologicalComplex.biprodXIso K L j) ≪≫
      biprod.mapIso (P.coord j) (Q.coord j) ≪≫
      biprodInterchange
        (ModuleCat.of R (Fin (P.r (j + 1)) → R))
        (ModuleCat.of R (Fin (P.r j) → R))
        (ModuleCat.of R (Fin (Q.r (j + 1)) → R))
        (ModuleCat.of R (Fin (Q.r j) → R)) ≪≫
      biprod.mapIso
        (standard_module_sum_iso_biprod (R := R) (P.r (j + 1)) (Q.r (j + 1))).symm
        (standard_module_sum_iso_biprod (R := R) (P.r j) (Q.r j)).symm
  refine ⟨{ r := r, coord := coord, differential := ?_ }⟩
  intro j
  -- The objectwise biproduct differential is the biproduct map of the two component
  -- differentials; the component normal forms then combine by `standard_biprod_projection_add`.
  dsimp [coord, r]
  simp only [Category.assoc]
  have hbiprod :
      biprod.map (P.coord (j + 1)).inv (Q.coord (j + 1)).inv ≫
          (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
          (K ⊞ L).d (j + 1) j ≫
          (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.map (P.coord j).hom (Q.coord j).hom =
      biprod.map (standard_biprod_projection (R := R) P.r j)
        (standard_biprod_projection (R := R) Q.r j) := by
    have hbiprodX :
        (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
            (K ⊞ L).d (j + 1) j ≫
            (HomologicalComplex.biprodXIso K L j).hom =
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
      calc
        (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
            (K ⊞ L).d (j + 1) j ≫
            (HomologicalComplex.biprodXIso K L j).hom =
          (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
            ((HomologicalComplex.biprodXIso K L (j + 1)).hom ≫
              biprod.map (K.d (j + 1) j) (L.d (j + 1) j)) := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦ (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫ f)
                (biprodXIso_differential_hom (R := R) (K := K) (L := L) j)
        _ = biprod.map (K.d (j + 1) j) (L.d (j + 1) j) := by
            simp
    calc
      biprod.map (P.coord (j + 1)).inv (Q.coord (j + 1)).inv ≫
          (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
          (K ⊞ L).d (j + 1) j ≫
          (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.map (P.coord j).hom (Q.coord j).hom =
        biprod.map (P.coord (j + 1)).inv (Q.coord (j + 1)).inv ≫
          ((HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
            (K ⊞ L).d (j + 1) j ≫
            (HomologicalComplex.biprodXIso K L j).hom) ≫
          biprod.map (P.coord j).hom (Q.coord j).hom := by
          simp only [Category.assoc]
      _ = biprod.map (P.coord (j + 1)).inv (Q.coord (j + 1)).inv ≫
          biprod.map (K.d (j + 1) j) (L.d (j + 1) j) ≫
          biprod.map (P.coord j).hom (Q.coord j).hom := by
          rw [hbiprodX]
      _ =
        biprod.map
          ((P.coord (j + 1)).inv ≫ K.d (j + 1) j ≫ (P.coord j).hom)
          ((Q.coord (j + 1)).inv ≫ L.d (j + 1) j ≫ (Q.coord j).hom) := by
          apply biprod.hom_ext <;> simp [Category.assoc]
      _ = biprod.map (standard_biprod_projection (R := R) P.r j)
          (standard_biprod_projection (R := R) Q.r j) := by
          rw [P.differential j, Q.differential j]
  calc
    biprod.map (standard_module_sum_iso_biprod (P.r (j + 1 + 1)) (Q.r (j + 1 + 1))).hom
          (standard_module_sum_iso_biprod (P.r (j + 1)) (Q.r (j + 1))).hom ≫
        (biprodInterchange (ModuleCat.of R (Fin (P.r (j + 1 + 1)) → R))
            (ModuleCat.of R (Fin (P.r (j + 1)) → R))
            (ModuleCat.of R (Fin (Q.r (j + 1 + 1)) → R))
            (ModuleCat.of R (Fin (Q.r (j + 1)) → R))).inv ≫
        (biprod.map (P.coord (j + 1)).inv (Q.coord (j + 1)).inv ≫
          (HomologicalComplex.biprodXIso K L (j + 1)).inv ≫
          (K ⊞ L).d (j + 1) j ≫
          (HomologicalComplex.biprodXIso K L j).hom ≫
          biprod.map (P.coord j).hom (Q.coord j).hom) ≫
        (biprodInterchange (ModuleCat.of R (Fin (P.r (j + 1)) → R))
            (ModuleCat.of R (Fin (P.r j) → R))
            (ModuleCat.of R (Fin (Q.r (j + 1)) → R))
            (ModuleCat.of R (Fin (Q.r j) → R))).hom ≫
        biprod.map (standard_module_sum_iso_biprod (P.r (j + 1)) (Q.r (j + 1))).inv
          (standard_module_sum_iso_biprod (P.r j) (Q.r j)).inv =
      biprod.map (standard_module_sum_iso_biprod (P.r (j + 1 + 1)) (Q.r (j + 1 + 1))).hom
          (standard_module_sum_iso_biprod (P.r (j + 1)) (Q.r (j + 1))).hom ≫
        (biprodInterchange (ModuleCat.of R (Fin (P.r (j + 1 + 1)) → R))
            (ModuleCat.of R (Fin (P.r (j + 1)) → R))
            (ModuleCat.of R (Fin (Q.r (j + 1 + 1)) → R))
            (ModuleCat.of R (Fin (Q.r (j + 1)) → R))).inv ≫
        biprod.map (standard_biprod_projection (R := R) P.r j)
          (standard_biprod_projection (R := R) Q.r j) ≫
        (biprodInterchange (ModuleCat.of R (Fin (P.r (j + 1)) → R))
            (ModuleCat.of R (Fin (P.r j) → R))
            (ModuleCat.of R (Fin (Q.r (j + 1)) → R))
            (ModuleCat.of R (Fin (Q.r j) → R))).hom ≫
        biprod.map (standard_module_sum_iso_biprod (P.r (j + 1)) (Q.r (j + 1))).inv
          (standard_module_sum_iso_biprod (P.r j) (Q.r j)).inv := by
        rw [hbiprod]
    _ =
      biprod.map (standard_module_sum_iso_biprod (P.r (j + 2)) (Q.r (j + 2))).hom
          (standard_module_sum_iso_biprod (P.r (j + 1)) (Q.r (j + 1))).hom ≫
        (biprodInterchange
          (ModuleCat.of R (Fin (P.r (j + 2)) → R))
          (ModuleCat.of R (Fin (P.r (j + 1)) → R))
          (ModuleCat.of R (Fin (Q.r (j + 2)) → R))
          (ModuleCat.of R (Fin (Q.r (j + 1)) → R))).inv ≫
        biprod.map (standard_biprod_projection (R := R) P.r j)
          (standard_biprod_projection (R := R) Q.r j) ≫
        (biprodInterchange
          (ModuleCat.of R (Fin (P.r (j + 1)) → R))
          (ModuleCat.of R (Fin (P.r j) → R))
          (ModuleCat.of R (Fin (Q.r (j + 1)) → R))
          (ModuleCat.of R (Fin (Q.r j) → R))).hom ≫
        biprod.map (standard_module_sum_iso_biprod (P.r (j + 1)) (Q.r (j + 1))).inv
          (standard_module_sum_iso_biprod (P.r j) (Q.r j)).inv := by
        simp
    _ = standard_biprod_projection (R := R) (fun k ↦ P.r k + Q.r k) j := by
        exact standard_biprod_projection_add (R := R) P.r Q.r j

/-- Helper for Chap10 Lemma 10 102 6: a direct sum of trivial complexes has a split-biproduct
projection profile. -/
private theorem biprodProjectionProfile_of_isDirectSumOfTrivialComplexes
    {K : ChainComplex (ModuleCat R) ℕ}
    (hK : IsDirectSumOfTrivialComplexes K) :
    Nonempty (BiprodProjectionProfile (R := R) K) := by
  -- Route correction: expose the structural induction frontier instead of hiding it in the
  -- final finite-free theorem. The already available generator and isomorphism cases close here.
  induction hK with
  | single₀ n =>
      -- The degree-zero generator uses the supported `0 ⊞ R^n` coordinate profile.
      exact nonempty_biprodProjectionProfile_single₀ (R := R) n
  | disk i n =>
      -- The two-term identity generator is now isolated as the canonical disk-profile helper.
      exact nonempty_biprodProjectionProfile_doubleIdentity (R := R) i n
  | identityDisk i =>
      -- The project identity disk is handled directly through its term and differential API.
      exact nonempty_biprodProjectionProfile_identityDiskComplex (R := R) i
  | biprod hK₁ hK₂ ih₁ ih₂ =>
      -- Biproduct closure consumes the two induction profiles.
      exact nonempty_biprodProjectionProfile_biprod (R := R) ih₁ ih₂
  | of_iso hK e ih =>
      -- Isomorphism invariance is already factored by `BiprodProjectionProfile.ofIso`.
      exact nonempty_biprodProjectionProfile_ofIso (R := R) ih e

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
    have hprofile : Nonempty (BiprodProjectionProfile (R := R) C.toChainComplex) :=
      biprodProjectionProfile_of_isDirectSumOfTrivialComplexes (R := R) hC
    obtain ⟨P⟩ := hprofile
    exact exists_standard_projection_profile_of_biprodProjectionProfile (R := R) (C := C) P

-- Proof sketch: identify the complex with a split exact sum of two-term identity complexes. In
-- that model each differential is a projection onto a free summand of rank equal to the relevant
-- alternating sum, adjacent projection ranks add to the rank of the middle term, and the maximal
-- minors include a unit so the associated ideal is the unit ideal.
/-- Chap10 Lemma 10 102 6: if the bounded finite free complex is isomorphic to a direct sum of trivial
two-term complexes, then each differential has the expected alternating rank formula, adjacent
differential ranks add to the rank of the middle term, and each ideal `I(φ_i)` is the unit ideal.
-/
@[stacks 00MW]
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
