import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_157_1
import stacks_proof.stacks_project.Chap10.Definition_10_102_5

universe u

open RingTheory

namespace FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- Helper for Chap10 Proposition 10 102 9: transposing a matrix does not change its fixed-size
minor ideal. -/
lemma minorIdeal_transpose_eq {ι κ : Type*}
    (r : ℕ) (A : Matrix ι κ R) :
    Matrix.minorIdeal r A.transpose = Matrix.minorIdeal r A := by
  classical
  refine le_antisymm ?_ ?_
  · -- Proof comment: every transpose-side minor is the transpose of an original-side minor.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hsub :
        A.transpose.submatrix e₁ e₂ = (A.submatrix e₂ e₁).transpose := by
      ext i j
      rfl
    change Matrix.det (A.transpose.submatrix e₁ e₂) ∈ Matrix.minorIdeal r A
    rw [hsub, Matrix.det_transpose]
    exact Matrix.det_submatrix_mem_minorIdeal r A e₂ e₁
  · -- Proof comment: apply the same transpose argument in the reverse direction.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    have hsub :
        A.submatrix e₁ e₂ = (A.transpose.submatrix e₂ e₁).transpose := by
      ext i j
      rfl
    change Matrix.det (A.submatrix e₁ e₂) ∈ Matrix.minorIdeal r A.transpose
    rw [hsub, Matrix.det_transpose]
    exact Matrix.det_submatrix_mem_minorIdeal r A.transpose e₂ e₁

/-- Helper for Chap10 Proposition 10 102 9: right multiplication by a square matrix does not
enlarge a fixed-size minor ideal. -/
lemma minorIdeal_mul_right_le {ι κ : Type*}
    [Fintype κ]
    (r : ℕ) (A : Matrix ι κ R) (C : Matrix κ κ R) :
    Matrix.minorIdeal r (A * C) ≤ Matrix.minorIdeal r A := by
  classical
  have hleft :
      Matrix.minorIdeal r ((A * C).transpose) ≤ Matrix.minorIdeal r A.transpose := by
    -- Proof comment: transpose converts right multiplication into the left-multiplication owner
    -- lemma that already exists in mathlib.
    simpa [Matrix.transpose_mul] using
      (Matrix.minorIdeal_mul_left_le (R := R) (r := r) C.transpose A.transpose)
  calc
    Matrix.minorIdeal r (A * C) = Matrix.minorIdeal r ((A * C).transpose) := by
      symm
      exact minorIdeal_transpose_eq (R := R) (r := r) (A := A * C)
    _ ≤ Matrix.minorIdeal r A.transpose := hleft
    _ = Matrix.minorIdeal r A := minorIdeal_transpose_eq (R := R) (r := r) (A := A)

/-- Helper for Chap10 Proposition 10 102 9: changing source and target coordinates by linear
automorphisms preserves the exterior rank. -/
lemma exteriorRank_eq_of_conj {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.exteriorRank
        (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) =
      LinearMap.exteriorRank φ := by
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
      -- Proof comment: expand the exterior-power functor across the conjugated composition.
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
        -- Proof comment: cancel the two inverse coordinate changes to recover the original map.
        ext x
        simp
      have hmaprecover :
          exteriorPower.map r φ =
            exteriorPower.map r eTarget.symm.toLinearMap ∘ₗ
              exteriorPower.map r
                (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ∘ₗ
              exteriorPower.map r eSource.toLinearMap := by
        have hmap := congrArg (exteriorPower.map r) hrecover
        simpa [exteriorPower.map_comp] using hmap
      calc
        exteriorPower.map r φ =
            exteriorPower.map r eTarget.symm.toLinearMap ∘ₗ
              exteriorPower.map r
                (eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) ∘ₗ
              exteriorPower.map r eSource.toLinearMap := hmaprecover
        _ = 0 := by
              simp [hconj]
  -- Proof comment: `Nat.findGreatest` sees the same predicate after the funext comparison.
  unfold LinearMap.exteriorRank
  rw [hpred]

/-- Helper for Chap10 Proposition 10 102 9: changing source and target coordinates by linear
automorphisms preserves the rank-minor ideal. -/
lemma rankMinorIdeal_eq_of_linearEquiv_conj {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    I(eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)) = I(φ) := by
  classical
  let f : (Fin m → R) →ₗ[R] (Fin n → R) :=
    eTarget.toLinearMap.comp (φ.comp eSource.symm.toLinearMap)
  let r := LinearMap.exteriorRank φ
  let sourceBasis := Pi.basisFun R (Fin m)
  let targetBasis := Pi.basisFun R (Fin n)
  have hrank : LinearMap.exteriorRank f = r := by
    -- Proof comment: first align the fixed minor size using exterior-rank invariance.
    simpa [f, r] using
      exteriorRank_eq_of_conj (R := R) φ eSource eTarget
  have hf_matrix :
      LinearMap.toMatrix sourceBasis targetBasis f =
        LinearMap.toMatrix targetBasis targetBasis eTarget.toLinearMap *
          (LinearMap.toMatrix sourceBasis targetBasis φ *
            LinearMap.toMatrix sourceBasis sourceBasis eSource.symm.toLinearMap) := by
    -- Proof comment: the conjugated linear map becomes left and right matrix multiplication.
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
    -- Proof comment: the reverse comparison uses the recovered expression for `φ`.
    ext x
    simp [f]
  have hφ_matrix :
      LinearMap.toMatrix sourceBasis targetBasis φ =
        LinearMap.toMatrix targetBasis targetBasis eTarget.symm.toLinearMap *
          (LinearMap.toMatrix sourceBasis targetBasis f *
            LinearMap.toMatrix sourceBasis sourceBasis eSource.toLinearMap) := by
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
  rw [LinearMap.rankMinorIdeal, LinearMap.rankMinorIdeal, hrank]
  exact le_antisymm hleft hright

/-- Helper for Chap10 Proposition 10 102 9: exterior rank is invariant under source and target
linear equivalences even when the finite coordinate sizes are written differently. -/
lemma exteriorRank_eq_of_linearEquiv_conj [Nontrivial R] {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R)) :
    LinearMap.exteriorRank (eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) =
      LinearMap.exteriorRank φ := by
  have hm : m' = m := InvariantBasisNumber.eq_of_fin_equiv eSource
  have hn : n = n' := InvariantBasisNumber.eq_of_fin_equiv eTarget
  cases hm
  cases hn
  simpa using
    exteriorRank_eq_of_conj (R := R) φ eSource.symm eTarget

/-- Helper for Chap10 Proposition 10 102 9: the rank-minor ideal is invariant under source and
target linear equivalences even when the finite coordinate sizes are written differently. -/
lemma rankMinorIdeal_eq_of_linearEquiv_conj' [Nontrivial R] {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R)) :
    I(eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) = I(φ) := by
  have hm : m' = m := InvariantBasisNumber.eq_of_fin_equiv eSource
  have hn : n = n' := InvariantBasisNumber.eq_of_fin_equiv eTarget
  cases hm
  cases hn
  simpa using
    rankMinorIdeal_eq_of_linearEquiv_conj (R := R) φ eSource.symm eTarget

/-- Helper for Chap10 Proposition 10 102 9: a single Buchsbaum-Eisenbud criterion clause is
invariant under source and target coordinate changes. -/
lemma criterionClause_iff_of_linearEquiv_conj [Nontrivial R]
    {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R))
    {a : ℤ} {d : WithTop ℕ} :
    ((LinearMap.exteriorRank (eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) : ℤ) = a ∧
        d ≤ (I(eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap))).depth R) ↔
      ((LinearMap.exteriorRank φ : ℤ) = a ∧ d ≤ (I(φ)).depth R) := by
  -- Proof comment: both pieces of the criterion are owner invariants under linear-equivalence
  -- conjugation, so the clause transports verbatim.
  rw [rankMinorIdeal_eq_of_linearEquiv_conj' (R := R) φ eSource eTarget,
    exteriorRank_eq_of_linearEquiv_conj (R := R) φ eSource eTarget]

end FiniteFreeComplex
