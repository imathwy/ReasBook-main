import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix RealInnerProductSpace
open LinearConstraintRelation

noncomputable section

section

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Rm" => Fin m → ℝ
local notation "Rn" => Fin n → ℝ
set_option linter.style.longLine false in
local notation "xorMixedAlternative" =>
  xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate_innerProduct

/-!
Source/core/bridge triage for this item.

- `core/canonical`: the owner abstractions are the mixed-constraint solution-set API
  `LinearConstraintRelation.feasibleSet`, the relation owner
  `LinearConstraintRelation.eqOn`, and the mixed equality/inequality alternative,
  here used through the inner-product bridge theorem from `Text_22_3_5`.
- `bridge/view`: this file is the matrix specialization of that owner theorem, obtained by encoding
  the constraints `x_j ≥ 0` as the weak inequalities `⟪-e_j, x⟫ ≤ 0` and the equations
  `Ax = a` as row equalities. The bridge uses the disjoint-union index `Fin n ⊕ Fin m`, so the
  nonnegativity and equality blocks remain separate without arithmetic index bookkeeping.

Domain-style sampling used here:
- `LinearConstraintRelation.feasibleSet`;
- `mixed_linear_constraint_solution_set_nonempty_iff`;
- the inner-product mixed-alternative theorem from `Text_22_3_5`;
- `row_inner_eq_mulVec` and `rowCombination_toLp_eq_mulVec_transpose`.

Primitive data vs derived API:
- primitive inputs: a real matrix `A : ℝ^{m×n}` and a right-hand side vector `a : ℝ^m`;
- derived API: the exclusive alternative between solvability of the nonnegative equality system
  and solvability of the transposed strict-separation certificate. No separate public primal or
  dual wrapper predicates are introduced.

Layer target: `bridge/view`, since the source statement is a direct matrix
reformulation of the chapter owner theorem for mixed weak inequalities and
equalities.
-/

private def constraintVec
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin n ⊕ Fin m → E :=
  Sum.elim
    (fun j : Fin n ↦ EuclideanSpace.single j (-1 : ℝ))
    (fun i : Fin m ↦ WithLp.toLp 2 (A i))

private def constraintScalar (a : Rm) : Fin n ⊕ Fin m → ℝ :=
  Sum.elim (fun _ : Fin n ↦ (0 : ℝ)) a

private def eqIndices : Set (Fin n ⊕ Fin m) :=
  Set.range Sum.inr

private theorem inl_not_mem_eqIndices (j : Fin n) :
    Sum.inl j ∉ (eqIndices : Set (Fin n ⊕ Fin m)) := by
  rintro ⟨i, hi⟩
  cases hi

private theorem inr_mem_eqIndices (i : Fin m) :
    Sum.inr i ∈ (eqIndices : Set (Fin n ⊕ Fin m)) :=
  ⟨i, rfl⟩

private theorem inner_negSingle_eq_neg_coord (j : Fin n) (x : E) :
    ⟪EuclideanSpace.single j (-1 : ℝ), x⟫ = -x j := by
  simpa using EuclideanSpace.inner_single_left j (-1 : ℝ) x

private theorem sum_negSingle_eq (v : Rn) :
    (∑ j : Fin n, (-v j) • EuclideanSpace.single j (-1 : ℝ) : E) = WithLp.toLp 2 v := by
  ext j
  simp [EuclideanSpace.single, Pi.single_apply]

private theorem inner_negSingle_toLp_eq_neg_coord (j : Fin n) (x : Rn) :
    ⟪EuclideanSpace.single j (-1 : ℝ), WithLp.toLp 2 x⟫ = -x j := by
  simpa using inner_negSingle_eq_neg_coord j (WithLp.toLp 2 x)

private theorem row_inner_eq_mulVec
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (x : E) :
    ⟪WithLp.toLp 2 (A i), x⟫ = (A *ᵥ x) i := by
  have hdot : ⟪WithLp.toLp 2 (A i), x⟫ = A i ⬝ᵥ x := by
    simpa [dotProduct, mul_comm] using
      EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 (A i)) x
  simpa [Matrix.mulVec] using hdot

private theorem row_inner_toLp_eq_mulVec
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (x : Rn) :
    ⟪WithLp.toLp 2 (A i), WithLp.toLp 2 x⟫ = (A *ᵥ x) i := by
  simpa using row_inner_eq_mulVec A i (WithLp.toLp 2 x)

private theorem rowCombination_eq_mulVec_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Rm) :
    (∑ i : Fin m, w i • A i : Rn) = Aᵀ *ᵥ w := by
  simpa [Matrix.mulVec_transpose] using (Matrix.vecMul_eq_sum w A).symm

private theorem rowCombination_toLp_eq_mulVec_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Rm) :
    (∑ i : Fin m, w i • WithLp.toLp 2 (A i) : E) = WithLp.toLp 2 (Aᵀ *ᵥ w) := by
  simpa using congrArg (WithLp.toLp 2) (rowCombination_eq_mulVec_transpose A w)

local notation "solutionSet[" A "; " a "]" =>
  (feasibleSet (eqOn eqIndices) (constraintVec A) (constraintScalar a) : Set E)

/-- Primal owner for Text 22.3.8: nonnegative vectors solving `A *ᵥ x = a`. -/
def nonnegativeEqualityPrimal
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) : Set Rn :=
  {x | 0 ≤ x ∧ A *ᵥ x = a}

/-- Dual owner for Text 22.3.8: transpose certificates with nonpositive `Aᵀ *ᵥ w`
and positive pairing `a ⬝ᵥ w`. -/
def nonpositiveDualCertificate
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) : Set Rm :=
  {w | Aᵀ *ᵥ w ≤ 0 ∧ 0 < a ⬝ᵥ w}

private theorem nonnegative_equality_solutionSet_nonempty_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) :
    (solutionSet[A; a]).Nonempty ↔
      (nonnegativeEqualityPrimal A a).Nonempty := by
  rw [mixed_linear_constraint_solution_set_nonempty_iff]
  constructor
  · rintro ⟨x, hxle, hxeq⟩
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj :
          ⟪constraintVec A (Sum.inl j : Fin n ⊕ Fin m), x⟫ ≤
            constraintScalar a (Sum.inl j : Fin n ⊕ Fin m) :=
        by
          simpa [real_inner_comm] using
            hxle (Sum.inl j : Fin n ⊕ Fin m) (inl_not_mem_eqIndices j)
      have hj0 : -x j ≤ 0 := by
        simpa [constraintVec, constraintScalar, inner_negSingle_eq_neg_coord] using hj
      exact neg_nonpos.mp hj0
    · ext i
      have hi :
          ⟪constraintVec A (Sum.inr i : Fin n ⊕ Fin m), x⟫ =
            constraintScalar a (Sum.inr i : Fin n ⊕ Fin m) :=
        by
          simpa [real_inner_comm] using
            hxeq (Sum.inr i : Fin n ⊕ Fin m) (inr_mem_eqIndices i)
      simpa [constraintVec, constraintScalar, row_inner_eq_mulVec A i x] using hi
  · rintro ⟨x, hx_nonneg, hx_eq⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · intro i hi
      cases i with
      | inl j =>
          have hj0 : -x j ≤ 0 := neg_nonpos.mpr (hx_nonneg j)
          change ⟪WithLp.toLp 2 x, EuclideanSpace.single j (-1 : ℝ)⟫ ≤ (0 : ℝ)
          rw [real_inner_comm, inner_negSingle_toLp_eq_neg_coord]
          exact hj0
      | inr i =>
          exfalso
          exact hi (inr_mem_eqIndices i)
    · intro i hi
      cases i with
      | inl j =>
          exfalso
          exact inl_not_mem_eqIndices j hi
      | inr i =>
          simpa [real_inner_comm, constraintVec, constraintScalar,
            row_inner_toLp_eq_mulVec A i x] using
            congrFun hx_eq i

private theorem nonnegative_equality_certificate_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) :
    (∃ u : Fin n ⊕ Fin m → ℝ,
      (∀ i : Fin n ⊕ Fin m, i ∉ eqIndices → 0 ≤ u i) ∧
        (∑ i : Fin n ⊕ Fin m, u i • constraintVec A i = 0) ∧
          (∑ i : Fin n ⊕ Fin m, u i * constraintScalar a i) < 0) ↔
      (nonpositiveDualCertificate A a).Nonempty := by
  constructor
  · rintro ⟨u, hu_nonneg, hu_sum, hu_scalar⟩
    let w : Rm := fun i ↦ -u (Sum.inr i)
    refine ⟨w, ?_, ?_⟩
    · intro j
      have hcoord :
          -u (Sum.inl j) + ∑ i : Fin m, A i j * u (Sum.inr i) = 0 := by
        have hsingle :
            ∑ x : Fin n, u (Sum.inl x) * ((Pi.single x (-1 : ℝ) : Fin n → ℝ) j) =
              -u (Sum.inl j) := by
          simp [Pi.single_apply]
        have h := congrArg (fun v : E ↦ v j) hu_sum
        simpa [constraintVec, Fintype.sum_sum_type, hsingle, mul_comm] using h
      have huj : 0 ≤ u (Sum.inl j) :=
        hu_nonneg (Sum.inl j) (inl_not_mem_eqIndices j)
      have hmulVec : (Aᵀ *ᵥ w) j = -u (Sum.inl j) := by
        have hcoord' : ∑ i : Fin m, A i j * u (Sum.inr i) = u (Sum.inl j) := by
          linarith
        calc
          (Aᵀ *ᵥ w) j = ∑ i : Fin m, A i j * (-u (Sum.inr i)) := by
            simp [Matrix.mulVec, dotProduct, w]
          _ = -∑ i : Fin m, A i j * u (Sum.inr i) := by
              simp_rw [mul_neg]
              rw [Finset.sum_neg_distrib]
          _ = -u (Sum.inl j) := by rw [hcoord']
      simpa [hmulVec] using neg_nonpos.mpr huj
    · simpa [w, constraintScalar, Fintype.sum_sum_type, dotProduct, mul_comm] using
        (neg_pos.mpr hu_scalar)
  · rintro ⟨w, hw_nonpos, hw_scalar⟩
    let u : Fin n ⊕ Fin m → ℝ :=
      Sum.elim (fun j : Fin n ↦ -(Aᵀ *ᵥ w) j) (fun i : Fin m ↦ -w i)
    refine ⟨u, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | inl j =>
          simpa [u] using neg_nonneg.mpr (hw_nonpos j)
      | inr i =>
          exfalso
          exact hi (inr_mem_eqIndices i)
    · calc
        ∑ i : Fin n ⊕ Fin m, u i • constraintVec A i
            = ∑ j : Fin n, (-(Aᵀ *ᵥ w) j) • EuclideanSpace.single j (-1 : ℝ) +
                ∑ i : Fin m, (-w i) • WithLp.toLp 2 (A i) := by
                  simp [u, constraintVec, Fintype.sum_sum_type]
        _ = WithLp.toLp 2 (Aᵀ *ᵥ w) - ∑ i : Fin m, w i • WithLp.toLp 2 (A i) := by
              rw [sum_negSingle_eq]
              simp_rw [neg_smul]
              rw [Finset.sum_neg_distrib]
              simp [sub_eq_add_neg]
        _ = 0 := by
              rw [rowCombination_toLp_eq_mulVec_transpose A w]
              simp
    · simpa [u, constraintScalar, Fintype.sum_sum_type, dotProduct, mul_comm] using
        (neg_neg_iff_pos.mpr hw_scalar)

-- Proof sketch: encode `x_j ≥ 0` as `⟪-e_j, x⟫ ≤ 0` on the `Fin n` summand and `Ax = a`
-- as equality constraints on the `Fin m` summand. Apply the mixed equality/inequality
-- alternative from `Text_22_3_5`. In the multiplier alternative, the first-block coefficients are
-- exactly `-(Aᵀ *ᵥ w)`, so the nonnegativity condition on those coefficients
-- is equivalent to `Aᵀ *ᵥ w ≤ 0`; the scalar inequality becomes
-- `0 < a ⬝ᵥ w` after negating the equality-block multipliers.
/-- Text 22.3.8: for a real matrix `A` and vector `a`, exactly one of the systems
`x ≥ 0`, `Ax = a` and `Aᵀ w ≤ 0`, `⟪a, w⟫ > 0` has a solution. -/
theorem xor_nonnegative_equality_primal_solution_or_dual_nonpositive_certificate
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) :
    Xor'
      (nonnegativeEqualityPrimal A a).Nonempty
      (nonpositiveDualCertificate A a).Nonempty := by
  rcases
    xorMixedAlternative (constraintVec A)
      (constraintScalar a)
      eqIndices with h | h
  · left
    exact ⟨(nonnegative_equality_solutionSet_nonempty_iff A a).mp h.1, fun hw ↦
      h.2 ((nonnegative_equality_certificate_iff A a).mpr hw)⟩
  · right
    exact ⟨(nonnegative_equality_certificate_iff A a).mp h.1, fun hx ↦
      h.2 ((nonnegative_equality_solutionSet_nonempty_iff A a).mpr hx)⟩
end
