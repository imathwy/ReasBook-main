import BauschkeLean.Chap22.Proposition_22_11
import BauschkeLean.Chap23.Proposition_23_35

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

-- Semantic recall note: `lean_leansearch` only surfaced generic monotonicity results, so the
-- chapter-local owners were verified from `Chap22.Proposition_22_11` and
-- `Chap23.Proposition_23_35`: the source hypotheses are expressed with
-- `A.IsUniformlyMonotone φ`, `A.IsStronglyMonotone β`, and the zero set owner `A.zeros`.

-- Source/core/bridge triage:
-- - `source-facing`: Corollary 23.37 asserts that `A.zeros` is a singleton under the Chapter 22
--   uniform or strong monotonicity hypotheses together with maximality.
-- - `core/canonical`: Proposition 23.35 gives the reusable zero-set uniqueness owner
--   `A.zeros.Subsingleton` once strict monotonicity is available.
-- - `bridge/view`: Proposition 22.11 supplies the surjectivity conclusion `A.range = Set.univ`,
--   and the zero-set existence step is the specialization `0 ∈ A.range ↔ A.zeros.Nonempty`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A uniformly monotone set-valued operator has a zero set with at most one point. -/
theorem zeros_subsingleton_of_isUniformlyMonotone
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (huniform : A.IsUniformlyMonotone φ) :
    A.zeros.Subsingleton :=
  zeros_subsingleton_of_isStrictlyMonotone huniform.isStrictlyMonotone

/-- A strongly monotone set-valued operator has a zero set with at most one point. -/
theorem zeros_subsingleton_of_isStronglyMonotone
    {A : SetValuedOperator H H} {β : ℝ} (hstrong : A.IsStronglyMonotone β) :
    A.zeros.Subsingleton :=
  zeros_subsingleton_of_isStrictlyMonotone hstrong.isStrictlyMonotone

variable [CompleteSpace H]

/-- Corollary 23.37 (1): let `A : H → 2^H` be maximally monotone and uniformly monotone with a
supercoercive modulus `φ`, meaning `φ t / t → +∞` as `t → +∞`. Then the zero set of `A` is a
singleton. -/
theorem exists_mem_zeros_eq_singleton_of_maximal_of_uniformlyMonotone_supercoerciveModulus
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (φ : NNReal → EReal)
    (huniform : A.IsUniformlyMonotone φ)
    (hsuper :
      Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
        Filter.atTop (nhds (⊤ : EReal))) :
    ∃ z ∈ A.zeros, A.zeros = {z} := by
  have hrange : A.range = Set.univ :=
    range_eq_univ_of_maximal_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone A hA
      (Or.inl ⟨φ, huniform, hsuper⟩)
  have hzero_range : (0 : H) ∈ A.range := by
    simp [hrange]
  have hzeros_nonempty : A.zeros.Nonempty := by
    rcases (mem_range_iff A 0).1 hzero_range with ⟨z, hz⟩
    exact ⟨z, by simpa using hz⟩
  rcases hzeros_nonempty with ⟨z, hz⟩
  exact ⟨z, hz, (zeros_subsingleton_of_isUniformlyMonotone huniform).eq_singleton_of_mem hz⟩

/-- Corollary 23.37 (2): let `A : H → 2^H` be maximally monotone and strongly monotone. Then the
zero set of `A` is a singleton. -/
theorem exists_mem_zeros_eq_singleton_of_maximal_of_isStronglyMonotone
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {β : ℝ}
    (hstrong : A.IsStronglyMonotone β) :
    ∃ z ∈ A.zeros, A.zeros = {z} := by
  have hrange : A.range = Set.univ :=
    range_eq_univ_of_maximal_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone A hA
      (Or.inr ⟨β, hstrong⟩)
  have hzero_range : (0 : H) ∈ A.range := by
    simp [hrange]
  have hzeros_nonempty : A.zeros.Nonempty := by
    rcases (mem_range_iff A 0).1 hzero_range with ⟨z, hz⟩
    exact ⟨z, by simpa using hz⟩
  rcases hzeros_nonempty with ⟨z, hz⟩
  exact ⟨z, hz, (zeros_subsingleton_of_isStronglyMonotone hstrong).eq_singleton_of_mem hz⟩

end SetValuedOperator
