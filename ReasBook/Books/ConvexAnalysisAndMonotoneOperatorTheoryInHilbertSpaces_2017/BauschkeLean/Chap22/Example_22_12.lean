import BauschkeLean.Chap20.Proposition_20_27
import BauschkeLean.Chap21.Corollary_21_24
import BauschkeLean.Chap22.Proposition_22_11

open scoped InnerProductSpace
open SetValuedOperator

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall: `lean_leansearch` only surfaced generic order-theoretic monotonicity lemmas,
-- so this file follows the local single-valued/ singleton-valued bridge from
-- `Chap20.Proposition_20_27` and the Chapter 22 monotonicity owners on `A.toSetValuedOperator`.

omit [CompleteSpace H] in
/-- Companion bridge for Example 22.12: if the singleton-valued operator associated with `A`
has full range and is strictly monotone, then the equation `A x = r` has exactly one solution. -/
theorem existsUnique_solution_of_strictlyMonotone_of_range_eq_univ
    (A : H → H) (hA_strict : A.toSetValuedOperator.IsStrictlyMonotone)
    (hA_range : A.toSetValuedOperator.range = Set.univ) (r : H) :
    ∃! x : H, A x = r := by
  have hA_range' : Set.range A = Set.univ := by
    simpa using hA_range
  have hr : r ∈ Set.range A := by
    rw [hA_range']
    simp
  rcases hr with ⟨x, rfl⟩
  refine ⟨x, rfl, ?_⟩
  intro y hy
  by_contra hxy
  have hxy' : x ≠ y := by
    exact fun h ↦ hxy h.symm
  have hpos : 0 < ⟪x - y, A x - A y⟫_ℝ :=
    hA_strict (by simp) (by simp) hxy'
  have hnot : ¬ 0 < ⟪x - y, A x - A y⟫_ℝ := by
    simp [hy]
  exact hnot hpos

/-- Example 22.12 (1): let `A : H → H` be hemicontinuous. If the associated singleton-valued
operator is strictly monotone and `‖A x‖ → +∞` as `‖x‖ → +∞`, then the equation `A x = r` has
exactly one solution. The ambient monotonicity hypothesis is absorbed by strict monotonicity. -/
theorem existsUnique_solution_of_monotone_hemicontinuous_of_strictlyMonotone_of_tendsto_norm
    (A : H → H) (hA_hemi : A.IsHemicontinuous) (r : H)
    (hA_strict : A.toSetValuedOperator.IsStrictlyMonotone)
    (hA_norm :
      Filter.Tendsto (fun x : H ↦ (‖A x‖ : EReal))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal))) :
    ∃! x : H, A x = r := by
  have hA_max :
      Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator :=
    toSetValuedOperator_isMaximallyMonotone_of_monotone_hemicontinuous A hA_strict.isMonotone
      hA_hemi
  have hA_range : A.toSetValuedOperator.range = Set.univ := by
    apply SetValuedOperator.range_eq_univ_of_maximal_of_tendsto_infEDist_zero
    · exact hA_max
    · have hA_infE :
          Filter.Tendsto
            (fun x : H ↦ ((Metric.infEDist (0 : H) (A.toSetValuedOperator x) : ENNReal) : EReal))
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds ((⊤ : ENNReal) : EReal)) := by
          have hrewrite :
              (fun x : H ↦
                ((Metric.infEDist (0 : H) (A.toSetValuedOperator x) : ENNReal) : EReal)) =
                fun x : H ↦ (‖A x‖ : EReal) := by
            funext x
            calc
              ((Metric.infEDist (0 : H) (A.toSetValuedOperator x) : ENNReal) : EReal)
                  = (↑‖A x‖ₑ : EReal) := by
                      simp [Function.toSetValuedOperator_apply, Metric.infEDist_singleton,
                        edist_nndist, enorm_eq_nnnorm]
              _ = ((ENNReal.ofReal ‖A x‖ : ENNReal) : EReal) := by
                    rw [ofReal_norm_eq_enorm]
              _ = (‖A x‖ : EReal) := by
                    rw [EReal.coe_ennreal_ofReal, max_eq_left (norm_nonneg _)]
          rw [hrewrite]
          exact hA_norm
      exact
        (EReal.tendsto_coe_ennreal :
          Filter.Tendsto
              (fun x : H ↦
                ((Metric.infEDist (0 : H) (A.toSetValuedOperator x) : ENNReal) : EReal))
              (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds ((⊤ : ENNReal) : EReal)) ↔
            Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A.toSetValuedOperator x))
              (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal))).1 hA_infE
  exact existsUnique_solution_of_strictlyMonotone_of_range_eq_univ A hA_strict hA_range r

/-- Example 22.12 (2): let `A : H → H` be hemicontinuous. If the associated singleton-valued
operator is uniformly monotone with a supercoercive modulus, then the equation `A x = r` has
exactly one solution. The ambient monotonicity hypothesis is absorbed by uniform monotonicity. -/
theorem existsUnique_solution_of_monotone_hemicontinuous_of_uniformlyMonotone_supercoerciveModulus
    (A : H → H) (hA_hemi : A.IsHemicontinuous) (r : H) (φ : NNReal → EReal)
    (hA_uniform : A.toSetValuedOperator.IsUniformlyMonotone φ)
    (hφ_super :
      Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
        Filter.atTop (nhds (⊤ : EReal))) :
    ∃! x : H, A x = r := by
  have hA_max :
      Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator :=
    toSetValuedOperator_isMaximallyMonotone_of_monotone_hemicontinuous A hA_uniform.isMonotone
      hA_hemi
  have hA_range : A.toSetValuedOperator.range = Set.univ := by
    exact
      range_eq_univ_of_maximal_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone
        A.toSetValuedOperator hA_max (Or.inl ⟨φ, hA_uniform, hφ_super⟩)
  exact existsUnique_solution_of_strictlyMonotone_of_range_eq_univ A
    hA_uniform.isStrictlyMonotone hA_range r

/-- Example 22.12 (3): let `A : H → H` be hemicontinuous. If the associated singleton-valued
operator is strongly monotone, then the equation `A x = r` has exactly one solution. The ambient
monotonicity hypothesis is absorbed by strong monotonicity. -/
theorem existsUnique_solution_of_monotone_hemicontinuous_of_stronglyMonotone
    (A : H → H) (hA_hemi : A.IsHemicontinuous) (r : H) {β : ℝ}
    (hA_strong : A.toSetValuedOperator.IsStronglyMonotone β) :
    ∃! x : H, A x = r := by
  have hA_max :
      Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator :=
    toSetValuedOperator_isMaximallyMonotone_of_monotone_hemicontinuous A hA_strong.isMonotone
      hA_hemi
  have hA_range : A.toSetValuedOperator.range = Set.univ := by
    exact
      range_eq_univ_of_maximal_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone
        A.toSetValuedOperator hA_max (Or.inr ⟨β, hA_strong⟩)
  exact existsUnique_solution_of_strictlyMonotone_of_range_eq_univ A
    hA_strong.isStrictlyMonotone hA_range r

end Function
