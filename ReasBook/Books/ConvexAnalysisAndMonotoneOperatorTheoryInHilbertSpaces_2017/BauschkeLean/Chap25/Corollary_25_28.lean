import BauschkeLean.Chap22.Proposition_22_11
import BauschkeLean.Chap23.Corollary_23_37
import BauschkeLean.Chap25.Corollary_25_27
import BauschkeLean.Chap25.Example_25_15

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

-- Semantic recall: `lean_leansearch` only surfaced unrelated order-theoretic `StrictMono*`
-- lemmas, so this file uses the verified local Chapter 22/23/25 owners
-- `IsUniformlyMonotone`, `IsThreeStarMonotone`, `Maximal IsMonotone`, `.range`, and `.zeros`,
-- together with the predecessor surjectivity theorems in `Corollary_25_27`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Corollary 25.28 (1): the surjectivity conclusion already follows from the weaker hypotheses
actually used here: `A` is monotone, `B` and `A + B` are maximally monotone, `B` is uniformly
monotone with modulus `φ : NNReal → EReal`, this modulus is supercoercive in the source radial
form `fun r : ℝ ↦ φ ‖r‖₊`, and either `A` is `3*` monotone or `A.dom ⊆ B.dom`. Then
`ran (A + B) = H`, formalized as `(A + B).range = Set.univ`. -/
theorem range_add_eq_univ_of_uniformlyMonotoneSupercoercive_of_threeStar_or_dom_subset
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone)
    (hB_max : Maximal IsMonotone B) (hAB_max : Maximal IsMonotone (A + B))
    {φ : NNReal → EReal} (hB_uniform : B.IsUniformlyMonotone φ)
    (hφ_super : ERealFunction.Supercoercive fun r : ℝ ↦ φ ‖r‖₊)
    (hreg : A.IsThreeStarMonotone ∨ A.dom ⊆ B.dom) :
    (A + B).range = Set.univ := by
  have hφ_tendsto :
      Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
        Filter.atTop (nhds (⊤ : EReal)) :=
    supercoerciveRadialModulus_tendsto_div_atTop hφ_super
  have hB_range : B.range = Set.univ :=
    range_eq_univ_of_maximal_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone
      B hB_max (Or.inl ⟨φ, hB_uniform, hφ_tendsto⟩)
  have hB_threeStar : B.IsThreeStarMonotone :=
    hB_uniform.isThreeStarMonotone_of_supercoercive_modulus hφ_super
  rcases hreg with hA_threeStar | hdom
  · exact range_add_eq_univ_of_isThreeStarMonotone
      hA_mono (Maximal.isMonotone hB_max)
      hAB_max (Or.inr hB_range) hA_threeStar hB_threeStar
  · exact range_add_eq_univ_of_dom_subset_and_isThreeStarMonotone
      hA_mono (Maximal.isMonotone hB_max)
      hAB_max (Or.inr hB_range) hdom hB_threeStar

/-- Corollary 25.28 (2): the singleton-zero conclusion for `A + B` already follows from the
weaker hypotheses actually used here: `A` is monotone, `A + B` is maximally monotone, and `B` is
uniformly monotone with a supercoercive radial modulus `φ`. This is recorded in the reusable
Chapter 23 surface as the existence of `z ∈ (A + B).zeros` with `(A + B).zeros = {z}`. -/
theorem exists_mem_zeros_eq_singleton_of_monotone_of_add_maximal_of_uniformlyMonotoneSupercoercive
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B))
    {φ : NNReal → EReal} (hB_uniform : B.IsUniformlyMonotone φ)
    (hφ_super : ERealFunction.Supercoercive fun r : ℝ ↦ φ ‖r‖₊) :
    ∃ z ∈ (A + B).zeros, (A + B).zeros = {z} := by
  have hφ_tendsto :
      Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
        Filter.atTop (nhds (⊤ : EReal)) :=
    supercoerciveRadialModulus_tendsto_div_atTop hφ_super
  have hsum_uniform : (A + B).IsUniformlyMonotone φ := by
    refine ⟨hB_uniform.modulusMonotone, hB_uniform.modulus_eq_zero_iff, ?_⟩
    intro x u y v hu hv
    rcases Set.mem_add.mp hu with ⟨uA, huA, uB, huB, rfl⟩
    rcases Set.mem_add.mp hv with ⟨vA, hvA, vB, hvB, rfl⟩
    have hA_pair : 0 ≤ ⟪x - y, uA - vA⟫_ℝ :=
      hA_mono huA hvA
    have hB_pair :
        φ ‖x - y‖₊ ≤ (⟪x - y, uB - vB⟫_ℝ : EReal) :=
      hB_uniform.ineq huB hvB
    have hsum_pair :
        (⟪x - y, uB - vB⟫_ℝ : EReal) ≤
          (⟪x - y, (uA + uB) - (vA + vB)⟫_ℝ : EReal) := by
      have hsum :
          ⟪x - y, (uA + uB) - (vA + vB)⟫_ℝ =
            ⟪x - y, uA - vA⟫_ℝ + ⟪x - y, uB - vB⟫_ℝ := by
        have hdecomp : (uA + uB) - (vA + vB) = (uA - vA) + (uB - vB) := by
          abel_nf
        rw [hdecomp, inner_add_right]
      have hle :
          ⟪x - y, uB - vB⟫_ℝ ≤ ⟪x - y, (uA + uB) - (vA + vB)⟫_ℝ := by
        rw [hsum]
        linarith
      exact_mod_cast hle
    exact le_trans hB_pair hsum_pair
  exact exists_mem_zeros_eq_singleton_of_maximal_of_uniformlyMonotone_supercoerciveModulus
    (A + B) hAB_max φ hsum_uniform hφ_tendsto

end SetValuedOperator
