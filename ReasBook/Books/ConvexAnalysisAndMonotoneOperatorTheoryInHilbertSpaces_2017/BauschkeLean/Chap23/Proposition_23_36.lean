import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap21.Corollary_21_23
import BauschkeLean.Chap21.Corollary_21_24
import BauschkeLean.Chap21.Corollary_21_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

-- Source/core/bridge triage:
-- - `source-facing`: Proposition 23.36 is the existence of a zero of a maximally monotone
--   operator under three Chapter 21 regularity hypotheses.
-- - `core/canonical`: the Chapter 21 owner results are
--   `range_eq_univ_iff_inverse_isLocallyBounded`,
--   `inverse_isLocallyBounded_of_maximal_of_tendsto_infEDist_zero`, and
--   `range_eq_univ_of_maximal_of_bounded_dom`.
-- - `bridge/view`: `A.zeros` is the `0`-fiber of `A`, so zero existence is the specialization
--   `0 ∈ A.range ↔ A.zeros.Nonempty`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 23.36 (1): if `A : H → 2^H` is maximally monotone and `A⁻¹` is locally bounded
everywhere on `H`, then the zero set `A.zeros` is nonempty. -/
theorem Maximal.zeros_nonempty_of_inverse_isLocallyBounded
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hloc : (A⁻¹).IsLocallyBounded) :
    A.zeros.Nonempty := by
  have hrange : A.range = Set.univ :=
    (range_eq_univ_iff_inverse_isLocallyBounded A hA).2 hloc
  have hzero_range : (0 : H) ∈ A.range := by
    simp [hrange]
  rcases (mem_range_iff A 0).1 hzero_range with ⟨x, hx⟩
  exact ⟨x, by simpa using hx⟩

/-- Proposition 23.36 (2): if `A : H → 2^H` is maximally monotone and
`Metric.infEDist (0 : H) (A x) → +∞` as `‖x‖ → +∞`, then the zero set `A.zeros` is nonempty. -/
theorem Maximal.zeros_nonempty_of_tendsto_infEDist_zero
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hinf :
      Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal))) :
    A.zeros.Nonempty := by
  exact Maximal.zeros_nonempty_of_inverse_isLocallyBounded hA
    (inverse_isLocallyBounded_of_maximal_of_tendsto_infEDist_zero A hA hinf)

/-- Proposition 23.36 (3): if `A : H → 2^H` is maximally monotone and `A.dom` is bounded, then
the zero set `A.zeros` is nonempty. -/
theorem Maximal.zeros_nonempty_of_bounded_dom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hdom_bounded : Bornology.IsBounded A.dom) :
    A.zeros.Nonempty := by
  exact Maximal.zeros_nonempty_of_inverse_isLocallyBounded hA
    ((range_eq_univ_iff_inverse_isLocallyBounded A hA).1
      (range_eq_univ_of_maximal_of_bounded_dom A hA hdom_bounded))

end SetValuedOperator
