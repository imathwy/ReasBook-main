import Mathlib
import BauschkeLean.Chap02.Lemma_2_14
import BauschkeLean.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

universe u v

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- `source-facing`: Proposition 20.14 is the textbook equivalence between monotonicity, the finite
-- Jensen inequality on `gra A`, and the corresponding two-point convexity statement on `gra A`.
-- `core/canonical`: Lemma 2.14 is the owner identity turning the Jensen defect of
-- `p ↦ ⟪p.1, p.2⟫_ℝ` into a weighted sum of monotonicity pairings.
-- `bridge/view`: a `ConvexOn` statement on `convexHull ℝ (gra A)` is a useful ambient reformulation
-- via `ConvexOn.map_sum_le`, but it is companion-only and not the main source-facing theorem.
-- Proof sketch: Lemma 2.14 rewrites the finite Jensen defect of the pairing on graph points as a
-- half-weighted sum of terms `⟪x i - x j, u i - u j⟫_ℝ`. Clause `(i)` makes each summand
-- nonnegative, yielding clause `(ii)`. The two-point statement in clause `(iii)` is the special
-- case of clause `(ii)`, and expanding its defect gives
-- `-α * (1 - α) * ⟪x - y, u - v⟫_ℝ`, recovering monotonicity.
/-- Proposition 20.14: for a set-valued operator `A`, the following are equivalent:
(i) `A` is monotone; (ii) the pairing `F(x, u) = ⟪x, u⟫_ℝ` satisfies the finite Jensen inequality
on graph points of `A`; (iii) `F` is convex along two-point combinations of graph points of `A`. -/
theorem tfae_isMonotone_graph_pairing_convexity (A : SetValuedOperator H H) :
    List.TFAE
      [A.IsMonotone,
        (∀ {ι : Type v} (s : Finset ι) (α : ι → ℝ) (p : ι → gra A),
          (∀ i ∈ s, 0 ≤ α i) →
            (∑ i ∈ s, α i) = 1 →
              ⟪(∑ i ∈ s, α i • (p i : H × H)).1, (∑ i ∈ s, α i • (p i : H × H)).2⟫_ℝ ≤
                ∑ i ∈ s, α i * ⟪(p i : H × H).1, (p i : H × H).2⟫_ℝ),
        (∀ ⦃p q : gra A⦄ ⦃α : ℝ⦄, 0 < α → α < 1 →
          ⟪(α • (p : H × H) + (1 - α) • (q : H × H)).1,
            (α • (p : H × H) + (1 - α) • (q : H × H)).2⟫_ℝ ≤
            α * ⟪(p : H × H).1, (p : H × H).2⟫_ℝ +
              (1 - α) * ⟪(q : H × H).1, (q : H × H).2⟫_ℝ)] := by
  tfae_have 1 → 2 := by
    intro hmono ι s α p
    classical
    have hsum_fst :
        (∑ i ∈ s, α i • (p i : H × H)).1 = ∑ i ∈ s, α i • (p i : H × H).1 := by
      induction s using Finset.induction_on with
      | empty =>
          simp
      | @insert i s hi hs =>
          simp [Finset.sum_insert, hi, hs]
    have hsum_snd :
        (∑ i ∈ s, α i • (p i : H × H)).2 = ∑ i ∈ s, α i • (p i : H × H).2 := by
      clear hsum_fst
      induction s using Finset.induction_on with
      | empty =>
          simp
      | @insert i s hi hs =>
          simp [Finset.sum_insert, hi, hs]
    intro hα_nonneg hα_sum
    -- Rewrite the Jensen defect by Lemma 2.14 and show the correction term is nonnegative.
    have hmono_graph := (SetValuedOperator.isMonotone_iff A).1 hmono
    have hidentity :
        ⟪(∑ i ∈ s, α i • (p i : H × H)).1, (∑ i ∈ s, α i • (p i : H × H)).2⟫_ℝ +
            (1 / 2 : ℝ) *
              ∑ i ∈ s, ∑ j ∈ s,
                α i * α j * ⟪(p i : H × H).1 - (p j : H × H).1,
                  (p i : H × H).2 - (p j : H × H).2⟫_ℝ =
          ∑ i ∈ s, α i * ⟪(p i : H × H).1, (p i : H × H).2⟫_ℝ := by
      rw [hsum_fst, hsum_snd]
      simpa using
        weighted_inner_eq_sum_inner_add_half_pairwise s
          (fun i ↦ (p i : H × H).1) (fun i ↦ (p i : H × H).2) α hα_sum
    have hcorr_nonneg :
        0 ≤
          (1 / 2 : ℝ) *
            ∑ i ∈ s, ∑ j ∈ s,
              α i * α j * ⟪(p i : H × H).1 - (p j : H × H).1,
                (p i : H × H).2 - (p j : H × H).2⟫_ℝ := by
      refine mul_nonneg (by norm_num) ?_
      refine Finset.sum_nonneg ?_
      intro i hi
      refine Finset.sum_nonneg ?_
      intro j hj
      have hpi : (p i : H × H).2 ∈ A (p i : H × H).1 := by
        exact (p i).property
      have hpj : (p j : H × H).2 ∈ A (p j : H × H).1 := by
        exact (p j).property
      exact mul_nonneg
        (mul_nonneg (hα_nonneg i hi) (hα_nonneg j hj))
        (hmono_graph hpi hpj)
    linarith
  tfae_have 2 → 3 := by
    intro hfinite p q α hα0 hα1
    let ι := ULift.{v} Unit ⊕ ULift.{v} Unit
    let β : ι → ℝ := fun i ↦ Sum.elim (fun _ ↦ α) (fun _ ↦ 1 - α) i
    let r : ι → gra A := fun i ↦ Sum.elim (fun _ ↦ p) (fun _ ↦ q) i
    have hβ_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ β i := by
      intro i hi
      rcases i with _ | _
      · simp [β]
        linarith
      · simp [β]
        linarith
    have hβ_sum : (∑ i ∈ (Finset.univ : Finset ι), β i) = 1 := by
      simp [ι, β, Fintype.sum_sum_type]
    -- Specialize the finite-family inequality to the two-point family `(p, q)`.
    have hspecial := hfinite (ι := ι) (Finset.univ : Finset ι) β r hβ_nonneg hβ_sum
    simpa [ι, β, r, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hspecial
  tfae_have 3 → 1 := by
    intro hconv
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hu hv
    let p : gra A := ⟨(x, u), by simpa [SetValuedOperator.mem_graph] using hu⟩
    let q : gra A := ⟨(y, v), by simpa [SetValuedOperator.mem_graph] using hv⟩
    -- Apply the two-point inequality at the midpoint and expand the pairing defect.
    have hmid_raw :
        ⟪(1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y,
          (1 / 2 : ℝ) • u + (1 - (1 / 2 : ℝ)) • v⟫_ℝ ≤
          (1 / 2 : ℝ) * ⟪x, u⟫_ℝ + (1 - (1 / 2 : ℝ)) * ⟪y, v⟫_ℝ := by
      simpa [p, q] using
        hconv (p := p) (q := q) (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have hmid :
        ⟪(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y, (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v⟫_ℝ ≤
          (1 / 2 : ℝ) * ⟪x, u⟫_ℝ + (1 / 2 : ℝ) * ⟪y, v⟫_ℝ := by
      nlinarith [hmid_raw]
    have hmid_expand :
        ⟪(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y, (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v⟫_ℝ =
          (1 / 4 : ℝ) * (⟪x, u⟫_ℝ + ⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ) := by
      rw [inner_add_left, inner_add_right, inner_add_right]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right]
      ring
    have hdefect :
        ⟪x - y, u - v⟫_ℝ = ⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ - ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      ring
    have hineq :
        (1 / 4 : ℝ) * (⟪x, u⟫_ℝ + ⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ) ≤
          (1 / 2 : ℝ) * ⟪x, u⟫_ℝ + (1 / 2 : ℝ) * ⟪y, v⟫_ℝ := by
      rw [hmid_expand] at hmid
      exact hmid
    nlinarith [hineq, hdefect]
  tfae_finish

end SetValuedOperator
