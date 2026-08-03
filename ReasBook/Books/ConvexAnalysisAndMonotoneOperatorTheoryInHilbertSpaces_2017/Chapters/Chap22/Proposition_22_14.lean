import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap22.Definition_22_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 22.14: every subgradient of a proper function is taken at a point of the
effective domain. -/
lemma subgradient_mem_dom_of_isProper
    {f : H → EReal} (hf : IsProper f) {x u : H} (hu : u ∈ (∂ f) x) :
    x ∈ dom f := by
  rcases hf.2 with ⟨y, hy_dom⟩
  rw [mem_dom_iff_ne_top] at hy_dom ⊢
  by_contra hx_top
  have hxy : ((⟪y - x, u⟫_ℝ : ℝ) : EReal) + f x ≤ f y :=
    (mem_subdifferential_iff f x u).1 hu y
  -- Evaluate the affine minorant at a known finite point to rule out `f x = ⊤`.
  rw [hx_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hxy
  exact hy_dom (top_le_iff.mp hxy)

/-- Helper for Proposition 22.14: a finite affine-minorant inequality in `EReal` yields the
corresponding real inequality after taking `toReal`. -/
lemma ereal_affine_ineq_le_toReal_sub_of_mem_dom
    {f : H → EReal} (hf : IsProper f) {x y u : H}
    (hx_dom : x ∈ dom f) (hy_dom : y ∈ dom f)
    (hxy : ((⟪y - x, u⟫_ℝ : ℝ) : EReal) + f x ≤ f y) :
    ⟪y - x, u⟫_ℝ ≤ (f y).toReal - (f x).toReal := by
  rw [mem_dom_iff_ne_top] at hx_dom hy_dom
  have hsub : (((⟪y - x, u⟫_ℝ : ℝ) : EReal)) ≤ f y - f x := by
    -- Move `f x` to the right to match the real-valued difference in the textbook proof.
    exact (EReal.le_sub_iff_add_le (.inl (hf.1 x)) (.inl hx_dom)).2 hxy
  have hsub_top : f y - f x ≠ ⊤ := by
    -- The difference of two finite-above, finite-below values is again finite above.
    rw [sub_eq_add_neg, EReal.add_ne_top_iff_of_ne_bot_of_ne_top]
    · exact hy_dom
    · simpa using hx_dom
    · simpa using hf.1 x
  have hreal : ⟪y - x, u⟫_ℝ ≤ (f y - f x).toReal := by
    exact EReal.toReal_le_toReal hsub (EReal.coe_ne_bot _) hsub_top
  -- Expand the `toReal` of the finite difference to the expected real subtraction.
  simpa [EReal.toReal_sub hy_dom (hf.1 y) hx_dom (hf.1 x)] using hreal

/-- Helper for Proposition 22.14: a finite sum of successive differences telescopes to the
endpoint difference. -/
lemma sum_range_succ_sub_eq_endpoint_sub
    {α : Type*} [AddCommGroup α] (a : ℕ → α) :
    ∀ n : ℕ, Finset.sum (Finset.range n) (fun i ↦ a (i + 1) - a i) = a n - a 0
  | 0 => by
      -- The empty telescoping sum has no interior terms.
      simp
  | n + 1 => by
      -- Peel off the final difference and combine it with the induction hypothesis.
      rw [Finset.sum_range_succ, sum_range_succ_sub_eq_endpoint_sub a n]
      abel_nf

/-- Proposition 22.14: if `f` is proper, then its subdifferential `∂ f` is cyclically
monotone. -/
theorem subdifferential_isCyclicallyMonotone
    {f : H → EReal} (hf : IsProper f) :
    (∂ f).IsCyclicallyMonotone := by
  refine ⟨?_⟩
  intro n hn
  refine ⟨hn, ?_⟩
  intro x u hu hxn
  have hn_pos : 0 < n := by
    omega
  have hx0_dom : x 0 ∈ dom f :=
    subgradient_mem_dom_of_isProper hf (hu 0 hn_pos)
  have hstep :
      ∀ i, i < n →
        ⟪x (i + 1) - x i, u i⟫_ℝ ≤ (f (x (i + 1))).toReal - (f (x i)).toReal := by
    intro i hi
    have hxi_dom : x i ∈ dom f :=
      subgradient_mem_dom_of_isProper hf (hu i hi)
    have hxi1_dom : x (i + 1) ∈ dom f := by
      by_cases hi1 : i + 1 < n
      · -- Interior points of the cycle inherit finiteness from their own subgradient membership.
        exact subgradient_mem_dom_of_isProper hf (hu (i + 1) hi1)
      · have hi1_eq : i + 1 = n := by
          omega
        -- The terminal point is identified with the initial point by the cycle condition.
        rw [hi1_eq, hxn]
        exact hx0_dom
    have hxy : ((⟪x (i + 1) - x i, u i⟫_ℝ : ℝ) : EReal) + f (x i) ≤ f (x (i + 1)) :=
      (mem_subdifferential_iff f (x i) (u i)).1 (hu i hi) (x (i + 1))
    -- Convert the one-step extended-real inequality into the real inequality used in the sum.
    exact ereal_affine_ineq_le_toReal_sub_of_mem_dom hf hxi_dom hxi1_dom hxy
  have hsum :
      Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) ≤
        Finset.sum (Finset.range n) (fun i ↦ (f (x (i + 1))).toReal - (f (x i)).toReal) := by
    -- Sum the textbook one-step inequalities over the entire cycle.
    exact Finset.sum_le_sum fun i hi ↦ hstep i (Finset.mem_range.mp hi)
  calc
    Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ)
        ≤ Finset.sum (Finset.range n) (fun i ↦ (f (x (i + 1))).toReal - (f (x i)).toReal) := hsum
    _ = (f (x n)).toReal - (f (x 0)).toReal := by
          simpa using sum_range_succ_sub_eq_endpoint_sub (fun i ↦ (f (x i)).toReal) n
    _ = 0 := by
          simp [hxn]

end ERealFunction
