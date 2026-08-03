import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap06.Definition_6_48
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall note: `lean_leansearch` did not return a direct owner theorem for this item; the
-- verified local surfaces are `rec`, `N[C]`, `A.dom`, and `Maximal IsMonotone A`.

omit [CompleteSpace H] in
/-- Helper for Proposition 21.17: the translated support inequality on `C - {p}` is equivalent to
the pointwise inner-product inequalities against all `y ∈ C`. -/
private lemma innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos
    {C : Set H} {u p : H} :
    innerSupremumOn (C - ({p} : Set H)) u ≤ 0 ↔ ∀ y ∈ C, ⟪y - p, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hsup
    -- Compare the translate `C - {p}` against `{0}` to recover pointwise inequalities.
    have hsep :
        innerSupremumOn (C - ({p} : Set H)) u ≤ innerInfimumOn ({0} : Set H) u := by
      simpa using hsup
    have hinner :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set H)) ({0} : Set H) u).1 hsep
    intro y hy
    have hy_sub : y - p ∈ C - ({p} : Set H) := by
      exact ⟨y, hy, p, by simp, rfl⟩
    simpa using hinner (y - p) hy_sub 0 (by simp)
  · intro hinner
    -- Expand every point of `C - {p}` as a difference `y - p` and repackage the family.
    have hsep :
        innerSupremumOn (C - ({p} : Set H)) u ≤ innerInfimumOn ({0} : Set H) u := by
      refine (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set H)) ({0} : Set H) u).2 ?_
      intro v hv z hz
      have hz0 : z = 0 := by
        simpa using hz
      subst hz0
      rcases hv with ⟨y, hy, q, hq, hvq⟩
      have hq_eq : q = p := by
        simpa using hq
      have hv_eq : v = y - p := by
        simpa [hq_eq] using hvq.symm
      simpa [hv_eq] using hinner y hy
    simpa using hsep

omit [CompleteSpace H] in
/-- Helper for Proposition 21.17: swapping the subtraction order flips the sign of the
corresponding inner product. -/
private lemma inner_sub_nonpos_iff_nonneg_inner_sub_swap {x y w : H} :
    ⟪y - x, w⟫_ℝ ≤ 0 ↔ 0 ≤ ⟪x - y, w⟫_ℝ := by
  have hxy : x - y = -(y - x) := by
    abel
  constructor
  · intro h
    rw [hxy, inner_neg_left]
    linarith
  · intro h
    have hyx : y - x = -(x - y) := by
      abel
    rw [hyx, inner_neg_left]
    linarith

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 21.17: one recession-cone step translates a point of `C` by `w`
inside `C`. -/
private lemma add_mem_of_mem_recessionCone
    {C : Set H} {u w : H} (hu : u ∈ C) (hw : w ∈ rec C) :
    u + w ∈ C := by
  rw [Set.mem_recessionCone_iff] at hw
  have hmem : w + u ∈ ({w} : Set H) + C := by
    exact ⟨w, by simp, u, hu, rfl⟩
  have hwu : w + u ∈ C := hw hmem
  simpa [add_comm] using hwu

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 21.17: iterating a recession direction keeps all natural translates of a
value inside the same value set. -/
private lemma add_nat_smul_mem_of_mem_recessionCone
    {A : SetValuedOperator H H} {x u w : H}
    (hu : u ∈ A x) (hw : w ∈ rec (A x)) :
    ∀ n : ℕ, u + n • w ∈ A x := by
  intro n
  induction n with
  | zero =>
      simpa using hu
  | succ n ih =>
      -- Apply one more recession-cone translate to the previously constructed value.
      have hstep : (u + n • w) + w ∈ A x :=
        add_mem_of_mem_recessionCone ih hw
      simpa [succ_nsmul, add_assoc] using hstep

/-- Helper for Proposition 21.17: if `a + n b` is nonnegative for every natural `n`, then the
slope `b` must be nonnegative. -/
private lemma nonneg_of_forall_nat_nonneg_add_mul
    {a b : ℝ} (h : ∀ n : ℕ, 0 ≤ a + (n : ℝ) * b) :
    0 ≤ b := by
  by_contra hb
  have hb_lt : b < 0 := lt_of_not_ge hb
  have hneg_pos : 0 < -b := by
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a / (-b) < n := exists_nat_gt (a / (-b))
  have hn' : a + (n : ℝ) * b < 0 := by
    have hn_real : a / (-b) < (n : ℝ) := by
      exact_mod_cast hn
    have hlt : a < (n : ℝ) * (-b) := by
      exact (div_lt_iff₀ hneg_pos).1 hn_real
    nlinarith
  exact not_lt_of_ge (h n) hn'

omit [CompleteSpace H] in
/-- Helper for Proposition 21.17: the halfspace defined by `0 ≤ ⟪x - y, w⟫` is closed. -/
private lemma isClosed_nonnegativeInnerHalfspace (x w : H) :
    IsClosed {y : H | 0 ≤ ⟪x - y, w⟫_ℝ} := by
  -- The defining function is continuous, so its nonnegative superlevel set is closed.
  simpa using
    isClosed_le
      (continuous_const : Continuous fun _ : H ↦ (0 : ℝ))
      ((continuous_const.sub continuous_id).inner continuous_const)

omit [CompleteSpace H] in
/-- Helper for Proposition 21.17: every recession direction of the value set is normal to
`closure A.dom` at `x`. -/
private lemma normalCone_closureDom_of_mem_recessionConeValue
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    {x w : H} (hx : x ∈ A.dom) (hw : w ∈ rec (A x)) :
    w ∈ N[closure A.dom] x := by
  have hx_closure : x ∈ closure A.dom := subset_closure hx
  obtain ⟨u, hu⟩ := hx
  have hmonoA := (SetValuedOperator.isMonotone_iff A).1 (Maximal.isMonotone hA)
  have hvalue_nat : ∀ n : ℕ, u + n • w ∈ A x :=
    add_nat_smul_mem_of_mem_recessionCone hu hw
  have hdom_nonneg : ∀ y ∈ A.dom, 0 ≤ ⟪x - y, w⟫_ℝ := by
    intro y hy
    obtain ⟨v, hv⟩ := hy
    -- Compare `(x, u + n • w)` with the graph point `(y, v)` for every `n`.
    have hineq : ∀ n : ℕ, 0 ≤ ⟪x - y, u - v⟫_ℝ + (n : ℝ) * ⟪x - y, w⟫_ℝ := by
      intro n
      have hmon : 0 ≤ ⟪x - y, (u + n • w) - v⟫_ℝ := hmonoA (hvalue_nat n) hv
      have hsplit :
          ⟪x - y, (u + n • w) - v⟫_ℝ =
            ⟪x - y, u - v⟫_ℝ + (n : ℝ) * ⟪x - y, w⟫_ℝ := by
        calc
          ⟪x - y, (u + n • w) - v⟫_ℝ
              = ⟪x - y, u + n • w⟫_ℝ - ⟪x - y, v⟫_ℝ := by
                  rw [inner_sub_right]
          _ = (⟪x - y, u⟫_ℝ + ⟪x - y, n • w⟫_ℝ) - ⟪x - y, v⟫_ℝ := by
                rw [inner_add_right]
          _ = (⟪x - y, u⟫_ℝ + (n : ℝ) * ⟪x - y, w⟫_ℝ) - ⟪x - y, v⟫_ℝ := by
                have hnsmul :
                    ⟪x - y, n • w⟫_ℝ = (n : ℝ) * ⟪x - y, w⟫_ℝ := by
                  rw [← Nat.cast_smul_eq_nsmul ℝ n w]
                  exact real_inner_smul_right (x - y) w (n : ℝ)
                rw [hnsmul]
          _ = ⟪x - y, u - v⟫_ℝ + (n : ℝ) * ⟪x - y, w⟫_ℝ := by
                rw [inner_sub_right]
                ring
      rw [hsplit] at hmon
      exact hmon
    exact nonneg_of_forall_nat_nonneg_add_mul hineq
  have hclosure_nonneg : ∀ y ∈ closure A.dom, 0 ≤ ⟪x - y, w⟫_ℝ := by
    let S : Set H := {y : H | 0 ≤ ⟪x - y, w⟫_ℝ}
    have hdom_subset : A.dom ⊆ S := by
      intro y hy
      exact hdom_nonneg y hy
    have hclosed : IsClosed S := isClosed_nonnegativeInnerHalfspace x w
    have hclosure_subset : closure A.dom ⊆ S := closure_minimal hdom_subset hclosed
    intro y hy
    exact hclosure_subset hy
  -- Rewrite the normal cone at `x` into the translated support inequality on `closure A.dom - {x}`.
  rw [Set.normalCone_of_mem hx_closure]
  refine (innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos).2 ?_
  intro y hy
  exact (inner_sub_nonpos_iff_nonneg_inner_sub_swap).2 (hclosure_nonneg y hy)

omit [CompleteSpace H] in
/-- Helper for Proposition 21.17: every normal vector to `closure A.dom` at `x` is a recession
direction of the value set `A x`. -/
private lemma mem_recessionCone_value_of_mem_normalCone_closureDom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    {x w : H} (hx : x ∈ A.dom) (hw : w ∈ N[closure A.dom] x) :
    w ∈ rec (A x) := by
  have hx_closure : x ∈ closure A.dom := subset_closure hx
  obtain ⟨u, hu⟩ := hx
  have hmonoA := (SetValuedOperator.isMonotone_iff A).1 (Maximal.isMonotone hA)
  have hclosure_nonneg : ∀ y ∈ closure A.dom, 0 ≤ ⟪x - y, w⟫_ℝ := by
    rw [Set.normalCone_of_mem hx_closure] at hw
    have hpointwise :=
      (innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos).1 hw
    intro y hy
    exact (inner_sub_nonpos_iff_nonneg_inner_sub_swap).1 (hpointwise y hy)
  rw [Set.mem_recessionCone_iff]
  intro z hz
  rcases hz with ⟨w', hw', u', hu', rfl⟩
  have hw_eq : w' = w := by
    simpa using hw'
  subst w'
  -- Route correction: use the Minty membership criterion at the translated value `u' + w`.
  have hmem : u' + w ∈ A x := by
    refine (SetValuedOperator.Maximal.mem_iff hA x (u' + w)).2 ?_
    intro y v hv
    have hy_dom : y ∈ A.dom := ⟨v, hv⟩
    have hbase : 0 ≤ ⟪x - y, u' - v⟫_ℝ := hmonoA hu' hv
    have hnormal : 0 ≤ ⟪x - y, w⟫_ℝ := hclosure_nonneg y (subset_closure hy_dom)
    have hsplit :
        ⟪x - y, (u' + w) - v⟫_ℝ =
          ⟪x - y, u' - v⟫_ℝ + ⟪x - y, w⟫_ℝ := by
      calc
        ⟪x - y, (u' + w) - v⟫_ℝ
            = ⟪x - y, u' + w⟫_ℝ - ⟪x - y, v⟫_ℝ := by
                rw [inner_sub_right]
        _ = (⟪x - y, u'⟫_ℝ + ⟪x - y, w⟫_ℝ) - ⟪x - y, v⟫_ℝ := by
              rw [inner_add_right]
        _ = ⟪x - y, u' - v⟫_ℝ + ⟪x - y, w⟫_ℝ := by
              rw [inner_sub_right]
              ring
    rw [hsplit]
    linarith
  simpa [add_comm] using hmem

omit [CompleteSpace H] in
/-- Proposition 21.17: if `A : H → 2^H` is maximally monotone and `x ∈ dom A`, then the
recession cone of the value set `A x` is the normal cone to `closure A.dom` at `x`. -/
theorem recessionCone_value_eq_normalCone_closure_dom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    {x : H} (hx : x ∈ A.dom) :
    rec (A x) = N[closure A.dom] x := by
  ext w
  constructor
  · -- Recession directions satisfy the normal-cone inequalities on the closure of the domain.
    exact normalCone_closureDom_of_mem_recessionConeValue A hA hx
  · -- Normal vectors translate every value of `A x` back into the same value set.
    exact mem_recessionCone_value_of_mem_normalCone_closureDom A hA hx

omit [CompleteSpace H] in
/-- At a domain point of a maximally monotone operator, membership in the recession cone of the
value set is equivalent to the defining normal-cone inequality for `closure A.dom` at that point. -/
theorem mem_recessionCone_value_iff_innerSupremumOn_closure_dom_nonpos
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    {x u : H} (hx : x ∈ A.dom) :
    u ∈ rec (A x) ↔ innerSupremumOn (closure A.dom - ({x} : Set H)) u ≤ 0 := by
  rw [recessionCone_value_eq_normalCone_closure_dom A hA hx]
  simp [Set.normalCone_of_mem (subset_closure hx)]

end SetValuedOperator
