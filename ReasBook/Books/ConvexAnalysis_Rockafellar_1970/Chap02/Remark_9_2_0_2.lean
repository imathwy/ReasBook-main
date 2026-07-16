import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Example_9_0_0_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: the remark records three observations about the recession-side hypothesis in
  Theorem 9.2: it is automatic when `h` has no recession directions, therefore also when
  `dom(h)` is bounded, and it fails for the opening example of Section 9.
- `core/canonical`: the owner declarations are `recessionFunction`, `Function.recessionCone`, the
  effective-domain owner `dom(·)`, and the theorem-9.2 recession-kernel owner
  `LinearMap.noAsymmetricRecessionKernel`.
- `bridge/view`: the section-opening counterexample is expressed through the Chapter 2 owner
  `orthantExponential` together with the shared first-coordinate bridge.

Domain-style sampling used here:
- `recessionFunction` and `Function.recessionCone`;
- `linearImage_lowerSemicontinuous_of_no_asymmetric_recession_kernel`;
- the boundedness owner `Bornology.IsBounded` on `dom(h)`;
- `orthantExponential_linearImage_fst_not_lowerSemicontinuousAt_zero`.

Primitive data vs derived API:
- primitive inputs: the linear map `A`, the function `h`, and the source-visible condition that
  `h` has no recession directions, rendered as
  `Function.recessionCone ((h)₀⁺) = {0}`;
- derived API: the automatic validity of Theorem 9.2's recession-kernel hypothesis, its bounded
  effective-domain specialization, and the failure statement for the opening example.

Layer target: this item stays `source-facing`, but it is stated directly with the chapter's
canonical recession owners rather than through a new wrapper around Theorem 9.2.
-/

section

variable {𝕜 α E F : Type*}
variable [Semiring 𝕜]
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: if `((h)₀⁺) z ≤ 0`, then `z` belongs to
-- `Function.recessionCone ((h)₀⁺)`, hence the singleton hypothesis forces `z = 0`.
-- The second hypothesis then becomes `0 < ((h)₀⁺) 0`, contradicting the first
-- inequality. Thus the pair of recession inequalities can never occur, so the kernel condition in
-- Theorem 9.2 is vacuous.
/-- Remark 9.2.0.2: if `h` has no directions of recession, formalized by
`Function.recessionCone ((h)₀⁺) = {0}`, then the recession-side hypothesis in
Theorem 9.2 is automatically satisfied. -/
  theorem linearImage_recession_kernel_condition_of_no_recession_directions
      (A : E →ₗ[𝕜] F) (h : E → WithBotTop α)
      (hno_recession : Function.recessionCone ((h)₀⁺) = ({0} : Set E)) :
      A.noAsymmetricRecessionKernel h := by
  intro z hz hneg
  have hz_mem : z ∈ Function.recessionCone ((h)₀⁺) := by
    exact hz
  have hz_zero : z = 0 := by
    have hz_singleton : z ∈ ({0} : Set E) := by
      have hz_mem' : z ∈ Function.recessionCone ((h)₀⁺) := hz_mem
      rwa [hno_recession] at hz_mem'
    simpa [Set.mem_singleton_iff] using hz_singleton
  have hz_nonpos : ((h)₀⁺) 0 ≤ 0 := by
    have h0_mem : (0 : E) ∈ Function.recessionCone ((h)₀⁺) := by
      simpa [hz_zero] using hz_mem
    simpa [Function.mem_recessionCone_iff] using h0_mem
  have hz_pos : 0 < ((h)₀⁺) 0 := by
    simpa [hz_zero] using hneg
  exact (not_lt_of_ge hz_nonpos hz_pos).elim

end

section

variable {E : Type*} [NormedAddCommGroup E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]

private theorem not_isBounded_range_add_nat_smul
    {K : Type*} [RCLike K] [NormedSpace K E]
    (x y : E) (hy : y ≠ 0) :
    ¬ Bornology.IsBounded (Set.range fun n : ℕ ↦ x + n • y) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : E)
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
  have hnorm : ‖x + n • y‖ ≤ R := by
    have hxR : x + n • y ∈ Metric.closedBall (0 : E) R := hR ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
  have hny : (n : ℝ) * ‖y‖ ≤ R + ‖x‖ := by
    calc
      (n : ℝ) * ‖y‖ = ‖(n : K) • y‖ := by
        simp [norm_smul]
      _ = ‖n • y‖ := by simp [Nat.cast_smul_eq_nsmul]
      _ = ‖(x + n • y) - x‖ := by simp
      _ ≤ ‖x + n • y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
  have hgt : R + ‖x‖ < (n : ℝ) * ‖y‖ := by
    exact (div_lt_iff₀ hy_norm).mp hn
  exact not_lt_of_ge hny hgt

-- Proof sketch: boundedness of the effective domain rules out any nonzero translation direction
-- that preserves finiteness. For `y ≠ 0`, pick `x` in the effective domain with `x + y` outside
-- it; then the defining supremum formula for `((h)₀⁺) y` contains the value `⊤`, so `y` cannot
-- lie in `Function.recessionCone ((h)₀⁺)`. Nonemptiness of `dom(h)` supplies a finite base point.
/-- If the effective domain is nonempty and bounded, then the recession function is `⊤`
in every nonzero direction. -/
theorem recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain
    {K : Type*} [RCLike K] [NormedSpace K E]
    (h : E → WithBotTop α)
    (hdom_nonempty : (dom(h)).Nonempty)
    (hdom_bounded : Bornology.IsBounded dom(h))
    (y : E) (hy : y ≠ 0) :
    ((h)₀⁺) y = ⊤ := by
  have hx0_exists : ∃ x : E, h x < ⊤ := by
    rcases hdom_nonempty with ⟨x, hx⟩
    exact ⟨x, mem_effectiveDomain.mp hx⟩
  have hx_out :
      ∃ x : E, h x < ⊤ ∧ ¬ h (x + y) < ⊤ := by
    by_contra hx_out
    push Not at hx_out
    rcases hx0_exists with ⟨x0, hx0_top⟩
    have hrange_subset :
        Set.range (fun n : ℕ ↦ x0 + n • y) ⊆ dom(h) := by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      induction n with
      | zero =>
          simpa [mem_effectiveDomain] using hx0_top
      | succ n ih =>
          have : h ((x0 + n • y) + y) < ⊤ := hx_out (x0 + n • y) ih
          simpa [mem_effectiveDomain, succ_nsmul, add_assoc] using this
    have hrange_bounded :
        Bornology.IsBounded (Set.range fun n : ℕ ↦ x0 + n • y) :=
      hdom_bounded.subset hrange_subset
    exact not_isBounded_range_add_nat_smul (K := K) x0 y hy hrange_bounded
  rcases hx_out with ⟨x, hx_top, hxy_not_top⟩
  have hxy_top : h (x + y) = ⊤ := le_antisymm le_top (le_of_not_gt hxy_not_top)
  rw [Function.recessionFunction_apply]
  refine le_antisymm le_top ?_
  refine le_sSup ?_
  exact ⟨x, by simpa [mem_effectiveDomain] using hx_top,
    by
      simpa [hxy_top, sub_eq_add_neg] using
        (WithBotTop.top_sub (x := h x) hx_top.ne).symm⟩

/-- If the effective domain is nonempty and bounded, then the function has no recession
directions. -/
theorem functionRecessionCone_eq_singleton_zero_of_bounded_effectiveDomain
    {K : Type*} [RCLike K] [NormedSpace K E]
    (h : E → WithBotTop α)
    (hdom_nonempty : (dom(h)).Nonempty)
    (hdom_bounded : Bornology.IsBounded dom(h)) :
    Function.recessionCone ((h)₀⁺) = ({0} : Set E) := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff]
    by_contra hy_ne
    have hy_nonpos : ((h)₀⁺) y ≤ 0 := by
      rwa [Function.mem_recessionCone_iff] at hy
    have hy_top : ((h)₀⁺) y = ⊤ :=
      recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain (K := K)
        h hdom_nonempty hdom_bounded y hy_ne
    have htop_not_le : ¬ ((⊤ : WithBotTop α) ≤ 0) := by
      exact not_le_of_gt (WithBotTop.coe_lt_top (0 : α))
    exact htop_not_le (hy_top ▸ hy_nonpos)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [Function.mem_recessionCone_iff, Function.recessionFunction_apply]
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, -, rfl⟩
    simpa using (WithBotTop.sub_self_le_zero (x := h x))

end

end

section

open scoped Rockafellar

-- Proof sketch: if the theorem-9.2 kernel condition held for the opening example, Theorem 9.2
-- would make `(LinearMap.fst ℝ ℝ ℝ) ◁ orthantExponential` lower semicontinuous,
-- contradicting the existing Section 9 example theorem that it is not
-- lower semicontinuous at `0`.
/-- The opening example of Section 9 violates the recession-side hypothesis from Theorem 9.2. -/
theorem orthantExponential_violates_linearImage_recession_kernel_condition :
    ¬ (LinearMap.fst ℝ ℝ ℝ).noAsymmetricRecessionKernel orthantExponential := by
  intro hkernel
  have himage_lsc :
      LowerSemicontinuous ((LinearMap.fst ℝ ℝ ℝ) ◁ orthantExponential) :=
    linearImage_lowerSemicontinuous_of_no_asymmetric_recession_kernel
      (LinearMap.fst ℝ ℝ ℝ)
      orthantExponential
      orthantExponential_isConvex
      orthantExponential_lowerSemicontinuous
      hkernel
  exact orthantExponential_linearImage_fst_not_lowerSemicontinuousAt_zero
    (himage_lsc.lowerSemicontinuousAt 0)

end
