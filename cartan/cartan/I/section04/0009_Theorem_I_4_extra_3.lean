import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- If all iterated derivatives of a one-variable analytic map vanish at a point, then the function
is identically zero on some neighborhood of that point. -/
-- Proof sketch: use `AnalyticAt.analyticOrderAt_eq_natCast` to show every finite vanishing order is
-- impossible, hence `analyticOrderAt f x₀ = ⊤`; then apply `analyticOrderAt_eq_top`.
theorem AnalyticAt.eventuallyEq_zero_of_forall_iteratedDeriv_eq_zero
    {f : 𝕜 → E} {x₀ : 𝕜} (hf : AnalyticAt 𝕜 f x₀)
    (hvanish : ∀ n : ℕ, iteratedDeriv n f x₀ = 0) :
    f =ᶠ[𝓝 x₀] 0 := by
  have horder_ne_zero : analyticOrderAt f x₀ ≠ 0 := by
    rw [hf.analyticOrderAt_ne_zero]
    simpa [iteratedDeriv_zero] using hvanish 0
  have htop : analyticOrderAt f x₀ = ⊤ := by
    cases horder : analyticOrderAt f x₀ with
    | top =>
        rfl
    | coe n =>
        cases n with
        | zero =>
            exact (horder_ne_zero horder).elim
        | succ n =>
            have hle : ((n + 2 : ℕ) : ℕ∞) ≤ analyticOrderAt f x₀ := by
              rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
              intro i hi
              exact hvanish i
            have hnot_le : ¬ ((n + 2 : ℕ) : ℕ∞) ≤ (n + 1 : ℕ∞) :=
              not_le_of_gt <| by exact_mod_cast Nat.lt_succ_self (n + 1)
            have hle' : ((n + 2 : ℕ) : ℕ∞) ≤ (n + 1 : ℕ∞) := by
              rwa [horder] at hle
            exact (hnot_le hle').elim
  change ∀ᶠ z in 𝓝 x₀, f z = 0
  exact analyticOrderAt_eq_top.mp htop

/-- Theorem I.4-extra-3: for a one-variable analytic map on a preconnected open set, the following
are equivalent: all iterated derivatives vanish at `x₀`, the function is identically zero on a
neighborhood of `x₀`, and the function is identically zero on all of `D`. -/
-- Proof sketch: `(a) → (b)` follows from infinite vanishing order at `x₀`, encoded by
-- `AnalyticAt.eventuallyEq_zero_of_forall_iteratedDeriv_eq_zero`; `(b) → (c)` is the canonical
-- identity principle `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`; `(c) → (a)`
-- follows because iterated derivatives respect equality on the open set `D`.
theorem analytic_zero_tfae_of_forall_iteratedDeriv_eq_zero
    {D : Set 𝕜} (hD_open : IsOpen D) (hD_preconnected : IsPreconnected D) {f : 𝕜 → E}
    (hf : AnalyticOnNhd 𝕜 f D) {x₀ : 𝕜} (hx₀ : x₀ ∈ D) :
    List.TFAE
      [ ∀ n : ℕ, iteratedDeriv n f x₀ = 0,
        f =ᶠ[𝓝 x₀] 0,
        Set.EqOn f 0 D ]
    := by
  tfae_have 1 → 2 := fun hvanish ↦
    (hf x₀ hx₀).eventuallyEq_zero_of_forall_iteratedDeriv_eq_zero hvanish
  tfae_have 2 → 3 := fun hzero ↦
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD_preconnected hx₀ hzero
  tfae_have 3 → 1 := fun hzero n ↦ by
    simpa using (hzero.iteratedDeriv_of_isOpen hD_open n) hx₀
  tfae_finish
