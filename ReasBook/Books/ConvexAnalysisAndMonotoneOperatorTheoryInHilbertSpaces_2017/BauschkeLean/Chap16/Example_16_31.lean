import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Example_13_8
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section RadialSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 16 31: if an `]-∞,+∞]`-valued function has nonempty effective domain, then
subgradient membership is equivalent to Fenchel--Young equality. -/
private lemma mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (_hdom : (effectiveDomain f).Nonempty) (x u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  -- Use Proposition 16.10 directly as the canonical Fenchel--Young criterion.
  simpa using ERealFunction.mem_subdifferential_iff_fenchel_young_eq
    (f := f) x u

/-- Helper for Example 16 31: an even member of `Γ₀(ℝ)` is finite at `0`. -/
private lemma zero_mem_effectiveDomain_of_even_mem_gammaZero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) :
    0 ∈ effectiveDomain φ := by
  rcases hφ.2.nonempty with ⟨t, ht⟩
  have hneg : -t ∈ effectiveDomain φ := by
    -- Evenness transfers finiteness from `t` to `-t`.
    rw [mem_effectiveDomain_iff] at ht ⊢
    simpa [heven t] using ht
  have hmid :
      (1 / 2 : ℝ) • t + (1 - 1 / 2 : ℝ) • (-t) ∈ effectiveDomain φ :=
    hφ.2.convex_effectiveDomain
      ht
      hneg
      (by norm_num)
      (by norm_num)
      (by norm_num)
  -- The midpoint of `t` and `-t` is `0`.
  have hzero : (1 / 2 : ℝ) • t + (1 - 1 / 2 : ℝ) • (-t) = 0 := by
    simp [smul_eq_mul]
    ring
  rw [hzero] at hmid
  simpa using hmid

/-- Helper for Example 16 31: equality in Cauchy--Schwarz is exactly the same-ray condition. -/
private lemma real_inner_eq_norm_mul_iff_same_ray (x u : H) :
    ⟪x, u⟫_ℝ = ‖x‖ * ‖u‖ ↔ SameRay ℝ x u := by
  -- Mathlib already identifies equality in Cauchy--Schwarz with lying on the same ray.
  simpa [sameRay_iff_norm_smul_eq, eq_comm] using
    (inner_eq_norm_mul_iff_real (x := x) (y := u))

/-- Helper for Example 16 31: on `ℝ`, the inner product and multiplication agree after coercion
to `EReal`. -/
private lemma ereal_real_inner_eq_mul (a b : ℝ) :
    ((⟪a, b⟫_ℝ : ℝ) : EReal) = (((a * b : ℝ) : EReal)) := by
  -- On `ℝ`, the real inner product is ordinary multiplication.
  have hinner : ⟪a, b⟫_ℝ = a * b := by
    calc
      ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
      _ = a * b := by simp
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hinner

/-- Helper for Example 16 31: on `ℝ`, the Fenchel--Young equality is exactly scalar
subdifferential membership. -/
private lemma scalar_fenchel_young_eq_iff_mem_subdifferential
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) (a b : ℝ) :
    (φ a : EReal) + φ.asEReal∗ b = (((a * b : ℝ) : EReal)) ↔ b ∈ (∂ φ) a := by
  have hdom : (effectiveDomain φ).Nonempty :=
    ⟨0, zero_mem_effectiveDomain_of_even_mem_gammaZero φ hφ heven⟩
  constructor
  · intro hEq
    -- Rewrite the scalar product as the real inner product, then invoke Proposition 16.10.
    have hEq_inner :
        (φ a : EReal) + φ.asEReal∗ b = ((⟪a, b⟫_ℝ : ℝ) : EReal) := by
      calc
        (φ a : EReal) + φ.asEReal∗ b = (((a * b : ℝ) : EReal)) := hEq
        _ = ((⟪a, b⟫_ℝ : ℝ) : EReal) := (ereal_real_inner_eq_mul a b).symm
    exact
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        φ hdom a b).2 hEq_inner
  · intro hb
    -- Conversely, Proposition 16.10 gives inner-product contact, which is just multiplication.
    have hEq_inner :
        (φ a : EReal) + φ.asEReal∗ b = ((⟪a, b⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        φ hdom a b).1 hb
    calc
      (φ a : EReal) + φ.asEReal∗ b = ((⟪a, b⟫_ℝ : ℝ) : EReal) := hEq_inner
      _ = (((a * b : ℝ) : EReal)) := ereal_real_inner_eq_mul a b

/-- Helper for Example 16 31: the radial subdifferential condition is the Fenchel--Young equality
for the radial function. -/
private lemma mem_subdifferential_comp_norm_iff_radial_fenchel_young_eq
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) (x u : H) :
    u ∈ (∂ (fun y : H ↦ φ ‖y‖)) x ↔
      (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  have hdom_radial : (effectiveDomain (fun y : H ↦ φ ‖y‖)).Nonempty := by
    refine ⟨0, ?_⟩
    -- Finiteness of `φ 0` makes the radial function finite at the origin.
    rw [mem_effectiveDomain_iff]
    simpa using
      (mem_effectiveDomain_iff.mp (zero_mem_effectiveDomain_of_even_mem_gammaZero φ hφ heven))
  have hconj_eval :
      (fun y : H ↦ φ ‖y‖).asEReal∗ u = φ.asEReal∗ ‖u‖ := by
    -- Example 13.8 identifies the radial conjugate pointwise.
    have hconj_fun :
        (fun y : H ↦ φ ‖y‖).asEReal∗ = φ.asEReal∗ ∘ (norm : H → ℝ) :=
      conjugate_comp_norm_eq_comp_norm_conjugate_of_even (H := H) φ heven
    have hconj_point := congrArg (fun g : H → EReal ↦ g u) hconj_fun
    simpa [Function.comp] using hconj_point
  -- Proposition 16.10 turns the radial subgradient condition into the radial contact equality.
  rw [mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
    (fun y : H ↦ φ ‖y‖) hdom_radial x u]
  rw [hconj_eval]

/-- Helper for Example 16 31: the radial Fenchel--Young equality splits into the scalar
subgradient relation and equality in Cauchy--Schwarz. -/
private lemma radial_fenchel_young_eq_iff_norm_mem_subdifferential_and_same_ray
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) (x u : H) :
    (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ = ((⟪x, u⟫_ℝ : ℝ) : EReal) ↔
      ‖u‖ ∈ (∂ φ) ‖x‖ ∧ SameRay ℝ x u := by
  constructor
  · intro hEq
    have hscalar_le :
        (((‖x‖ * ‖u‖ : ℝ) : EReal)) ≤ (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ := by
      -- Scalar Fenchel--Young gives the lower bound by the product of the norms.
      calc
        (((‖x‖ * ‖u‖ : ℝ) : EReal)) = ((⟪‖x‖, ‖u‖⟫_ℝ : ℝ) : EReal) := by
          exact (ereal_real_inner_eq_mul ‖x‖ ‖u‖).symm
        _ ≤ (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ := by
          simpa using
            (fenchel_young_inequality
              (f := φ.asEReal) (isProper_of_mem_gammaZero hφ) ‖x‖ ‖u‖)
    have hinner_le :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (((‖x‖ * ‖u‖ : ℝ) : EReal)) :=
      EReal.coe_le_coe_iff.mpr (real_inner_le_norm x u)
    have hscalar_eq :
        (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
      have hcontact_le :
          (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ ≤ (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
        rw [hEq]
        exact hinner_le
      exact le_antisymm hcontact_le hscalar_le
    have hscalar_subgradient : ‖u‖ ∈ (∂ φ) ‖x‖ := by
      -- Equality in the scalar Fenchel--Young inequality is exactly scalar subdifferentiability.
      exact (scalar_fenchel_young_eq_iff_mem_subdifferential φ hφ heven ‖x‖ ‖u‖).1 hscalar_eq
    have hinner_eq :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
      exact hEq.symm.trans hscalar_eq
    have hray : SameRay ℝ x u := by
      -- Equality in Cauchy--Schwarz is the same-ray condition.
      exact
        (real_inner_eq_norm_mul_iff_same_ray (x := x) (u := u)).1
          (EReal.coe_eq_coe_iff.mp hinner_eq)
    exact ⟨hscalar_subgradient, hray⟩
  · rintro ⟨hu, hray⟩
    have hscalar_eq :
        (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
      -- Rebuild the scalar Fenchel--Young equality from scalar subgradient membership.
      exact (scalar_fenchel_young_eq_iff_mem_subdifferential φ hφ heven ‖x‖ ‖u‖).2 hu
    have hinner_eq :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
      -- The same-ray condition restores equality in Cauchy--Schwarz.
      exact EReal.coe_eq_coe_iff.mpr <|
        (real_inner_eq_norm_mul_iff_same_ray (x := x) (u := u)).2 hray
    calc
      (φ ‖x‖ : EReal) + φ.asEReal∗ ‖u‖ = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := hscalar_eq
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hinner_eq.symm

-- Proof sketch: Theorem 16.29 rewrites membership in the subdifferential of `x ↦ φ ‖x‖` as
-- Fenchel--Young equality. Example 13.8 identifies the conjugate of this radial function with
-- `u ↦ φ^*(‖u‖)`, Proposition 13.15 gives the scalar Fenchel--Young inequality
-- `φ(‖x‖) + φ^*(‖u‖) ≥ ‖x‖ * ‖u‖`, and Fact 2.11 bounds `⟪x, u⟫` by `‖x‖ * ‖u‖`. Equality in
-- both inequalities is equivalent to `‖u‖ ∈ ∂φ(‖x‖)` and to `x` and `u` lying on the same
-- nonnegative ray.
/-- Example 16 31: for an even function `φ ∈ Γ₀(ℝ)`, a vector `u` belongs to the subdifferential
of the radial function `x ↦ φ ‖x‖` at `x` exactly when `‖u‖` belongs to the subdifferential of
`φ` at `‖x‖` and `x` and `u` lie on the same nonnegative ray. -/
theorem mem_subdifferential_comp_norm_iff_norm_mem_subdifferential_and_same_ray
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) (x u : H) :
    u ∈ (∂ (fun y : H ↦ φ ‖y‖)) x ↔
      ‖u‖ ∈ (∂ φ) ‖x‖ ∧ SameRay ℝ x u := by
  -- First rewrite the radial subgradient condition as Fenchel--Young equality.
  exact
    (mem_subdifferential_comp_norm_iff_radial_fenchel_young_eq φ hφ heven x u).trans
      (radial_fenchel_young_eq_iff_norm_mem_subdifferential_and_same_ray φ hφ heven x u)

end RadialSubdifferential

end ERealFunction
