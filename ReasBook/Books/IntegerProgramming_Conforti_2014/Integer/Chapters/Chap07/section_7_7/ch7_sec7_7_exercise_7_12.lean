import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain sampling for this exercise:
- primary domain: sequence-independent lifting functions for minimal covers, with the goal of
  proving superadditivity on `[0, b]`
- inspected upstream declarations:
  * `SequenceIndependentLifting.is_superadditive_on_Icc` from Theorem 7.7, the
    `core/canonical` owner for superadditivity on `[0, b]`
  * `theorem_7_4_mu` from Theorem 7.4 and `theorem_7_16_cover_sum` from Theorem 7.16, the
    chapter-level owners for ordered-cover partial sums in more specialized ambient models
  * `flow_cover_excess` from Theorem 7.9, the chapter-level owner for the excess parameter in the
    finite flow-cover setting

This file stays `source-facing`: the ordered sequence `a`, its partial sums `μ`, the excess
`λ = μ_t - b`, the auxiliary quantities `ρ_h`, the intervals `F_h` and `S_h`, and the resulting
piecewise lifting function `g` are the mathematical objects named in Exercise 7.12 itself.
Only the superadditivity predicate is reused directly from the upstream canonical owner. The
implementation helper used to assemble `g` is kept internal because it is derived API rather than
source-level data. -/

open SequenceIndependentLifting

/-- The partial sums `μ_h = a₀ + ⋯ + a_{h-1}` of the ordered cover weights used in
Exercise 7.12. -/
def exercise_7_12_mu
    (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | h + 1 => exercise_7_12_mu a h + a h

/-- The initial partial sum in Exercise 7.12 is `μ₀ = 0`. -/
@[simp] theorem exercise_7_12_mu_zero
    (a : ℕ → ℝ) :
    exercise_7_12_mu a 0 = 0 :=
  rfl

/-- The partial sums in Exercise 7.12 satisfy the recursive relation
`μ_{h+1} = μ_h + a_h`. -/
@[simp] theorem exercise_7_12_mu_succ
    (a : ℕ → ℝ)
    (h : ℕ) :
    exercise_7_12_mu a (h + 1) = exercise_7_12_mu a h + a h :=
  rfl

/-- The recursive owner `exercise_7_12_mu` agrees with the explicit sum
`μ_h = a₀ + ⋯ + a_{h-1}`. -/
theorem exercise_7_12_mu_eq_sum
    (a : ℕ → ℝ)
    (h : ℕ) :
    exercise_7_12_mu a h = (Finset.range h).sum fun i ↦ a i := by
  induction h with
  | zero =>
      simp
  | succ h ih =>
      rw [exercise_7_12_mu_succ, Finset.sum_range_succ, ih]

/-- The cover excess `λ = μ_t - b` used in Exercise 7.12. -/
def exercise_7_12_cover_excess
    (a : ℕ → ℝ)
    (t : ℕ)
    (b : ℝ) : ℝ :=
  exercise_7_12_mu a t - b

/-- Expanding `exercise_7_12_cover_excess a t b` recovers the source formula `λ = μ_t - b`. -/
theorem exercise_7_12_cover_excess_eq
    (a : ℕ → ℝ)
    (t : ℕ)
    (b : ℝ) :
    exercise_7_12_cover_excess a t b = exercise_7_12_mu a t - b :=
  rfl

/-- The excess quantities `ρ_h = max (0, a_h - (a₀ - λ))` used in the GNS auxiliary lifting
function `(7.12)`. -/
def exercise_7_12_rho
    (a : ℕ → ℝ)
    (lam : ℝ) : ℕ → ℝ :=
  fun h ↦ max 0 (a h - (a 0 - lam))

/-- Evaluating `exercise_7_12_rho a λ` at `h` recovers the source formula
`ρ_h = max (0, a_h - (a₀ - λ))`. -/
@[simp] theorem exercise_7_12_rho_apply
    (a : ℕ → ℝ)
    (lam : ℝ)
    (h : ℕ) :
    exercise_7_12_rho a lam h = max 0 (a h - (a 0 - lam)) :=
  rfl

/-- The interval `F_h = (μ_h - λ + ρ_h, μ_{h+1} - λ]` appearing in the piecewise definition of
the auxiliary lifting function `g` from `(7.12)`. -/
def exercise_7_12_F
    (μ ρ : ℕ → ℝ)
    (lam : ℝ)
    (h : ℕ) : Set ℝ :=
  Set.Ioc (μ h - lam + ρ h) (μ (h + 1) - lam)

/-- Membership in `exercise_7_12_F μ ρ λ h` means lying in the interval
`(μ_h - λ + ρ_h, μ_{h+1} - λ]`. -/
theorem mem_exercise_7_12_F_iff
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ} :
    z ∈ exercise_7_12_F μ ρ lam h ↔ μ h - lam + ρ h < z ∧ z ≤ μ (h + 1) - lam := Iff.rfl

/-- The interval `S_h = (μ_h - λ, μ_h - λ + ρ_h]` appearing in the piecewise definition of the
auxiliary lifting function `g` from `(7.12)`. -/
def exercise_7_12_S
    (μ ρ : ℕ → ℝ)
    (lam : ℝ)
    (h : ℕ) : Set ℝ :=
  Set.Ioc (μ h - lam) (μ h - lam + ρ h)

/-- Membership in `exercise_7_12_S μ ρ λ h` means lying in the interval
`(μ_h - λ, μ_h - λ + ρ_h]`. -/
theorem mem_exercise_7_12_S_iff
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ} :
    z ∈ exercise_7_12_S μ ρ lam h ↔ μ h - lam < z ∧ z ≤ μ h - lam + ρ h := Iff.rfl

/-- The pointwise value contributed by the `h`-th piece of the auxiliary lifting function
`g` from `(7.12)`. -/
private noncomputable def pieceValue
    (μ ρ : ℕ → ℝ)
    (lam z : ℝ)
    (h : ℕ) : ℝ :=
  let _ := Classical.propDecidable
  if z ∈ exercise_7_12_F μ ρ lam h then
    (h : ℝ)
  else if 1 ≤ h ∧ z ∈ exercise_7_12_S μ ρ lam h then
    (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1
  else
    0

/-- The canonical auxiliary lifting function `g` from `(7.12)`, formed by taking the maximum
piece value among the first `t` stages and fixing the value `0` at the origin. -/
noncomputable def exercise_7_12_g
    (t : ℕ)
    (μ ρ : ℕ → ℝ)
    (lam : ℝ) : ℝ → ℝ :=
  let _ := Classical.propDecidable
  fun z ↦
    if z = 0 then
      0
    else
      sSup ({0} ∪ {r | ∃ h ∈ Finset.range t, r = pieceValue μ ρ lam z h})

/-- At the origin, the auxiliary lifting function `(7.12)` vanishes. -/
theorem exercise_7_12_g_zero
    {t : ℕ}
    {μ ρ : ℕ → ℝ}
    {lam : ℝ} :
    exercise_7_12_g t μ ρ lam 0 = 0 := by
  classical
  simp [exercise_7_12_g]

private theorem exercise_7_12_g_pieceSet_bddAbove
    (t : ℕ)
    (μ ρ : ℕ → ℝ)
    (lam z : ℝ) :
    BddAbove ({0} ∪ {r | ∃ h ∈ Finset.range t, r = pieceValue μ ρ lam z h}) := by
  have hfinite :
      ({r | ∃ h ∈ Finset.range t, r = pieceValue μ ρ lam z h} : Set ℝ).Finite := by
    refine ((Finset.finite_toSet (Finset.range t)).image (pieceValue μ ρ lam z)).subset ?_
    rintro r ⟨h, hh, rfl⟩
    exact ⟨h, by simpa using hh, rfl⟩
  have hzero : ({0} : Set ℝ).Finite := by simp
  exact hzero.bddAbove.union hfinite.bddAbove

/-- Membership in `F_h` with `h < t` contributes the stage value `h` to the supremum defining
the auxiliary lifting function `(7.12)`. -/
theorem exercise_7_12_le_g_of_mem_F
    {t : ℕ}
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ}
    (hh : h < t)
    (hz0 : z ≠ 0)
    (hz : z ∈ exercise_7_12_F μ ρ lam h) :
    (h : ℝ) ≤ exercise_7_12_g t μ ρ lam z := by
  classical
  have hmem :
      (h : ℝ) ∈
        ({0} ∪ {r | ∃ k ∈ Finset.range t, r = pieceValue μ ρ lam z k}) := by
    right
    refine ⟨h, by simpa using hh, ?_⟩
    simp [pieceValue, hz]
  simpa [exercise_7_12_g, hz0] using
    (le_csSup_of_le (exercise_7_12_g_pieceSet_bddAbove t μ ρ lam z) hmem le_rfl)

/-- Membership in `S_h` with `1 ≤ h < t` contributes the source affine interpolation value to the
supremum defining the auxiliary lifting function `(7.12)`. -/
theorem exercise_7_12_le_g_of_mem_S
    {t : ℕ}
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ}
    (h1 : 1 ≤ h)
    (hh : h < t)
    (hz0 : z ≠ 0)
    (hz : z ∈ exercise_7_12_S μ ρ lam h) :
    (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 ≤ exercise_7_12_g t μ ρ lam z := by
  classical
  have hz_not_mem_F : z ∉ exercise_7_12_F μ ρ lam h := by
    intro hzF
    exact not_lt_of_ge hz.2 hzF.1
  have hmem :
      (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 ∈
        ({0} ∪ {r | ∃ k ∈ Finset.range t, r = pieceValue μ ρ lam z k}) := by
    right
    refine ⟨h, by simpa using hh, ?_⟩
    simp [pieceValue, hz_not_mem_F, h1, hz]
  simpa [exercise_7_12_g, hz0] using
    (le_csSup_of_le (exercise_7_12_g_pieceSet_bddAbove t μ ρ lam z) hmem le_rfl)

/-- Exercise 7.12. Let `a₀ ≥ ⋯ ≥ a_{t-1} > 0` be the ordered cover weights, let
`μ_h = a₀ + ⋯ + a_{h-1}`, let `λ = μ_t - b`, and let `ρ_h = max (0, a_h - (a₀ - λ))`.
If the prefix cover of size `t` is minimal and `μ₁ - λ ≥ ρ₁ > 0`, then the GNS auxiliary
lifting function `(7.12)` is superadditive on `[0, b]`. -/
theorem exercise_7_12_g_superadditive_on_Icc
    (t : ℕ)
    (a : ℕ → ℝ)
    (b : ℝ)
    (ht : 1 < t)
    (ha_pos : ∀ ⦃h : ℕ⦄, h < t → 0 < a h)
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    (hcover_drop_last : exercise_7_12_mu a t - a (t - 1) ≤ b)
    (hcover_sum : b < exercise_7_12_mu a t)
    (hmu1 :
      exercise_7_12_mu a 1 - exercise_7_12_cover_excess a t b ≥
        exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1)
    (hrho1_pos : 0 < exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1) :
    let μ := exercise_7_12_mu a
    let lam := exercise_7_12_cover_excess a t b
    let ρ := exercise_7_12_rho a lam
    is_superadditive_on_Icc (exercise_7_12_g t μ ρ lam) b := sorry
