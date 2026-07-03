import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_8_0_1 (from Chap01) -/
noncomputable section

open scoped Pointwise Rockafellar
open Function

section

variable {E : Type*} {R : Type*} {𝕜 : Type*}
variable [Monoid R] [Zero R] [Preorder R]
variable [ConditionallyCompleteLattice 𝕜]
variable [Add 𝕜]
variable [ZeroLEOneClass R] [NoBotOrder 𝕜]
variable [MulAction R 𝕜] [MulAction R E]

variable (R)

omit [ConditionallyCompleteLattice 𝕜] [Add 𝕜] [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: a `WithTopBot` value that is neither `⊤` nor `⊥` is represented by a
finite scalar. -/
private theorem withTopBot_exists_coe_of_ne_top_ne_bot {x : WithTopBot 𝕜}
    (hxtop : x ≠ ⊤) (hxbot : x ≠ ⊥) :
    ∃ a : 𝕜, (a : WithTopBot 𝕜) = x := by
  cases x with
  | none =>
      exact (hxtop rfl).elim
  | some x' =>
      cases x' with
      | bot =>
          exact (hxbot rfl).elim
      | coe a =>
          exact ⟨a, rfl⟩

omit [Add 𝕜] [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: order comparison between finite `WithTopBot` values is the same as
order comparison in the base scalar type. -/
private theorem withTopBot_coe_le_coe_iff {a b : 𝕜} :
    ((a : WithTopBot 𝕜) ≤ (b : WithTopBot 𝕜)) ↔ a ≤ b := by
  constructor
  · intro h
    exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp h)
  · intro h
    exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr h)

omit [ConditionallyCompleteLattice 𝕜] [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: the finite coercion of a sum matches addition in `WithTopBot`. -/
private theorem withTopBot_coe_add (a b : 𝕜) :
    ((a + b : 𝕜) : WithTopBot 𝕜) = (a : WithTopBot 𝕜) + b := by
  simp [WithTop.coe_add, WithBot.coe_add]

omit [Add 𝕜] [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: a finite height in `WithTopBot` is never above `⊤`. -/
private theorem withTopBot_top_not_le_coe (μ : 𝕜) :
    ¬ ((⊤ : WithTopBot 𝕜) ≤ (μ : WithTopBot 𝕜)) := by
  simp [top_le_iff]

omit [Add 𝕜] [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: comparing the vertical infimum of the global epigraph `epi f` with a
finite scalar is the same as comparing `f x` with that scalar. -/
private theorem verticalInfimum_epi_le_iff
    (f : E → WithTopBot 𝕜) (x : E) (μ : 𝕜) :
    Function.verticalInfimum (epi f) x ≤ μ ↔ f x ≤ μ := by
  constructor
  · intro hμ
    -- Push the epigraph lower bound `f x ≤ verticalInfimum (epi f) x` through the finite upper
    -- bound on the vertical infimum.
    by_cases htop : f x = (⊤ : WithTopBot 𝕜)
    · have hfx_le : f x ≤ Function.verticalInfimum (epi f) x :=
        Function.le_verticalInfimum_of_subset_epi (subset_rfl : epi f ⊆ epi f) x
      have htop_le : (⊤ : WithTopBot 𝕜) ≤ (μ : WithTopBot 𝕜) := by
        simpa [htop] using le_trans hfx_le hμ
      exact False.elim (withTopBot_top_not_le_coe (μ := μ) htop_le)
    · by_cases hbot : f x = (⊥ : WithTopBot 𝕜)
      · simp [hbot]
      · exact
          le_trans
            (Function.le_verticalInfimum_of_subset_epi (subset_rfl : epi f ⊆ epi f) x)
            hμ
  · intro hμ
    -- Reinsert the witness `(x, μ)` into the epigraph and use the owner upper-bound theorem.
    exact
      Function.verticalInfimum_le_of_mem ((mem_epi_restrict_iff).2 ⟨by simp, hμ⟩)

local notation "R≥0" => Set.Ici (0 : R)

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition forms, for each `fᵢ`, the epigraph family of the
  right scalar multiples `λ ↦ λ •ʳ fᵢ`, then takes the unit slice of the
  fiberwise sum of those families over the common base variable `(λ, x)`.
- `core/canonical`: the chapter owner abstractions are
  `rightScalarMulEpigraphFamily`, `+ᶠ` from `Theorem_3_6`, and
  `Function.verticalInfimum` from Theorem 5.3.
- `bridge/view`: the imported owner family already packages the scaled epigraphs
  `λ ↦ λ •ʳ f`; this file uses the thin reparenthesized view with base `(λ, x)` needed by `+ᶠ`.
  At `λ = 1`, it reduces to the ordinary epigraphs of `f₁` and `f₂`, so the unit slice becomes
  the epigraph of `f₁ + f₂`.
- Primitive data vs derived API: the source-facing unit slice is primitive here and is built
  from the owner family `rightScalarMulEpigraphFamily` through that thin view; the unit-slice
  vertical-infimum formula and its identification with `f₁ + f₂` are derived API.

Domain-style sampling used here:
- `epi`;
- `(+ᶠ)`;
- `Set.mem_fiberwiseSum`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_epi`;
- `WithTopBot.add_eq_bot_iff`;
- `WithTopBot.top_add_of_ne_bot`;
- `WithTopBot.add_top_of_ne_bot`;
- `WithTopBot.canLift_iff_ne_top_ne_bot`.

The source states this proposition for proper convex functions. The unit-slice construction and its
`sInf` formula make sense for arbitrary `WithTopBot 𝕜`-valued functions, but identifying the
resulting vertical infimum with `f₁ + f₂` only needs the pointwise exclusion of the mixed
`⊥`/`⊤` pathologies of `WithTopBot` addition, namely the two branches `f₁ x = ⊤, f₂ x = ⊥` and
`f₂ x = ⊤, f₁ x = ⊥`. The "somewhere finite" component of properness and all convexity
hypotheses are redundant for this displayed equality, so the main declaration is refined to that
minimal faithful interface.
- Ambient minimization: the imported owner declarations already live over the smaller scalar-action
  layer needed to scale the base variable inside the epigraph construction. This file uses no
  additive, module, coordinate, finite-dimensional, or `Fin`-specific structure on `E`, and the
  scalar layer `R` is explicit and independent of the codomain layer `𝕜`.
-/

/-- Helper for Text 5.8.0.1: the reparenthesized right-scaled epigraph family over the common
base variable `(λ, x)`. -/
private def rightScalarMulEpigraphFiberView (f : E → WithTopBot 𝕜) : Set ((R × E) × 𝕜) :=
  {p |
    0 ≤ p.1.1 ∧ Function.verticalInfimum (((p.1.1 : R) • (epi f : Set (E × 𝕜)))) p.1.2 ≤ p.2}

omit [Add 𝕜] [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: the unit slice of the reparenthesized family is the ordinary
epigraph inequality for `f`. -/
@[simp] private theorem mem_rightScalarMulEpigraphFiberView_one
    (f : E → WithTopBot 𝕜) (x : E) (μ : 𝕜) :
    (((1 : R), x), μ) ∈ rightScalarMulEpigraphFiberView R f ↔ f x ≤ μ := by
  constructor
  · intro hmem
    rcases hmem with ⟨-, hμ⟩
    -- At `λ = 1`, the scaled epigraph is the ordinary epigraph, and its vertical infimum is
    -- detected by the same finite-height inequality.
    have hμ' : Function.verticalInfimum (epi f) x ≤ μ := by
      simpa [rightScalarMulEpigraphFiberView, one_smul] using hμ
    exact (verticalInfimum_epi_le_iff (f := f) (x := x) (μ := μ)).1 hμ'
  · intro hμ
    -- Reinsert the unit-slice point into the reparenthesized family using the epigraph witness at
    -- height `μ`.
    have hμ' : Function.verticalInfimum ((1 : R) • epi f) x ≤ μ := by
      have hμ'' : Function.verticalInfimum (epi f) x ≤ μ :=
        (verticalInfimum_epi_le_iff (f := f) (x := x) (μ := μ)).2 hμ
      simpa [one_smul] using hμ''
    exact ⟨zero_le_one, hμ'⟩

/-- Helper for Text 5.8.0.1: the unit slice of the fiberwise sum of the two scaled epigraph
families over the common base `(λ, x)`. -/
def unit_slice_right_scalar_epigraph_sum (f₁ f₂ : E → WithTopBot 𝕜) : Set (E × 𝕜) :=
  {p |
    (((1 : R), p.1), p.2) ∈
      rightScalarMulEpigraphFiberView R f₁ +ᶠ rightScalarMulEpigraphFiberView R f₂}

omit [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: a point `(x, μ)` belongs to the textbook unit slice exactly when
the scalar height `μ` splits as `μ = μ₁ + μ₂` with `μ₁` and `μ₂` lying above `f₁ x` and `f₂ x`,
respectively. -/
theorem mem_unit_slice_right_scalar_epigraph_sum
    (f₁ f₂ : E → WithTopBot 𝕜) (x : E) (μ : 𝕜) :
    (x, μ) ∈ unit_slice_right_scalar_epigraph_sum R f₁ f₂ ↔
      ∃ μ₁ μ₂ : 𝕜, f₁ x ≤ μ₁ ∧ f₂ x ≤ μ₂ ∧ μ₁ + μ₂ = μ := by
  -- Expand the fiberwise-sum witnesses and rewrite each unit slice back to the base functions.
  change (((1 : R), x), μ) ∈
      rightScalarMulEpigraphFiberView R f₁ +ᶠ rightScalarMulEpigraphFiberView R f₂ ↔
    ∃ μ₁ μ₂ : 𝕜, f₁ x ≤ μ₁ ∧ f₂ x ≤ μ₂ ∧ μ₁ + μ₂ = μ
  constructor
  · intro hmem
    rcases (Set.mem_fiberwiseSum
      (C₁ := rightScalarMulEpigraphFiberView R f₁)
      (C₂ := rightScalarMulEpigraphFiberView R f₂)
      (x := (((1 : R), x), μ))).1 hmem with ⟨μ₁, μ₂, h₁, h₂, hsum⟩
    exact ⟨μ₁, μ₂,
      (mem_rightScalarMulEpigraphFiberView_one (R := R) (f := f₁) (x := x) (μ := μ₁)).1 h₁,
      (mem_rightScalarMulEpigraphFiberView_one (R := R) (f := f₂) (x := x) (μ := μ₂)).1 h₂,
      hsum⟩
  · rintro ⟨μ₁, μ₂, h₁, h₂, hsum⟩
    have hmem₁ : (((1 : R), x), μ₁) ∈ rightScalarMulEpigraphFiberView R f₁ :=
      (mem_rightScalarMulEpigraphFiberView_one (R := R) (f := f₁) (x := x) (μ := μ₁)).2 h₁
    have hmem₂ : (((1 : R), x), μ₂) ∈ rightScalarMulEpigraphFiberView R f₂ :=
      (mem_rightScalarMulEpigraphFiberView_one (R := R) (f := f₂) (x := x) (μ := μ₂)).2 h₂
    exact (Set.mem_fiberwiseSum
      (C₁ := rightScalarMulEpigraphFiberView R f₁)
      (C₂ := rightScalarMulEpigraphFiberView R f₂)
      (x := (((1 : R), x), μ))).2 ⟨μ₁, μ₂, hmem₁, hmem₂, hsum⟩

end

section

variable {E : Type*} {𝕜 : Type*}

/-- Helper for Text 5.8.0.1: pointwise compatibility for `WithTopBot` addition, excluding the
mixed `⊤/⊥` branches. -/
def NoMixedTopBot (f₁ f₂ : E → WithTopBot 𝕜) : Prop :=
  ∀ x : E, (f₁ x = ⊤ → f₂ x ≠ ⊥) ∧ (f₂ x = ⊤ → f₁ x ≠ ⊥)

end

section

variable {E : Type*} {R : Type*} {𝕜 : Type*}
variable [Monoid R] [Zero R] [Preorder R] [ZeroLEOneClass R]
variable [AddCommGroup 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [NoBotOrder 𝕜]
variable [MulAction R 𝕜] [MulAction R E]

variable (R)

-- Proof sketch: expand membership in the unit slice by
-- `mem_unit_slice_right_scalar_epigraph_sum`. In the mixed `⊤/⊥` branches excluded by the
-- compatibility guard `h_no_mixed`, the right-hand side is impossible. If one value is `⊥`, any
-- scalar height belongs to the slice; if both values are finite, the slice is exactly the upper
-- ray above the finite sum.
omit [NoBotOrder 𝕜] in
/-- A point `(x, μ)` lies in the unit slice exactly when the scalar height `μ` lies above the
pointwise sum `f₁ x + f₂ x`, assuming that a `⊤` value of one summand never coincides with a
`⊥` value of the other summand. -/
theorem mem_unit_slice_right_scalar_epigraph_sum_iff_add_le
    (f₁ f₂ : E → WithTopBot 𝕜)
    (h_no_mixed : NoMixedTopBot f₁ f₂)
    (x : E) (μ : 𝕜) :
    (x, μ) ∈ unit_slice_right_scalar_epigraph_sum R f₁ f₂ ↔ f₁ x + f₂ x ≤ μ := by
  rw [mem_unit_slice_right_scalar_epigraph_sum R f₁ f₂ x μ]
  -- Route correction: work by the source proof's `⊤`/`⊥` case split, then reduce the finite
  -- branch to ordered-group arithmetic on lifted scalar representatives.
  by_cases h₁top : f₁ x = ⊤
  · have h₂bot : f₂ x ≠ (⊥ : WithTopBot 𝕜) := by
      exact (h_no_mixed x).1 h₁top
    constructor
    · rintro ⟨μ₁, _, hμ₁, -, -⟩
      have : False := by
        simp [h₁top] at hμ₁
      exact False.elim this
    · intro hμ
      -- The left summand is `⊤`, and the compatibility guard rules out the only
      -- branch where `⊤ + _` would collapse to `⊥`.
      have hsum_top : f₁ x + f₂ x = (⊤ : WithTopBot 𝕜) := by
        rw [h₁top]
        cases hfx₂ : f₂ x with
        | none =>
            rfl
        | some x₂ =>
            cases x₂ with
            | bot =>
                exact False.elim (h₂bot hfx₂)
            | coe a =>
                rfl
      have htop_le : (⊤ : WithTopBot 𝕜) ≤ (μ : WithTopBot 𝕜) := by
        rw [← hsum_top]
        exact hμ
      exact False.elim (withTopBot_top_not_le_coe (μ := μ) htop_le)
  by_cases h₂top : f₂ x = ⊤
  · have h₁bot : f₁ x ≠ (⊥ : WithTopBot 𝕜) := by
      exact (h_no_mixed x).2 h₂top
    constructor
    · rintro ⟨_, μ₂, -, hμ₂, -⟩
      have : False := by
        simp [h₂top] at hμ₂
      exact False.elim this
    · intro hμ
      -- The symmetric `⊤` branch uses the same owner lemma on the right.
      have hsum_top : f₁ x + f₂ x = (⊤ : WithTopBot 𝕜) := by
        rw [h₂top]
        cases hfx₁ : f₁ x with
        | none =>
            rfl
        | some x₁ =>
            cases x₁ with
            | bot =>
                exact False.elim (h₁bot hfx₁)
            | coe a =>
                rfl
      have htop_le : (⊤ : WithTopBot 𝕜) ≤ (μ : WithTopBot 𝕜) := by
        rw [← hsum_top]
        exact hμ
      exact False.elim (withTopBot_top_not_le_coe (μ := μ) htop_le)
  by_cases h₁bot : f₁ x = ⊥
  · constructor
    · intro _
      -- Once `f₁ x = ⊥`, the source-side sum is automatically below every finite height.
      have hsum_bot : f₁ x + f₂ x = (⊥ : WithTopBot 𝕜) := by
        rw [h₁bot]
        cases hfx₂ : f₂ x with
        | none =>
            exact False.elim (h₂top hfx₂)
        | some x₂ =>
            cases x₂ with
            | bot =>
                rfl
            | coe a =>
                rfl
      rw [hsum_bot]
      exact bot_le
    · intro _
      by_cases h₂bot' : f₂ x = ⊥
      · exact ⟨μ, 0, by simp [h₁bot], by simp [h₂bot'], by simp⟩
      · have h₂top' : f₂ x ≠ (⊤ : WithTopBot 𝕜) := by
          simpa using h₂top
        -- Lift the finite value of `f₂ x`, then absorb the remaining height into `μ₁`.
        rcases withTopBot_exists_coe_of_ne_top_ne_bot h₂top' h₂bot' with ⟨r₂, hr₂⟩
        refine ⟨μ - r₂, r₂, ?_, ?_, by simp⟩
        · simp [h₁bot]
        · simp [hr₂]
  by_cases h₂bot : f₂ x = ⊥
  · constructor
    · intro _
      -- The symmetric `f₂ x = ⊥` branch again collapses the sum to `⊥`.
      have hsum_bot : f₁ x + f₂ x = (⊥ : WithTopBot 𝕜) := by
        rw [h₂bot]
        cases hfx₁ : f₁ x with
        | none =>
            exact False.elim (h₁top hfx₁)
        | some x₁ =>
            cases x₁ with
            | bot =>
                rfl
            | coe a =>
                rfl
      rw [hsum_bot]
      exact bot_le
    · intro _
      have h₁top' : f₁ x ≠ (⊤ : WithTopBot 𝕜) := by
        simpa using h₁top
      have h₁bot' : f₁ x ≠ (⊥ : WithTopBot 𝕜) := by
        simpa using h₁bot
      -- This is the symmetric finite branch: lift `f₁ x` and put the remainder into `μ₂`.
      rcases withTopBot_exists_coe_of_ne_top_ne_bot h₁top' h₁bot' with ⟨r₁, hr₁⟩
      refine ⟨r₁, μ - r₁, ?_, ?_, by simp⟩
      · simp [hr₁]
      · simp [h₂bot]
  have h₁top' : f₁ x ≠ (⊤ : WithTopBot 𝕜) := by
    simpa using h₁top
  have h₁bot' : f₁ x ≠ (⊥ : WithTopBot 𝕜) := by
    simpa using h₁bot
  have h₂top' : f₂ x ≠ (⊤ : WithTopBot 𝕜) := by
    simpa using h₂top
  have h₂bot' : f₂ x ≠ (⊥ : WithTopBot 𝕜) := by
    simpa using h₂bot
  -- Once both values are finite, the source proof reduces to ordinary ordered-group arithmetic.
  rcases withTopBot_exists_coe_of_ne_top_ne_bot h₁top' h₁bot' with ⟨r₁, hr₁⟩
  rcases withTopBot_exists_coe_of_ne_top_ne_bot h₂top' h₂bot' with ⟨r₂, hr₂⟩
  constructor
  · rintro ⟨μ₁, μ₂, hμ₁, hμ₂, hsum⟩
    have hμ₁' : r₁ ≤ μ₁ := by
      exact withTopBot_coe_le_coe_iff.mp <| by simpa [hr₁] using hμ₁
    have hμ₂' : r₂ ≤ μ₂ := by
      exact withTopBot_coe_le_coe_iff.mp <| by simpa [hr₂] using hμ₂
    have hle : r₁ + r₂ ≤ μ := by
      calc
        r₁ + r₂ ≤ μ₁ + μ₂ := add_le_add hμ₁' hμ₂'
        _ = μ := hsum
    have hle_coe : (((r₁ + r₂ : 𝕜) : WithTopBot 𝕜)) ≤ (μ : WithTopBot 𝕜) :=
      withTopBot_coe_le_coe_iff.mpr hle
    simpa [withTopBot_coe_add, hr₁, hr₂] using hle_coe
  · intro hμ
    have hμ' : r₁ + r₂ ≤ μ := by
      exact withTopBot_coe_le_coe_iff.mp <| by
        simpa [withTopBot_coe_add, hr₁, hr₂] using hμ
    have hr₂le : r₂ ≤ μ - r₁ := by
      exact (le_sub_iff_add_le).2 (by simpa [add_assoc, add_left_comm, add_comm] using hμ')
    refine ⟨r₁, μ - r₁, ?_, ?_, by simp⟩
    · simp [hr₁]
    · have hμ₂ : ((r₂ : 𝕜) : WithTopBot 𝕜) ≤ ((μ - r₁ : 𝕜) : WithTopBot 𝕜) :=
          withTopBot_coe_le_coe_iff.mpr hr₂le
      simpa [hr₂] using hμ₂

omit [NoBotOrder 𝕜] in
/-- Helper for Text 5.8.0.1: the unit slice of the fiberwise sum of the two scaled epigraph
families is exactly the canonical epigraph `epi (f₁ + f₂)`, provided the mixed `⊤/⊥` branches
are excluded. -/
theorem unit_slice_right_scalar_epigraph_sum_eq_epi_add
    (f₁ f₂ : E → WithTopBot 𝕜)
    (h_no_mixed : NoMixedTopBot f₁ f₂) :
    unit_slice_right_scalar_epigraph_sum R f₁ f₂ = epi (f₁ + f₂) := by
  ext p
  rcases p with ⟨x, μ⟩
  simpa [mem_epi_iff] using
    mem_unit_slice_right_scalar_epigraph_sum_iff_add_le R f₁ f₂ h_no_mixed x μ

omit [IsOrderedAddMonoid 𝕜] in
/-- Helper for Text 5.8.0.1: the vertical infimum of the global epigraph of `g` recovers `g`
itself. -/
private theorem verticalInfimum_epi_eq
    (g : E → WithTopBot 𝕜) :
    Function.verticalInfimum (epi g) = g := by
  apply le_antisymm
  · intro x
    by_cases htop : g x = (⊤ : WithTopBot 𝕜)
    · -- In the `⊤` branch, the target inequality is automatic.
      simp [htop]
    · by_cases hbot : g x = (⊥ : WithTopBot 𝕜)
      · -- If `g x = ⊥`, every finite height lies in the epigraph above `x`, so the infimum is
        -- forced down to `⊥`.
        have hle_all : ∀ μ : 𝕜, Function.verticalInfimum (epi g) x ≤ μ := by
          intro μ
          exact
            Function.verticalInfimum_le_of_mem
              ((mem_epi_restrict_iff).2 ⟨by simp, by simp [hbot]⟩)
        have hbot' : Function.verticalInfimum (epi g) x = (⊥ : WithTopBot 𝕜) := by
          by_contra hne
          cases hvi : Function.verticalInfimum (epi g) x with
          | none =>
              have htop' : Function.verticalInfimum (epi g) x = (⊤ : WithTopBot 𝕜) := by
                simpa [WithTopBot] using hvi
              have : (⊤ : WithTopBot 𝕜) ≤ (0 : 𝕜) := by
                simpa [htop'] using hle_all 0
              exact (withTopBot_top_not_le_coe (μ := 0) this).elim
          | some z =>
              cases hz : z with
              | bot =>
                  have hbot'' : Function.verticalInfimum (epi g) x = (⊥ : WithTopBot 𝕜) := by
                    simpa [WithTopBot, hz] using hvi
                  exact hne hbot''
              | coe a =>
                  have hcoe : Function.verticalInfimum (epi g) x = (a : WithTopBot 𝕜) := by
                    simpa [WithTopBot, hz] using hvi
                  rcases exists_not_ge a with ⟨μ, hnaμ⟩
                  have haμ : (a : WithTopBot 𝕜) ≤ μ := by
                    simpa [hcoe] using hle_all μ
                  exact hnaμ (withTopBot_coe_le_coe_iff.mp haμ)
        simp [hbot, hbot']
      · -- In the finite branch, evaluate the vertical-infimum inequality at the finite height
        -- witness coming from `(x, g x) ∈ epi g`.
        rcases withTopBot_exists_coe_of_ne_top_ne_bot htop hbot with ⟨a, ha⟩
        have hle : Function.verticalInfimum (epi g) x ≤ a := by
          exact
            Function.verticalInfimum_le_of_mem
              ((mem_epi_restrict_iff).2 ⟨by simp, by simp [ha]⟩)
        simpa [ha] using hle
  · -- The reverse inequality is the canonical lower bound of a function by the vertical infimum
    -- of any containing epigraph.
    exact Function.le_verticalInfimum_of_subset_epi (subset_rfl : epi g ⊆ epi g)

-- Proof sketch: first identify the unit slice with the canonical epigraph `epi (f₁ + f₂)` via
-- `unit_slice_right_scalar_epigraph_sum_eq_epi_add`. Then apply the owner theorem
-- `Function.verticalInfimum_epi`.
/-- Text 5.8.0.1: if neither function takes the value `+∞` at a point where the other takes the
value `-∞`, then the vertical infimum obtained from the unit slice of the fiberwise sum of their
two scaled epigraphs is exactly the pointwise sum `f₁ + f₂`. -/
theorem unit_slice_right_scalar_epigraph_sum_infimum_eq_add
    (f₁ f₂ : E → WithTopBot 𝕜)
    (h_no_mixed : NoMixedTopBot f₁ f₂) :
    Function.verticalInfimum (unit_slice_right_scalar_epigraph_sum R f₁ f₂) = f₁ + f₂ := by
  rw [unit_slice_right_scalar_epigraph_sum_eq_epi_add R f₁ f₂ h_no_mixed]
  exact verticalInfimum_epi_eq (g := f₁ + f₂)

/-! ### Text_5_8_0_2 (from Chap01) -/
noncomputable section

open scoped Rockafellar

namespace Function

/-- Helper for Text 5.8.0.2: the `WithTopBot`-valued heights in the vertical fiber of `F` above
`x`. -/
def verticalHeights (F : Set (E × 𝕜)) (x : E) : Set (WithTopBot 𝕜) :=
  ((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F}

/-- Helper for Text 5.8.0.2: the vertical infimum of `F` takes the infimum of the heights in the
vertical fiber above each base point. -/
noncomputable def verticalInfimum [ConditionallyCompleteLattice 𝕜] (F : Set (E × 𝕜)) :
    E → WithTopBot 𝕜 :=
  fun x ↦ sInf (verticalHeights F x)

/-- Helper for Text 5.8.0.2: every point of `F` gives an upper bound on the vertical infimum at
its base point. -/
theorem verticalInfimum_le_of_mem [ConditionallyCompleteLattice 𝕜]
    {F : Set (E × 𝕜)} {x : E} {μ : 𝕜} (h : (x, μ) ∈ F) :
    verticalInfimum F x ≤ μ := by
  exact sInf_le ⟨μ, h, rfl⟩

/-- Helper for Text 5.8.0.2: if `F` lies in the epigraph of `h`, then `h` is pointwise bounded
above by the vertical infimum attached to `F`. -/
theorem le_verticalInfimum_of_subset_epi [ConditionallyCompleteLattice 𝕜]
    {F : Set (E × 𝕜)} {h : E → WithTopBot 𝕜} (hF : F ⊆ epi h) :
    h ≤ verticalInfimum F := by
  intro x
  refine le_sInf ?_
  rintro _ ⟨μ, hμF, rfl⟩
  simpa [verticalHeights, mem_epi_restrict_iff] using hF hμF

end Function

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

local notation "R≥0" => Set.Ici (0 : R)

variable [Zero R] [Preorder R]
variable [ConditionallyCompleteLattice 𝕜] [SMul R 𝕜] [SMul R E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition forms, for each `fᵢ`, the three-variable family obtained from
  the scaled epigraph vertical-infimum view of `fᵢ`, then takes the common-`λ` sum set `K`, its
  `λ = 1` slice `F`, and the vertical infimum of that slice.
- `core/canonical`: the owner abstractions are the earlier chapter declarations
  `+ᶠ` from `Theorem_3_6`, the chapter epigraph owner `epi` applied to the
  canonical function `(λ, x) ↦ verticalInfimum (λ • epi f) x`,
  the item-local owner `Function.verticalInfimum`, and the item-local
  `infimal_convolution` owner below.
- `bridge/view`: the source set `K` is a thin view of the owner `+ᶠ` over the
  common scalar parameter, built directly from the public family
  `rightScalarMulEpigraphFamily`; at `λ = 1`, the scaled-epigraph vertical infimum is just `f`,
  so the slice
  `F` becomes the ordinary epigraph-sum description of infimal convolution from the earlier
  section.
- `primitive data vs derived API`: the source-facing family
  `rightScalarMulEpigraphFamily` is primitive for the later Minkowski-sum item, while the present
  source-facing slice `F` is defined directly from the owners
  `rightScalarMulEpigraphFamily` and `+ᶠ`. The function on the slice is presented
  through the owner `Function.verticalInfimum`, and the identification with the item-local
  `infimal_convolution` is derived API.

Domain-style sampling used here:
- `(+ᶠ)`;
- `Set.mem_fiberwiseSum`;
- `epi`;
- `mem_epi_restrict_iff`;
- `rightScalarMulEpigraphFamily`;
- `Function.verticalInfimum`;
- the item-local `infimal_convolution` owner.

The book states this proposition for proper convex functions, but the displayed identification of
the constructed function with `f₁ □ f₂` depends only on the item-local infimal-convolution owner
and the earlier right-scalar-multiple owner, so the redundant properness and convexity hypotheses
are omitted from the main declaration. The only function-side guard that remains is the pointwise
exclusion of `⊥`, matching the textbook surface without forcing extra structure into the owner.
- Ambient minimization: the primitive owner `rightScalarMulEpigraphFamily` uses only the scalar
  action and the preorder structure needed to form the nonnegative scalar parameter; the scalar
  parameter type and codomain are kept
  separate (`R` and `𝕜`) so this owner does not force the ambient codomain to coincide with the
  scaling type. The primitive common-`λ` slice itself needs additive structure only on the scalar
  height coordinate used by `+ᶠ`; additive structure on `E` appears only when comparing that slice
  with the ordinary epigraph Minkowski sum and then with `infimal_convolution`. No additive-group
  structure is frozen into the public theorem surface.
-/

/-- The three-variable epigraph family of the right scalar multiples `f λ`, with the nonnegative
scalar parameter recorded in the first coordinate. -/
def rightScalarMulEpigraphFamily (f : E → WithTopBot 𝕜) : Set (R × E × 𝕜) :=
  {p |
    ∃ h_lam : 0 ≤ p.1,
      Function.verticalInfimum ((((⟨p.1, h_lam⟩ : R≥0) : R) • epi f) : Set (E × 𝕜)) p.2.1 ≤
        p.2.2}

/-- Membership in `rightScalarMulEpigraphFamily` is exactly the epigraph inequality for the
corresponding canonical scaled epigraph owner. -/
@[simp] theorem mem_rightScalarMulEpigraphFamily
    (f : E → WithTopBot 𝕜) (lam : R≥0) (x : E) (μ : 𝕜) :
    ((lam : R), x, μ) ∈ rightScalarMulEpigraphFamily f ↔
      Function.verticalInfimum ((lam : R) • epi f) x ≤ μ := by
  constructor
  · rintro ⟨h_lam, hμ⟩
    -- Compare the witness packaged from `h_lam` with the canonical subtype `lam`.
    have hsubtype : (⟨(lam : R), h_lam⟩ : R≥0) = lam := by
      ext
      rfl
    simpa [hsubtype] using hμ
  · intro h
    -- Reinsert the canonical nonnegative scalar as the defining witness.
    exact ⟨lam.2, by simpa using h⟩

/-- A point `((λ : R), x, μ)` lies in the right-scalar-multiple epigraph family exactly when
the height `μ` lies above the vertical-infimum value at `x` of the scaled epigraph `λ (epi f)`. -/
@[simp] theorem mem_rightScalarMulEpigraphFamily_verticalInfimum
    (f : E → WithTopBot 𝕜) (lam : R≥0) (x : E) (μ : 𝕜) :
    ((lam : R), x, μ) ∈ rightScalarMulEpigraphFamily f ↔
      Function.verticalInfimum ((lam : R) • epi f) x ≤ μ := by
  -- This is the direct owner-level membership rewrite for the scaled epigraph family.
  exact mem_rightScalarMulEpigraphFamily (f := f) (lam := lam) x μ

end

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

local notation "R≥0" => Set.Ici (0 : R)

variable [Monoid R] [Zero R] [Preorder R]
variable [ConditionallyCompleteLattice 𝕜] [MulAction R 𝕜] [MulAction R E]

/-- At the unit scalar, membership in the right-scalar-multiple epigraph family is exactly
membership in the ordinary epigraph of `f`. -/
@[simp] theorem mem_rightScalarMulEpigraphFamily_one
    [ZeroLEOneClass R] [NoBotOrder 𝕜]
    (f : E → WithTopBot 𝕜) (x : E) (μ : 𝕜) :
    ((1 : R), x, μ) ∈ rightScalarMulEpigraphFamily f ↔ f x ≤ μ := by
  constructor
  · intro h
    have h_vertical : Function.verticalInfimum (epi f) x ≤ μ := by
      simpa [one_smul] using
        (mem_rightScalarMulEpigraphFamily (f := f)
          (lam := (⟨(1 : R), zero_le_one⟩ : R≥0)) x μ).mp h
    exact (Function.le_verticalInfimum_of_subset_epi
      (F := epi f) (h := f) (by intro p hp; simpa using hp) x).trans h_vertical
  · intro h
    have h_mem : (x, μ) ∈ epi f := by
      simpa using h
    have h_vertical : Function.verticalInfimum (epi f) x ≤ μ :=
      Function.verticalInfimum_le_of_mem h_mem
    have h_vertical' : Function.verticalInfimum ((1 : R) • epi f) x ≤ μ := by
      simpa [one_smul] using h_vertical
    simpa [one_smul] using
      (mem_rightScalarMulEpigraphFamily (f := f)
        (lam := (⟨(1 : R), zero_le_one⟩ : R≥0)) x μ).mpr h_vertical'

end

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

variable [Zero R] [One R] [Preorder R]
variable [ConditionallyCompleteLattice 𝕜] [SMul R 𝕜]
variable [Add E] [Add 𝕜]
variable [SMul R E]

/-- The slice `F` at `λ = 1` of the owner fiberwise sum of the two common-`λ` epigraph views,
viewed as a subset of `E × 𝕜`. The scalar parameter type `R` is explicit because the slice lives in
`E × 𝕜` and does not otherwise determine `R` by type inference. -/
def common_scalar_epigraph_slice (R : Type*)
    [Zero R] [One R] [Preorder R]
    [ConditionallyCompleteLattice 𝕜] [SMul R 𝕜]
    [Add E] [Add 𝕜] [SMul R E]
    (f₁ f₂ : E → WithTopBot 𝕜) : Set (E × 𝕜) :=
  {q |
    ((1 : R), q.1, q.2) ∈
      rightScalarMulEpigraphFamily f₁ +ᶠ rightScalarMulEpigraphFamily f₂}

-- Proof sketch: rewrite the source-facing slice by
-- `common_scalar_epigraph_slice_eq_epi_add`, then identify the resulting vertical infimum with the
-- item-local infimal-convolution owner.
end

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

variable [Monoid R] [Zero R] [Preorder R] [ZeroLEOneClass R]
variable [ConditionallyCompleteLattice 𝕜] [MulAction R 𝕜]
variable [NoBotOrder 𝕜]
variable [Add 𝕜]
variable [Add E] [MulAction R E]

/-- The unit slice `F` is exactly the Minkowski sum of the two chapter epigraph owners
`epi f₁` and `epi f₂`. -/
theorem common_scalar_epigraph_slice_eq_epi_add
    (f₁ f₂ : E → WithTopBot 𝕜) :
    common_scalar_epigraph_slice R f₁ f₂ =
      epi f₁ + epi f₂ := by
  refine Set.ext fun p ↦ ?_
  rcases p with ⟨x, μ⟩
  constructor
  · intro hp
    -- Expand the common-`λ` fiberwise-sum witnesses and rewrite each `λ = 1` slice to an
    -- ordinary epigraph inequality.
    rcases (by
      simpa [common_scalar_epigraph_slice, Set.mem_fiberwiseSum] using hp :
        ∃ x₁ μ₁ x₂ μ₂,
          ((1 : R), x₁, μ₁) ∈ rightScalarMulEpigraphFamily f₁ ∧
            ((1 : R), x₂, μ₂) ∈ rightScalarMulEpigraphFamily f₂ ∧
              x₁ + x₂ = x ∧ μ₁ + μ₂ = μ) with
      ⟨x₁, μ₁, x₂, μ₂, h₁, h₂, hsumx, hsummu⟩
    refine Set.mem_add.mpr
      ⟨(x₁, μ₁), ?_, (x₂, μ₂), ?_, Prod.ext hsumx hsummu⟩
    · simpa using (mem_rightScalarMulEpigraphFamily_one f₁ x₁ μ₁).mp h₁
    · simpa using (mem_rightScalarMulEpigraphFamily_one f₂ x₂ μ₂).mp h₂
  · intro hp
    -- Read a point of the Minkowski sum as two epigraph points and package them back into the
    -- common-`λ` fiberwise sum at `λ = 1`.
    rcases Set.mem_add.mp hp with ⟨⟨x₁, μ₁⟩, h₁, ⟨x₂, μ₂⟩, h₂, hsum⟩
    have hsumx : x₁ + x₂ = x := by simpa using congrArg Prod.fst hsum
    have hsummu : μ₁ + μ₂ = μ := by simpa using congrArg Prod.snd hsum
    have hmem₁ : ((1 : R), x₁, μ₁) ∈ rightScalarMulEpigraphFamily f₁ :=
      (mem_rightScalarMulEpigraphFamily_one f₁ x₁ μ₁).mpr <| by simpa using h₁
    have hmem₂ : ((1 : R), x₂, μ₂) ∈ rightScalarMulEpigraphFamily f₂ :=
      (mem_rightScalarMulEpigraphFamily_one f₂ x₂ μ₂).mpr <| by simpa using h₂
    simpa [common_scalar_epigraph_slice, Set.mem_fiberwiseSum] using
      (show ∃ x₁ μ₁ x₂ μ₂,
          ((1 : R), x₁, μ₁) ∈ rightScalarMulEpigraphFamily f₁ ∧
            ((1 : R), x₂, μ₂) ∈ rightScalarMulEpigraphFamily f₂ ∧
              x₁ + x₂ = x ∧ μ₁ + μ₂ = μ from
        ⟨x₁, μ₁, x₂, μ₂, hmem₁, hmem₂, hsumx, hsummu⟩)

end

section

open Function
open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

variable [Monoid R] [Zero R] [Preorder R] [ZeroLEOneClass R]
variable [ConditionallyCompleteLattice 𝕜] [MulAction R 𝕜]
variable [NoBotOrder 𝕜]
variable [Add 𝕜]
variable [Add E] [MulAction R E]

/-- Helper for Text 5.8.0.2: the item-local infimal convolution is the vertical infimum of the
Minkowski sum of the two epigraphs. -/
def infimal_convolution (f₁ f₂ : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  verticalInfimum (epi f₁ + epi f₂)

infixl:70 " □ " => infimal_convolution

/-- Text 5.8.0.2: applying `Function.verticalInfimum` to the `λ = 1` slice of the common-`λ`
sum of the epigraph families of the right scalar multiples of `f₁` and `f₂` yields the infimal
convolution `f₁ □ f₂`, provided both functions are nowhere `⊥`. -/
theorem verticalInfimum_common_scalar_epigraph_slice_eq_infimal_convolution
    (f₁ f₂ : E → WithTopBot 𝕜)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    verticalInfimum (common_scalar_epigraph_slice R f₁ f₂) =
      (f₁ □ f₂ : E → WithTopBot 𝕜) := by
  let _ := hf₁_ne_bot
  let _ := hf₂_ne_bot
  -- Replace the source-defined unit slice by the canonical epigraph Minkowski sum.
  rw [common_scalar_epigraph_slice_eq_epi_add (f₁ := f₁) (f₂ := f₂)]
  -- The item-local infimal-convolution owner is exactly this vertical infimum.
  rfl

end

/-! ### Text_5_8_0_3 (from Chap01) -/
noncomputable section

section

variable {E : Type*} {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

variable (f₁ f₂ : E → WithTopBot 𝕜)

variable [IsStrictOrderedRing 𝕜]

namespace Function

/-- Helper for Text 5.8.0.3: the vertical infimum of a set of finite-height epigraph points is the
pointwise infimum of the corresponding scalar fibers. -/
noncomputable def verticalInfimumOfEpigraphSet (F : Set (E × 𝕜)) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F})

/-- Helper for Text 5.8.0.3: Rockafellar's convex hull of a function is the vertical infimum of
the convex hull of its epigraph. -/
noncomputable def convexHullOfEpigraph (g : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  verticalInfimumOfEpigraphSet (_root_.convexHull 𝕜 (epi g))

local notation "verticalInfimum" => Function.verticalInfimumOfEpigraphSet
local notation:max "conv(" g ")" => Function.convexHullOfEpigraph g

/-- Helper for Text 5.8.0.3: the epigraph of the pointwise infimum of two functions is exactly
the union of their epigraphs. -/
private theorem epi_inf_eq_union_epi
    {E : Type*} {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜]
    (f₁ f₂ : E → WithTopBot 𝕜) :
    epi (f₁ ⊓ f₂) = epi f₁ ∪ epi f₂ := by
  -- Membership in the epigraph of a pointwise infimum is a disjunction in a linear order.
  ext p
  simp

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.8.0.3 identifies `conv(f₁ ⊓ f₂)` with the vertical infimum attached to
  `convexHull 𝕜 (epi f₁ ∪ epi f₂)`.
- `core/canonical`: the only owners needed here are the vertical fiber infimum and the convex hull
  of an epigraph.
- `bridge/view`: the proof is the direct rewrite `epi (f₁ ⊓ f₂) = epi f₁ ∪ epi f₂`.
- Primitive data vs derived API: the pair `(f₁, f₂)` is primitive; the function equality is the
  source-facing derived statement.

Domain-style sampling used here:
- `verticalInfimum`;
- `_root_.convexHull`;
- `epi`.
-/

/-- Helper for Text 5.8.0.3: unfolding Rockafellar's function convex hull and rewriting the
epigraph of the pointwise infimum gives the canonical two-function identity. -/
theorem conv_inf_eq_verticalInfimum_convexHull_union_epi
    : conv(f₁ ⊓ f₂) =
        verticalInfimum (_root_.convexHull 𝕜 (epi f₁ ∪ epi f₂)) := by
  -- Unfold Rockafellar's `conv` owner and rewrite the infimum epigraph as a union.
  let _ : IsStrictOrderedRing 𝕜 := inferInstance
  simp [Function.convexHullOfEpigraph, epi_inf_eq_union_epi]

/-- Text 5.8.0.3 in source-facing form: the vertical infimum attached to the convex hull of the
union of the two scalar epigraphs is `conv(f₁ ⊓ f₂)`. -/
theorem verticalInfimum_convexHull_union_epi_eq_conv_inf
    : verticalInfimum (_root_.convexHull 𝕜 (epi f₁ ∪ epi f₂)) =
        conv(f₁ ⊓ f₂) := by
  -- The labeled theorem is the symmetric restatement of the canonical orientation above.
  simpa using (conv_inf_eq_verticalInfimum_convexHull_union_epi
    (f₁ := f₁) (f₂ := f₂)).symm

end Function

end

/-! ### Text_5_8_0_4 (from Chap01) -/
noncomputable section

section

open scoped Pointwise

variable {E : Type*} {α : Type*} (R : Type*)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.8.0.4 forms the intersection `K₁ ∩ K₂` of the two scaled epigraph
  families attached to `f₁` and `f₂`, then takes its unit slice
  `F = {(x, μ) | (1, x, μ) ∈ K₁ ∩ K₂}`.
- `core/canonical`: the chapter owner abstractions are the imported three-variable family
  `rightScalarMulEpigraphFamily`, its unit-slice membership theorem
  `mem_rightScalarMulEpigraphFamily_one`, the epigraph owner `epi`, the pointwise supremum owner
  `f₁ ⊔ f₂` on `E → WithTopBot α`, and the function-level owner
  `Function.verticalInfimum` from `Theorem_5_3`.
- `bridge/view`: the unit slice of the intersection of the two owner families
  `rightScalarMulEpigraphFamily f₁` and `rightScalarMulEpigraphFamily f₂` is exactly the
  epigraph `epi (f₁ ⊔ f₂)`, so the attached function is obtained canonically by applying
  `Function.verticalInfimum` to that slice.
- Primitive data vs derived API: the only primitive set retained here is the source-facing unit
  slice `F` built from the imported owner family; the fiberwise membership criterion and the
  resulting `Function.verticalInfimum = f₁ ⊔ f₂` statement are derived API, while the raw
  `sInf = (f₁ ⊔ f₂) x` formula is only a companion specification.

Domain-style sampling used here:
- `rightScalarMulEpigraphFamily`;
- `mem_rightScalarMulEpigraphFamily_one`;
- the source-facing unit-slice set expression
  `{p | ((1 : R), p.1, p.2) ∈ rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂}`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_epi`;
- `sup_le_iff` in the lattice `WithTopBot α`.

The source phrases the proposition for proper convex functions, but the displayed unit-slice
identity depends only on the canonical scaled-epigraph owner API already established earlier in the
chapter, so the properness and convexity hypotheses are redundant and omitted.
- Ambient minimization: the primitive source-facing slice expression
  `{p | ((1 : R), p.1, p.2) ∈ rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂}`
  only needs the scalar data needed to form the imported family
  `rightScalarMulEpigraphFamily` together with a distinguished unit scalar `1`; stronger action
  laws are only required by the derived `λ = 1` simplification theorems. The file uses no
  additive, module, coordinate, finite-dimensional, or `Fin`-specific structure.

Layer target: `bridge/view`; this file exposes the textbook unit slice directly as a source-facing
set expression and states the bridge theorems on the canonical owners `epi` and
`Function.verticalInfimum`.
-/

section

variable [Monoid R] [Zero R] [Preorder R]
variable [ConditionallyCompleteLattice α]
variable [MulAction R α] [MulAction R E]
variable [ZeroLEOneClass R] [NoBotOrder α]

@[simp] theorem mem_unit_slice_right_scalar_epigraph_inter
    (f₁ f₂ : E → WithTopBot α) (x : E) (μ : α) :
    (x, μ) ∈ ({p : E × α |
      ((1 : R), p.1, p.2) ∈
        (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)} : Set (E × α)) ↔
      f₁ x ≤ μ ∧ f₂ x ≤ μ := by
  simp

-- Proof sketch: membership in the unit slice means simultaneous membership in the two canonical
-- scaled epigraphs at `λ = 1`. Rewrite each side with
-- `mem_rightScalarMulEpigraphFamily_one`, then package the two inequalities through
-- the canonical pointwise supremum owner `f₁ ⊔ f₂`.
/-- The unit slice of the two scaled epigraph families is exactly the epigraph of the pointwise
maximum, expressed through the canonical binary supremum owner `f₁ ⊔ f₂`. -/
theorem unit_slice_right_scalar_epigraph_inter_eq_epi_sup
    (f₁ f₂ : E → WithTopBot α) :
    ({p : E × α |
      ((1 : R), p.1, p.2) ∈
        (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)} : Set (E × α)) =
      epi (f₁ ⊔ f₂) := by
  ext p
  rcases p with ⟨x, μ⟩
  simp [sup_le_iff]

/-- Helper for Text 5.8.0.4: the vertical infimum of the global epigraph of `g` recovers `g`
itself. -/
private theorem withTopBot_coe_le_coe_iff {β : Type*} [Preorder β] {a b : β} :
    ((a : WithTopBot β) ≤ (b : WithTopBot β)) ↔ a ≤ b := by
  constructor
  · intro h
    exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp h)
  · intro h
    simp [h]

/-- Helper for Text 5.8.0.4: the vertical infimum of the global epigraph of `g` recovers `g`
itself. -/
private theorem verticalInfimum_epi_eq
    (g : E → WithTopBot α) :
    Function.verticalInfimum (epi g) = g := by
  apply le_antisymm
  · intro x
    by_cases htop : g x = (⊤ : WithTopBot α)
    · simp [Function.verticalInfimum, Function.verticalHeights, epi, htop]
    · by_cases hbot : g x = (⊥ : WithTopBot α)
      · have hle_all : ∀ μ : α, Function.verticalInfimum (epi g) x ≤ μ := by
          intro μ
          exact Function.verticalInfimum_le_of_mem
            ((mem_epi_restrict_iff).2 ⟨by simp, by simp [hbot]⟩)
        have hbot' : Function.verticalInfimum (epi g) x = (⊥ : WithTopBot α) := by
          classical
          by_contra hne
          cases hvi : Function.verticalInfimum (epi g) x with
          | none =>
              have htop' : Function.verticalInfimum (epi g) x = (⊤ : WithTopBot α) := by
                simpa [WithTopBot] using hvi
              let μ0 : α := Classical.choice inferInstance
              have : (⊤ : WithTopBot α) ≤ μ0 := by
                simpa [htop'] using hle_all μ0
              have hnot : ¬ ((⊤ : WithTopBot α) ≤ μ0) := by simp
              exact (hnot this).elim
          | some z =>
              cases hz : z with
              | bot =>
                  have hbot'' : Function.verticalInfimum (epi g) x = (⊥ : WithTopBot α) := by
                    simpa [WithTopBot, hz] using hvi
                  exact hne hbot''
              | coe a =>
                  have hcoe : Function.verticalInfimum (epi g) x = (a : WithTopBot α) := by
                    simpa [WithTopBot, hz] using hvi
                  rcases exists_not_ge a with ⟨μ, hnaμ⟩
                  have haμ : (a : WithTopBot α) ≤ μ := by
                    simpa [hcoe] using hle_all μ
                  exact hnaμ (withTopBot_coe_le_coe_iff.mp haμ)
        simp [hbot, hbot']
      · cases h : g x with
        | none => contradiction
        | some z =>
            cases hz : z with
            | bot =>
                have : g x = (⊥ : WithTopBot α) := by
                  simpa [WithTopBot, hz] using h
                exact (hbot this).elim
            | coe a =>
                have ha : g x = (a : WithTopBot α) := by
                  simpa [WithTopBot, hz] using h
                have hxepi : (x, a) ∈ epi g := by
                  exact (mem_epi_restrict_iff).2 ⟨by simp, by simp [ha]⟩
                have hle : Function.verticalInfimum (epi g) x ≤ a :=
                  Function.verticalInfimum_le_of_mem hxepi
                simpa [ha] using hle
  · exact Function.le_verticalInfimum_of_subset_epi (subset_rfl : epi g ⊆ epi g)

-- Proof sketch: rewrite the source-facing unit slice as the intrinsic scalar epigraph of
-- `f₁ ⊔ f₂` using `unit_slice_right_scalar_epigraph_inter_eq_epi_sup`, then apply the owner
-- theorem `verticalInfimum_epi`.
/-- Text 5.8.0.4: the vertical infimum function of the unit slice
`F = {(x, μ) | (1, x, μ) ∈ K₁ ∩ K₂}` is the pointwise maximum of `f₁` and `f₂`,
expressed through the canonical pointwise supremum owner `f₁ ⊔ f₂`. -/
theorem unit_slice_right_scalar_epigraph_inter_infimum_eq_sup
    (f₁ f₂ : E → WithTopBot α) :
    Function.verticalInfimum
      ({p : E × α |
        ((1 : R), p.1, p.2) ∈
          (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)}) =
      f₁ ⊔ f₂ := by
  rw [unit_slice_right_scalar_epigraph_inter_eq_epi_sup R f₁ f₂]
  exact verticalInfimum_epi_eq (g := f₁ ⊔ f₂)

/-- The intrinsic height-set owner `verticalHeights` of the unit slice above `x` has
infimum equal to the pointwise supremum `(f₁ ⊔ f₂) x`. -/
theorem sInf_unit_slice_right_scalar_epigraph_inter_eq_sup
    (f₁ f₂ : E → WithTopBot α) (x : E) :
    sInf
        (Function.verticalHeights
          ({p : E × α |
            ((1 : R), p.1, p.2) ∈
              (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)})
          x) =
      (f₁ ⊔ f₂) x := by
  simpa [Function.verticalInfimum] using
    congrFun (unit_slice_right_scalar_epigraph_inter_infimum_eq_sup R f₁ f₂) x

end

end

/-! ### Theorem_5_8_1 (from Chap01) -/
open scoped BigOperators
open scoped Rockafellar
open Function

noncomputable section

section

variable {E : Type*}
variable {ι : Type*}
variable {𝕜 : Type*}
variable {α : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.8.1 forms, from a finite family of convex functions, the function
  sending `x` to the infimum over all decompositions `x = ∑ i xᵢ` of the finite maximum of the
  values `fᵢ(xᵢ)`.
- `core/canonical`: once the ambient ordered-scalar module structure is available, this source
  owner is the chapter owner `Function.linearImage` from Theorem 5.7 applied to the finite-sum map
  `xs ↦ ∑ i, xs i` and the product-space maximum `xs ↦ ⨆ i, f i (xs i)`.
- `bridge/view`: the `Function.linearImage` presentation is the canonical bridge to the chapter
  owner; the older support-set/`verticalInfimum` packaging is only an implementation view and is
  not kept as primitive public API.
- Primitive data vs derived API: the primitive source data are the family `f` and the
  decomposition relation `∑ i, xᵢ = x`; `infimal_max_convolution` is therefore defined directly by
  the source infimum. The `Function.linearImage` comparison and convexity theorem are derived API.

Domain-style sampling used here:
- `Function.linearImage`, `Function.linearImage_eq_sInf_image`, and
  `Function.isConvex_linearImage` from `Theorem_5_7`;
- `Function.IsConvex.iSup` from `Theorem_5_5`;
- `LinearMap.lsum` / `LinearMap.lsum_apply` from mathlib's finite-product linear algebra API;
- the finite-family owner `finiteInfimalConvolution` from `Text_5_4_1`, which uses the same
  decomposition-image pattern with `∑ i` in place of `⨆ i`.

Layer target: `source-facing`; the textbook operation remains the public owner, defined directly by
its decomposition infimum, while the chapter owner `Function.linearImage` is exposed as the
canonical bridge under stronger ambient module hypotheses.
-/

private def infimalMaxConvolutionFamilyMaximum [ConditionallyCompleteLattice α] [Fintype ι]
    (f : ι → E → WithBotTop α) : (ι → E) → WithBotTop α :=
  fun xs ↦ ⨆ i, f i (xs i)

private def infimalMaxConvolutionDecompositionFiber [AddCommMonoid E] [Fintype ι] (x : E) :
    Set (ι → E) :=
  {xs : ι → E | (∑ i, xs i) = x}

private def infimalMaxConvolutionSumMap [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [Fintype ι] :
    (ι → E) →ₗ[𝕜] E :=
  let _ := Classical.decEq ι
  LinearMap.lsum 𝕜 (fun _ : ι ↦ E) ℕ fun _ ↦ LinearMap.id

section Geometric

variable [ConditionallyCompleteLattice α] [AddCommMonoid E] [Fintype ι]

/-- The finite infimal max-convolution of a finite family of `WithBotTop α`-valued functions
sends `x` to the infimum over all decompositions `x = ∑ i xᵢ` of the finite maximum value among
the terms `f i (xᵢ)`. -/
def infimal_max_convolution (f : ι → E → WithBotTop α) : E → WithBotTop α :=
  fun x ↦
    sInf
      (infimalMaxConvolutionFamilyMaximum f ''
        infimalMaxConvolutionDecompositionFiber (ι := ι) x)

/-- The value of `infimal_max_convolution f` at `x` is the infimum of the image of the
decomposition fiber `xs ↦ ⨆ i, f i (xs i)` with `∑ i, xs i = x`. -/
theorem infimal_max_convolution_eq_sInf_image_decompositions
    (f : ι → E → WithBotTop α) (x : E) :
    infimal_max_convolution f x =
      sInf
        (infimalMaxConvolutionFamilyMaximum f ''
          infimalMaxConvolutionDecompositionFiber (ι := ι) x) := rfl

/-- The value of `infimal_max_convolution f` at `x` is the infimum, over all decompositions
`x = ∑ i xᵢ`, of the finite supremum `⨆ i, f i (xᵢ)`. -/
theorem infimal_max_convolution_eq_sInf_decompositions
    (f : ι → E → WithBotTop α) (x : E) :
    infimal_max_convolution f x =
      sInf {r : WithBotTop α | ∃ xs : ι → E, (∑ i, xs i) = x ∧ r = ⨆ i, f i (xs i)} := by
  rw [infimal_max_convolution_eq_sInf_image_decompositions]
  congr 1
  ext r
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, rfl⟩
  · rintro ⟨xs, hxs, rfl⟩
    exact ⟨xs, hxs, rfl⟩

section

variable [Semiring 𝕜] [Module 𝕜 E]

-- Proof sketch: `Function.linearImage` is already the chapter owner for fiberwise infima along a
-- linear map. For the canonical finite-product sum map
-- `LinearMap.lsum 𝕜 (fun _ : ι ↦ E) ℕ (fun _ ↦ LinearMap.id)`, its fiber over `x` is exactly the
-- set of decompositions of `x`, and the source-facing value assigned to such a decomposition is
-- the family maximum `⨆ i, f i (xs i)`. This bridge stays private because its implementation
-- terms require local helper names and proof-only `DecidableEq` plumbing; the public API keeps
-- only the source-facing owner and its convexity theorem.
private theorem infimal_max_convolution_eq_linearImage
    (f : ι → E → WithBotTop α) :
    infimal_max_convolution f =
      (infimalMaxConvolutionSumMap (𝕜 := 𝕜) (E := E) (ι := ι)) ◁
        infimalMaxConvolutionFamilyMaximum f := by
  classical
  funext x
  rw [infimal_max_convolution_eq_sInf_image_decompositions, linearImage_eq_sInf_image]
  congr 1
  ext r
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    refine ⟨xs, ?_, rfl⟩
    simpa [infimalMaxConvolutionDecompositionFiber, infimalMaxConvolutionSumMap,
      LinearMap.lsum_apply] using hxs
  · rintro ⟨xs, hxs, rfl⟩
    refine ⟨xs, ?_, rfl⟩
    simpa [infimalMaxConvolutionDecompositionFiber, infimalMaxConvolutionSumMap,
      LinearMap.lsum_apply] using hxs

end

end Geometric

section

variable [ConditionallyCompleteLinearOrder 𝕜] [AddCommMonoid E] [Fintype ι]
variable [Ring 𝕜] [Module 𝕜 E]
variable [IsStrictOrderedRing 𝕜]

-- Proof sketch: rewrite `infimal_max_convolution f` as the chapter owner
-- `Function.linearImage` of the canonical sum map on the product space `ι → E` applied to the
-- family maximum `xs ↦ ⨆ i, f i (xs i)`. For each `i`, the coordinate function
-- `xs ↦ f i (xs i)` is convex by composing `f i` with `LinearMap.proj i`, and the family maximum
-- is then convex by `Function.IsConvex.iSup`. Apply `Function.isConvex_linearImage`.
/-- Theorem 5.8.1: if `f₁, …, f_m` are convex functions, then the function
`x ↦ inf {max {f₁(x₁), …, f_m(x_m)} | x₁ + ··· + x_m = x}` is convex. -/
theorem Function.isConvex_infimal_max_convolution
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (infimal_max_convolution f).IsConvex 𝕜 := by
  classical
  rw [infimal_max_convolution_eq_linearImage (𝕜 := 𝕜) (E := E) (ι := ι) (f := f)]
  refine isConvex_linearImage (infimalMaxConvolutionSumMap (𝕜 := 𝕜) (E := E) (ι := ι))
    (infimalMaxConvolutionFamilyMaximum f) ?_
  have hfamily :
      infimalMaxConvolutionFamilyMaximum f =
        ⨆ i, (f i) ∘ (LinearMap.proj i : (ι → E) →ₗ[𝕜] E) := by
    funext xs
    simp [infimalMaxConvolutionFamilyMaximum]
  rw [hfamily]
  refine IsConvex.iSup fun i ↦ ?_
  simpa using (hf_convex i).comp_linearMap (LinearMap.proj i : (ι → E) →ₗ[𝕜] E)

end

section

variable [ConditionallyCompleteLattice α]
variable [AddCommGroup E]

-- Proof sketch: specialize `infimal_max_convolution_eq_sInf_decompositions` to `Fin 2`, where a
-- decomposition of `x` is exactly a pair `(x - y, y)`. The finite supremum over two coordinates
-- becomes `⊔`, and the decomposition set is the image of `y ↦ f₁ (x - y) ⊔ f₂ y`.
/-- Canonical `Fin 2` instance of `infimal_max_convolution`: in a lattice codomain, the binary
family supremum is `⊔`, so the operation is a one-parameter infimum of `f₁ (x - y) ⊔ f₂ y`. -/
theorem infimal_max_convolution_two_apply_sup
    (f₁ f₂ : E → WithBotTop α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x =
      ⨅ y : E, (f₁ (x - y)) ⊔ (f₂ y) := by
  have hsup : ∀ xs : Fin 2 → E,
      (⨆ i : Fin 2, (![f₁, f₂] i) (xs i)) = (f₁ (xs 0)) ⊔ (f₂ (xs 1)) := by
    intro xs
    rw [← Finset.sup_univ_eq_iSup, Finset.univ_fin2]
    simp
  have hdecomp :
      {r : WithBotTop α |
          ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧ r = ⨆ i : Fin 2, (![f₁, f₂] i) (xs i)} =
        {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧
            r = (f₁ (xs 0)) ⊔ (f₂ (xs 1))} := by
    ext r
    constructor
    · rintro ⟨xs, hx, hr⟩
      exact ⟨xs, hx, hr.trans (hsup xs)⟩
    · rintro ⟨xs, hx, hr⟩
      exact ⟨xs, hx, hr.trans (hsup xs).symm⟩
  have hset :
      {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧ r = (f₁ (xs 0)) ⊔ (f₂ (xs 1))} =
        (fun y : E ↦ (f₁ (x - y)) ⊔ (f₂ y)) '' Set.univ := by
    ext r
    constructor
    · rintro ⟨xs, hx, rfl⟩
      refine ⟨xs 1, Set.mem_univ _, ?_⟩
      have hx' : xs 0 + xs 1 = x := by
        simpa [Fin.sum_univ_two] using hx
      have hx0 : xs 0 = x - xs 1 := by
        exact eq_sub_iff_add_eq.mpr hx'
      simp [hx0]
    · rintro ⟨y, -, rfl⟩
      refine ⟨![x - y, y], ?_, rfl⟩
      rw [Fin.sum_univ_two]
      exact sub_add_cancel x y
  calc
    infimal_max_convolution ![f₁, f₂] x
        = sInf {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧
            r = ⨆ i : Fin 2, (![f₁, f₂] i) (xs i)} :=
          infimal_max_convolution_eq_sInf_decompositions _ _
    _ = sInf {r : WithBotTop α | ∃ xs : Fin 2 → E, (∑ i, xs i) = x ∧
          r = (f₁ (xs 0)) ⊔ (f₂ (xs 1))} := congrArg sInf hdecomp
    _ = ⨅ y : E, (f₁ (x - y)) ⊔ (f₂ y) := by
          rw [hset, sInf_image]
          simp

end

section

variable [ConditionallyCompleteLinearOrder α]
variable [AddCommGroup E]

/-- Textbook linear-order specialization of `infimal_max_convolution_two_apply_sup`: in this
setting `⊔` is `max`, yielding the one-parameter infimum of the binary maximum. -/
theorem infimal_max_convolution_two_apply
    (f₁ f₂ : E → WithBotTop α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x =
      ⨅ y : E, max (f₁ (x - y)) (f₂ y) := by
  simpa [sup_eq_maxDefault] using
    infimal_max_convolution_two_apply_sup (f₁ := f₁) (f₂ := f₂) x

end

end

/-! ### Theorem_5_8_2 (from Chap01) -/
open scoped BigOperators

noncomputable section

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*} {α : Type*}
variable [Preorder 𝕜] [AddCommMonoid 𝕜] [One 𝕜]
variable [AddCommMonoid α]
variable [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.8.2 forms the function
  `g(x) = inf {∑ i, (fᵢ λᵢ)(x) | λᵢ ≥ 0, ∑ i, λᵢ = 1}` from a finite family of convex
  functions.
- `core/canonical`: the chapter owner abstractions already fixed upstream are
  `StdSimplex 𝕜 ι` from `Definition_2_2_10`, `Function.IsConvex`, `rightScalarMul`,
  the complete-lattice infimum `⨅ w : StdSimplex 𝕜 ι, ...` on function space, and the
  vertical-infimum owner `Function.verticalInfimum`; the proof pattern is governed by the owner
  theorems
  `Function.isConvex_sum_of_bot_lt` and
  `Function.isConvex_verticalInfimum`.
- `bridge/view`: the simplex constraint is carried by `w : StdSimplex 𝕜 ι`, while the
  nonnegative scalar passed to `rightScalarMul` at coordinate `i` is the canonical owner-side
  datum `⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)`; the convexity proof
  views the pointwise `iInf` through the
  corresponding support-set/vertical-infimum construction, but that wrapper is now only internal
  proof data rather than the public owner.
- Primitive data vs derived API: the simplex owner object and the pointwise `iInf` of the
  corresponding weighted-sum functions are the source-facing data; the explicit `sInf`
  coordinate formula and convexity statement are derived API.
- Layer target: `source-facing`; the simplex infimum remains the public object, while the ambient
  convexity, complete-lattice, and right-scalar APIs are reused from the chapter owners instead of
  being redeclared locally.

Domain-style sampling used here:
- `StdSimplex` from `Definition_2_2_10`;
- `StdSimplex.total` from mathlib's `ConvexSpace`;
- `Function.isConvex_sum_of_bot_lt` from `Theorem_5_2`;
- `rightScalarMul` from `Text_5_4_2`;
- the direct simplex `iInf` owner pattern in Theorem 5.8.4's
  `weighted_infimal_max_convolution`;
- `Function.verticalInfimum` from `Theorem_5_3`;
- `Function.isConvex_verticalInfimum` from `Theorem_5_3`.
- `simplex_right_scalar_infimal_maximum` / `weighted_infimal_max_convolution` in Theorems 5.8.3
  and 5.8.4, whose public owner layer already keeps `ι : Type*` abstract.
- `Function.IsConvex.rightScalarMul` from `Text_5_4_2`.
- Ambient minimization: the source-facing definition and its `sInf` specification only use the
  ambient `𝕜`-scalar action needed by `rightScalarMul`, and `StdSimplex` is indexed by an
  arbitrary finite type. The owner therefore stays at the generic codomain
  `WithBotTop α`; the stronger additive commutative `𝕜`-module structure and codomain
  specialization to `WithBotTop 𝕜` appear only in the derived convexity theorem.
- Primitive-vs-derived refinement: the extra pointwise condition `∀ i x, ⊥ < f i x` is not
  redundant data here; it is the owner-minimal hypothesis used to keep the finite-sum convexity
  route inside chapter owners, while the textbook properness wording is recovered below as a thin
  companion
  via `Function.IsProper.bot_lt`.
-/

variable (𝕜)

/-- The simplex-weighted infimum of right scalar multiples of a finite family `f` sends `x` to
the infimum of `∑ i, (f i wᵢ)(x)` over all simplex weights `w : StdSimplex 𝕜 ι`. The public
owner is the direct pointwise `iInf` over the weighted-sum family, rather than a parallel
support-set wrapper. -/
def simplex_right_scalar_infimal_sum (f : ι → E → WithBotTop α) : E → WithBotTop α :=
  ⨅ w : StdSimplex 𝕜 ι,
    w.sum fun i _ ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i

/-- The value of `simplex_right_scalar_infimal_sum f` at `x` is the infimum over simplex
weights of the sum of the corresponding weighted right scalar multiples. -/
theorem simplex_right_scalar_infimal_sum_eq_sInf
    (f : ι → E → WithBotTop α) (x : E) :
    simplex_right_scalar_infimal_sum 𝕜 f x =
      sInf
        {r : WithBotTop α |
          ∃ w : StdSimplex 𝕜 ι,
            r =
              (w.sum fun i _ ↦
                (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i) x} := by
  rw [simplex_right_scalar_infimal_sum, iInf_apply, ← sInf_range]
  congr
  ext r
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by simpa using hw.symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by simpa using hw.symm⟩

end

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

-- Proof sketch: for each simplex weight `w`, the function
-- `x ↦ (w.sum fun i _ ↦ ((⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i)) x`
-- is convex by combining
-- `Function.IsConvex.rightScalarMul` with the chapter owner theorem
-- `Function.isConvex_sum_of_bot_lt`; the pointwise `⊥`-exclusion is needed here and
-- comes from the hypotheses below. The direct public owner
-- `⨅ w : StdSimplex 𝕜 ι,
--   w.sum (fun i _ ↦ ((⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i))` is then
-- viewed through the corresponding
-- support-set/vertical-infimum construction, so Theorem 5.3 yields convexity.
-- Equivalently, for each `i`, let
-- `Kᵢ = {(λ, x, μ) | 0 ≤ λ ∧ (⟨λ, _⟩ : Set.Ici (0 : 𝕜)) •ʳ f i x ≤ μ}` in `𝕜 × E × 𝕜`;
-- convexity of `f i` gives convexity of this scaled-epigraph family. Form the convex set of
-- triples `(w, x, μ)` with `w : StdSimplex 𝕜 ι` and `μ = w.sum (fun i _ ↦ μᵢ)`, where each
-- `(⟨w.weights i, w.nonneg i⟩, x, μᵢ)` lies in `Kᵢ`. Its simplex slice has
-- vertical infimum exactly `simplex_right_scalar_infimal_sum 𝕜 f`, so Theorem 5.3 yields
-- convexity. No dense-order hypothesis on `𝕜` is needed at this owner layer.
/-- Theorem 5.8.2: the simplex-weighted infimum of a finite family of convex functions is convex.
The owner-minimal chapter form keeps the pointwise `⊥`-exclusion needed by the finite-sum
convexity API; the textbook properness wording is recovered below as a thin companion. -/
theorem isConvex_simplex_right_scalar_infimal_sum
    (f : ι → E → WithBotTop 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_sum 𝕜 f).IsConvex 𝕜 := sorry

/-- Textbook properness-form restatement of Theorem 5.8.2. This companion adds no new
mathematics: `(f i).IsProper` is used only to recover the pointwise `⊥`-exclusion
required by `Function.isConvex_simplex_right_scalar_infimal_sum`. -/
theorem isConvex_simplex_right_scalar_infimal_sum_of_proper
    (f : ι → E → WithBotTop 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_sum 𝕜 f).IsConvex 𝕜 := by
  exact isConvex_simplex_right_scalar_infimal_sum f
    (fun i x ↦ (hf_proper i).bot_lt x)
    hf_convex

end Function

end
