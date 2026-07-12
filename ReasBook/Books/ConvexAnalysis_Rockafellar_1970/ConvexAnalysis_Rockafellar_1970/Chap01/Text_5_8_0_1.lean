import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Eorder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

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
