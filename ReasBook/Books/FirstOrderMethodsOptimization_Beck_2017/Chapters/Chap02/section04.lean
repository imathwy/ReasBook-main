import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_4 (from Chap02) -/
open Filter
open scoped Topology

universe u

variable {E : Type u}

section

variable [TopologicalSpace E] (g : E → EReal)

/- Definition 2.4: an extended-real-valued function is continuous over its domain exactly when it
is continuous on its effective domain in the canonical mathlib sense `ContinuousOn g
(effective_domain g)`. -/
#check (ContinuousOn g (effective_domain g))

end

section

variable [TopologicalSpace E] [FirstCountableTopology E] {g : E → EReal}

-- Proof sketch: rewrite `ContinuousOn g (effective_domain g)` as continuity of the restricted
-- map on the subtype `effective_domain g`, use `continuous_iff_seqContinuous`, then translate the
-- subtype convergence hypothesis back to ambient convergence with `tendsto_subtype_rng`.
/-- In a first-countable domain, continuity of an extended-real-valued function on its effective
domain is equivalent to preservation of limits of sequences valued in that domain. -/
theorem continuousOn_effective_domain_iff_subtype_seq_tendsto :
    ContinuousOn g (effective_domain g) ↔
      ∀ x : ℕ → effective_domain g, ∀ xstar : effective_domain g,
        Tendsto (fun n ↦ (x n : E)) atTop (𝓝 (xstar : E)) →
          Tendsto (fun n ↦ g (x n : E)) atTop (𝓝 (g (xstar : E))) := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_seqContinuous, SeqContinuous]
  constructor
  · intro hg x xstar hx
    simpa using hg ((tendsto_subtype_rng).2 hx)
  · intro hg x xstar hx
    simpa using hg x xstar ((tendsto_subtype_rng).1 hx)

end

/-! ### Example_2_4 (from Chap02) -/
open scoped BigOperators

universe u

/-- The scalar `{0, 1}`-valued indicator of the nonzero locus, expressed via the canonical set
indicator. -/
noncomputable def l0Indicator (y : ℝ) : ℝ :=
  ({0} : Set ℝ)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y

-- Proof sketch: unfold `l0Indicator`; since `0 ∉ ({0} : Set ℝ)ᶜ`, the indicator takes the value
-- `0` at the origin.
/-- The scalar `ℓ₀` indicator vanishes at the origin. -/
@[simp] theorem l0Indicator_zero :
    l0Indicator 0 = 0 := by
  simp [l0Indicator]

-- Proof sketch: unfold `l0Indicator`; when `y ≠ 0`, the point lies in `({0} : Set ℝ)ᶜ`, so the
-- indicator takes the constant branch value `1`.
/-- Away from the origin, the scalar `ℓ₀` indicator is `1`. -/
@[simp] theorem l0Indicator_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    l0Indicator y = 1 := by
  simp [l0Indicator, hy]

section

-- Proof sketch: unfold `l0Indicator`; if `a < 0`, neither branch can satisfy
-- `l0Indicator y ≤ a`, since both possible values `0` and `1` are nonnegative.
/-- The sublevel set of `l0Indicator` is empty below `0`. -/
theorem l0Indicator_sublevelSet_of_lt_zero {a : ℝ} (ha : a < 0) :
    l0Indicator ⁻¹' Set.Iic a = ∅ := sorry

-- Proof sketch: unfold `l0Indicator`; for `0 ≤ a < 1`, the inequality
-- `l0Indicator y ≤ a` holds exactly when the branch value is `0`, i.e. exactly when `y = 0`.
/-- Between `0` and `1`, the sublevel set of `l0Indicator` is the singleton `{0}`. -/
theorem l0Indicator_sublevelSet_of_nonneg_of_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    l0Indicator ⁻¹' Set.Iic a = ({0} : Set ℝ) := sorry

-- Proof sketch: unfold `l0Indicator`; both possible values `0` and `1` are bounded above by any
-- `a ≥ 1`, so every real number lies in the sublevel set.
/-- Once the level is at least `1`, the sublevel set of `l0Indicator` is all of `ℝ`. -/
theorem l0Indicator_sublevelSet_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    l0Indicator ⁻¹' Set.Iic a = Set.univ := sorry

-- Proof sketch: apply `lowerSemicontinuous_iff_isClosed_preimage`; the previous three lemmas give
-- an explicit description of every sublevel set, and each resulting set is closed in `ℝ`.
/-- The scalar indicator entering the `ℓ₀` example is closed, i.e. lower semicontinuous. -/
theorem l0Indicator_lowerSemicontinuous :
    LowerSemicontinuous l0Indicator := sorry

section

variable {ι : Type u} [Fintype ι]

-- Proof sketch: `hammingNorm x` is the canonical owner object for the number of nonzero
-- coordinates of `x`, while each term `l0Indicator (x i)` contributes `1` exactly when `x i ≠ 0`
-- and `0` otherwise; compare the resulting finite sum with `(hammingNorm x : ℝ)`.
/-- The `ℓ₀` count is the finite sum of the scalar nonzero indicators of the coordinates. -/
theorem hammingNorm_eq_sum_l0Indicator (x : ι → ℝ) :
    (hammingNorm x : ℝ) = ∑ i, l0Indicator (x i) := sorry

-- Proof sketch: rewrite the real-valued `ℓ₀` count using `hammingNorm_eq_sum_l0Indicator`; for
-- each coordinate `i`, the map `x ↦ l0Indicator (x i)` is lower semicontinuous by composing
-- `l0Indicator_lowerSemicontinuous` with the continuous evaluation map `x ↦ x i`, and then apply
-- `lowerSemicontinuous_sum`.
/-- Example 2.4: the `ℓ₀` function on a finite real coordinate space is closed, equivalently
lower semicontinuous, because it is the finite sum of the coordinatewise nonzero indicator. -/
theorem hammingNorm_lowerSemicontinuous :
    LowerSemicontinuous (fun x : ι → ℝ ↦ (hammingNorm x : ℝ)) := sorry

end

end

/-! ### Lemma_2_4 (from Chap02) -/
open scoped Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: expand `support_function`; for `α ≥ 0`, move the scalar through the dual pairing
-- and then through the supremum over the nonempty image set.
/-- Lemma 2.4 (1): (a) the support function is positively homogeneous in the dual variable:
for a nonempty set `C` and `α ≥ 0`, one has `σ_C (α y) = α σ_C (y)`. -/
theorem support_function_nonneg_smul_dual
    (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) {α : ℝ} (hα : 0 ≤ α) :
    support_function C (α • y) = (α : EReal) * support_function C y := sorry

-- Proof sketch: expand `support_function`; for each `x ∈ C`, linearity gives
-- `(y₁ + y₂) x = y₁ x + y₂ x`, and taking suprema over the same set yields the usual
-- subadditivity inequality; for `C = ∅`, both sides reduce to `⊥`-valued expressions in `EReal`.
/-- Lemma 2.4 (2): (b) the support function is subadditive on the dual space:
for any set `C`, `σ_C (y₁ + y₂) ≤ σ_C (y₁) + σ_C (y₂)`. -/
theorem support_function_add_le
    (C : Set E) (y₁ y₂ : Module.Dual ℝ E) :
    support_function C (y₁ + y₂) ≤ support_function C y₁ + support_function C y₂ := sorry

-- Proof sketch: rewrite `α • C` as the image of `C` under `x ↦ α • x`, expand
-- `support_function`, and use `y (α • x) = α * y x` with `α ≥ 0` to pull the scalar outside the
-- supremum.
/-- Lemma 2.4 (3): (c) scaling the set by a nonnegative scalar scales its support function by the
same scalar. -/
theorem support_function_smul_set
    (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) {α : ℝ} (hα : 0 ≤ α) :
    support_function (α • C) y = (α : EReal) * support_function C y := sorry

-- Proof sketch: rewrite `A + B` as the Minkowski sum of pointwise additions, expand the defining
-- supremum, use `y (a + b) = y a + y b`, and separate the supremum over pairs into the sum of the
-- two one-variable suprema; if either set is empty, both sides are `⊥` by the definition of
-- `support_function` and `EReal.add_bot`/`EReal.bot_add`.
/-- Lemma 2.4 (4): (d) the support function of a Minkowski sum equals the sum of the support
functions. -/
theorem support_function_minkowski_sum
    (A B : Set E) (y : Module.Dual ℝ E) :
    support_function (A + B) y = support_function A y + support_function B y := sorry

end

/-! ### Proposition_2_4 (from Chap02) -/
noncomputable section

-- Proof sketch: specialize `support_function_eq_indicatorFunction_polarCone` to the nonnegative
-- orthant `Set.Ici (0 : Fin n → ℝ)`. Under the Euclidean identification
-- `dotProductEquiv ℝ (Fin n) : ℝ^n ≃ₗ (ℝ^n)*`, membership in the polar cone is exactly
-- coordinatewise nonpositivity, so the indicator becomes the one of the Euclidean-dual image of
-- `Set.Iic 0`.
private theorem polar_cone_nonnegative_orthant_eq_image_nonpositive_orthant (n : ℕ) :
    polar_cone (Set.Ici (0 : Fin n → ℝ)) =
      dotProductEquiv ℝ (Fin n) '' Set.Iic (0 : Fin n → ℝ) := by
  ext y
  constructor
  · intro hy
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm y, ?_, by simp⟩
    intro i
    have hyi : y (Pi.single i (1 : ℝ)) ≤ 0 :=
      (mem_polar_cone _ _).mp hy (Pi.single i 1) (by simp)
    simpa [dotProductEquiv] using hyi
  · rintro ⟨v, hv, rfl⟩
    rw [mem_polar_cone]
    intro x hx
    simpa [dotProductEquiv, zero_dotProduct] using
      dotProduct_le_dotProduct_of_nonneg_right hv hx

/-- Proposition 2.4: in `ℝ^n`, under the Euclidean identification of the dual with `ℝ^n`, the
support function of the nonnegative orthant is the indicator function of the nonpositive orthant. -/
theorem support_function_nonnegative_orthant_eq_indicator_nonpositive_dual_orthant
    (n : ℕ) :
    support_function (Set.Ici (0 : Fin n → ℝ)) =
      extendedIndicator (dotProductEquiv ℝ (Fin n) '' Set.Iic (0 : Fin n → ℝ)) := by
  calc
    support_function (Set.Ici (0 : Fin n → ℝ))
        = extendedIndicator (polar_cone (Set.Ici (0 : Fin n → ℝ))) :=
          support_function_eq_indicatorFunction_polarCone (Set.Ici (0 : Fin n → ℝ))
            (by
              rw [isCone_iff_smul_mem]
              intro a ha x hx i
              simpa using mul_nonneg ha (hx i))
            (by simp)
    _ = extendedIndicator (dotProductEquiv ℝ (Fin n) '' Set.Iic (0 : Fin n → ℝ)) := by
          congr 1
          simpa using polar_cone_nonnegative_orthant_eq_image_nonpositive_orthant n

/-! ### Theorem_2_4 (from Chap02) -/
universe u

variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: apply `LowerSemicontinuousOn.exists_isMinOn` on the compact set `C`; then compare
-- the minimizer with a point of `C ∩ effective_domain f` to show
-- that the minimizing point also lies in `effective_domain f`.
/-- Theorem 2.4 (2): if `f` is lower semicontinuous on a compact set `C` and `C` meets the
effective domain of `f`, then `f` attains its minimum on `C`, and the minimizer can be chosen in
the effective domain. -/
theorem exists_isMinOn_on_compact (f : E → EReal) (C : Set E)
    (h_lsc : LowerSemicontinuousOn f C)
    (hC : IsCompact C)
    (hCdom : (C ∩ effective_domain f).Nonempty) :
    ∃ x ∈ C ∩ effective_domain f, IsMinOn f C x := by
  obtain ⟨y, hyC, hy_dom⟩ := hCdom
  obtain ⟨x, hxC, hxmin⟩ := h_lsc.exists_isMinOn ⟨y, hyC⟩ hC
  refine ⟨x, ⟨hxC, ?_⟩, hxmin⟩
  exact lt_of_le_of_lt (isMinOn_iff.mp hxmin y hyC) hy_dom

-- Proof sketch: if `C` is empty, any real number is a lower bound. Otherwise choose a minimizer
-- `x⋆` from the owner theorem `LowerSemicontinuousOn.exists_isMinOn`. If `f x⋆ = ⊤`, then
-- minimality forces `f = ⊤` on `C`, so again any real number is a lower bound. If `f x⋆ ≠ ⊤`,
-- the local non-`⊥` hypothesis on `C` makes `(f x⋆).toReal` a genuine real number whose coercion
-- back to `EReal` equals `f x⋆`, and minimality gives the desired lower bound.
/-- Theorem 2.4 (1): if `f` is lower semicontinuous on a compact set `C`, never takes the value
`-∞` on `C`, then `f` admits a real lower bound on `C`. -/
theorem exists_real_lower_bound_on_compact (f : E → EReal) (C : Set E)
    (h_lsc : LowerSemicontinuousOn f C)
    (h_ne_bot : ∀ x ∈ C, f x ≠ ⊥)
    (hC : IsCompact C) :
    ∃ m : ℝ, ∀ x ∈ C, (m : EReal) ≤ f x := by
  by_cases hCne : C.Nonempty
  · obtain ⟨x, hxC, hxmin⟩ := h_lsc.exists_isMinOn hCne hC
    by_cases hx_top : f x = ⊤
    · refine ⟨0, ?_⟩
      intro y hyC
      have hxy : f x ≤ f y := isMinOn_iff.mp hxmin y hyC
      have hy_top : f y = ⊤ := by simpa [hx_top] using hxy
      simp [hy_top]
    · refine ⟨(f x).toReal, ?_⟩
      intro y hyC
      have hxcoe : ((f x).toReal : EReal) = f x := EReal.coe_toReal hx_top (h_ne_bot x hxC)
      simpa [hxcoe] using isMinOn_iff.mp hxmin y hyC
  · refine ⟨0, ?_⟩
    intro x hxC
    exact (hCne ⟨x, hxC⟩).elim

section

variable {E : Type u} [PseudoMetricSpace E] [ProperSpace E]

-- Proof sketch: choose `x₀ ∈ effective_domain f` from properness and minimize `f` on the closed
-- bounded real sublevel set `{x | f x ≤ (f x₀).toReal}`. Properness makes that sublevel set
-- compact, and points outside it have strictly larger objective value, so the same minimizer is
-- global.
/-- A proper lower-semicontinuous extended-real-valued function on a proper pseudometric space,
whose real sublevel sets are all bounded, attains its minimum on `univ`. The minimizer can be
chosen in the effective domain. -/
theorem exists_isMinOn_univ_of_bounded_real_sublevelSets (f : E → EReal)
    (hproper : IsProperExtendedRealFunction f) (h_lsc : LowerSemicontinuous f)
    (hlevel : ∀ a : ℝ, Bornology.IsBounded {x | f x ≤ (a : EReal)}) :
    ∃ x ∈ effective_domain f, IsMinOn f Set.univ x := by
  obtain ⟨x₀, hx₀⟩ := hproper.effective_domain_nonempty
  have hx₀_eq : (((f x₀).toReal : ℝ) : EReal) = f x₀ :=
    EReal.coe_toReal hx₀.ne (hproper.ne_bot x₀)
  let C : Set E := {x | f x ≤ (((f x₀).toReal : ℝ) : EReal)}
  have hC_closed : IsClosed C := by
    simpa [C] using
      (lowerSemicontinuous_iff_isClosed_real_sublevelSets f).mp h_lsc (f x₀).toReal
  have hC_bounded : Bornology.IsBounded C := by
    simpa [C] using hlevel (f x₀).toReal
  have hC_compact : IsCompact C := Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded
  have hx₀C : x₀ ∈ C := by
    simp [C, hx₀_eq]
  obtain ⟨x, hxC, hxmin⟩ :=
    exists_isMinOn_on_compact f C (h_lsc.lowerSemicontinuousOn C) hC_compact ⟨x₀, hx₀C, hx₀⟩
  refine ⟨x, hxC.2, ?_⟩
  intro y _
  by_cases hyC : y ∈ C
  · exact isMinOn_iff.mp hxmin y hyC
  · have hlt : (((f x₀).toReal : ℝ) : EReal) < f y := by
      exact lt_of_not_ge (by simpa [C] using hyC)
    exact hxC.1.trans hlt.le

end
