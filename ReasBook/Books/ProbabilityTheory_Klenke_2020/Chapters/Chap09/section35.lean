import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_9_35 (from Items/Chap09) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

private lemma abs_rpow_convexOn_univ (p : ℝ) (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hrange_abs : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact abs_nonneg y
    · intro hx
      exact ⟨x, Set.mem_univ x, abs_of_nonneg hx⟩
  have hrpow : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ) (fun x : ℝ ↦ x ^ p) := by
    simpa [hrange_abs] using convexOn_rpow hp
  have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
    simpa [Real.norm_eq_abs] using
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))
  simpa using hrpow.comp habs
    (by
      simpa [hrange_abs] using
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans zero_le_one hp)))

section

variable [SigmaFiniteFiltration μ ℱ]

/-- Theorem 9.35 (1): if `X` is a martingale and `φ : ℝ → ℝ` is convex, then integrability of the
positive part of `φ ∘ X_t` at every time implies that the process `φ(X_t)` is a submartingale. -/
-- Proof sketch: convexity on `ℝ` gives Jensen's inequality for conditional expectation, and the
-- positive-part integrability hypothesis supplies the integrability needed to promote the resulting
-- conditional expectation inequality to the submartingale API.
theorem submartingale_convex_comp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    (hX : Martingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_int : ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ) :
    Submartingale (fun i ω ↦ φ (X i ω)) ℱ μ := sorry

/-- Theorem 9.35 (2): if the time index has a greatest element, then integrability of the positive
part of `φ(X_t)` at the terminal time implies the same integrability at every earlier time. -/
-- Proof sketch: write each earlier value `X i` as the conditional expectation of the terminal value
-- `X ⊤`, apply Jensen's inequality to the convex map `x ↦ (φ x)⁺`, and conclude by monotonicity of
-- expectation under conditional expectation.
theorem integrable_pos_convex_comp_of_top {X : ι → Ω → ℝ} {φ : ℝ → ℝ} [OrderTop ι]
    (hX : Martingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_top : Integrable (fun ω ↦ (φ (X ⊤ ω))⁺) μ) :
    ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ := sorry

/-- Theorem 9.35 (3): if `p ≥ 1` and every `|X_t|^p` is integrable, then the process
`(|X_t|^p)_{t ∈ I}` is a submartingale. -/
-- Proof sketch: specialize part (1) to the convex function `x ↦ |x| ^ p`, using the standard
-- convexity result for `p ≥ 1` together with the assumed integrability of the power process.
theorem submartingale_abs_rpow {X : ι → Ω → ℝ} {p : ℝ}
    (hX : Martingale X ℱ μ) (hp : 1 ≤ p)
    (hXp : ∀ i, Integrable (fun ω ↦ |X i ω| ^ p) μ) :
    Submartingale (fun i ω ↦ |X i ω| ^ p) ℱ μ := by
  refine submartingale_convex_comp hX (abs_rpow_convexOn_univ p hp) ?_
  intro i
  convert hXp i using 1
  ext ω
  exact max_eq_left (Real.rpow_nonneg (abs_nonneg _) _)

end
