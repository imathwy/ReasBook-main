import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

section General

variable {X Y : ι → Ω → ℝ}

-- Proof sketch: combine `Supermartingale.neg` and `Submartingale.neg`, noting that negating twice
-- returns the original process.
/-- Theorem 9.32 (1): A process is a supermartingale exactly when its pointwise negative is a
submartingale. -/
theorem supermartingale_iff_neg_submartingale :
    Supermartingale X ℱ μ ↔ Submartingale (-X) ℱ μ := sorry

-- Proof sketch: scale each martingale by `a` and `b` using `Martingale.smul`, then add the two
-- resulting martingales with `Martingale.add`.
/-- Theorem 9.32 (2): Real linear combinations of two martingales are again martingales. -/
theorem martingale_linear_combination (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ)
    (a b : ℝ) :
    Martingale (a • X + b • Y) ℱ μ := sorry

-- Proof sketch: apply `Supermartingale.smul_nonneg` to `X` and `Y`, then use
-- `Supermartingale.add` to combine the two nonnegative scalar multiples.
/-- Theorem 9.32 (3): Nonnegative real linear combinations of two supermartingales are again
supermartingales. -/
theorem supermartingale_nonneg_linear_combination (hX : Supermartingale X ℱ μ)
    (hY : Supermartingale Y ℱ μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Supermartingale (a • X + b • Y) ℱ μ := sorry

-- Proof sketch: negate both supermartingales to obtain submartingales, use
-- `Submartingale.sup` on the pointwise maxima, and negate back to identify the pointwise minimum.
/-- Theorem 9.32 (4): The pointwise minimum of two supermartingales is again a supermartingale. -/
theorem supermartingale_inf (hX : Supermartingale X ℱ μ) (hY : Supermartingale Y ℱ μ) :
    Supermartingale (X ⊓ Y) ℱ μ := sorry

end General

variable {𝒢 : Filtration ℕ m0}

section Nat

variable {X : ℕ → Ω → ℝ}

-- Proof sketch: set `Y s = μ[X T | 𝒢 s]`; this is a martingale by `martingale_condExp`, it lies
-- below `X` by the supermartingale property, and the expectation hypothesis forces equality at
-- every time `s ≤ T`.
/-- Theorem 9.32 (5): If a discrete-time supermartingale has `μ[X T] ≥ μ[X 0]`, then its
conditional-expectation inequality is an equality at all times `s ≤ t ≤ T`. -/
theorem supermartingale_condExp_ae_eq_of_expectation_ge [SigmaFiniteFiltration μ 𝒢]
    (hX : Supermartingale X 𝒢 μ) {T s t : ℕ} (hst : s ≤ t) (htT : t ≤ T)
    (hEX : μ[X T] ≥ μ[X 0]) :
    μ[X t | 𝒢 s] =ᵐ[μ] X s := sorry

-- Proof sketch: for fixed `s ≤ t`, choose `N` with `t ≤ T N` using `T N → ∞`, apply the previous
-- finite-horizon equality theorem with horizon `T N`, and conclude that all defining
-- conditional-expectation inequalities of the supermartingale are equalities.
/-- Theorem 9.32 (6): If `μ[X (T N)] ≥ μ[X 0]` along a sequence of times tending to infinity,
then the supermartingale is in fact a martingale. -/
theorem supermartingale_martingale_of_expectation_ge_along_subsequence
    [SigmaFiniteFiltration μ 𝒢] (hX : Supermartingale X 𝒢 μ) {T : ℕ → ℕ}
    (hT : Tendsto T atTop atTop) (hEX : ∀ N, μ[X (T N)] ≥ μ[X 0]) :
    Martingale X 𝒢 μ := sorry

end Nat
