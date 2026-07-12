import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- The open annulus `ρ₂ < |z| < ρ₁` in the complex plane. -/
def complexOpenAnnulus (ρ₂ ρ₁ : ENNReal) : Set ℂ :=
  {z | ρ₂ < (‖z‖₊ : ENNReal) ∧ (‖z‖₊ : ENNReal) < ρ₁}

/-- The closed annulus `r₂ ≤ |z| ≤ r₁` in the complex plane. -/
def complexClosedAnnulus (r₂ r₁ : NNReal) : Set ℂ :=
  {z | r₂ ≤ ‖z‖₊ ∧ ‖z‖₊ ≤ r₁}

/-- The `n`th term of the Laurent family with coefficients `a`. -/
noncomputable def laurentTerm (a : ℤ → ℂ) (n : ℤ) (z : ℂ) : ℂ :=
  a n * z ^ n

lemma complexClosedAnnulus_subset_complexOpenAnnulus
    {ρ₂ ρ₁ : ENNReal} {r₂ r₁ : NNReal}
    (hρ₂ : ρ₂ < (r₂ : ENNReal)) (hρ₁ : (r₁ : ENNReal) < ρ₁) :
    complexClosedAnnulus r₂ r₁ ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
  intro z hz
  rcases hz with ⟨hz₂, hz₁⟩
  exact
    ⟨lt_of_lt_of_le hρ₂ (by exact_mod_cast hz₂), lt_of_le_of_lt (by exact_mod_cast hz₁) hρ₁⟩

lemma isClosed_complexClosedAnnulus (r₂ r₁ : NNReal) :
    IsClosed (complexClosedAnnulus r₂ r₁) := by
  simpa [complexClosedAnnulus] using
    (isClosed_le continuous_const continuous_nnnorm).inter
      (isClosed_le continuous_nnnorm continuous_const)

lemma isCompact_complexClosedAnnulus (r₂ r₁ : NNReal) :
    IsCompact (complexClosedAnnulus r₂ r₁) := by
  refine (isCompact_closedBall (0 : ℂ) (r₁ : ℝ)).of_isClosed_subset
    (isClosed_complexClosedAnnulus r₂ r₁) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  simpa using hz.2

/-- Definition III.4-extra-1: a Laurent series `∑ a_n z^n` in the annulus
`ρ₂ < |z| < ρ₁` is an integer-indexed series that converges locally uniformly on that annulus. -/
def IsLaurentSeriesOnAnnulus (a : ℤ → ℂ) (ρ₂ ρ₁ : ENNReal) : Prop :=
  SummableLocallyUniformlyOn (laurentTerm a) (complexOpenAnnulus ρ₂ ρ₁)

/-- A Laurent series on an annulus converges uniformly on every closed subannulus strictly
contained in it. -/
-- Proof sketch: the closed subannulus is a compact subset of the ambient open annulus, so local
-- uniform summability upgrades to uniform summability there.
theorem IsLaurentSeriesOnAnnulus.summableUniformlyOn_closedAnnulus
    {a : ℤ → ℂ} {ρ₂ ρ₁ : ENNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {r₂ r₁ : NNReal} (hρ₂ : ρ₂ < (r₂ : ENNReal)) (hρ₁ : (r₁ : ENNReal) < ρ₁) :
    SummableUniformlyOn (laurentTerm a) (complexClosedAnnulus r₂ r₁) := by
  let s := complexClosedAnnulus r₂ r₁
  have hs : IsCompact s := isCompact_complexClosedAnnulus r₂ r₁
  have hsubset : s ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    complexClosedAnnulus_subset_complexOpenAnnulus hρ₂ hρ₁
  have hsum :
      HasSumLocallyUniformlyOn (laurentTerm a) (fun z ↦ ∑' n : ℤ, laurentTerm a n z) s :=
    (ha.mono hsubset).hasSumLocallyUniformlyOn
  have hsum' :
      HasSumUniformlyOn (laurentTerm a) (fun z ↦ ∑' n : ℤ, laurentTerm a n z) s := by
    rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
    rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]
    exact hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hsum
  exact hsum'.summableUniformlyOn
