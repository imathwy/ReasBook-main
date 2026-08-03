import BauschkeLean.Chap10.Proposition_10_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

section

variable {f : H → Set.Ioi (⊥ : EReal)}

-- In this owner API, `f : H → ]-∞,+∞]` already rules out the value `-∞`, and
-- `hconv.nonempty` supplies the nonempty effective domain. Thus the explicit binder
-- `hconv : ConvexOn f (effectiveDomain f)` is exactly the source's proper-convex hypothesis in
-- the current canonical surface.

-- Proof sketch: the forward implication is `UniformlyConvex.modulus_eq_zero_iff` specialized to
-- the exact modulus. For the reverse implication, use Proposition 10.12 to obtain monotonicity
-- and the value at `0`, then verify the defining Jensen inequality for
-- `UniformlyConvex f (exactModulusOfConvexity f)` from the infimum property of
-- `exactModulusOfConvexity`.
/-- Helper for Corollary 10.13: every modulus of uniform convexity is bounded above by the exact
modulus of convexity. -/
theorem UniformlyConvex.le_exactModulusOfConvexity
    {ψ : NNReal → EReal} (hf : UniformlyConvex f ψ) (r : NNReal) :
    ψ r ≤ exactModulusOfConvexity f r := by
  -- Compare `ψ r` with every witness in the defining infimum of the exact modulus.
  rw [exactModulusOfConvexity]
  refine le_sInf ?_
  intro δ hδ
  rcases hδ with ⟨x, hx, y, hy, hxy, α, hα, rfl⟩
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
  let d : ℝ := α * (1 - α)
  have hgap :
      (d : EReal) * ψ ‖x - y‖₊ ≤ jensenGap f α x y := by
    simpa [d] using hf.gap_le hx hy hα0 hα1
  have hden_pos : (0 : EReal) < (d : EReal) := by
    dsimp [d]
    exact_mod_cast show 0 < α * (1 - α) by nlinarith
  -- Divide by the positive normalization factor to recover the normalized-gap bound.
  have hdiv :
      ψ ‖x - y‖₊ ≤ jensenGap f α x y / (d : EReal) :=
    (EReal.le_div_iff_mul_le hden_pos (EReal.coe_ne_top d)).2
      (by simpa [mul_comm] using hgap)
  simpa [d, hxy] using hdiv

/-- The exact modulus of convexity is itself a modulus of uniform convexity precisely when it
vanishes only at `0`. -/
theorem exactModulusOfConvexity_uniformlyConvex_iff
    (hconv : ConvexOn f (effectiveDomain f)) :
    UniformlyConvex f (exactModulusOfConvexity f) ↔
      ∀ r : NNReal, exactModulusOfConvexity f r = 0 ↔ r = 0 := by
  constructor
  · intro hf r
    -- Read the zero-set characterization directly from the uniform-convexity structure.
    exact hf.modulus_eq_zero_iff r
  · intro hzero
    -- Assemble the canonical uniform-convexity witness from Proposition 10.12.
    refine ⟨hconv.nonempty, subset_rfl, exactModulusOfConvexity_monotone hconv, hzero, ?_⟩
    intro x hx y hy α hα0 hα1
    have hgap :
        exactModulusOfConvexity f ‖x - y‖₊ ≤
          jensenGap f α x y / (α * (1 - α) : ℝ) :=
      exactModulusOfConvexity_le_normalizedGap f hx hy rfl ⟨hα0, hα1⟩
    let d : ℝ := α * (1 - α)
    have hgap' :
        exactModulusOfConvexity f ‖x - y‖₊ ≤ jensenGap f α x y / (d : EReal) := by
      simpa [d] using hgap
    have hden_pos : (0 : EReal) < (d : EReal) := by
      dsimp [d]
      exact_mod_cast show 0 < α * (1 - α) by nlinarith
    -- Convert the normalized-gap estimate back to the Jensen-gap form in `UniformlyConvex`.
    simpa [d, mul_comm] using
      (EReal.le_div_iff_mul_le hden_pos (EReal.coe_ne_top d)).1 hgap'

/-- Corollary 10.13: a proper convex `]-∞,+∞]`-valued function is uniformly convex for some
modulus if and only if its exact modulus of convexity vanishes only at `0`. -/
theorem uniformlyConvex_exists_iff_exactModulusOfConvexity_eq_zero_iff
    (hconv : ConvexOn f (effectiveDomain f)) :
    (∃ ψ : NNReal → EReal, UniformlyConvex f ψ) ↔
      ∀ r : NNReal, exactModulusOfConvexity f r = 0 ↔ r = 0 := by
  constructor
  · rintro ⟨ψ, hf⟩ r
    constructor
    · intro hExact
      -- Compare the exact modulus with the given one and use that every modulus is nonnegative.
      have hψ_nonneg : 0 ≤ ψ r := by
        rw [← (hf.modulus_eq_zero_iff 0).2 rfl]
        exact hf.monotone bot_le
      have hψ_le : ψ r ≤ exactModulusOfConvexity f r :=
        hf.le_exactModulusOfConvexity r
      have hψ_zero : ψ r = 0 := by
        exact le_antisymm (hExact ▸ hψ_le) hψ_nonneg
      exact (hf.modulus_eq_zero_iff r).1 hψ_zero
    · intro hr
      -- At radius `0`, Proposition 10.12 already identifies the exact modulus with `0`.
      simpa [hr] using exactModulusOfConvexity_zero hconv
  · intro hzero
    -- Reuse the exact modulus itself as the uniform-convexity witness.
    exact ⟨exactModulusOfConvexity f, (exactModulusOfConvexity_uniformlyConvex_iff hconv).2 hzero⟩

/-- If `f` is uniformly convex with some modulus, then its exact modulus of convexity vanishes only
at `0`. -/
theorem UniformlyConvex.exactModulusOfConvexity_eq_zero_iff
    {f : H → Set.Ioi (⊥ : EReal)} {ψ : NNReal → EReal} (hf : UniformlyConvex f ψ)
    (r : NNReal) :
    exactModulusOfConvexity f r = 0 ↔ r = 0 := by
  exact
    (uniformlyConvex_exists_iff_exactModulusOfConvexity_eq_zero_iff
      (UniformlyConvex.convexOn hf)).1 ⟨ψ, hf⟩ r

/-- A strongly convex function is uniformly convex with its exact modulus of convexity. -/
theorem StronglyConvex.uniformlyConvex_exactModulusOfConvexity
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hf : StronglyConvex f β) :
    UniformlyConvex f (exactModulusOfConvexity f) := by
  have h_uniform : UniformlyConvex f (strongConvexityModulus β) := hf.uniformlyConvex
  exact
    (exactModulusOfConvexity_uniformlyConvex_iff (UniformlyConvex.convexOn h_uniform)).2
      (UniformlyConvex.exactModulusOfConvexity_eq_zero_iff h_uniform)

end

end ERealFunction
