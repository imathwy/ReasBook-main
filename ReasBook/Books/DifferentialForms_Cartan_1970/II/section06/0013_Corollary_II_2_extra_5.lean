import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0007_Theorem_I»
import DifferentialForms_Cartan_1970.II.section06.«0012_Theorem_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

variable {D : Set ℂ} {f : ℂ → ℂ} {z₀ z₁ : ℂ}

/-- Helper for Corollary II.2-extra-5: removing a singleton leaves a codiscrete-within subset. -/
lemma diff_singleton_mem_codiscreteWithin {D : Set ℂ} {a : ℂ} :
    D \ {a} ∈ Filter.codiscreteWithin D := by
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hxD
  by_cases haD : a ∈ D
  · have hunion : (D \ {a}) ∪ Dᶜ = ({a} : Set ℂ)ᶜ := by
      ext z
      classical
      by_cases hza : z = a
      · simp [hza, haD]
      · by_cases hzD : z ∈ D <;> simp [hza, hzD]
    rw [hunion]
    by_cases hxa : x = a
    · -- At the exceptional point, the punctured neighborhood filter already lives on `{a}ᶜ`.
      simpa [hxa] using (self_mem_nhdsWithin : ({x}ᶜ : Set ℂ) ∈ 𝓝[({x}ᶜ)] x)
    · -- Away from `a`, the complement of `{a}` is an ordinary open neighborhood.
      have hopen : IsOpen ({a}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
      exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hxa)
  · have hdiff : D \ ({a} : Set ℂ) = D := by
      ext z
      simp [haD]
    rw [hdiff, union_compl_self]
    simpa using (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝[≠] x)

/-- Helper for Corollary II.2-extra-5: the affine map `w ↦ z₀ + (z₁ - z₀) w` straightens the
exceptional affine line to the real axis. -/
lemma preimage_affine_line_eq_real_axis_of_ne {z₀ z₁ : ℂ} (h01 : z₀ ≠ z₁) :
    (fun w : ℂ ↦ z₀ + (z₁ - z₀) * w) ⁻¹' (line[ℝ, z₀, z₁] : Set ℂ) = {w : ℂ | w.im = 0} := by
  ext w
  constructor
  · intro hw
    simp only [Set.mem_preimage] at hw
    have hw' : ((z₁ - z₀) * w) +ᵥ z₀ ∈ line[ℝ, z₀, z₁] := by
      simpa [vadd_eq_add, add_comm] using hw
    rw [vadd_left_mem_affineSpan_pair] at hw'
    rcases hw' with ⟨r, hr⟩
    have hw_eq : w = (r : ℂ) := by
      have hrw : (r : ℂ) = w := by
        have hmul : (r : ℂ) * (z₁ - z₀) = w * (z₁ - z₀) := by
          simpa [smul_eq_mul, mul_comm] using hr
        exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm h01)) hmul
      exact hrw.symm
    -- Cancelling the nonzero slope shows the parameter is real.
    simpa [hw_eq]
  · intro hw
    simp only [Set.mem_preimage]
    have hw' : ((z₁ - z₀) * w) +ᵥ z₀ ∈ line[ℝ, z₀, z₁] := by
      rw [vadd_left_mem_affineSpan_pair]
      refine ⟨w.re, ?_⟩
      have hw_eq : w = (w.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using hw
      -- Once `w` is real, the affine parametrization is exactly the real line map.
      calc
        (w.re : ℝ) • (z₁ - z₀) = ((w.re : ℂ) * (z₁ - z₀)) := by simp [smul_eq_mul]
        _ = (z₁ - z₀) * w := by
          rw [hw_eq]
          simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
    simpa [vadd_eq_add, add_comm] using hw'

/-- Helper for Corollary II.2-extra-5: precomposing by the nondegenerate affine straightening map
preserves holomorphicity away from the exceptional line. -/
lemma differentiableOn_precomp_nonzero_mul_add_off_real_axis
    {D : Set ℂ} {f : ℂ → ℂ} {z₀ z₁ : ℂ} (h01 : z₀ ≠ z₁)
    (hf_diff : DifferentiableOn ℂ f (D \ line[ℝ, z₀, z₁])) :
    DifferentiableOn ℂ (fun w : ℂ ↦ f (z₀ + (z₁ - z₀) * w))
      (((fun w : ℂ ↦ z₀ + (z₁ - z₀) * w) ⁻¹' D) \ {w : ℂ | w.im = 0}) := by
  let ψ : ℂ → ℂ := fun w ↦ z₀ + (z₁ - z₀) * w
  have hψ : Differentiable ℂ ψ := by
    simpa [ψ] using ((differentiable_id.const_mul (z₁ - z₀)).const_add z₀)
  have hψ_diff :
      DifferentiableOn ℂ ψ (((fun w : ℂ ↦ z₀ + (z₁ - z₀) * w) ⁻¹' D) \ {w : ℂ | w.im = 0}) :=
    hψ.differentiableOn
  have hmaps :
      MapsTo ψ (((fun w : ℂ ↦ z₀ + (z₁ - z₀) * w) ⁻¹' D) \ {w : ℂ | w.im = 0})
        (D \ line[ℝ, z₀, z₁]) := by
    intro w hw
    rcases hw with ⟨hwD, hwOff⟩
    refine ⟨hwD, ?_⟩
    have hwOff' : w ∉ ψ ⁻¹' (line[ℝ, z₀, z₁] : Set ℂ) := by
      rwa [preimage_affine_line_eq_real_axis_of_ne h01]
    simpa [ψ] using hwOff'
  -- Compose the given differentiable-on hypothesis with the affine straightening map.
  simpa [ψ, Function.comp] using hf_diff.comp hψ_diff hmaps

/-- Helper for Corollary II.2-extra-5: differentiability of the affine pullback implies
differentiability of the original function after composing with the inverse affine map. -/
lemma differentiableOn_of_differentiableOn_precomp_nonzero_mul_add
    {D : Set ℂ} {f : ℂ → ℂ} {a c : ℂ} (hc : c ≠ 0)
    (hg : DifferentiableOn ℂ (fun w : ℂ ↦ f (a + c * w)) (((fun w : ℂ ↦ a + c * w) ⁻¹' D))) :
    DifferentiableOn ℂ f D := by
  let φ : ℂ → ℂ := fun z ↦ (z - a) / c
  have hφ_inv : ∀ z : ℂ, a + c * φ z = z := by
    intro z
    change a + c * ((z - a) / c) = z
    field_simp [hc]
    ring
  have hφ : Differentiable ℂ φ := by
    -- The inverse affine map is holomorphic everywhere because `c ≠ 0`.
    simpa [φ, div_eq_mul_inv, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using
      ((differentiable_id.sub_const a).mul_const c⁻¹)
  have hφ_diff : DifferentiableOn ℂ φ D := hφ.differentiableOn
  have hmaps : MapsTo φ D (((fun w : ℂ ↦ a + c * w) ⁻¹' D)) := by
    intro z hz
    -- The inverse affine change of variables sends points of `D` back to the pullback domain.
    change a + c * φ z ∈ D
    simpa [hφ_inv z] using hz
  have hfun : ((fun w : ℂ ↦ f (a + c * w)) ∘ φ) = f := by
    funext z
    simp [Function.comp, hφ_inv z]
  -- Evaluating the affine map on its inverse recovers the original function globally.
  simpa [hfun] using (hg.comp hφ_diff hmaps)

/-- Corollary II.2-extra-5: a continuous complex function on an open set `D` that is holomorphic
off some possibly degenerate affine real line in `ℂ` is holomorphic on all of `D`. -/
-- Proof sketch: if the exceptional line degenerates to a singleton, apply the isolated-point
-- version of Theorem I'. Otherwise straighten the exceptional affine line by a complex rotation and
-- translation to a horizontal line, apply the horizontal-line version of Theorem I' to obtain that
-- `f(z) dz` is conservative on `D`, then invoke
-- `differentiableOn_of_isConservativeOn_of_continuousOn` on the open set `D`.
theorem continuous_holomorphic_off_line_differentiableOn
    (hD : IsOpen D) (hf_cont : ContinuousOn f D)
    (hf_diff : DifferentiableOn ℂ f (D \ line[ℝ, z₀, z₁])) :
    DifferentiableOn ℂ f D := by
  by_cases h01 : z₀ = z₁
  · -- If the line degenerates to a point, reduce to the isolated-singularity form of Theorem I'.
    have hline : (line[ℝ, z₀, z₁] : Set ℂ) = {z₀} := by
      subst h01
      simpa using (AffineSubspace.coe_affineSpan_singleton (k := ℝ) (V := ℂ) z₀)
    have hf_diff' : DifferentiableOn ℂ f (D \ ({z₀} : Set ℂ)) := by
      simpa [hline] using hf_diff
    have hf_closed : Complex.IsConservativeOn f D :=
      continuous_holomorphic_off_isolated_points_isConservativeOn hf_cont
        diff_singleton_mem_codiscreteWithin hf_diff'
    -- Theorem 4 upgrades closedness of `f(z) dz` back to holomorphicity on the open set.
    exact differentiableOn_of_isConservativeOn_of_continuousOn hD hf_cont hf_closed
  · let ψ : ℂ → ℂ := fun w ↦ z₀ + (z₁ - z₀) * w
    let D' : Set ℂ := ψ ⁻¹' D
    let g : ℂ → ℂ := f ∘ ψ
    have hψ_cont : Continuous ψ := by
      show Continuous (fun w : ℂ ↦ z₀ + (z₁ - z₀) * w)
      exact continuous_const.add (continuous_const.mul continuous_id)
    have hD' : IsOpen D' := by
      -- The affine straightening map is continuous, so the pullback domain stays open.
      simpa [D'] using hD.preimage hψ_cont
    have hg_cont : ContinuousOn g D' := by
      -- Continuity also pulls back through the affine parametrization of the line.
      simpa [g, D', ψ, Function.comp] using
        hf_cont.comp hψ_cont.continuousOn (by
          intro w hw
          exact hw)
    have hg_diff_off :
        DifferentiableOn ℂ g (D' \ {w : ℂ | w.im = 0}) := by
      -- The exceptional affine line becomes the horizontal real axis in the new coordinates.
      simpa [g, D', ψ, Function.comp] using
        differentiableOn_precomp_nonzero_mul_add_off_real_axis h01 hf_diff
    have hg_closed : Complex.IsConservativeOn g D' :=
      continuous_holomorphic_off_horizontal_line_isConservativeOn (y := 0) hg_cont hg_diff_off
    have hg_diff : DifferentiableOn ℂ g D' :=
      differentiableOn_of_isConservativeOn_of_continuousOn hD' hg_cont hg_closed
    -- Compose with the inverse affine map to transfer differentiability back to `f`.
    simpa [g, D', ψ, Function.comp] using
      differentiableOn_of_differentiableOn_precomp_nonzero_mul_add
        (a := z₀) (c := z₁ - z₀) (sub_ne_zero.mpr (Ne.symm h01)) hg_diff

/-- Pointwise form of Corollary II.2-extra-5. -/
theorem continuous_holomorphic_off_line_differentiableAt
    (hD : IsOpen D) (hf_cont : ContinuousOn f D)
    (hf_diff : DifferentiableOn ℂ f (D \ line[ℝ, z₀, z₁])) :
    ∀ z ∈ D, DifferentiableAt ℂ f z := by
  intro z hz
  exact
    (continuous_holomorphic_off_line_differentiableOn hD hf_cont hf_diff z hz).differentiableAt
      (hD.mem_nhds hz)
