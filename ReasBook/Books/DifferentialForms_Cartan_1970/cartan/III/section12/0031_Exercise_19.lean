import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0031_Proposition_8_3»
import DifferentialForms_Cartan_1970.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.III.section11.«0008_Proposition_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note: this item lives in one-variable complex analysis on oriented boundaries.
-- The source-facing boundary owner is `IsOrientedBoundaryOf`; the holomorphy owner for
-- neighborhood-of-`K` hypotheses is Mathlib's canonical `AnalyticOnNhd`; the bridge/view
-- ingredient is `Path.closedPathIndex_add_eq_of_abs_lt` from Proposition 8.3; and the
-- core/canonical zero-count owner is `MeromorphicOn.divisor`, already used by the chapter
-- argument principle. The theorem below therefore stays a direct divisor-sum statement, with no
-- parallel local zero-count wrapper and no auxiliary open-set witness in the public API.

open MeromorphicOn
open scoped BigOperators unitInterval

noncomputable section

universe u

/-- Helper for Cartan section12 0031_Exercise_19: the strict boundary domination
`‖g z‖ < ‖f z‖` forces both `f z` and `(f + g) z` to be nonzero. -/
lemma boundaryNonvanishingOfAbsLt
    {K : Set ℂ} {f g : ℂ → ℂ}
    (hboundary : ∀ z ∈ frontier K, ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : z ∈ frontier K) :
    f z ≠ 0 ∧ (f z + g z) ≠ 0 := by
  -- First exclude a boundary zero of `f`, because then the strict inequality would read
  -- `‖g z‖ < 0`.
  have hlt : ‖g z‖ < ‖f z‖ := hboundary z hz
  have hfz : f z ≠ 0 := by
    intro hf0
    have hlt0 : ‖g z‖ < (0 : ℝ) := by
      simpa only [hf0, norm_zero] using hlt
    exact (not_lt_of_ge (norm_nonneg _)) hlt0
  constructor
  · exact hfz
  · -- A boundary zero of `f + g` would force equal norms for `f z` and `g z`, contradicting the
    -- same strict inequality.
    intro hsum0
    have hnorm : ‖f z‖ = ‖g z‖ := by
      calc
        ‖f z‖ = ‖-g z‖ := by
          congr
          exact eq_neg_of_add_eq_zero_left hsum0
        _ = ‖g z‖ := norm_neg _
    have hlt' : ‖f z‖ < ‖f z‖ := by
      simpa only [hnorm] using hlt
    exact lt_irrefl _ hlt'

/-- Helper for Cartan section12 0031_Exercise_19: if an analytic function is nonvanishing on the
frontier of a compact owner, then its divisor vanishes on that frontier. -/
lemma boundaryDivisorZeroOfFrontierNonvanishing
    {K : Set ℂ} {h : ℂ → ℂ} (hK : IsCompact K)
    (hanalytic : AnalyticOnNhd ℂ h K)
    (hnonzero : ∀ z ∈ frontier K, h z ≠ 0)
    {z : ℂ} (hz : z ∈ frontier K) :
    divisor h K z = 0 := by
  -- Move the frontier point into `K`, then apply the canonical analytic/nonvanishing divisor
  -- vanishing lemma.
  have hzK : z ∈ K := hK.isClosed.frontier_subset hz
  exact divisor_eq_zero_of_analyticOnNhd_nonvanishing hanalytic hzK (hnonzero z hz)

/-- Helper for Cartan section12 0031_Exercise_19: changing variables along a mapped closed path
rewrites the normalized `logDeriv` integral as the normalized index-form integral on the mapped
loop. -/
lemma normalizedLogDerivEqMappedIndexIntegral
    {z : ℂ} {γ : Path z z} {D : Set ℂ} {h : ℂ → ℂ}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hD_open : IsOpen D) (hγD : Set.range γ ⊆ D)
    (hh_diff : DifferentiableOn ℂ h D)
    (hγ_nonzero : ∀ t : I, h (γ t) ≠ 0) :
    (∫ᶜ z in γ, ((logDeriv h dz) z)) / (2 * Real.pi * Complex.I : ℂ) =
      (∫ᶜ w in γ.map' ((hh_diff.continuousOn).mono hγD), indexForm 0 w) /
        (2 * Real.pi * Complex.I : ℂ) := by
  have hcont_inv : ContinuousOn (fun w : ℂ ↦ w⁻¹) (h '' Set.range γ) := by
    -- The mapped path avoids `0`, so inversion is continuous on its image.
    refine continuousOn_inv₀.mono ?_
    intro w hw hw0
    rcases hw with ⟨z, hz, rfl⟩
    rcases hz with ⟨t, rfl⟩
    exact hγ_nonzero t hw0
  have hchange :=
    Path.curveIntegral_map'_eq_curveIntegral_mul_deriv
      (γ := γ) hγ_piecewise hD_open hγD hh_diff hcont_inv
  -- Rewrite the pullback integrand into `logDeriv h = h' / h` and the mapped integral into
  -- the standard index form at `0`.
  calc
    (∫ᶜ z in γ, ((logDeriv h dz) z)) / (2 * Real.pi * Complex.I : ℂ)
        =
      (∫ᶜ z in γ,
          (1 : ℂ →L[ℂ] ℂ).smulRight ((fun w : ℂ ↦ w⁻¹) (h z) * deriv h z)) /
        (2 * Real.pi * Complex.I : ℂ) := by
            simp [Complex.scalarOneForm, logDeriv, div_eq_mul_inv, mul_comm]
    _ =
      (∫ᶜ w in γ.map' ((hh_diff.continuousOn).mono hγD),
          (1 : ℂ →L[ℂ] ℂ).smulRight ((fun w : ℂ ↦ w⁻¹) w)) /
        (2 * Real.pi * Complex.I : ℂ) := by
            rw [← hchange]
    _ =
      (∫ᶜ w in γ.map' ((hh_diff.continuousOn).mono hγD), indexForm 0 w) /
        (2 * Real.pi * Complex.I : ℂ) := by
            simp [indexForm]

/-- Cartan section12 0031_Exercise_19. Exercise 19: Rouché's theorem on an oriented boundary. If
`f` and `g` are holomorphic on a
neighborhood of `K`, if `Γ` is the oriented boundary of `K`, and if `‖g z‖ < ‖f z‖` for every
boundary point `z ∈ frontier K`, then `f + g` and `f` have the same total divisor sum on `K`;
equivalently, they have the same number of zeros in `K` counted with multiplicity. -/
theorem rouche_theorem_on_oriented_boundary
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ) {f g : ℂ → ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ)
    (hf : AnalyticOnNhd ℂ f K)
    (hg : AnalyticOnNhd ℂ g K)
    (hboundary : ∀ z ∈ frontier K, ‖g z‖ < ‖f z‖) :
    ∑ᶠ z, divisor (f + g) K z = ∑ᶠ z, divisor f K z := by
  let D : Set ℂ := {z | AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z}
  have hD_open : IsOpen D := by
    -- Use the natural analytic locus shared by `f` and `g` as the open owner for both
    -- argument-principle applications.
    simpa [D] using (isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)
  have hKD : K ⊆ D := by
    intro z hz
    exact ⟨hf z hz, hg z hz⟩
  have hf_meromorphic : MeromorphicOn f D := by
    intro z hz
    exact (hz.1).meromorphicAt
  have hfg_meromorphic : MeromorphicOn (f + g) D := by
    intro z hz
    exact (hz.1.add hz.2).meromorphicAt
  have hf_diff : DifferentiableOn ℂ f D := by
    intro z hz
    exact hz.1.differentiableAt.differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g D := by
    intro z hz
    exact hz.2.differentiableAt.differentiableWithinAt
  have hfg_diff : DifferentiableOn ℂ (f + g) D := by
    intro z hz
    exact (hz.1.add hz.2).differentiableAt.differentiableWithinAt
  have hboundary_f_nonzero : ∀ z ∈ frontier K, f z ≠ 0 := by
    intro z hz
    exact (boundaryNonvanishingOfAbsLt hboundary hz).1
  have hboundary_fg_nonzero : ∀ z ∈ frontier K, (f z + g z) ≠ 0 := by
    intro z hz
    exact (boundaryNonvanishingOfAbsLt hboundary hz).2
  have hboundary_divisor_f :
      ∀ z ∈ frontier K, divisor f K z = 0 := by
    intro z hz
    exact
      boundaryDivisorZeroOfFrontierNonvanishing hΓ.isCompact hf hboundary_f_nonzero hz
  have hboundary_divisor_fg :
      ∀ z ∈ frontier K, divisor (f + g) K z = 0 := by
    intro z hz
    exact
      boundaryDivisorZeroOfFrontierNonvanishing hΓ.isCompact (hf.add hg) hboundary_fg_nonzero hz
  have harg_fg :
      (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (f + g) dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) =
        ∑ᶠ z, (divisor (f + g) K z : ℂ) := by
    -- Apply the argument principle to `f + g` with the shared analytic owner `D`.
    simpa using
      argument_principle_on_oriented_boundary
        (Γ := Γ) (D := D) (K := K) (f := f + g) (a := 0)
        hfg_meromorphic hD_open hKD hΓ
        (by
          intro z hz
          simpa using hboundary_divisor_fg z hz)
  have harg_f :
      (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv f dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) =
        ∑ᶠ z, (divisor f K z : ℂ) := by
    -- Apply the same argument principle to `f`.
    simpa using
      argument_principle_on_oriented_boundary
        (Γ := Γ) (D := D) (K := K) (f := f) (a := 0)
        hf_meromorphic hD_open hKD hΓ
        (by
          intro z hz
          simpa using hboundary_divisor_f z hz)
  have hcomponent :
      ∀ i : ι,
        (∫ᶜ z in (Γ i).toPath, ((logDeriv (f + g) dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) =
          (∫ᶜ z in (Γ i).toPath, ((logDeriv f dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := by
    intro i
    have hRangeD : Set.range (Γ i).toPath ⊆ D := by
      intro z hz
      exact hKD (hΓ.isCompact.isClosed.frontier_subset (hΓ.range_toPath_subset_frontier i hz))
    let ηf := (Γ i).toPath.map' ((hf_diff.continuousOn).mono hRangeD)
    let ηg := (Γ i).toPath.map' ((hg_diff.continuousOn).mono hRangeD)
    let ηfg := (Γ i).toPath.map' ((hfg_diff.continuousOn).mono hRangeD)
    have hηf_nonzero : ∀ t : I, ηf t ≠ 0 := by
      intro t
      change f ((Γ i).toPath t) ≠ 0
      exact hboundary_f_nonzero _ (hΓ.range_toPath_subset_frontier i ⟨t, rfl⟩)
    have hηfg_nonzero : ∀ t : I, ηfg t ≠ 0 := by
      intro t
      change (f ((Γ i).toPath t) + g ((Γ i).toPath t)) ≠ 0
      exact hboundary_fg_nonzero _ (hΓ.range_toPath_subset_frontier i ⟨t, rfl⟩)
    have hlt_path : ∀ t : I, ‖ηg t‖ < ‖ηf t‖ := by
      intro t
      change ‖g ((Γ i).toPath t)‖ < ‖f ((Γ i).toPath t)‖
      exact hboundary _ (hΓ.range_toPath_subset_frontier i ⟨t, rfl⟩)
    have hηfg_eq : ηfg = ηf.add ηg := by
      ext t
      simp [ηfg, ηf, ηg, Path.map'_apply]
    -- Convert each logarithmic-derivative integral to the mapped-loop index integral, then apply
    -- Proposition 8.3 to the boundary loops `f ∘ Γᵢ` and `g ∘ Γᵢ`.
    calc
      (∫ᶜ z in (Γ i).toPath, ((logDeriv (f + g) dz) z)) /
          (2 * Real.pi * Complex.I : ℂ)
          =
        (∫ᶜ w in ηfg, indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ) := by
            exact
              normalizedLogDerivEqMappedIndexIntegral
                (γ := (Γ i).toPath) (D := D) (h := f + g)
                (hΓ.piecewiseDifferentiable i) hD_open hRangeD hfg_diff hηfg_nonzero
      _ = closedPathIndex ηfg ⟨0, by
            intro hz
            rcases hz with ⟨t, ht⟩
            exact hηfg_nonzero t ht⟩ := by
              rw [closedPathIndex_def]
      _ = closedPathIndex ηf ⟨0, by
            intro hz
            rcases hz with ⟨t, ht⟩
            exact hηf_nonzero t ht⟩ := by
              simpa [hηfg_eq] using
                (Path.closedPathIndex_add_eq_of_abs_lt (γ := ηf) (γ₁ := ηg) hlt_path)
      _ = (∫ᶜ w in ηf, indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ) := by
            rw [closedPathIndex_def]
      _ =
        (∫ᶜ z in (Γ i).toPath, ((logDeriv f dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) := by
            symm
            exact
              normalizedLogDerivEqMappedIndexIntegral
                (γ := (Γ i).toPath) (D := D) (h := f)
                (hΓ.piecewiseDifferentiable i) hD_open hRangeD hf_diff hηf_nonzero
  have hsum_components :
      (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (f + g) dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) =
        (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv f dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) := by
    -- Rewrite the normalized sum as the sum of normalized components, then substitute the
    -- componentwise Rouché equalities.
    calc
      (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (f + g) dz) z)) /
          (2 * Real.pi * Complex.I : ℂ)
          =
        ∑ i,
          (∫ᶜ z in (Γ i).toPath, ((logDeriv (f + g) dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ =
        ∑ i,
          (∫ᶜ z in (Γ i).toPath, ((logDeriv f dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hcomponent i
      _ =
        (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv f dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) := by
              symm
              simp [div_eq_mul_inv, Finset.sum_mul]
  have hcomplex :
      ∑ᶠ z, (divisor (f + g) K z : ℂ) = ∑ᶠ z, (divisor f K z : ℂ) := by
    -- Assemble the two argument-principle identities with the componentwise boundary comparison.
    calc
      ∑ᶠ z, (divisor (f + g) K z : ℂ)
          = (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (f + g) dz) z)) /
              (2 * Real.pi * Complex.I : ℂ) := by
                symm
                exact harg_fg
      _ = (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv f dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := hsum_components
      _ = ∑ᶠ z, (divisor f K z : ℂ) := harg_f
  have hmap_fg :
      ((∑ᶠ z, divisor (f + g) K z : ℤ) : ℂ) =
        ∑ᶠ z, (divisor (f + g) K z : ℂ) := by
    -- Push the complex cast through the finitely supported divisor sum for `f + g`.
    simpa using
      map_finsum (Int.castRingHom ℂ)
        (divisor_support_finite_of_isCompact (K := K) (g := f + g) hΓ.isCompact)
  have hmap_f :
      ((∑ᶠ z, divisor f K z : ℤ) : ℂ) =
        ∑ᶠ z, (divisor f K z : ℂ) := by
    -- Do the same finite-support cast rewrite for `f`.
    simpa using
      map_finsum (Int.castRingHom ℂ)
        (divisor_support_finite_of_isCompact (K := K) (g := f) hΓ.isCompact)
  have hcast :
      ((∑ᶠ z, divisor (f + g) K z : ℤ) : ℂ) =
        ((∑ᶠ z, divisor f K z : ℤ) : ℂ) := by
    calc
      ((∑ᶠ z, divisor (f + g) K z : ℤ) : ℂ)
          = ∑ᶠ z, (divisor (f + g) K z : ℂ) := hmap_fg
      _ = ∑ᶠ z, (divisor f K z : ℂ) := hcomplex
      _ = ((∑ᶠ z, divisor f K z : ℤ) : ℂ) := hmap_f.symm
  exact_mod_cast hcast
