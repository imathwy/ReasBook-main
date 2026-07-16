import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2».BoundaryCircleIntegrals
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0012_Exercise_4».CircleBoundaryGeometry

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-
This remark is a `bridge/view`: its source content is the residue sum on the Riemann sphere, while
the chapter's residue owner is the compact oriented-boundary theorem on a closed disc. The finite
residue data is therefore stated on one explicit enclosing disc `Metric.closedBall 0 R`, and the
residue at infinity is recorded by the chapter's global owner `ResidueAtInfinityCircleEq`, whose
threshold radius guarantees the contour formula on every sufficiently large circle. For rational
functions, the residue owner stays the core/canonical `meromorphicTrailingCoeffAt`, and the
rational theorem below is only a specialization of the generic bridge theorem.
-/

/-- Helper for Cartan section11 0004_Remark_III_5_extra_3: the literal rational evaluation
`z ↦ p.eval z / q.eval z` is meromorphic on the whole complex plane. -/
lemma rationalEval_meromorphicOn_univ
    (p q : Polynomial ℂ) :
    MeromorphicOn (fun w : ℂ ↦ p.eval w / q.eval w) Set.univ := by
  have hpmer : MeromorphicOn (fun w : ℂ ↦ p.eval w) Set.univ := by
    -- Polynomial evaluation is entire, hence meromorphic, on `Set.univ`.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) p).meromorphicOn
  have hqmer : MeromorphicOn (fun w : ℂ ↦ q.eval w) Set.univ := by
    -- The same entire-function argument applies to the denominator polynomial.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) q).meromorphicOn
  -- Meromorphicity is stable under pointwise division.
  simpa using hpmer.div hqmer

/-- Helper for Cartan section11 0004_Remark_III_5_extra_3: the meromorphic normal form of a
rational function is holomorphic away from the prescribed pole finset. -/
lemma rationalNormalForm_differentiableOn_compl_poleFinset
    (p q : Polynomial ℂ) (s : Finset ℂ)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w : ℂ ↦ p.eval w / q.eval w) z < 0 ↔ z ∈ s) :
    DifferentiableOn ℂ
      (toMeromorphicNFOn (fun w : ℂ ↦ p.eval w / q.eval w) Set.univ)
      (↑s : Set ℂ)ᶜ := by
  intro z hz
  let f : ℂ → ℂ := fun w : ℂ ↦ p.eval w / q.eval w
  have hmeromorphic : MeromorphicOn f Set.univ :=
    rationalEval_meromorphicOn_univ p q
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- Outside the pole finset, the local meromorphic order cannot be negative.
    by_contra hneg
    exact hz ((hpoles z).1 (lt_of_not_ge hneg))
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f Set.univ) z := by
    -- Passing to normal form preserves the local meromorphic order on `Set.univ`.
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hmeromorphic (by simp)]
    exact horder_nonneg_f
  have hnf : MeromorphicNFAt (toMeromorphicNFOn f Set.univ) z :=
    (meromorphicNFOn_toMeromorphicNFOn f Set.univ) (by simp)
  have hdiffAt : DifferentiableAt ℂ (toMeromorphicNFOn f Set.univ) z := by
    -- The normal-form representative is analytic, hence differentiable, at every non-pole point.
    exact (hnf.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).differentiableAt
  -- Nonnegative order at the normal-form representative gives analyticity, hence differentiability.
  exact hdiffAt.differentiableWithinAt

/-- Helper for Cartan section11 0004_Remark_III_5_extra_3: replacing the rational function by its
meromorphic normal form does not change a chosen local residue-circle witness on `Set.univ`. -/
lemma localResidueCircle_toMeromorphicNFOn_of_rational
    (p q : Polynomial ℂ) {K : Set ℂ} {z : ℂ} {residue_z : ℂ}
    (hres :
      LocalResidueCircle
        K
        Set.univ
        (fun w : ℂ ↦ p.eval w / q.eval w)
        z
        residue_z) :
    LocalResidueCircle
      K
      Set.univ
      (toMeromorphicNFOn (fun w : ℂ ↦ p.eval w / q.eval w) Set.univ)
      z
      residue_z := by
  let f : ℂ → ℂ := fun w : ℂ ↦ p.eval w / q.eval w
  have hmeromorphic : MeromorphicOn f Set.univ :=
    rationalEval_meromorphicOn_univ p q
  rcases hres with ⟨R, hR, hRK, hRD, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, ?_⟩
  have hEq :
      (fun w ↦ toMeromorphicNFOn f Set.univ w) =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
        f := by
    exact
      (toMeromorphicNFOn_eqOn_codiscrete (U := Set.univ) hmeromorphic).symm.filter_mono
        (Filter.codiscreteWithin_mono (by
          intro w hw
          simp))
  -- The contour integral only depends on the codiscrete boundary values on the circle.
  calc
    ∮ w in C(z, R), toMeromorphicNFOn f Set.univ w = ∮ w in C(z, R), f w := by
      exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
    _ = (2 * Real.pi * Complex.I : ℂ) * residue_z := hcircleR

/-- Helper for Cartan section11 0004_Remark_III_5_extra_3: the residue-at-infinity owner for a
rational function transfers unchanged to its meromorphic normal form on `Set.univ`. -/
lemma residueAtInfinityCircleEq_toMeromorphicNFOn_of_rational
    (p q : Polynomial ℂ) {residueAtInfinity : ℂ}
    (hres_infty :
      ResidueAtInfinityCircleEq
        (fun w : ℂ ↦ p.eval w / q.eval w)
        residueAtInfinity) :
    ResidueAtInfinityCircleEq
      (toMeromorphicNFOn (fun w : ℂ ↦ p.eval w / q.eval w) Set.univ)
      residueAtInfinity := by
  let f : ℂ → ℂ := fun w : ℂ ↦ p.eval w / q.eval w
  have hmeromorphic : MeromorphicOn f Set.univ :=
    rationalEval_meromorphicOn_univ p q
  rcases hres_infty with ⟨R₀, hR₀, hcircle⟩
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR
  have hEq :
      (fun w ↦ toMeromorphicNFOn f Set.univ w) =ᶠ[Filter.codiscreteWithin (Metric.sphere 0 |R|)]
        f := by
    exact
      (toMeromorphicNFOn_eqOn_codiscrete (U := Set.univ) hmeromorphic).symm.filter_mono
        (Filter.codiscreteWithin_mono (by
          intro w hw
          simp))
  have hRne : R ≠ 0 := by
    exact (ne_of_gt (lt_of_lt_of_le hR₀ hR))
  -- The same codiscrete comparison applies on every sufficiently large boundary circle.
  calc
    ∮ w in C(0, R), toMeromorphicNFOn f Set.univ w = ∮ w in C(0, R), f w := by
      exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hRne
    _ = -(2 * Real.pi * Complex.I : ℂ) * residueAtInfinity := hcircle R hR

/-
The unisolated `LocalResidueCircle` version of the sphere-residue bridge is intentionally not
stated below. It is too weak: a chosen local circle around one listed singularity may enclose a
second listed singularity, so the recorded coefficient is not forced to be the local residue at
that point. The corrected statements below use `IsolatedLocalResidueCircle`, whose separation field
prevents this failure and matches the source proof's “small circles around the singularities” step.
-/

/-- Remark III.5-extra-3 (1): if `f` is holomorphic away from the finite set `s`, and if the
finite residues are realized on the closed disc `Metric.closedBall 0 R` by the chapter's canonical
isolated local residue-circle owner, while the chapter's canonical residue-at-infinity owner holds on all
sufficiently large circles, then the sum of the finite residues together with the residue at
infinity is zero. -/
theorem sum_residue_at_add_residue_at_infinity_eq_zero_of_holomorphic_off_finite_set
    (f : ℂ → ℂ) (s : Finset ℂ) (residue : ℂ → ℂ) (residueAtInfinity : ℂ) (R : ℝ)
    (hhol : DifferentiableOn ℂ f (↑s : Set ℂ)ᶜ)
    (hres :
      ∀ z ∈ s, IsolatedLocalResidueCircle (Metric.closedBall 0 R) Set.univ s f z (residue z))
    (hres_infty : ResidueAtInfinityCircleEq f residueAtInfinity) :
    s.sum residue + residueAtInfinity = 0 := by
  classical
  rcases hres_infty with ⟨R₀, hR₀, hcircle_infty⟩
  let T : ℝ := max R R₀
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (boundary_circle_path (0 : ℂ) T).toClosedPath
  have hTpos : 0 < T := lt_of_lt_of_le hR₀ (le_max_right R R₀)
  have hRT : R ≤ T := le_max_left R R₀
  have hR₀T : R₀ ≤ T := le_max_right R R₀
  have hΓ :
      IsOrientedBoundaryOf (Metric.closedBall (0 : ℂ) T) Γ := by
    -- Reuse the canonical closed-disc boundary owner; the two circle-path wrappers are the same.
    simpa [Γ, boundary_circle_path, positive_circle_path] using
      (closedBallBoundary_isOrientedBoundaryOf (a := (0 : ℂ)) (r := T) hTpos)
  have hsInterior :
      (↑s : Set ℂ) ⊆ interior (Metric.closedBall (0 : ℂ) T) := by
    intro z hz
    rcases hres z hz with ⟨ρ, hρ, hρK, hρD, hsep, hdiffρ, hcircleρ⟩
    let _ := hρD
    let _ := hsep
    let _ := hdiffρ
    let _ := hcircleρ
    have hzR : z ∈ interior (Metric.closedBall (0 : ℂ) R) := by
      exact hρK (Metric.mem_closedBall_self hρ.le)
    exact interior_mono (Metric.closedBall_subset_closedBall hRT) hzR
  have hboundary_disjoint :
      ∀ i : Unit, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ) := by
    intro i
    refine Set.disjoint_left.2 ?_
    intro z hzRange hzS
    have hzFront : z ∈ frontier (Metric.closedBall (0 : ℂ) T) :=
      hΓ.range_toPath_subset_frontier i hzRange
    have hzInterior : z ∈ interior (Metric.closedBall (0 : ℂ) T) :=
      hsInterior (by simpa using hzS)
    exact (Set.disjoint_left.1 disjoint_interior_frontier) hzInterior hzFront
  have hresT :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle (Metric.closedBall (0 : ℂ) T) Set.univ s f z (residue z) := by
    -- Enlarge the owner disc while retaining the source-text choice of mutually disjoint local
    -- residue circles around the finitely many singularities.
    intro z hz
    rcases hres z hz with ⟨ρ, hρ, hρK, hρD, hsep, hdiffρ, hcircleρ⟩
    refine ⟨ρ, hρ, ?_, hρD, hsep, hdiffρ, hcircleρ⟩
    exact hρK.trans (interior_mono (Metric.closedBall_subset_closedBall hRT))
  have hboundary_sum :
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, (f dz) z =
        (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
    -- Apply the frozen oriented-boundary residue theorem on the large enclosing closed disc.
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (K := Metric.closedBall (0 : ℂ) T) (D := Set.univ)
        (f := f) (s := s) (residue := residue)
        hΓ (by intro z hz; simp) isOpen_univ hboundary_disjoint
        (by simpa [Set.diff_eq] using hhol) hresT
  have hboundary_circle :
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, (f dz) z =
        ∮ z in C(0, T), f z := by
    -- Collapse the singleton boundary family back to the standard circle integral.
    calc
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, (f dz) z =
          ∫ᶜ z in (boundary_circle_path (0 : ℂ) T).toClosedPath.toPath, (f dz) z := by
            simp only [Γ, Finset.univ_unique, Finset.sum_singleton]
      _ = ∫ᶜ z in boundary_circle_path (0 : ℂ) T, (f dz) z := by
            rw [loop_toClosedPath_toPath_eq_cast]
            simp
      _ = ∮ z in C(0, T), f z := by
            exact curveIntegral_boundary_circle_eq_circleIntegral (f := f) (a := (0 : ℂ)) (r := T)
  have htwopi :
      (2 * Real.pi * Complex.I : ℂ) * s.sum residue =
        -(2 * Real.pi * Complex.I : ℂ) * residueAtInfinity := by
    calc
      (2 * Real.pi * Complex.I : ℂ) * s.sum residue =
          ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, (f dz) z := hboundary_sum.symm
      _ = ∮ z in C(0, T), f z := hboundary_circle
      _ = -(2 * Real.pi * Complex.I : ℂ) * residueAtInfinity := hcircle_infty T hR₀T
  have htwopi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hsum_neg : s.sum residue = -residueAtInfinity := by
    exact mul_left_cancel₀ htwopi_ne (by simpa [mul_neg] using htwopi)
  -- Cancel the nonzero `2π i` factor to recover the sphere-style residue identity.
  simpa [eq_neg_iff_add_eq_zero] using hsum_neg

section Rational

variable (p q : Polynomial ℂ)

local notation "f" => fun w : ℂ ↦ p.eval w / q.eval w

/-- Cartan section11 0004_Remark_III_5_extra_3. Remark III.5-extra-3: for a rational function,
the sum of the canonical finite residues together with the residue at infinity is zero provided
`s` is exactly its finite pole set and the finite residues are recorded on the chosen closed disc
`Metric.closedBall 0 R` by the chapter's canonical isolated local residue-circle owner specialized to
`meromorphicTrailingCoeffAt`, while the residue at infinity is supplied by the chapter's global
owner `ResidueAtInfinityCircleEq` on all sufficiently large circles. -/
theorem sum_meromorphicTrailingCoeffAt_add_residue_at_infinity_eq_zero_of_rational
    (s : Finset ℂ) (residueAtInfinity : ℂ) (R : ℝ)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ↔ z ∈ s)
    (hres :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          (Metric.closedBall 0 R)
          Set.univ
          s
          f
          z
          (meromorphicTrailingCoeffAt f z))
    (hres_infty : ResidueAtInfinityCircleEq f residueAtInfinity) :
    s.sum (meromorphicTrailingCoeffAt f) + residueAtInfinity = 0 := by
  let g : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  have hhol : DifferentiableOn ℂ g (↑s : Set ℂ)ᶜ := by
    -- Route correction: the raw quotient need not be holomorphic at removable common roots, so
    -- the proof runs on the meromorphic normal form instead.
    simpa [g] using rationalNormalForm_differentiableOn_compl_poleFinset p q s hpoles
  have hres_g :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          (Metric.closedBall (0 : ℂ) R)
          Set.univ
          s
          g
          z
          (meromorphicTrailingCoeffAt f z) := by
    intro z hz
    rcases hres z hz with ⟨ρ, hρ, hρK, hρD, hsep, hdiffρ, hcircleρ⟩
    refine ⟨ρ, hρ, hρK, hρD, hsep, ?_, ?_⟩
    · refine hhol.mono ?_
      intro w hw
      have hw_not_s : w ∉ (↑s : Set ℂ) := by
        intro hws
        have hw_ne_z : w ≠ z := by
          intro hwz
          exact hw.2 (by simpa [hwz])
        exact hsep w (by simpa using hws) hw_ne_z (Metric.ball_subset_closedBall hw.1)
      simpa using hw_not_s
    · have hmeromorphic : MeromorphicOn f Set.univ :=
        rationalEval_meromorphicOn_univ p q
      have hEq :
          (fun w ↦ toMeromorphicNFOn f Set.univ w)
            =ᶠ[Filter.codiscreteWithin (Metric.sphere z |ρ|)] f := by
        exact
          (toMeromorphicNFOn_eqOn_codiscrete (U := Set.univ) hmeromorphic).symm.filter_mono
            (Filter.codiscreteWithin_mono (by
              intro w hw
              simp))
      calc
        ∮ w in C(z, ρ), g w = ∮ w in C(z, ρ), f w := by
          exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hρ.ne'
        _ = (2 * Real.pi * Complex.I : ℂ) * meromorphicTrailingCoeffAt f z := hcircleρ
  have hres_infty_g : ResidueAtInfinityCircleEq g residueAtInfinity := by
    -- The same codiscrete comparison transfers the residue-at-infinity contour owner.
    simpa [g] using residueAtInfinityCircleEq_toMeromorphicNFOn_of_rational p q hres_infty
  -- Apply the generic sphere-style residue identity to the holomorphic normal form.
  exact
    sum_residue_at_add_residue_at_infinity_eq_zero_of_holomorphic_off_finite_set
      g s (meromorphicTrailingCoeffAt f) residueAtInfinity R hhol hres_g hres_infty_g

end Rational
