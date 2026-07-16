import DifferentialForms_Cartan_1970.cartan.III.section09.«0001_Theorem_III_3_extra_1»
import DifferentialForms_Cartan_1970.cartan.III.section12.«0022_Exercise_10»
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Function Metric Set

-- Domain sampling note: this proposition lies in one-variable complex analysis on the unit disc.
-- Relevant owner declarations in the surrounding chapter/project are:
-- * `HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)` for disc automorphisms;
-- * `Function.IsFixedPt` for the fixed-point hypothesis;
-- * `eqOn_id_on_unit_disc_of_two_fixed_points` and the Schwarz-lemma equality API in
--   `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`.
-- The theorem is source-facing, while `HolomorphicIsomorph` is the core/canonical owner and any
-- unpacked `{f, g}` inverse-data formulation is only a bridge/view. Primitive data is therefore a
-- single disc automorphism together with its fixed point at `0`; the inverse map and disc
-- preservation properties are derived from the owner abstraction and should not remain primitive
-- public parameters here.

/-- Helper for Proposition 6.1: a holomorphic automorphism of the unit disc maps the disc to
itself. -/
private theorem holomorphicIsomorph_mapsTo_unit_disc
    (e : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    MapsTo e (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  -- Rewrite source membership into the owner `OpenPartialHomeomorph` API and push it forward.
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using hz
  simpa [e.target_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source

/-- Helper for Proposition 6.1: the inverse branch of a disc automorphism also preserves the unit
disc. -/
private theorem holomorphicIsomorph_symm_mapsTo_unit_disc
    (e : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    MapsTo ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  -- The inverse map is controlled by the target-to-source part of the owner API.
  have hz_target : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
    simpa [e.target_eq] using hz
  simpa [e.source_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_target hz_target

/-- Helper for Proposition 6.1: if a disc automorphism fixes `0`, then so does its inverse. -/
private theorem holomorphicIsomorph_symm_fixes_zero
    (e : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hfix : Function.IsFixedPt e 0) :
    ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) 0 = 0 := by
  have hzero_source : (0 : ℂ) ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simp [e.source_eq]
  -- Rewrite `0` as `e 0` and cancel through the inverse branch on the genuine source.
  calc
    ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) 0
        = ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (e 0) := by rw [hfix.eq]
    _ = 0 := by simpa using (e : OpenPartialHomeomorph ℂ ℂ).left_inv hzero_source

/-- Helper for Proposition 6.1: Schwarz' lemma applied to the automorphism and its inverse forces
preservation of the norm on the unit disc. -/
private theorem unit_disc_automorphism_fixing_zero_norm_eq_norm
    (e : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hfix : Function.IsFixedPt e 0) :
    ∀ z, z ∈ ball (0 : ℂ) 1 → ‖e z‖ = ‖z‖ := by
  intro z hz
  have he_diff : DifferentiableOn ℂ e (ball (0 : ℂ) 1) :=
    e.analyticOn_toFun.differentiableOn
  have he_maps : MapsTo e (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    holomorphicIsomorph_mapsTo_unit_disc e
  have hforward : ‖e z‖ ≤ ‖z‖ :=
    schwarz_lemma_norm_le e he_diff he_maps hfix.eq z hz
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using hz
  have hez : e z ∈ ball (0 : ℂ) 1 := he_maps hz
  have hsymm_diff :
      DifferentiableOn ℂ ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (ball (0 : ℂ) 1) :=
    e.analyticOn_invFun.differentiableOn
  have hsymm_maps :
      MapsTo ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    holomorphicIsomorph_symm_mapsTo_unit_disc e
  have hsymm_fix : ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) 0 = 0 :=
    holomorphicIsomorph_symm_fixes_zero e hfix
  have hback : ‖z‖ ≤ ‖e z‖ := by
    -- Apply Schwarz to the inverse map at `e z`, then rewrite the left-hand side
    -- using `e.symm (e z) = z`.
    simpa [(e : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source] using
      schwarz_lemma_norm_le
        ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) hsymm_diff hsymm_maps hsymm_fix (e z) hez
  exact le_antisymm hforward hback

/-- Helper for Proposition 6.1: norm preservation at the explicit point `1 / 2` triggers the
rigidity clause of Schwarz' lemma, so the automorphism is multiplication by a unit scalar. -/
private theorem unit_disc_automorphism_fixing_zero_is_linear_unitary
    (e : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hfix : Function.IsFixedPt e 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ EqOn e (fun z ↦ a * z) (ball (0 : ℂ) 1) := by
  have he_diff : DifferentiableOn ℂ e (ball (0 : ℂ) 1) :=
    e.analyticOn_toFun.differentiableOn
  have he_maps : MapsTo e (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    holomorphicIsomorph_mapsTo_unit_disc e
  have hz₀ : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    -- The explicit witness `1 / 2` lies strictly inside the unit disc.
    rw [mem_ball_zero_iff]
    norm_num
  have hz₀_ne : (1 / 2 : ℂ) ≠ 0 := by
    norm_num
  have hnorm_eq : ‖e (1 / 2 : ℂ)‖ = ‖(1 / 2 : ℂ)‖ :=
    unit_disc_automorphism_fixing_zero_norm_eq_norm e hfix (1 / 2 : ℂ) hz₀
  -- Feed the explicit equality case back into the rigidity statement of Schwarz' lemma.
  exact schwarz_lemma_rigidity e he_diff he_maps hfix.eq hz₀ hz₀_ne hnorm_eq

/-- Helper for Proposition 6.1: a complex number of norm `1` is exactly its unit-circle
exponential with angle `arg a`. -/
private theorem unit_complex_eq_exp_arg {a : ℂ} (ha : ‖a‖ = 1) :
    a = Complex.exp (Complex.arg a * Complex.I) := by
  -- Recover the unit complex number from its polar decomposition and then use `‖a‖ = 1`.
  calc
    a = ‖a‖ * Complex.exp (Complex.arg a * Complex.I) := by
      exact (Complex.norm_mul_exp_arg_mul_I a).symm
    _ = Complex.exp (Complex.arg a * Complex.I) := by
      simp [ha]

/-- Proposition 6.1. A biholomorphic automorphism of the open unit disc that fixes `0` is a
rotation `z ↦ exp (θ I) * z` for some real angle `θ`. -/
theorem unit_disc_automorphism_fixing_zero_is_rotation
    (e : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hfix : Function.IsFixedPt e 0) :
    ∃ θ : ℝ,
      EqOn e (fun z ↦ Complex.exp (θ * Complex.I) * z) (ball (0 : ℂ) 1) := by
  rcases unit_disc_automorphism_fixing_zero_is_linear_unitary e hfix with ⟨a, ha, hlinear⟩
  refine ⟨Complex.arg a, ?_⟩
  intro z hz
  -- The source proof now concludes by rewriting the unit scalar into exponential form.
  calc
    e z = a * z := hlinear hz
    _ = Complex.exp (Complex.arg a * Complex.I) * z := by
      simpa using congrArg (fun w : ℂ ↦ w * z) (unit_complex_eq_exp_arg ha)
