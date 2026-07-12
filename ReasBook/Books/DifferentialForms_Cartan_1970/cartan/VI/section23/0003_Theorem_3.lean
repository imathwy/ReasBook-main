import Mathlib
import DifferentialForms_Cartan_1970.VI.RiemannSphere
import DifferentialForms_Cartan_1970.VI.section23.«0002_Theorem_2»
import DifferentialForms_Cartan_1970.VI.section23.«0004_Lemma_VI_2_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Domain sampling / source-core-bridge triage:

* Primary domain: biholomorphic automorphisms of the standard Riemann sphere and their
  realization by homographies.
* Relevant owner declarations inspected upstream:
  - `RiemannSphere.RiemannSphere`
  - `RiemannSphere.equivOnePoint`
  - `OnePoint.instGLAction`
  - `OnePoint.smul_some_eq_ite`
  - `OnePoint.smul_infty_eq_ite`
* Source-facing layer: a biholomorphic automorphism of the fixed chapter owner
  `RiemannSphere.RiemannSphere`.
* Core/canonical owner: the standard complex-manifold structure already carried by
  `RiemannSphere.RiemannSphere`.
* Bridge/view layer: the set-theoretic identification `RiemannSphere.equivOnePoint` to
  `OnePoint ℂ`, where mathlib's canonical `GL (Fin 2) ℂ` action gives the homography formulas.

Primitive data is only the biholomorphic automorphism of the canonical Riemann sphere. The
homographic realization on `OnePoint ℂ` is derived bridge/view API.
-/

open scoped Manifold

/- Helper recalls: mathlib already owns the canonical homography action on `OnePoint ℂ`. -/
recall OnePoint.smul_some_eq_ite
recall OnePoint.smul_infty_eq_ite

namespace RiemannSphere

/-- Helper for Theorem 3: the chapter's Riemann sphere is definitionally the one-point
compactification of `ℂ`, so the source-facing bridge to `OnePoint ℂ` is the identity equivalence. -/
abbrev equivOnePoint : RiemannSphere ≃ OnePoint ℂ :=
  Equiv.refl _

/-- Helper for Theorem 3: the affine chart on the finite part of the Riemann sphere is a
manifold-local diffeomorphism. -/
lemma affine_open_partial_homeomorph_mdifferentiable :
    RiemannSphere.affineOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · -- The forward affine chart is one of the preferred complex charts on the sphere.
    have hcont :
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph
          RiemannSphere.affineOpenPartialHomeomorph.source := by
      simpa [RiemannSphere.chartAt_coe, extChartAt_coe, Function.comp]
        using contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
    exact hcont.mdifferentiableOn one_ne_zero
  · -- Its inverse branch is the inverse preferred chart at the same finite base point.
    have hcont :
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph.symm
          RiemannSphere.affineOpenPartialHomeomorph.target := by
      simpa [RiemannSphere.chartAt_coe, extChartAt_coe_symm, Function.comp]
        using contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
    exact hcont.mdifferentiableOn one_ne_zero

/-- Helper for Theorem 3: the `∞`-chart on the Riemann sphere is a manifold-local
diffeomorphism. -/
lemma infty_open_partial_homeomorph_mdifferentiable :
    RiemannSphere.inftyOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · -- The forward `∞`-chart is the preferred chart at `∞`.
    have hcont :
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.inftyOpenPartialHomeomorph
          RiemannSphere.inftyOpenPartialHomeomorph.source := by
      simpa [RiemannSphere.chartAt_infty, Function.comp]
        using contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := (OnePoint.infty : RiemannSphere))
    exact hcont.mdifferentiableOn one_ne_zero
  · -- Its inverse branch is the inverse preferred chart at `∞`.
    have hcont :
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.inftyOpenPartialHomeomorph.symm
          RiemannSphere.inftyOpenPartialHomeomorph.target := by
      simpa [RiemannSphere.chartAt_infty, Function.comp]
        using contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := (OnePoint.infty : RiemannSphere))
    exact hcont.mdifferentiableOn one_ne_zero

/-- Helper for Theorem 3: the inverse affine chart is likewise a manifold-local diffeomorphism. -/
lemma affine_open_partial_homeomorph_symm_mdifferentiable :
    RiemannSphere.affineOpenPartialHomeomorph.symm.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  -- Swapping an open partial homeomorphism with its inverse just swaps the two differentiability
  -- requirements.
  constructor
  · exact affine_open_partial_homeomorph_mdifferentiable.2
  · exact affine_open_partial_homeomorph_mdifferentiable.1

/-- Helper for Theorem 3: conjugating a sphere automorphism by the affine chart gives the planar
open partial homeomorphism on the finite part. -/
noncomputable def sphere_automorphism_fixing_infty_to_plane_partialHomeomorph
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere) :
    OpenPartialHomeomorph ℂ ℂ :=
  RiemannSphere.affineOpenPartialHomeomorph.symm.trans
    σ.toHomeomorph.toOpenPartialHomeomorph |>.trans RiemannSphere.affineOpenPartialHomeomorph

/-- Helper for Theorem 3: if a sphere automorphism fixes `∞`, then it sends every finite point to
another finite point. -/
lemma sphere_automorphism_fixing_infty_maps_finite
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (hfix : σ OnePoint.infty = OnePoint.infty) (z : ℂ) :
    σ (z : RiemannSphere) ≠ OnePoint.infty := by
  -- Apply the inverse automorphism and use that `∞` is the unique point mapping to `∞`.
  have hsymm_fix : σ.symm (OnePoint.infty : RiemannSphere) = OnePoint.infty := by
    apply σ.injective
    simp [hfix]
  intro hz
  have hpre : ((z : ℂ) : RiemannSphere) = OnePoint.infty := by
    simpa [hsymm_fix] using congrArg σ.symm hz
  have hne : ((z : ℂ) : RiemannSphere) ≠ OnePoint.infty := by
    simp
  exact hne hpre

/-- Helper for Theorem 3: after fixing `∞`, the conjugated plane map is defined on all of `ℂ`. -/
lemma sphere_automorphism_fixing_infty_to_plane_source_eq_univ
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (hfix : σ OnePoint.infty = OnePoint.infty) :
    (sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ).source = Set.univ := by
  -- The only possible obstruction is hitting `∞` after applying `σ`, and the fixed-`∞`
  -- hypothesis rules that out on finite points.
  ext z
  change z ∈ (sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ).source ↔ z ∈ Set.univ
  constructor
  · intro _
    simp
  · intro _
    rw [sphere_automorphism_fixing_infty_to_plane_partialHomeomorph, OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_source]
      exact ⟨by exact Set.mem_univ z, by simp⟩
    · change σ (((RiemannSphere.affineOpenPartialHomeomorph.symm) z : RiemannSphere))
        ∈ RiemannSphere.affineOpenPartialHomeomorph.source
      simpa [RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart] using
        sphere_automorphism_fixing_infty_maps_finite σ hfix z

/-- Helper for Theorem 3: the same conjugated plane map is onto all of `ℂ`. -/
lemma sphere_automorphism_fixing_infty_to_plane_target_eq_univ
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (hfix : σ OnePoint.infty = OnePoint.infty) :
    (sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ).target = Set.univ := by
  -- The target statement is the source statement for the inverse automorphism, which fixes `∞`
  -- for the same reason.
  have hsymm_fix : σ.symm (OnePoint.infty : RiemannSphere) = OnePoint.infty := by
    apply σ.injective
    simp [hfix]
  ext z
  change z ∈ (sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ).target ↔ z ∈ Set.univ
  constructor
  · intro _
    simp
  · intro _
    rw [sphere_automorphism_fixing_infty_to_plane_partialHomeomorph, OpenPartialHomeomorph.trans_target]
    refine ⟨?_, ?_⟩
    · change z ∈ RiemannSphere.affineOpenPartialHomeomorph.target
      exact Set.mem_univ z
    · rw [OpenPartialHomeomorph.trans_target]
      refine ⟨?_, ?_⟩
      · simp
      · simpa [RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart] using
          sphere_automorphism_fixing_infty_maps_finite σ.symm hsymm_fix z

/-- Helper for Theorem 3: the conjugated plane map is `C¹`, hence analytic on all of `ℂ`. -/
lemma sphere_automorphism_fixing_infty_to_plane_analyticOn_toFun
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (hfix : σ OnePoint.infty = OnePoint.infty) :
    AnalyticOnNhd ℂ (sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ) Set.univ := by
  let e := sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ
  have hσ :
      σ.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    -- A global manifold equivalence is locally differentiable on both branches.
    exact σ.toOpenPartialHomeomorph_mdifferentiable one_ne_zero
  have he :
      e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    -- Conjugate the sphere automorphism by the affine chart on the source and target.
    exact OpenPartialHomeomorph.MDifferentiable.trans
      (OpenPartialHomeomorph.MDifferentiable.trans
        affine_open_partial_homeomorph_symm_mdifferentiable
        hσ)
      affine_open_partial_homeomorph_mdifferentiable
  have hsource : e.source = Set.univ :=
    sphere_automorphism_fixing_infty_to_plane_source_eq_univ σ hfix
  -- On the plane, `C¹` on the whole open source is enough to recover analyticity.
  simpa [e, hsource] using
    he.1.differentiableOn.analyticOnNhd (by simpa [hsource] using e.open_source)

/-- Helper for Theorem 3: the inverse conjugated plane map is analytic on all of `ℂ`. -/
lemma sphere_automorphism_fixing_infty_to_plane_analyticOn_invFun
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (hfix : σ OnePoint.infty = OnePoint.infty) :
    AnalyticOnNhd ℂ (sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ).symm Set.univ := by
  let e := sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ
  have hσ :
      σ.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    -- A global manifold equivalence is locally differentiable on both branches.
    exact σ.toOpenPartialHomeomorph_mdifferentiable one_ne_zero
  have he :
      e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    -- Conjugate the sphere automorphism by the affine chart on the source and target.
    exact OpenPartialHomeomorph.MDifferentiable.trans
      (OpenPartialHomeomorph.MDifferentiable.trans
        affine_open_partial_homeomorph_symm_mdifferentiable
        hσ)
      affine_open_partial_homeomorph_mdifferentiable
  have htarget : e.target = Set.univ :=
    sphere_automorphism_fixing_infty_to_plane_target_eq_univ σ hfix
  -- The inverse branch is handled identically on the target.
  simpa [e, htarget] using
    he.2.differentiableOn.analyticOnNhd (by simpa [htarget] using e.open_target)

/-- Helper for Theorem 3: fixing `∞` lets us conjugate a sphere automorphism to a holomorphic
automorphism of the whole complex plane. -/
noncomputable def sphere_automorphism_fixing_infty_to_plane_automorphism
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (hfix : σ OnePoint.infty = OnePoint.infty) :
    HolomorphicIsomorph Set.univ Set.univ :=
  ⟨sphere_automorphism_fixing_infty_to_plane_partialHomeomorph σ, ⟨
    sphere_automorphism_fixing_infty_to_plane_source_eq_univ σ hfix,
    sphere_automorphism_fixing_infty_to_plane_target_eq_univ σ hfix,
    sphere_automorphism_fixing_infty_to_plane_analyticOn_toFun σ hfix,
    sphere_automorphism_fixing_infty_to_plane_analyticOn_invFun σ hfix⟩⟩

/-- Helper for Theorem 3: the standard upper-triangular matrix with nonzero diagonal coefficient
has nonzero determinant. -/
lemma upper_triangular_affine_det_ne_zero (a : ℂˣ) (b : ℂ) :
    Matrix.det (!![((a : ℂ)), b; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  -- The determinant is just the nonzero affine coefficient.
  simp [Matrix.det_fin_two]

/-- Helper for Theorem 3: the upper-triangular matrix `[[a, b], [0, 1]]` acts on `OnePoint ℂ` by
the affine map `z ↦ a z + b` and fixes `∞`. -/
lemma upper_triangular_matrix_represents_affine_map
    (a : ℂˣ) (b z : ℂ) :
    let g : GL (Fin 2) ℂ :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        (!![((a : ℂ)), b; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
        (upper_triangular_affine_det_ne_zero a b)
    g • ((z : ℂ) : OnePoint ℂ) = (((a : ℂ) * z + b : ℂ) : OnePoint ℂ) ∧
      g • (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := by
  -- The Möbius denominator is constantly `1`, so the action reduces to the affine formula.
  let g : GL (Fin 2) ℂ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![((a : ℂ)), b; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (upper_triangular_affine_det_ne_zero a b)
  constructor
  · simp [g, OnePoint.smul_some_eq_ite]
  · simp [g, OnePoint.smul_infty_eq_ite]

/-- Helper for Theorem 3: a sphere automorphism fixing `∞` is already an affine homography. -/
lemma sphere_automorphism_fixing_infty_is_affine_homography
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (hfix : σ OnePoint.infty = OnePoint.infty) :
    ∃ g : GL (Fin 2) ℂ,
      ∀ z : RiemannSphere, equivOnePoint (σ z) = g • equivOnePoint z := by
  let e := sphere_automorphism_fixing_infty_to_plane_automorphism σ hfix
  obtain ⟨a, b, hab⟩ := complex_plane_automorphism_affine e
  let g : GL (Fin 2) ℂ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![((a : ℂ)), b; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (upper_triangular_affine_det_ne_zero a b)
  refine ⟨g, ?_⟩
  intro z
  cases z using OnePoint.rec with
  | infty =>
      -- Both the sphere automorphism and the upper-triangular homography fix `∞`.
      have hg : g • (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := by
        simpa [g] using (upper_triangular_matrix_represents_affine_map a b 0).2
      simpa [equivOnePoint, hfix] using hg.symm
  | coe w =>
      -- On finite points, the conjugated plane automorphism is exactly the affine map from
      -- Theorem 2, so we pull the equality back through the affine chart.
      have hwfinite : σ (w : RiemannSphere) ≠ OnePoint.infty :=
        sphere_automorphism_fixing_infty_maps_finite σ hfix w
      have hchart :
          (e : OpenPartialHomeomorph ℂ ℂ) w =
            RiemannSphere.affineOpenPartialHomeomorph (σ (w : RiemannSphere)) := by
        change
          RiemannSphere.affineOpenPartialHomeomorph
            (σ (((RiemannSphere.affineOpenPartialHomeomorph.symm) w : RiemannSphere))) =
              RiemannSphere.affineOpenPartialHomeomorph (σ (w : RiemannSphere))
        simp [RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart]
      have hsphere :
          σ (w : RiemannSphere) = (((a : ℂ) * w + b : ℂ) : RiemannSphere) := by
        calc
          σ (w : RiemannSphere) =
              RiemannSphere.affineOpenPartialHomeomorph.symm ((e : OpenPartialHomeomorph ℂ ℂ) w) := by
                rw [hchart]
                exact (RiemannSphere.affineOpenPartialHomeomorph.left_inv hwfinite).symm
          _ = (((a : ℂ) * w + b : ℂ) : RiemannSphere) := by
                rw [hab w]
                rfl
      have hg :
          g • ((w : ℂ) : OnePoint ℂ) = (((a : ℂ) * w + b : ℂ) : OnePoint ℂ) := by
        simpa [g] using (upper_triangular_matrix_represents_affine_map a b w).1
      simpa [equivOnePoint, hsphere] using hg.symm

/-- Helper for Theorem 3: the matrix `[[0, 1], [1, -c]]` has nonzero determinant, so it defines
the basic homography sending `c` to `∞`. -/
lemma point_to_infty_matrix_det_ne_zero (c : ℂ) :
    Matrix.det (!![(0 : ℂ), 1; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  -- The determinant is `-1`, independently of the chosen center `c`.
  simp [Matrix.det_fin_two]

/-- Helper for Theorem 3: the basic homography `z ↦ 1 / (z - c)` is represented on `OnePoint ℂ`
by the matrix `[[0, 1], [1, -c]]`. -/
lemma point_to_infty_matrix_smul_finite (c z : ℂ) :
    let g : GL (Fin 2) ℂ :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        (!![(0 : ℂ), 1; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ)
        (point_to_infty_matrix_det_ne_zero c)
    g • ((z : ℂ) : OnePoint ℂ) =
      if z = c then OnePoint.infty else (((z - c)⁻¹ : ℂ) : OnePoint ℂ) := by
  -- The Möbius denominator is `z - c`, so the action is the expected inversion after translation.
  let g : GL (Fin 2) ℂ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![(0 : ℂ), 1; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ)
      (point_to_infty_matrix_det_ne_zero c)
  by_cases hz : z = c
  · subst hz
    simp [g, OnePoint.smul_some_eq_ite]
  · have hsub : z - c ≠ 0 := sub_ne_zero.mpr hz
    have hsum : z + -c ≠ 0 := by
      simpa [sub_eq_add_neg] using hsub
    simp [g, OnePoint.smul_some_eq_ite, hz, hsum, sub_eq_add_neg, div_eq_inv_mul, mul_comm]

/-- Helper for Theorem 3: the same matrix sends the finite point `c` itself to `∞`. -/
lemma point_to_infty_matrix_smul_center (c : ℂ) :
    let g : GL (Fin 2) ℂ :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        (!![(0 : ℂ), 1; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ)
        (point_to_infty_matrix_det_ne_zero c)
    g • ((c : ℂ) : OnePoint ℂ) = OnePoint.infty := by
  -- This is the vanishing-denominator special case of the previous explicit formula.
  simpa using point_to_infty_matrix_smul_finite c c

/-- Helper for Theorem 3: the source-faithful point mover sending a finite center `c` to `∞`
uses the Möbius formula `z ↦ (z - c)⁻¹`, with `∞ ↦ 0` and `c ↦ ∞`. -/
noncomputable def point_to_infty_map (c : ℂ) : RiemannSphere → RiemannSphere
  | OnePoint.infty => ((0 : ℂ) : RiemannSphere)
  | (z : ℂ) => if z = c then OnePoint.infty else (((z - c)⁻¹ : ℂ) : RiemannSphere)

/-- Helper for Theorem 3: the inverse source-faithful point mover sends `∞` back to `c`,
`0` back to `∞`, and otherwise uses `w ↦ c + w⁻¹`. -/
noncomputable def point_from_infty_map (c : ℂ) : RiemannSphere → RiemannSphere
  | OnePoint.infty => ((c : ℂ) : RiemannSphere)
  | (w : ℂ) => if w = 0 then OnePoint.infty else (((c + w⁻¹ : ℂ)) : RiemannSphere)

/-- Helper for Theorem 3: the explicit inverse formula really inverts `point_to_infty_map`
on every sphere point. -/
lemma point_from_infty_left_inverse (c : ℂ) :
    Function.LeftInverse (point_from_infty_map c) (point_to_infty_map c) := by
  intro z
  cases z using OnePoint.rec with
  | infty =>
      -- The forward map sends `∞` to `0`, and the inverse sends `0` back to `∞`.
      simp [point_to_infty_map, point_from_infty_map]
  | coe z =>
      by_cases hz : z = c
      · -- At the center `c`, the forward map lands at `∞`.
        subst hz
        simp [point_to_infty_map, point_from_infty_map]
      · -- Away from the center, the two Möbius formulas are literal inverses.
        have hsub : z - c ≠ 0 := sub_ne_zero.mpr hz
        have hsum : c + (z - c) = z := by ring
        simp [point_to_infty_map, point_from_infty_map, hz, hsub, hsum]

/-- Helper for Theorem 3: the same formulas also invert in the opposite order. -/
lemma point_from_infty_right_inverse (c : ℂ) :
    Function.RightInverse (point_from_infty_map c) (point_to_infty_map c) := by
  intro z
  cases z using OnePoint.rec with
  | infty =>
      -- The inverse sends `∞` to `c`, and the forward map sends `c` back to `∞`.
      simp [point_to_infty_map, point_from_infty_map]
  | coe w =>
      by_cases hw : w = 0
      · -- The inverse sends `0` to `∞`, which the forward map returns to `0`.
        subst hw
        simp [point_to_infty_map, point_from_infty_map]
      · -- Away from `0`, the inverse Möbius formula undoes the forward one.
        have hwinv : w⁻¹ ≠ 0 := inv_ne_zero hw
        have hne : c + w⁻¹ ≠ c := by
          intro h
          have hw0 : w⁻¹ = 0 := by
            have h' : c + w⁻¹ = c + 0 := by simpa using h
            exact add_left_cancel h'
          exact hwinv hw0
        have hsub : c + w⁻¹ - c = w⁻¹ := by ring
        simp [point_to_infty_map, point_from_infty_map, hw, hwinv, hne, hsub]

/-- Helper for Theorem 3: the explicit Möbius point mover is already an equivalence of the
underlying sphere set. The remaining work is to package its manifold regularity. -/
noncomputable def point_to_infty_equiv (c : ℂ) : RiemannSphere ≃ RiemannSphere where
  toFun := point_to_infty_map c
  invFun := point_from_infty_map c
  left_inv := point_from_infty_left_inverse c
  right_inv := point_from_infty_right_inverse c

/-- Helper for Theorem 3: the explicit point mover sends its chosen center to `∞`. -/
lemma point_to_infty_map_center (c : ℂ) :
    point_to_infty_map c ((c : ℂ) : RiemannSphere) = OnePoint.infty := by
  -- This is the center branch in the explicit definition.
  simp [point_to_infty_map]

/-- Helper for Theorem 3: the explicit point mover realizes the already-chosen matrix
`[[0, 1], [1, -c]]` on `equivOnePoint`. -/
lemma point_to_infty_map_eq_matrix_action (c : ℂ) :
    ∃ g : GL (Fin 2) ℂ,
      point_to_infty_map c ((c : ℂ) : RiemannSphere) = OnePoint.infty ∧
      ∀ z : RiemannSphere, equivOnePoint (point_to_infty_map c z) = g • equivOnePoint z := by
  let g : GL (Fin 2) ℂ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![(0 : ℂ), 1; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ)
      (point_to_infty_matrix_det_ne_zero c)
  refine ⟨g, point_to_infty_map_center c, ?_⟩
  intro z
  cases z using OnePoint.rec with
  | infty =>
      -- At `∞`, the matrix action also lands at `0`.
      simp [g, point_to_infty_map, equivOnePoint, OnePoint.smul_infty_eq_ite]
  | coe z =>
      -- On finite points, reuse the already-established Möbius matrix formula.
      simpa [g, point_to_infty_map, equivOnePoint] using
        (point_to_infty_matrix_smul_finite c z).symm

/-- Helper for Theorem 3: the explicit point mover is bijective because we already packaged it as
an equivalence of the underlying sphere set. -/
lemma point_to_infty_map_bijective (c : ℂ) :
    Function.Bijective (point_to_infty_map c) :=
  (point_to_infty_equiv c).bijective

/-- Helper for Theorem 3: the affine chart is `C¹` on its source. -/
lemma affine_open_partial_homeomorph_contMDiffOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph
      RiemannSphere.affineOpenPartialHomeomorph.source := by
  -- The affine chart is one of the preferred complex charts on the sphere.
  simpa [RiemannSphere.chartAt_coe, extChartAt_coe, Function.comp] using
    contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))

/-- Helper for Theorem 3: the inverse affine chart is `C¹` on its source. -/
lemma affine_open_partial_homeomorph_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph.symm
      RiemannSphere.affineOpenPartialHomeomorph.target := by
  -- The inverse affine chart is the inverse preferred chart at a finite point.
  simpa [RiemannSphere.chartAt_coe, extChartAt_coe_symm, Function.comp] using
    contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))

/-- Helper for Theorem 3: the `∞`-chart is `C¹` on its source. -/
lemma infty_open_partial_homeomorph_contMDiffOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.inftyOpenPartialHomeomorph
      RiemannSphere.inftyOpenPartialHomeomorph.source := by
  -- The `∞`-chart is the preferred chart centered at `∞`.
  simpa [RiemannSphere.chartAt_infty, Function.comp] using
    contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := (OnePoint.infty : RiemannSphere))

/-- Helper for Theorem 3: the inverse `∞`-chart is `C¹` on its source. -/
lemma infty_open_partial_homeomorph_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.inftyOpenPartialHomeomorph.symm
      RiemannSphere.inftyOpenPartialHomeomorph.target := by
  -- The inverse `∞`-chart is the inverse preferred chart at `∞`.
  simpa [RiemannSphere.chartAt_infty, Function.comp] using
    contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := (OnePoint.infty : RiemannSphere))

/-- Helper for Theorem 3: translation by `-c` is a global complex diffeomorphism of `ℂ`. -/
noncomputable def sub_const_diffeomorph (c : ℂ) : ℂ ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ where
  toEquiv :=
    { toFun := fun z ↦ z - c
      invFun := fun w ↦ w + c
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
  contMDiff_toFun := by
    -- Translation is affine in the standard complex coordinates.
    simpa [sub_eq_add_neg] using
      ((contMDiff_id : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 fun z : ℂ ↦ z).add contMDiff_const)
  contMDiff_invFun := by
    -- The inverse translation is affine as well.
    simpa using
      ((contMDiff_id : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 fun z : ℂ ↦ z).add contMDiff_const)

/-- Helper for Theorem 3: the planar rational branch `w ↦ w / (1 - c w)` is defined exactly away
from the zero set of its denominator. -/
def point_to_infty_rational_source (c : ℂ) : Set ℂ :=
  {w : ℂ | 1 - c * w ≠ 0}

/-- Helper for Theorem 3: the inverse planar rational branch `u ↦ u / (1 + c u)` is defined
exactly away from the zero set of its denominator. -/
def point_to_infty_rational_target (c : ℂ) : Set ℂ :=
  {u : ℂ | 1 + c * u ≠ 0}

/-- Helper for Theorem 3: the forward rational denominator rewrites to the inverse affine factor
after applying the source-faithful planar branch. -/
lemma point_to_infty_rational_forward_denominator (c w : ℂ)
    (hw : w ∈ point_to_infty_rational_source c) :
    1 + c * (w / (1 - c * w)) = (1 - c * w)⁻¹ := by
  -- Clear the nonzero denominator once and reduce the identity to polynomial algebra.
  have hw0 : 1 - c * w ≠ 0 := hw
  field_simp [hw0]
  ring

/-- Helper for Theorem 3: the inverse rational denominator rewrites to the inverse affine factor
before returning from the `∞`-chart model. -/
lemma point_to_infty_rational_inverse_denominator (c u : ℂ)
    (hu : u ∈ point_to_infty_rational_target c) :
    1 - c * (u / (1 + c * u)) = (1 + c * u)⁻¹ := by
  -- This is the same Möbius denominator identity on the target side.
  have hu0 : 1 + c * u ≠ 0 := hu
  field_simp [hu0]
  ring

/-- Helper for Theorem 3: the source denominator nonvanishing condition is open. -/
lemma point_to_infty_rational_source_isOpen (c : ℂ) :
    IsOpen (point_to_infty_rational_source c) := by
  -- The source is the complement of the zero fiber of a continuous affine function.
  simpa [point_to_infty_rational_source] using
    (isOpen_ne_fun
      (continuous_const.sub (continuous_const.mul continuous_id))
      continuous_const)

/-- Helper for Theorem 3: the target denominator nonvanishing condition is open. -/
lemma point_to_infty_rational_target_isOpen (c : ℂ) :
    IsOpen (point_to_infty_rational_target c) := by
  -- The target is the same kind of affine nonvanishing locus.
  simpa [point_to_infty_rational_target] using
    (isOpen_ne_fun
      (continuous_const.add (continuous_const.mul continuous_id))
      continuous_const)

/-- Helper for Theorem 3: the planar rational branch sends its source into its target. -/
lemma point_to_infty_rational_map_source (c w : ℂ)
    (hw : w ∈ point_to_infty_rational_source c) :
    w / (1 - c * w) ∈ point_to_infty_rational_target c := by
  -- Rewrite the new denominator to an inverse of the old one, which is still nonzero.
  have hw0 : 1 - c * w ≠ 0 := hw
  simpa [point_to_infty_rational_target, point_to_infty_rational_forward_denominator c w hw] using
    inv_ne_zero hw0

/-- Helper for Theorem 3: the inverse planar rational branch sends its target back into its
source. -/
lemma point_to_infty_rational_map_target (c u : ℂ)
    (hu : u ∈ point_to_infty_rational_target c) :
    u / (1 + c * u) ∈ point_to_infty_rational_source c := by
  -- The same denominator rewrite works in the reverse direction.
  have hu0 : 1 + c * u ≠ 0 := hu
  simpa [point_to_infty_rational_source, point_to_infty_rational_inverse_denominator c u hu] using
    inv_ne_zero hu0

/-- Helper for Theorem 3: the forward and inverse rational formulas are inverse on the source
locus. -/
lemma point_to_infty_rational_left_inv (c w : ℂ)
    (hw : w ∈ point_to_infty_rational_source c) :
    (w / (1 - c * w)) / (1 + c * (w / (1 - c * w))) = w := by
  -- Rewrite the second denominator first, then clear the original nonzero denominator.
  have hw0 : 1 - c * w ≠ 0 := hw
  rw [point_to_infty_rational_forward_denominator c w hw]
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_assoc, inv_mul_cancel₀ hw0, mul_one]

/-- Helper for Theorem 3: the inverse and forward rational formulas are inverse on the target
locus. -/
lemma point_to_infty_rational_right_inv (c u : ℂ)
    (hu : u ∈ point_to_infty_rational_target c) :
    (u / (1 + c * u)) / (1 - c * (u / (1 + c * u))) = u := by
  -- Again rewrite the remaining denominator before clearing it.
  have hu0 : 1 + c * u ≠ 0 := hu
  rw [point_to_infty_rational_inverse_denominator c u hu]
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_assoc, inv_mul_cancel₀ hu0, mul_one]

/-- Helper for Theorem 3: the forward rational branch is continuous on its nonvanishing source
locus. -/
lemma point_to_infty_rational_toFun_continuousOn (c : ℂ) :
    ContinuousOn (fun w : ℂ ↦ w / (1 - c * w)) (point_to_infty_rational_source c) := by
  -- Use the standard continuity rule for division with a pointwise nonvanishing denominator.
  refine ContinuousOn.div₀ continuousOn_id ?_ ?_
  · simpa using
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  · intro w hw
    exact hw

/-- Helper for Theorem 3: the inverse rational branch is continuous on its nonvanishing target
locus. -/
lemma point_to_infty_rational_invFun_continuousOn (c : ℂ) :
    ContinuousOn (fun u : ℂ ↦ u / (1 + c * u)) (point_to_infty_rational_target c) := by
  -- The inverse branch is the same division pattern with the target denominator.
  refine ContinuousOn.div₀ continuousOn_id ?_ ?_
  · simpa using
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  · intro u hu
    exact hu

/-- Helper for Theorem 3: the forward rational branch is `C¹` on its nonvanishing source
locus. -/
lemma point_to_infty_rational_toFun_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun w : ℂ ↦ w / (1 - c * w))
      (point_to_infty_rational_source c) := by
  -- Differentiate the numerator and denominator separately, then divide on the nonvanishing
  -- locus.
  refine ContMDiffOn.div₀ contMDiffOn_id ?_ ?_
  · simpa using (contMDiffOn_const.sub (contMDiffOn_const.mul contMDiffOn_id))
  · intro w hw
    exact hw

/-- Helper for Theorem 3: the inverse rational branch is `C¹` on its nonvanishing target
locus. -/
lemma point_to_infty_rational_invFun_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun u : ℂ ↦ u / (1 + c * u))
      (point_to_infty_rational_target c) := by
  -- The inverse branch has the same structure, with `1 + c u` in the denominator.
  refine ContMDiffOn.div₀ contMDiffOn_id ?_ ?_
  · simpa using (contMDiffOn_const.add (contMDiffOn_const.mul contMDiffOn_id))
  · intro u hu
    exact hu

/-- Helper for Theorem 3: the rational branch around `∞` is an open partial homeomorphism of `ℂ`.
-/
noncomputable def point_to_infty_rational_openPartialHomeomorph (c : ℂ) :
    OpenPartialHomeomorph ℂ ℂ :=
  { toPartialEquiv :=
      { toFun := fun w ↦ w / (1 - c * w)
        invFun := fun u ↦ u / (1 + c * u)
        source := point_to_infty_rational_source c
        target := point_to_infty_rational_target c
        map_source' := point_to_infty_rational_map_source c
        map_target' := point_to_infty_rational_map_target c
        left_inv' := point_to_infty_rational_left_inv c
        right_inv' := point_to_infty_rational_right_inv c }
    open_source := point_to_infty_rational_source_isOpen c
    open_target := point_to_infty_rational_target_isOpen c
    continuousOn_toFun := point_to_infty_rational_toFun_continuousOn c
    continuousOn_invFun := point_to_infty_rational_invFun_continuousOn c }

/-- Helper for Theorem 3: the rational branch around `∞` is `C¹` on its source. -/
lemma point_to_infty_rational_openPartialHomeomorph_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_rational_openPartialHomeomorph c)
      (point_to_infty_rational_openPartialHomeomorph c).source := by
  -- Unfold the packaged branch back to the explicit rational formula proved just above.
  simpa [point_to_infty_rational_openPartialHomeomorph] using
    point_to_infty_rational_toFun_contMDiffOn c

/-- Helper for Theorem 3: the inverse rational branch is `C¹` on its source. -/
lemma point_to_infty_rational_openPartialHomeomorph_symm_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_rational_openPartialHomeomorph c).symm
      (point_to_infty_rational_openPartialHomeomorph c).target := by
  -- The inverse packaged branch is the explicit inverse rational formula on the target locus.
  simpa [point_to_infty_rational_openPartialHomeomorph] using
    point_to_infty_rational_invFun_contMDiffOn c

/-- Helper for Theorem 3: once an `OpenPartialHomeomorph` has `C¹` forward and inverse branches,
it can be repackaged as a `PartialDiffeomorph` without further transport work. -/
noncomputable def partialDiffeomorph_of_openPartialHomeomorph
    {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace N] [ChartedSpace ℂ N]
    (e : OpenPartialHomeomorph M N)
    (he_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 e e.source)
    (he_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 e.symm e.target) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) M N 1 :=
  { toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he_to
    contMDiffOn_invFun := he_inv }

-- On the whole finite part of the sphere, the source point-mover is the composition
-- "affine chart, translate by `-c`, then invert back through the `∞`-chart".
/-- Helper for Theorem 3: the finite-point branch is the chart-level transport of
`z ↦ z - c` followed by the inverse `∞`-chart. -/
noncomputable def point_to_infty_finite_openPartialHomeomorph (c : ℂ) :
    OpenPartialHomeomorph RiemannSphere RiemannSphere :=
  (RiemannSphere.affineOpenPartialHomeomorph.transHomeomorph
      (sub_const_diffeomorph c).toHomeomorph).trans
    RiemannSphere.inftyOpenPartialHomeomorph.symm

/-- Helper for Theorem 3: the finite-point chart transport is `C¹` on its source. -/
lemma point_to_infty_finite_openPartialHomeomorph_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_finite_openPartialHomeomorph c)
      (point_to_infty_finite_openPartialHomeomorph c).source := by
  -- Compose the finite affine chart, the global translation, and the inverse `∞`-chart.
  have htranslate :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (sub_const_diffeomorph c) Set.univ :=
    (sub_const_diffeomorph c).contMDiff_toFun.contMDiffOn
  have htranslated :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        ((sub_const_diffeomorph c) ∘ RiemannSphere.affineOpenPartialHomeomorph)
        (RiemannSphere.affineOpenPartialHomeomorph.source ∩
          RiemannSphere.affineOpenPartialHomeomorph ⁻¹' Set.univ) :=
    htranslate.comp' affine_open_partial_homeomorph_contMDiffOn
  have hinfty :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        (RiemannSphere.inftyOpenPartialHomeomorph.symm ∘
          ((sub_const_diffeomorph c) ∘ RiemannSphere.affineOpenPartialHomeomorph))
        ((RiemannSphere.affineOpenPartialHomeomorph.source ∩
            RiemannSphere.affineOpenPartialHomeomorph ⁻¹' Set.univ) ∩
          ((sub_const_diffeomorph c) ∘ RiemannSphere.affineOpenPartialHomeomorph) ⁻¹'
            RiemannSphere.inftyOpenPartialHomeomorph.symm.source) :=
    infty_open_partial_homeomorph_symm_contMDiffOn.comp' htranslated
  simpa [point_to_infty_finite_openPartialHomeomorph, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.trans_source, Function.comp_def,
    Set.preimage_inter, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hinfty

/-- Helper for Theorem 3: the inverse finite-point chart transport is `C¹` on its source. -/
lemma point_to_infty_finite_openPartialHomeomorph_symm_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_finite_openPartialHomeomorph c).symm
      (point_to_infty_finite_openPartialHomeomorph c).target := by
  -- Reverse the same chart transport using the inverse translation and the affine inverse chart.
  have htranslate :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (sub_const_diffeomorph c).symm Set.univ :=
    (sub_const_diffeomorph c).symm.contMDiff_toFun.contMDiffOn
  have htranslated :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        ((sub_const_diffeomorph c).symm ∘ RiemannSphere.inftyOpenPartialHomeomorph)
        (RiemannSphere.inftyOpenPartialHomeomorph.source ∩
          RiemannSphere.inftyOpenPartialHomeomorph ⁻¹' Set.univ) :=
    htranslate.comp' infty_open_partial_homeomorph_contMDiffOn
  have haffine :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        (RiemannSphere.affineOpenPartialHomeomorph.symm ∘
          ((sub_const_diffeomorph c).symm ∘ RiemannSphere.inftyOpenPartialHomeomorph))
        ((RiemannSphere.inftyOpenPartialHomeomorph.source ∩
            RiemannSphere.inftyOpenPartialHomeomorph ⁻¹' Set.univ) ∩
          ((sub_const_diffeomorph c).symm ∘ RiemannSphere.inftyOpenPartialHomeomorph) ⁻¹'
            RiemannSphere.affineOpenPartialHomeomorph.symm.source) :=
    affine_open_partial_homeomorph_symm_contMDiffOn.comp' htranslated
  simpa [point_to_infty_finite_openPartialHomeomorph, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.trans_target, Function.comp_def,
    Set.preimage_inter, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using haffine

noncomputable def point_to_infty_finite_partialDiffeomorph (c : ℂ) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere RiemannSphere 1 :=
  partialDiffeomorph_of_openPartialHomeomorph
    (point_to_infty_finite_openPartialHomeomorph c)
    (point_to_infty_finite_openPartialHomeomorph_contMDiffOn c)
    (point_to_infty_finite_openPartialHomeomorph_symm_contMDiffOn c)

/-- Helper for Theorem 3: the finite-branch partial diffeomorphism agrees with the explicit
source point-mover on its whole source. -/
lemma point_to_infty_finite_partialDiffeomorph_eqOn (c : ℂ) :
    Set.EqOn (point_to_infty_map c) (point_to_infty_finite_partialDiffeomorph c)
      (point_to_infty_finite_partialDiffeomorph c).source := by
  intro x hx
  cases x using OnePoint.rec with
  | infty =>
      -- The finite branch is only defined on the affine chart source, so `∞` cannot occur here.
      exfalso
      simpa [point_to_infty_finite_partialDiffeomorph, point_to_infty_finite_openPartialHomeomorph,
        partialDiffeomorph_of_openPartialHomeomorph, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.transHomeomorph_eq_trans, RiemannSphere.affineOpenPartialHomeomorph,
        RiemannSphere.affineChart] using hx
  | coe z =>
      -- On a finite point, the transported branch is exactly the source formula
      -- `if z = c then ∞ else (z - c)⁻¹`.
      by_cases hz : z = c
      · subst hz
        have htranslate : (sub_const_diffeomorph z) z = z - z := rfl
        have hzero : (sub_const_diffeomorph z) z = 0 := by
          simpa [htranslate] using sub_self z
        simpa [point_to_infty_map, point_to_infty_finite_partialDiffeomorph,
          point_to_infty_finite_openPartialHomeomorph, partialDiffeomorph_of_openPartialHomeomorph,
          OpenPartialHomeomorph.transHomeomorph_eq_trans, hzero,
          RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart,
          RiemannSphere.inftyOpenPartialHomeomorph, RiemannSphere.inftyChart, RiemannSphere.inftyInv]
      · have htranslate : (sub_const_diffeomorph c) z = z - c := by
          rfl
        have hsub : z - c ≠ 0 := sub_ne_zero.mpr hz
        simpa [point_to_infty_map, point_to_infty_finite_partialDiffeomorph,
          point_to_infty_finite_openPartialHomeomorph, partialDiffeomorph_of_openPartialHomeomorph,
          OpenPartialHomeomorph.transHomeomorph_eq_trans, htranslate, hsub,
          RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart,
          RiemannSphere.inftyOpenPartialHomeomorph, RiemannSphere.inftyChart, RiemannSphere.inftyInv,
          hz]

-- Near `∞`, the source point-mover is given in the preferred charts by the rational map
-- `w ↦ w / (1 - c w)`.
/-- Helper for Theorem 3: the `∞`-branch is the chart-level transport of
`w ↦ w / (1 - c w)` from the `∞`-chart back to the affine chart. -/
noncomputable def point_to_infty_infty_openPartialHomeomorph (c : ℂ) :
    OpenPartialHomeomorph RiemannSphere RiemannSphere :=
  (RiemannSphere.inftyOpenPartialHomeomorph.trans
      (point_to_infty_rational_openPartialHomeomorph c)).trans
    RiemannSphere.affineOpenPartialHomeomorph.symm

/-- Helper for Theorem 3: the `∞`-branch chart transport is `C¹` on its source. -/
lemma point_to_infty_infty_openPartialHomeomorph_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_infty_openPartialHomeomorph c)
      (point_to_infty_infty_openPartialHomeomorph c).source := by
  -- Compose the `∞`-chart, the rational planar branch, and the inverse affine chart.
  have hrational :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        ((point_to_infty_rational_openPartialHomeomorph c) ∘
          RiemannSphere.inftyOpenPartialHomeomorph)
        (RiemannSphere.inftyOpenPartialHomeomorph.source ∩
          RiemannSphere.inftyOpenPartialHomeomorph ⁻¹'
            (point_to_infty_rational_openPartialHomeomorph c).source) :=
    (point_to_infty_rational_openPartialHomeomorph_contMDiffOn c).comp'
      infty_open_partial_homeomorph_contMDiffOn
  have haffine :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        (RiemannSphere.affineOpenPartialHomeomorph.symm ∘
          ((point_to_infty_rational_openPartialHomeomorph c) ∘
            RiemannSphere.inftyOpenPartialHomeomorph))
        ((RiemannSphere.inftyOpenPartialHomeomorph.source ∩
            RiemannSphere.inftyOpenPartialHomeomorph ⁻¹'
              (point_to_infty_rational_openPartialHomeomorph c).source) ∩
          ((point_to_infty_rational_openPartialHomeomorph c) ∘
            RiemannSphere.inftyOpenPartialHomeomorph) ⁻¹'
            RiemannSphere.affineOpenPartialHomeomorph.symm.source) :=
    affine_open_partial_homeomorph_symm_contMDiffOn.comp' hrational
  simpa [point_to_infty_infty_openPartialHomeomorph, OpenPartialHomeomorph.trans_assoc,
    OpenPartialHomeomorph.trans_source, Function.comp_def, Set.preimage_inter, Set.inter_assoc,
    Set.inter_left_comm, Set.inter_comm] using haffine

/-- Helper for Theorem 3: the inverse `∞`-branch chart transport is `C¹` on its source. -/
lemma point_to_infty_infty_openPartialHomeomorph_symm_contMDiffOn (c : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_infty_openPartialHomeomorph c).symm
      (point_to_infty_infty_openPartialHomeomorph c).target := by
  -- Reverse the transport using the affine chart and the inverse rational branch.
  have hrational :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        ((point_to_infty_rational_openPartialHomeomorph c).symm ∘
          RiemannSphere.affineOpenPartialHomeomorph)
        (RiemannSphere.affineOpenPartialHomeomorph.source ∩
          RiemannSphere.affineOpenPartialHomeomorph ⁻¹'
            (point_to_infty_rational_openPartialHomeomorph c).symm.source) :=
    (point_to_infty_rational_openPartialHomeomorph_symm_contMDiffOn c).comp'
      affine_open_partial_homeomorph_contMDiffOn
  have hinfty :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1
        (RiemannSphere.inftyOpenPartialHomeomorph.symm ∘
          ((point_to_infty_rational_openPartialHomeomorph c).symm ∘
            RiemannSphere.affineOpenPartialHomeomorph))
        ((RiemannSphere.affineOpenPartialHomeomorph.source ∩
            RiemannSphere.affineOpenPartialHomeomorph ⁻¹'
              (point_to_infty_rational_openPartialHomeomorph c).symm.source) ∩
          ((point_to_infty_rational_openPartialHomeomorph c).symm ∘
            RiemannSphere.affineOpenPartialHomeomorph) ⁻¹'
            RiemannSphere.inftyOpenPartialHomeomorph.symm.source) :=
    infty_open_partial_homeomorph_symm_contMDiffOn.comp' hrational
  simpa [point_to_infty_infty_openPartialHomeomorph, OpenPartialHomeomorph.trans_assoc,
    OpenPartialHomeomorph.trans_target, Function.comp_def, Set.preimage_inter, Set.inter_assoc,
    Set.inter_left_comm, Set.inter_comm] using hinfty

/-- Helper for Theorem 3: away from `0` and `c`, the `∞`-chart branch simplifies to the same
Möbius formula as the source point-mover. -/
lemma point_to_infty_infty_chart_formula (c z : ℂ) (hz0 : z ≠ 0) (hzc : z ≠ c) :
    z⁻¹ / (1 - c * z⁻¹) = (z - c)⁻¹ := by
  -- Clear the two nonzero denominators once and reduce the identity to polynomial algebra.
  have hsub : z - c ≠ 0 := sub_ne_zero.mpr hzc
  field_simp [hz0, hsub]

noncomputable def point_to_infty_infty_partialDiffeomorph (c : ℂ) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere RiemannSphere 1 :=
  partialDiffeomorph_of_openPartialHomeomorph
    (point_to_infty_infty_openPartialHomeomorph c)
    (point_to_infty_infty_openPartialHomeomorph_contMDiffOn c)
    (point_to_infty_infty_openPartialHomeomorph_symm_contMDiffOn c)

/-- Helper for Theorem 3: the `∞`-branch partial diffeomorphism agrees with the explicit source
point-mover on its source neighborhood. -/
lemma point_to_infty_infty_partialDiffeomorph_eqOn (c : ℂ) :
    Set.EqOn (point_to_infty_map c) (point_to_infty_infty_partialDiffeomorph c)
      (point_to_infty_infty_partialDiffeomorph c).source := by
  intro x hx
  cases x using OnePoint.rec with
  | infty =>
      -- At `∞`, the transported rational branch lands at the finite point `0`.
      simp [point_to_infty_map, point_to_infty_infty_partialDiffeomorph,
        point_to_infty_infty_openPartialHomeomorph, partialDiffeomorph_of_openPartialHomeomorph,
        OpenPartialHomeomorph.trans_apply, point_to_infty_rational_openPartialHomeomorph,
        RiemannSphere.inftyOpenPartialHomeomorph, RiemannSphere.inftyChart,
        RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart]
  | coe z =>
      -- On the source neighborhood, the chart transport is the rational formula
      -- `z⁻¹ / (1 - c z⁻¹)`, which simplifies to `(z - c)⁻¹`.
      have hzsource := hx
      simp [point_to_infty_infty_partialDiffeomorph, point_to_infty_infty_openPartialHomeomorph,
        partialDiffeomorph_of_openPartialHomeomorph, OpenPartialHomeomorph.trans_source,
        point_to_infty_rational_openPartialHomeomorph, point_to_infty_rational_source,
        RiemannSphere.inftyOpenPartialHomeomorph, RiemannSphere.inftyChart,
        RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart] at hzsource
      rcases hzsource with ⟨hz0, hden⟩
      have hzc : z ≠ c := by
        intro hzc
        subst hzc
        simpa [hz0] using hden
      simp [point_to_infty_map, point_to_infty_infty_partialDiffeomorph,
        point_to_infty_infty_openPartialHomeomorph, partialDiffeomorph_of_openPartialHomeomorph,
        point_to_infty_rational_openPartialHomeomorph,
        RiemannSphere.inftyOpenPartialHomeomorph, RiemannSphere.inftyChart,
        RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart, hzc]
      rw [point_to_infty_infty_chart_formula c z hz0 hzc]

/-- Helper for Theorem 3: the explicit point-mover is a local diffeomorphism at every sphere
point, using the finite branch away from `∞` and the rational branch near `∞`. -/
lemma point_to_infty_map_isLocalDiffeomorphAt (c : ℂ) (x : RiemannSphere) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_map c) x := by
  cases x using OnePoint.rec with
  | infty =>
      -- Near `∞`, use the branch transported through the `∞`-chart.
      refine ⟨point_to_infty_infty_partialDiffeomorph c, ?_, point_to_infty_infty_partialDiffeomorph_eqOn c⟩
      simp [point_to_infty_infty_partialDiffeomorph, point_to_infty_infty_openPartialHomeomorph,
        partialDiffeomorph_of_openPartialHomeomorph, OpenPartialHomeomorph.trans_source,
        point_to_infty_rational_openPartialHomeomorph, point_to_infty_rational_source,
        RiemannSphere.inftyOpenPartialHomeomorph, RiemannSphere.inftyChart,
        RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart]
  | coe z =>
      -- Every finite point lies in the source of the affine-translation-`∞` branch.
      refine ⟨point_to_infty_finite_partialDiffeomorph c, ?_, point_to_infty_finite_partialDiffeomorph_eqOn c⟩
      simp [point_to_infty_finite_partialDiffeomorph, point_to_infty_finite_openPartialHomeomorph,
        partialDiffeomorph_of_openPartialHomeomorph, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.transHomeomorph_eq_trans, sub_const_diffeomorph,
        RiemannSphere.affineOpenPartialHomeomorph, RiemannSphere.affineChart,
        RiemannSphere.inftyOpenPartialHomeomorph, RiemannSphere.inftyChart]

/-- Helper for Theorem 3: the explicit point-mover is a local diffeomorphism everywhere on the
sphere. -/
lemma point_to_infty_map_isLocalDiffeomorph (c : ℂ) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 (point_to_infty_map c) := by
  intro x
  exact point_to_infty_map_isLocalDiffeomorphAt c x

/-- Helper for Theorem 3: the explicit point-mover upgrades to a biholomorphic sphere
automorphism by combining its local diffeomorphism structure with the already-proved bijectivity.
-/
noncomputable def point_to_infty_automorphism (c : ℂ) :
    RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere :=
  IsLocalDiffeomorph.diffeomorphOfBijective
    (point_to_infty_map_isLocalDiffeomorph c)
    (point_to_infty_map_bijective c)

/-- Helper for Theorem 3: every sphere point can be moved to `∞` by a biholomorphic automorphism
that is already represented by a `GL₂(ℂ)` homography on `OnePoint ℂ`. -/
lemma point_to_infty_is_homographic_automorphism (p : RiemannSphere) :
    ∃ η : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere,
      ∃ g : GL (Fin 2) ℂ,
        η p = OnePoint.infty ∧
          ∀ z : RiemannSphere, equivOnePoint (η z) = g • equivOnePoint z := by
  cases p using OnePoint.rec with
  | infty =>
      -- The point at infinity is already fixed by the identity automorphism and the identity
      -- matrix action.
      refine ⟨Diffeomorph.refl (I := 𝓘(ℂ)) (M := RiemannSphere) (n := 1), 1, ?_, ?_⟩
      · simp
      · intro z
        simp [equivOnePoint]
  | coe c =>
      -- For a finite point `c`, use the explicit source point-mover and its matrix witness.
      obtain ⟨g, hcenter, hg⟩ := point_to_infty_map_eq_matrix_action c
      refine ⟨point_to_infty_automorphism c, g, ?_, ?_⟩
      · simpa [point_to_infty_automorphism] using hcenter
      · intro z
        simpa [point_to_infty_automorphism] using hg z

/-- Helper for Theorem 3: every point of the sphere can be moved to `∞` by an explicit
homographic matrix action on `OnePoint ℂ`. -/
lemma point_to_infty_has_matrix_witness (p : RiemannSphere) :
    ∃ g : GL (Fin 2) ℂ, g • equivOnePoint p = OnePoint.infty := by
  -- The point at infinity is already fixed by the identity matrix, while a finite point `c` is
  -- moved by the translation-plus-inversion matrix from the source proof.
  cases p using OnePoint.rec with
  | infty =>
      refine ⟨1, ?_⟩
      simp [equivOnePoint]
  | coe c =>
      let g : GL (Fin 2) ℂ :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero
          (!![(0 : ℂ), 1; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ)
          (point_to_infty_matrix_det_ne_zero c)
      refine ⟨g, ?_⟩
      simpa [equivOnePoint, g] using point_to_infty_matrix_smul_center c

/-- Helper for Theorem 3: once the left composition `η ∘ σ` is homographic, the homography for
`σ` is recovered by cancelling the known homography for `η`. -/
lemma homography_witness_of_left_composition
    (σ η : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere)
    (gη gτ : GL (Fin 2) ℂ)
    (hη : ∀ z : RiemannSphere, equivOnePoint (η z) = gη • equivOnePoint z)
    (hτ : ∀ z : RiemannSphere, equivOnePoint ((σ.trans η) z) = gτ • equivOnePoint z) :
    ∀ z : RiemannSphere, equivOnePoint (σ z) = (gη⁻¹ * gτ) • equivOnePoint z := by
  intro z
  have hησ : equivOnePoint (η (σ z)) = gη • equivOnePoint (σ z) := hη (σ z)
  have hτz : equivOnePoint (η (σ z)) = gτ • equivOnePoint z := by
    simpa [Diffeomorph.coe_trans, Function.comp_def] using hτ z
  -- Apply `gη⁻¹` to the composed equality and simplify the resulting group action.
  calc
    equivOnePoint (σ z) = gη⁻¹ • (gη • equivOnePoint (σ z)) := by
      simp
    _ = gη⁻¹ • equivOnePoint (η (σ z)) := by
      rw [← hησ]
    _ = gη⁻¹ • (gτ • equivOnePoint z) := by
      rw [hτz]
    _ = (gη⁻¹ * gτ) • equivOnePoint z := by
      rw [mul_smul]

/-- Theorem 3: every biholomorphic automorphism of the standard Riemann sphere is induced by a
homography. The source-facing automorphism lives on the canonical owner `RiemannSphere`, and the
homography acts on the bridge carrier `OnePoint ℂ` via the canonical `GL (Fin 2) ℂ` action. -/
theorem riemann_sphere_automorphism_is_homography
    (σ : RiemannSphere ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere) :
    ∃ g : GL (Fin 2) ℂ, ∀ z : RiemannSphere, equivOnePoint (σ z) = g • equivOnePoint z := by
  by_cases hfix : σ OnePoint.infty = OnePoint.infty
  · -- This is the affine stabilizer case from the source proof.
    exact sphere_automorphism_fixing_infty_is_affine_homography σ hfix
  · -- Route correction: the stabilizer-at-`∞` branch is now complete. The remaining source-faithful
    -- step is to compose `σ` with an explicit Möbius sphere automorphism sending `σ ∞` to `∞`,
    -- and then transport the already-proved stabilizer case back to `σ`.
    obtain ⟨η, gη, hηfix, hη⟩ := point_to_infty_is_homographic_automorphism (σ OnePoint.infty)
    have hfix_trans : (σ.trans η) OnePoint.infty = OnePoint.infty := by
      simpa [Diffeomorph.coe_trans, Function.comp_def] using hηfix
    obtain ⟨gτ, hτ⟩ := sphere_automorphism_fixing_infty_is_affine_homography (σ.trans η) hfix_trans
    refine ⟨gη⁻¹ * gτ, homography_witness_of_left_composition σ η gη gτ hη hτ⟩

end RiemannSphere
