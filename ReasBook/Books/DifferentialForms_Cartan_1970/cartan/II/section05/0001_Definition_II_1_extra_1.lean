import Mathlib

noncomputable section

open scoped unitInterval

universe u

/-- The real affine plane used for curvilinear integrals in this section. -/
abbrev Plane := ℝ × ℝ

namespace Path

section Differentiability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}

/-- Definition II.1-extra-1: a path is differentiable when its extension to `ℝ` is `C^1` on
the unit interval. -/
def IsDifferentiable (γ : Path a b) : Prop :=
  ContDiffOn ℝ 1 γ.extend I

/-- A path is differentiable exactly when its extension to `ℝ` is `C^1` on `[0,1]`. -/
theorem isDifferentiable_iff (γ : Path a b) :
    γ.IsDifferentiable ↔ ContDiffOn ℝ 1 γ.extend I :=
  Iff.rfl

/-- A differentiable path has a `C^1` extension on `[0,1]`. -/
theorem IsDifferentiable.contDiffOn {γ : Path a b} (hγ : γ.IsDifferentiable) :
    ContDiffOn ℝ 1 γ.extend I :=
  hγ

/-- A path is piecewise differentiable when `[0,1]` admits a finite subdivision on whose
successive closed subintervals the extension of the path is `C^1`. -/
def IsPiecewiseDifferentiable (γ : Path a b) : Prop :=
  ∃ n : ℕ, ∃ subdiv : Fin (n + 2) → ℝ,
    StrictMono subdiv ∧
    subdiv 0 = 0 ∧
    subdiv (Fin.last (n + 1)) = 1 ∧
    ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ))

/-- A piecewise differentiable path is exactly one with a finite `C^1` subdivision of `[0,1]`. -/
theorem isPiecewiseDifferentiable_iff (γ : Path a b) :
    γ.IsPiecewiseDifferentiable ↔
      ∃ n : ℕ, ∃ subdiv : Fin (n + 2) → ℝ,
        StrictMono subdiv ∧
        subdiv 0 = 0 ∧
        subdiv (Fin.last (n + 1)) = 1 ∧
        ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) :=
  Iff.rfl

/-- Helper for Definition II.1-extra-1: the trivial subdivision `0 < 1` realizes `[0,1]` as a
single closed piece. -/
private lemma unit_interval_single_piece_subdivision :
    ∃ subdiv : Fin 2 → ℝ,
      StrictMono subdiv ∧
      subdiv 0 = 0 ∧
      subdiv (Fin.last 1) = 1 ∧
      ∀ i : Fin 1, Set.Icc (subdiv i.castSucc) (subdiv i.succ) = I := by
  refine ⟨fun i ↦ (i : ℝ), ?_⟩
  refine ⟨?_, by simp, by norm_num, ?_⟩
  · intro i j hij
    have hij_nat : (i : ℕ) < (j : ℕ) := hij
    have hcast : (((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)) := by
      exact_mod_cast hij_nat
    simpa using hcast
  · intro i
    -- `Fin 1` has a unique point, so the only subinterval is `[0,1]`.
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    ext t
    simp [unitInterval]

/-- A globally `C^1` path is piecewise differentiable. -/
theorem IsDifferentiable.isPiecewiseDifferentiable {γ : Path a b} (hγ : γ.IsDifferentiable) :
    γ.IsPiecewiseDifferentiable := by
  -- The source proof uses the one-piece subdivision of the parameter interval.
  rcases unit_interval_single_piece_subdivision with ⟨subdiv, hsubdiv, h0, h1, hI⟩
  refine ⟨0, subdiv, hsubdiv, h0, h1, ?_⟩
  intro i
  -- The unique piece is the whole unit interval, so the global `C^1` hypothesis applies directly.
  rw [hI i]
  exact hγ.contDiffOn

/-- Helper for Definition II.1-extra-1: the constant path has a globally `C^1` extension. -/
private lemma isDifferentiable_refl (a : E) : (Path.refl a).IsDifferentiable := by
  -- The extension of the constant path is the constant map on `ℝ`.
  rw [IsDifferentiable, Path.refl_extend]
  simpa using (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ a) I)

/-- Constant paths are piecewise differentiable. -/
lemma isPiecewiseDifferentiable_refl (a : E) : (Path.refl a).IsPiecewiseDifferentiable := by
  -- Reuse the global-to-piecewise theorem after identifying the path as globally `C^1`.
  exact (isDifferentiable_refl a).isPiecewiseDifferentiable

end Differentiability

end Path

/-- The canonical `ℝ`-linear `1`-form on `ℝ²` corresponding to the textbook expression
`P dx + Q dy`. -/
noncomputable def planarDifferentialForm {𝕜 : Type u} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    (P Q : Plane → 𝕜) : Plane → Plane →L[ℝ] 𝕜 :=
  fun p ↦
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (P p) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Q p)

notation:65 P " dx" "+" Q " dy" => planarDifferentialForm P Q

@[simp]
theorem planarDifferentialForm_apply {𝕜 : Type u} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    (P Q : Plane → 𝕜) (p v : Plane) :
    (P dx + Q dy) p v = v.1 • P p + v.2 • Q p := by
  simp [planarDifferentialForm]

namespace Complex

/-- The complex-plane view of the canonical planar `1`-form `P dx + Q dy`. -/
noncomputable abbrev planarDifferentialForm {𝕜 : Type u} [NormedAddCommGroup 𝕜]
    [NormedSpace ℝ 𝕜] (P Q : ℂ → 𝕜) : ℂ → ℂ →L[ℝ] 𝕜 :=
  fun z ↦ Complex.reCLM.smulRight (P z) + Complex.imCLM.smulRight (Q z)

/-- Continuous coefficients give a continuous planar differential form `P dx + Q dy` on `ℂ`. -/
theorem planarDifferentialForm_continuousOn {𝕜 : Type u} [NormedAddCommGroup 𝕜]
    [NormedSpace ℝ 𝕜] {D : Set ℂ} {P Q : ℂ → 𝕜}
    (hP : ContinuousOn P D) (hQ : ContinuousOn Q D) :
    ContinuousOn (planarDifferentialForm P Q) D := by
  -- Each summand is obtained by composing the coefficient with the continuous bilinear
  -- `smulRight` operator, so continuity follows termwise and then by addition.
  have hP' : ContinuousOn (fun z ↦ Complex.reCLM.smulRight (P z)) D := by
    simpa using
      (ContinuousLinearMap.smulRightL ℝ ℂ 𝕜).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ Complex.reCLM) D).prodMk hP)
  have hQ' : ContinuousOn (fun z ↦ Complex.imCLM.smulRight (Q z)) D := by
    simpa using
      (ContinuousLinearMap.smulRightL ℝ ℂ 𝕜).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ Complex.imCLM) D).prodMk hQ)
  -- The planar form is the sum of these two continuous summands.
  simpa [Complex.planarDifferentialForm] using hP'.add hQ'

/-- The complex-linear `1`-form corresponding to the scalar field `f(z) dz`. Its source-facing
surface is the notation `f dz`. -/
abbrev scalarOneForm (f : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z ↦ (1 : ℂ →L[ℂ] ℂ).smulRight (f z)

notation:65 f " dz" => scalarOneForm f

notation:65 P " dx" "+" Q " dy" => planarDifferentialForm P Q

@[simp]
theorem planarDifferentialForm_apply {𝕜 : Type u} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    (P Q : ℂ → 𝕜) (z v : ℂ) :
    (P dx + Q dy) z v = v.re • P z + v.im • Q z := by
  simp [Complex.planarDifferentialForm]

@[simp]
theorem scalarOneForm_apply (f : ℂ → ℂ) (z v : ℂ) :
    (f dz) z v = v * f z := by
  simp [scalarOneForm]

@[simp]
theorem scalarOneForm_restrictScalars (f : ℂ → ℂ) (z : ℂ) :
    ((f dz) z).restrictScalars ℝ = f z • (1 : ℂ →L[ℝ] ℂ) := by
  ext v
  simp [scalarOneForm, mul_comm]

/-- The real-linear `1`-form underlying the complex scalar form `f(z) dz`. -/
abbrev realScalarOneForm (f : ℂ → ℂ) : ℂ → ℂ →L[ℝ] ℂ :=
  fun z ↦ ((f dz) z).restrictScalars ℝ

@[simp]
theorem realScalarOneForm_eq_smul (f : ℂ → ℂ) (z : ℂ) :
    realScalarOneForm f z = f z • (1 : ℂ →L[ℝ] ℂ) := by
  simpa [realScalarOneForm] using scalarOneForm_restrictScalars f z

end Complex

/- Curvilinear integration in this section is the canonical mathlib `curveIntegral` on paths and
`1`-forms. -/
#check curveIntegral

/- Path reversal is the canonical `Path.symm`, and the corresponding sign change of the integral
is the canonical theorem `curveIntegral_symm`. -/
#check Path.symm
#check curveIntegral_symm

/- Reparametrization of paths is the canonical owner `Path.reparam`. -/
#check Path.reparam

end
