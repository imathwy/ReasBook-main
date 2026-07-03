import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type v} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Definition II.1-extra-4: a function `f` is a primitive of a differential form `ω` on `D`
when the differential of `f` equals `ω` at every point of `D`. -/
def IsPrimitiveOn (D : Set E) (ω : E → E →L[𝕜] G) (f : E → G) : Prop :=
  ∀ p ∈ D, HasFDerivAt f (ω p) p

/-- A differential form has a primitive on `D` when some potential has it as Fréchet derivative at
every point of `D`. -/
def HasPrimitiveOn (D : Set E) (ω : E → E →L[𝕜] G) : Prop :=
  ∃ f : E → G, IsPrimitiveOn D ω f

/-- Restricting a chosen primitive to a smaller domain preserves primitivity. -/
theorem IsPrimitiveOn.mono
    {D U : Set E} {ω : E → E →L[𝕜] G} {f : E → G} (hf : IsPrimitiveOn D ω f) (hU : U ⊆ D) :
    IsPrimitiveOn U ω f := fun p hp ↦ hf p (hU hp)

/-- Composing a primitive with a continuous linear map yields a primitive of the composed
differential form. -/
theorem IsPrimitiveOn.comp
    {D : Set E} {ω : E → E →L[𝕜] G} {f : E → G} (hf : IsPrimitiveOn D ω f)
    (L : G →L[𝕜] H) :
    IsPrimitiveOn D (fun z ↦ L.comp (ω z)) (L ∘ f) := by
  intro z hz
  simpa [Function.comp] using (L.hasFDerivAt.comp z (hf z hz))

/-- Restricting the domain preserves the existence of a primitive. -/
theorem HasPrimitiveOn.mono
    {D U : Set E} {ω : E → E →L[𝕜] G} (hω : HasPrimitiveOn D ω) (hU : U ⊆ D) :
    HasPrimitiveOn U ω := by
  rcases hω with ⟨f, hf⟩
  exact ⟨f, hf.mono hU⟩

/-- Composing a primitive witness with a continuous linear map preserves existence of a
primitive. -/
theorem HasPrimitiveOn.comp
    {D : Set E} {ω : E → E →L[𝕜] G} (hω : HasPrimitiveOn D ω) (L : G →L[𝕜] H) :
    HasPrimitiveOn D (fun z ↦ L.comp (ω z)) := by
  rcases hω with ⟨f, hf⟩
  exact ⟨L ∘ f, hf.comp L⟩

/-- For the complex differential form `f(z) dz`, a complex primitive is a primitive for the
associated real-linear `1`-form. -/
theorem Complex.IsExactOn.hasPrimitiveOn {D : Set ℂ} {f : ℂ → ℂ}
    (hf : Complex.IsExactOn f D) :
    HasPrimitiveOn D (Complex.realScalarOneForm f) := by
  rcases hf with ⟨g, hg⟩
  exact ⟨g, fun z hz ↦ by
    simpa using (hg z hz).complexToReal_fderiv⟩

/-- A primitive of the real-linear form `f(z) dz` is exactly a complex primitive of `f`. -/
theorem HasPrimitiveOn.isExactOn {D : Set ℂ} {f : ℂ → ℂ}
    (hf : HasPrimitiveOn D (Complex.realScalarOneForm f)) :
    Complex.IsExactOn f D := by
  rcases hf with ⟨g, hg⟩
  refine ⟨g, fun z hz ↦ ?_⟩
  have hg' : HasFDerivAt g (Complex.realScalarOneForm f z) z := hg z hz
  have hCR : fderiv ℝ g z Complex.I = Complex.I • fderiv ℝ g z 1 := by
    rw [hg'.fderiv, Complex.realScalarOneForm_eq_smul]
    simp [smul_eq_mul, mul_comm]
  simpa [hg'.fderiv] using complexOfReal_hasDerivAt hg'.differentiableAt hCR

-- Proof sketch: `f - g` has zero Fréchet derivative on `D`, hence the canonical open-set
-- derivative-equality theorem makes `f - g` constant on each preconnected component of `D`.
/-- Two primitives of the same differential form on a preconnected open set differ by an additive
constant. -/
theorem IsPrimitiveOn.sub_eqOn_const_of_isOpen_isPreconnected {D : Set E} (hD_open : IsOpen D)
    [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] [NormedSpace ℝ G]
    (hD_preconnected : IsPreconnected D) {ω : E → E →L[𝕜] G} {f g : E → G}
    (hf : IsPrimitiveOn D ω f) (hg : IsPrimitiveOn D ω g) :
    ∃ c : G, D.EqOn (fun p ↦ f p - g p) (fun _ ↦ c) := by
  have hf_diff : DifferentiableOn 𝕜 f D :=
    fun p hp ↦ (hf p hp).differentiableAt.differentiableWithinAt
  have hg_diff : DifferentiableOn 𝕜 g D :=
    fun p hp ↦ (hg p hp).differentiableAt.differentiableWithinAt
  obtain ⟨c, hfg⟩ :=
    hD_open.exists_eq_add_of_fderiv_eq hD_preconnected hf_diff hg_diff fun p hp ↦ by
      rw [(hf p hp).fderiv, (hg p hp).fderiv]
  exact ⟨c, fun p hp ↦ by
    rw [sub_eq_iff_eq_add']
    exact hfg hp⟩

end

section

variable {𝕜 : Type v} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]

-- Proof sketch: identify the derivative of `f` with the linear map `planarDifferentialForm P Q p`,
-- then compose with the canonical coordinate inclusions to recover the two coordinate derivatives.
/-- A primitive of `P dx + Q dy` has `x`- and `y`-partial derivatives `P` and `Q`. -/
theorem IsPrimitiveOn.hasDerivAt_coord_of_planarDifferentialForm
    {D : Set Plane} {P Q f : Plane → 𝕜} (hf : IsPrimitiveOn D (P dx+Q dy) f) :
    ∀ p ∈ D,
      HasDerivAt (fun x : ℝ ↦ f (x, p.2)) (P p) p.1 ∧
      HasDerivAt (fun y : ℝ ↦ f (p.1, y)) (Q p) p.2 := by
  intro p hp
  constructor
  · have hleft : HasFDerivAt (fun x : ℝ ↦ (x, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
      hasFDerivAt_prodMk_left p.1 p.2
    have hleft_fderiv :
        ((P dx+Q dy) p).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (P p) := by
      ext
      simp [planarDifferentialForm_apply]
    change HasFDerivAt (fun x : ℝ ↦ f (x, p.2)) ((1 : ℝ →L[ℝ] ℝ).smulRight (P p)) p.1
    simpa [hleft_fderiv] using (hf p hp).comp p.1 hleft
  · have hright : HasFDerivAt (fun y : ℝ ↦ (p.1, y)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hright_fderiv :
        ((P dx+Q dy) p).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (Q p) := by
      ext
      simp [planarDifferentialForm_apply]
    change HasFDerivAt (fun y : ℝ ↦ f (p.1, y)) ((1 : ℝ →L[ℝ] ℝ).smulRight (Q p)) p.2
    simpa [hright_fderiv] using (hf p hp).comp p.2 hright

end
