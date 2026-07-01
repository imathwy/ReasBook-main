import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped unitInterval

namespace Complex

namespace IsExactOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem add {U : Set ℂ} {ω₁ ω₂ : ℂ → E} (hω₁ : IsExactOn ω₁ U) (hω₂ : IsExactOn ω₂ U) :
    IsExactOn (ω₁ + ω₂) U := by
  rcases hω₁ with ⟨F₁, hF₁⟩
  rcases hω₂ with ⟨F₂, hF₂⟩
  refine ⟨F₁ + F₂, ?_⟩
  intro z hz
  simpa using (hF₁ z hz).add (hF₂ z hz)

theorem smul {U : Set ℂ} (a : ℂ) {ω : ℂ → E} (hω : IsExactOn ω U) :
    IsExactOn (a • ω) U := by
  rcases hω with ⟨F, hF⟩
  refine ⟨a • F, ?_⟩
  intro z hz
  simpa using (hF z hz).const_smul a

-- Proof sketch: the difference `F - G` has zero derivative on `U`, hence is locally constant on
-- the open set `U`; preconnectedness makes it constant on `U`, and the common value at `y` is `0`.
/-- Two primitives on an open preconnected set with the same normalization at `y` agree on `U`. -/
theorem eqOn_of_isOpen_isPreconnected
    {U : Set ℂ} (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U)
    {f F G : ℂ → E} (hFy : F y = 0) (hGy : G y = 0)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) (hG : ∀ z ∈ U, HasDerivAt G (f z) z) :
    Set.EqOn F G U := by
  have hF_diff : DifferentiableOn ℂ F U := fun z hz ↦
    (hF z hz).differentiableAt.differentiableWithinAt
  have hG_diff : DifferentiableOn ℂ G U := fun z hz ↦
    (hG z hz).differentiableAt.differentiableWithinAt
  -- On an open preconnected set, two functions with the same derivative differ by a constant.
  obtain ⟨c, hc⟩ :=
    hU_open.exists_eq_add_of_fderiv_eq hU_preconnected hF_diff hG_diff fun z hz ↦ by
      rw [(hF z hz).hasFDerivAt.fderiv, (hG z hz).hasFDerivAt.fderiv]
  have hc_zero : c = 0 := by
    simpa [hFy, hGy] using (hc hy).symm
  intro z hz
  simpa [hc_zero] using hc hz

-- Proof sketch: choose any primitive of `f` normalized by `F(y) = 0`, then force a canonical
-- ambient representative by declaring it to be `0` outside `U`; uniqueness follows from
-- `eqOn_of_isOpen_isPreconnected`.
/-- Re-centering the canonical exactness owner at `y` produces Cartan's normalized primitive
`f_y`, realized as the unique normalized primitive on `U` extended by `0` off `U`. -/
theorem existsUnique_primitiveAt
    {U : Set ℂ} {f : ℂ → E} (hf : IsExactOn f U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U) :
    ∃! F : ℂ → E, (∀ z ∉ U, F z = 0) ∧ F y = 0 ∧ ∀ z ∈ U, HasDerivAt F (f z) z := by
  classical
  obtain ⟨F₀, hF₀y, hF₀⟩ := hf.with_val_at y 0
  let F : ℂ → E := fun z ↦ if z ∈ U then F₀ z else 0
  refine ⟨F, ?_, ?_⟩
  · constructor
    · intro z hz
      simp [F, hz]
    constructor
    · -- The ambient extension preserves the normalization at `y`.
      simpa [F, hy] using hF₀y
    · intro z hz
      -- Near points of `U`, the extension agrees with the genuine primitive `F₀`.
      have hF_eq : F =ᶠ[nhds z] F₀ := by
        filter_upwards [hU_open.mem_nhds hz] with w hw
        simp [F, hw]
      exact (hF₀ z hz).congr_of_eventuallyEq hF_eq
  · intro G hG
    rcases hG with ⟨hG_zero, hGy, hG_deriv⟩
    have hFy : F y = 0 := by
      simpa [F, hy] using hF₀y
    funext z
    by_cases hz : z ∈ U
    · -- On `U`, uniqueness follows from the normalized-primitive comparison lemma.
      exact
        (eqOn_of_isOpen_isPreconnected hU_open hU_preconnected hy
          hFy hGy
          (by
            intro w hw
            have hF_eq : F =ᶠ[nhds w] F₀ := by
              filter_upwards [hU_open.mem_nhds hw] with u hu
              simp [F, hu]
            exact (hF₀ w hw).congr_of_eventuallyEq hF_eq)
          hG_deriv) hz |>.symm
    · -- Off `U`, both ambient representatives are forced to vanish.
      rw [hG_zero z hz]
      simp [F, hz]

/-- Cartan's normalized primitive `f_y` on an open preconnected domain, with the canonical ambient
realization equal to `0` off `U`. -/
def primitiveAt {U : Set ℂ} {f : ℂ → E} (hf : IsExactOn f U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U) : ℂ → E :=
  Classical.choose <| ExistsUnique.exists <| hf.existsUnique_primitiveAt hU_open hU_preconnected hy

private theorem primitiveAt_spec
    {U : Set ℂ} {f : ℂ → E} (hf : IsExactOn f U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U) :
    (∀ z ∉ U, hf.primitiveAt hU_open hU_preconnected hy z = 0) ∧
      hf.primitiveAt hU_open hU_preconnected hy y = 0 ∧
        ∀ z ∈ U, HasDerivAt (hf.primitiveAt hU_open hU_preconnected hy) (f z) z :=
  Classical.choose_spec <|
    ExistsUnique.exists <| hf.existsUnique_primitiveAt hU_open hU_preconnected hy

/-- A normalized primitive on `U` extended by `0` off `U` is necessarily Cartan's `f_y`. -/
theorem eq_primitiveAt
    {U : Set ℂ} {f F : ℂ → E} (hf : IsExactOn f U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U)
    (hF_zero : ∀ z ∉ U, F z = 0) (hFy : F y = 0)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) :
    F = hf.primitiveAt hU_open hU_preconnected hy := by
  -- Compare the candidate against the canonical witness chosen from the unique existence theorem.
  exact
    ExistsUnique.unique (hf.existsUnique_primitiveAt hU_open hU_preconnected hy)
      ⟨hF_zero, hFy, hF⟩
      (hf.primitiveAt_spec hU_open hU_preconnected hy)

@[simp] theorem primitiveAt_eq_zero_of_not_mem
    {U : Set ℂ} {f : ℂ → E} (hf : IsExactOn f U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U) {z : ℂ} (hz : z ∉ U) :
    hf.primitiveAt hU_open hU_preconnected hy z = 0 := by
  rcases hf.primitiveAt_spec hU_open hU_preconnected hy with ⟨hF, _, _⟩
  exact hF z hz

@[simp] theorem primitiveAt_basepoint
    {U : Set ℂ} {f : ℂ → E} (hf : IsExactOn f U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U) :
    hf.primitiveAt hU_open hU_preconnected hy y = 0 := by
  rcases hf.primitiveAt_spec hU_open hU_preconnected hy with ⟨_, hFy, _⟩
  exact hFy

theorem hasDerivAt_primitiveAt
    {U : Set ℂ} {f : ℂ → E} (hf : IsExactOn f U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (hf.primitiveAt hU_open hU_preconnected hy) (f z) z := by
  rcases hf.primitiveAt_spec hU_open hU_preconnected hy with ⟨_, _, hF⟩
  exact hF z hz

end IsExactOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- Proof sketch: apply the uniqueness of Cartan's normalized primitive to the canonical primitive
-- of `ω₁ + ω₂` and to the sum of the canonical primitives of `ω₁` and `ω₂`.
/-- Exercise 2 (1): Cartan's normalized primitive `f_y` is additive in the closed form. -/
theorem primitiveAt_add
    {U : Set ℂ} (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U)
    {ω₁ ω₂ : ℂ → E} (hω₁ : IsExactOn ω₁ U) (hω₂ : IsExactOn ω₂ U) :
    (hω₁.add hω₂).primitiveAt hU_open hU_preconnected hy =
      hω₁.primitiveAt hU_open hU_preconnected hy +
        hω₂.primitiveAt hU_open hU_preconnected hy := by
  -- The sum of the normalized primitives satisfies the same defining conditions.
  symm
  refine (hω₁.add hω₂).eq_primitiveAt hU_open hU_preconnected hy ?_ ?_ ?_
  · intro z hz
    simp [hz]
  · simp
  · intro z hz
    simpa using
      (hω₁.hasDerivAt_primitiveAt hU_open hU_preconnected hy hz).add
        (hω₂.hasDerivAt_primitiveAt hU_open hU_preconnected hy hz)

-- Proof sketch: scalar multiplication preserves exactness, and the normalized primitive of `aω`
-- is the scalar multiple of the normalized primitive of `ω`.
/-- Scalar multiplication commutes with Cartan's normalized primitive `f_y`. -/
theorem primitiveAt_smul
    {U : Set ℂ} (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U) {y : ℂ} (hy : y ∈ U)
    {a : ℂ} {ω : ℂ → E} (hω : IsExactOn ω U) :
    (hω.smul a).primitiveAt hU_open hU_preconnected hy =
      a • hω.primitiveAt hU_open hU_preconnected hy := by
  -- Scalar multiples are characterized by the same normalization and derivative data.
  symm
  refine (hω.smul a).eq_primitiveAt hU_open hU_preconnected hy ?_ ?_ ?_
  · intro z hz
    simp [hz]
  · simp
  · intro z hz
    simpa using (hω.hasDerivAt_primitiveAt hU_open hU_preconnected hy hz).const_smul a

/- Exercise 2 (2): this is the canonical curve-integral linearity theorem
`curveIntegral_fun_smul`, applied in the exercise to the complex one-form `ω dz`. -/
recall curveIntegral_fun_smul

end Complex
