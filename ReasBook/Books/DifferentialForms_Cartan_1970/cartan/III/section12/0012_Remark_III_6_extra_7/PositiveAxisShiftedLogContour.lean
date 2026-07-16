import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.III.section12.SectorArc
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».ShiftedLogResidueData
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisContourIntegrals
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeDifferentiability
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeRange
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisRealIntegral
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisResidueLocalization

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on a single `C¹` subinterval of a
complex path, the scalar pullback `t ↦ γ'(t) * φ(γ(t))` is interval-integrable. -/
private lemma positiveAxisScalarPullbackIntervalIntegrableOnPiece
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} {l u : ℝ} (hlt : l < u)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc l u)) {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ (γ.extend '' Set.Icc l u)) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume l u := by
  have hDerivWithin :
      ContinuousOn (fun t ↦ derivWithin γ.extend (Set.Icc l u) t) (Set.Icc l u) := by
    exact (hγ.derivWithin (m := 0) (uniqueDiffOn_Icc hlt) (by simp)).continuousOn
  have hCoeff : ContinuousOn (fun t ↦ φ (γ.extend t)) (Set.Icc l u) := by
    refine hφ.comp (by fun_prop) ?_
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIntWithin :
      IntervalIntegrable
        (fun t ↦ derivWithin γ.extend (Set.Icc l u) t * φ (γ.extend t))
        MeasureTheory.volume l u :=
    (hDerivWithin.mul hCoeff).intervalIntegrable_of_Icc hlt.le
  refine hIntWithin.congr_ae ?_
  rw [Set.uIoc_of_le hlt.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  exact by simp [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: interval-integrability on each `C¹`
subdivision piece of a path upgrades to interval-integrability on the whole parameter interval. -/
private lemma positiveAxisScalarPullbackIntervalIntegrableOfSubdivision
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁}
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv) (h0 : subdiv 0 = 0)
    (h1 : subdiv (Fin.last (n + 1)) = 1)
    (hpieces : ∀ i : Fin (n + 1),
      ContDiffOn ℝ 1 γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ)))
    {φ : ℂ → ℂ}
    (hφ : ∀ i : Fin (n + 1),
      ContinuousOn φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ))) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume 0 1 := by
  let a : ℕ → ℝ := fun k ↦
    if hk : k ≤ n + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  have hInt :
      IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume
        (a 0) (a (n + 1)) := by
    refine IntervalIntegrable.trans_iterate ?_
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk0 : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    simpa [a, i, hk0, hk1] using
      positiveAxisScalarPullbackIntervalIntegrableOnPiece (γ := γ) hlt (hpieces i) (hφ i)
  have h0' : a 0 = 0 := by simp [a, h0]
  have h1' : a (n + 1) = 1 := by
    simpa [a] using h1
  simpa [h0', h1'] using hInt

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: a continuous scalar field defines a
curve-integrable scalar `1`-form along any piecewise differentiable complex path whose image stays
in the domain. -/
private lemma positiveAxis_curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
    {D : Set ℂ} {φ : ℂ → ℂ} {z₀ z₁ : ℂ} {γ : Path z₀ z₁}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hφ : ContinuousOn φ D) (hγD : Set.range γ ⊆ D) :
    CurveIntegrable (fun z ↦ (φ dz) z) γ := by
  rcases hγ_piecewise with ⟨n, subdiv, hsubdiv, h0, h1, hpieces⟩
  have hCoeff :
      ∀ i : Fin (n + 1),
        ContinuousOn φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    intro i
    refine hφ.mono ?_
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ I := Path.subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
    simpa [Path.extend_apply γ htI] using hγD ⟨⟨t, htI⟩, rfl⟩
  have hInt :
      IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume 0 1 :=
    positiveAxisScalarPullbackIntervalIntegrableOfSubdivision hsubdiv h0 h1 hpieces hCoeff
  have hIntForm :
      IntervalIntegrable (fun t ↦ (φ dz) (γ.extend t) (deriv γ.extend t)) MeasureTheory.volume
        0 1 := by
    simpa [Complex.scalarOneForm_apply] using hInt
  rw [CurveIntegrable]
  refine hIntForm.congr_ae ?_
  rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  simp [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the source-faithful adjusted branch
`log (-z) + π i` differs from the shifted branch only by the constant multiple `π i` of the
meromorphic normal-form rational factor. This is the pointwise algebraic bridge needed before the
contour-level residue correction is applied. -/
lemma shiftedLogAdjustedBranch_split
    (P Q : Polynomial ℂ) (z : ℂ) :
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
        (Complex.log (-z) + Real.pi * Complex.I) =
      shiftedLogRationalNormalForm P Q z +
        (Real.pi * Complex.I) * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z := by
  let a := toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z
  -- Expand the named shifted branch once, then distribute the rational normal-form factor across
  -- the added constant `π i`.
  change a * (Complex.log (-z) + Real.pi * Complex.I) =
      a * Complex.log (-z) + (Real.pi * Complex.I) * a
  rw [mul_add, mul_comm a (Real.pi * Complex.I)]

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on the shifted slit domain, the same
`π i` coefficient-scaling formula also applies to the meromorphic normal-form factor used in the
contour integral. This removes the remaining local residue ambiguity in the adjusted-branch pivot. -/
lemma meromorphicTrailingCoeffAt_piMul_shiftedNormalForm
    (P Q : Polynomial ℂ) {z : ℂ} (hz : z ∈ shiftedLogDomain) :
    meromorphicTrailingCoeffAt
        (fun w ↦
          (Real.pi * Complex.I : ℂ) *
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain w) z =
      (Real.pi * Complex.I : ℂ) * meromorphicTrailingCoeffAt (rationalEval P Q) z := by
  let c : ℂ := Real.pi * Complex.I
  have hEq :
      (fun w ↦ c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain w) =ᶠ[nhdsWithin z {z}ᶜ]
        (fun w ↦ c * rationalEval P Q w) := by
    have hNF :=
      (rationalEval_meromorphicOn_shiftedLogDomain P Q).toMeromorphicNFOn_eq_self_on_nhdsNE hz
    -- Off the base point, the normal form agrees with the literal rational quotient.
    filter_upwards [hNF] with w hw
    simp [c, hw]
  -- Transfer the trailing coefficient through the punctured-neighborhood equality, then use the
  -- constant-scaling formula for the literal rational kernel.
  calc
    meromorphicTrailingCoeffAt
        (fun w ↦ c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain w) z =
      meromorphicTrailingCoeffAt (fun w ↦ c * rationalEval P Q w) z := by
        exact meromorphicTrailingCoeffAt_congr_nhdsNE hEq
    _ = c * meromorphicTrailingCoeffAt (rationalEval P Q) z := by
        have hconst : MeromorphicAt (fun _ : ℂ ↦ c) z := by
          -- The branch-correction factor is constant, hence meromorphic, at every point.
          fun_prop
        have hrat : MeromorphicAt (rationalEval P Q) z := by
          -- Inside the shifted slit domain, the rational kernel is meromorphic as a quotient of
          -- entire polynomial evaluations.
          exact (rationalEval_meromorphicOn_shiftedLogDomain P Q) z hz
        -- Apply the scalar-multiplication formula for trailing coefficients at the actual pole.
        change meromorphicTrailingCoeffAt (((fun _ : ℂ ↦ c) * rationalEval P Q)) z =
            c * meromorphicTrailingCoeffAt (rationalEval P Q) z
        simpa [c, smul_eq_mul, mul_assoc] using
          hconst.meromorphicTrailingCoeffAt_smul hrat

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on any positive ray whose angle stays
in the principal strip `(-π, π)`, the complex logarithm is the real logarithm of the radius plus
the angle term. This is the exact polar-value bridge used on the repaired slit lips. -/
lemma positiveAxis_log_circleMap_of_pos
    {x β : ℝ} (hx : 0 < x) (hβ : β ∈ Set.Ioo (-Real.pi) Real.pi) :
    Complex.log (circleMap 0 x β) = (Real.log x : ℂ) + β * Complex.I := by
  -- Factor the ray point as a positive real scalar times `exp (β i)`, then evaluate the branch
  -- logarithm on the principal strip.
  rw [circleMap_zero, Complex.log_ofReal_mul hx (Complex.exp_ne_zero _)]
  simpa using
    (Complex.log_exp (x := (β : ℂ) * Complex.I) (by simpa using hβ.1)
      (by simpa using hβ.2.le))

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on the upper lip written with the
complementary angle `α ∈ (0, π)`, the source-faithful adjusted branch `log (-z) + π i` reduces
exactly to `log x + (π - α) i`. -/
lemma positiveAxisAdjustedBranch_upperLip_value
    {x α : ℝ} (hx : 0 < x) (hα : α ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Complex.log (-circleMap 0 x (Real.pi - α)) + Real.pi * Complex.I =
      (Real.log x : ℂ) + (Real.pi - α) * Complex.I := by
  have hneg :
      -circleMap 0 x (Real.pi - α) = circleMap 0 x (-α) := by
    -- Moving to the upper lip and then negating lands on the principal-strip ray of angle `-α`.
    rw [Complex.ext_iff]
    constructor <;> simp [circleMap_zero_re, circleMap_zero_im, Real.cos_pi_sub, Real.sin_pi_sub]
  have hangle : -α ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [hα.1, hα.2]
  calc
    Complex.log (-circleMap 0 x (Real.pi - α)) + Real.pi * Complex.I =
      Complex.log (circleMap 0 x (-α)) + Real.pi * Complex.I := by
        rw [hneg]
    _ = ((Real.log x : ℂ) + (-α) * Complex.I) + Real.pi * Complex.I := by
        simpa using congrArg (fun z : ℂ ↦ z + Real.pi * Complex.I)
          (positiveAxis_log_circleMap_of_pos hx hangle)
    _ = (Real.log x : ℂ) + (Real.pi - α) * Complex.I := by
        ring_nf

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on the lower lip written with the
same complementary angle `α ∈ (0, π)`, the adjusted branch `log (-z) + π i` reduces exactly to
`log x + (π + α) i`. -/
lemma positiveAxisAdjustedBranch_lowerLip_value
    {x α : ℝ} (hx : 0 < x) (hα : α ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Complex.log (-circleMap 0 x (α - Real.pi)) + Real.pi * Complex.I =
      (Real.log x : ℂ) + (Real.pi + α) * Complex.I := by
  have hneg :
      -circleMap 0 x (α - Real.pi) = circleMap 0 x α := by
    -- Negating the reflected lower-lip point lands on the principal-strip ray of angle `α`.
    rw [Complex.ext_iff]
    constructor <;> simp [circleMap_zero_re, circleMap_zero_im, Real.cos_sub_pi, Real.sin_sub_pi]
  have hangle : α ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [hα.1, hα.2]
  calc
    Complex.log (-circleMap 0 x (α - Real.pi)) + Real.pi * Complex.I =
      Complex.log (circleMap 0 x α) + Real.pi * Complex.I := by
        rw [hneg]
    _ = ((Real.log x : ℂ) + α * Complex.I) + Real.pi * Complex.I := by
        simpa using congrArg (fun z : ℂ ↦ z + Real.pi * Complex.I)
          (positiveAxis_log_circleMap_of_pos hx hangle)
    _ = (Real.log x : ℂ) + (Real.pi + α) * Complex.I := by
        ring_nf

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on the upper lip, the original shifted
branch `log (-z)` is the adjusted branch with the constant `π i` removed, so its boundary value is
`log x - α i`. -/
lemma positiveAxisShiftedBranch_upperLip_value
    {x α : ℝ} (hx : 0 < x) (hα : α ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Complex.log (-circleMap 0 x (Real.pi - α)) =
      (Real.log x : ℂ) - α * Complex.I := by
  -- Remove the constant `π i` from the already normalized adjusted-branch upper-lip formula.
  have hadj :=
    positiveAxisAdjustedBranch_upperLip_value (x := x) (α := α) hx hα
  calc
    Complex.log (-circleMap 0 x (Real.pi - α)) =
        (Complex.log (-circleMap 0 x (Real.pi - α)) + Real.pi * Complex.I) -
          Real.pi * Complex.I := by ring
    _ = ((Real.log x : ℂ) + (Real.pi - α) * Complex.I) - Real.pi * Complex.I := by
        rw [hadj]
    _ = (Real.log x : ℂ) - α * Complex.I := by
        ring_nf

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on the lower lip, the original shifted
branch `log (-z)` is the adjusted lower-lip value with the same constant `π i` removed, hence
`log x + α i`. -/
lemma positiveAxisShiftedBranch_lowerLip_value
    {x α : ℝ} (hx : 0 < x) (hα : α ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Complex.log (-circleMap 0 x (α - Real.pi)) =
      (Real.log x : ℂ) + α * Complex.I := by
  -- The lower-lip normalization is the same subtraction of the constant `π i`.
  have hadj :=
    positiveAxisAdjustedBranch_lowerLip_value (x := x) (α := α) hx hα
  calc
    Complex.log (-circleMap 0 x (α - Real.pi)) =
        (Complex.log (-circleMap 0 x (α - Real.pi)) + Real.pi * Complex.I) -
          Real.pi * Complex.I := by ring
    _ = ((Real.log x : ℂ) + (Real.pi + α) * Complex.I) - Real.pi * Complex.I := by
        rw [hadj]
    _ = (Real.log x : ℂ) + α * Complex.I := by
        ring_nf

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: after rewriting the adjusted branch on
the upper slit lip, the radial interval kernel is the explicit boundary-value expression at the
complementary angle `α`. -/
abbrev positiveAxisAdjustedUpperLipKernel
    (P Q : Polynomial ℂ) (α x : ℝ) : ℂ :=
  Complex.exp ((Real.pi - α) * Complex.I) *
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain (circleMap 0 x (Real.pi - α)) *
      ((Real.log x : ℂ) + (Real.pi - α) * Complex.I)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: after rewriting the adjusted branch on
the lower slit lip, the radial interval kernel is the companion explicit boundary-value expression
at the same complementary angle `α`. -/
abbrev positiveAxisAdjustedLowerLipKernel
    (P Q : Polynomial ℂ) (α x : ℝ) : ℂ :=
  Complex.exp ((α - Real.pi) * Complex.I) *
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain (circleMap 0 x (α - Real.pi)) *
      ((Real.log x : ℂ) + (Real.pi + α) * Complex.I)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the adjusted upper and lower slit
boundary values combine into one paired interval kernel. This is the source-faithful contour
normalization target for the repaired positive-axis keyhole. -/
abbrev positiveAxisAdjustedLipPairKernel
    (P Q : Polynomial ℂ) (α x : ℝ) : ℂ :=
  positiveAxisAdjustedLowerLipKernel P Q α x -
    positiveAxisAdjustedUpperLipKernel P Q α x

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: after rewriting the original shifted
branch on the upper slit lip, the radial interval kernel is the explicit boundary-value expression
with logarithmic factor `log x - α i`. -/
abbrev positiveAxisShiftedUpperLipKernel
    (P Q : Polynomial ℂ) (α x : ℝ) : ℂ :=
  Complex.exp ((Real.pi - α) * Complex.I) *
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain (circleMap 0 x (Real.pi - α)) *
      ((Real.log x : ℂ) - α * Complex.I)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: after rewriting the original shifted
branch on the lower slit lip, the companion radial interval kernel carries the logarithmic factor
`log x + α i`. -/
abbrev positiveAxisShiftedLowerLipKernel
    (P Q : Polynomial ℂ) (α x : ℝ) : ℂ :=
  Complex.exp ((α - Real.pi) * Complex.I) *
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain (circleMap 0 x (α - Real.pi)) *
      ((Real.log x : ℂ) + α * Complex.I)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the original shifted-log lip pair is
the difference between the lower and upper shifted boundary kernels at the same complementary
angle `α`. -/
abbrev positiveAxisShiftedLipPairKernel
    (P Q : Polynomial ℂ) (α x : ℝ) : ℂ :=
  positiveAxisShiftedLowerLipKernel P Q α x -
    positiveAxisShiftedUpperLipKernel P Q α x

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: at the limiting angle `α = π`, the
shifted lip-pair kernel jumps by `2π i` times the meromorphic normal-form rational factor on the
positive real axis. This is the sign benchmark for the remaining lip asymptotic. -/
lemma positiveAxisShiftedLipPairKernel_pi
    (P Q : Polynomial ℂ) (x : ℝ) :
    positiveAxisShiftedLipPairKernel P Q Real.pi x =
      (2 * Real.pi * Complex.I : ℂ) *
        toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain (x : ℂ) := by
  -- At `α = π`, both lips collapse to the positive ray and only the logarithmic jump survives.
  simp [positiveAxisShiftedLipPairKernel, positiveAxisShiftedUpperLipKernel,
    positiveAxisShiftedLowerLipKernel, circleMap_zero]
  ring

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: once the upper and lower adjusted
branch values are rewritten explicitly, the generic radial-lip bridge packages their sum as one
interval integral of the paired adjusted kernel. -/
lemma positiveAxisAdjustedBranchUpperLower_curveIntegral_eq_adjustedLipPairInterval
    (P Q : Polynomial ℂ) (ρ₀ ρ₁ α : ℝ) (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (hρ₀ρ₁ : ρ₀ ≤ ρ₁)
    (hα : α ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hupperInt :
      IntervalIntegrable (positiveAxisAdjustedUpperLipKernel P Q α) volume ρ₀ ρ₁)
    (hlowerInt :
      IntervalIntegrable (positiveAxisAdjustedLowerLipKernel P Q α) volume ρ₀ ρ₁) :
    (∫ᶜ z in Path.segment (circleMap 0 ρ₁ (Real.pi - α)) (circleMap 0 ρ₀ (Real.pi - α)),
      (((fun z ↦
        toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
          (Complex.log (-z) + Real.pi * Complex.I)) dz) z)) +
      (∫ᶜ z in Path.segment (circleMap 0 ρ₀ (α - Real.pi)) (circleMap 0 ρ₁ (α - Real.pi)),
        (((fun z ↦
          toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
            (Complex.log (-z) + Real.pi * Complex.I)) dz) z)) =
      ∫ x in ρ₀..ρ₁, positiveAxisAdjustedLipPairKernel P Q α x := by
  let g : ℂ → ℂ := fun z ↦
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
      (Complex.log (-z) + Real.pi * Complex.I)
  have hupperRaw :
      IntervalIntegrable
        (fun x : ℝ ↦
          Complex.exp ((((Real.pi - α : ℝ) : ℂ) * Complex.I)) *
            g (circleMap 0 x (Real.pi - α)))
        volume ρ₀ ρ₁ := by
    -- Replace the upper-lip branch value by its exact logarithmic normal form before using the
    -- generic radial bridge.
    refine IntervalIntegrable.congr ?_ hupperInt
    intro x hx
    have hxIoc : x ∈ Set.Ioc ρ₀ ρ₁ := by
      simpa [Set.uIoc_of_le hρ₀ρ₁] using (hx : x ∈ Set.uIoc ρ₀ ρ₁)
    have hxpos : 0 < x := lt_trans hρ₀ hxIoc.1
    simp [g, positiveAxisAdjustedUpperLipKernel,
      positiveAxisAdjustedBranch_upperLip_value (x := x) (α := α) hxpos hα, mul_assoc]
  have hlowerRaw :
      IntervalIntegrable
        (fun x : ℝ ↦
          Complex.exp ((((α - Real.pi : ℝ) : ℂ) * Complex.I)) *
            g (circleMap 0 x (α - Real.pi)))
        volume ρ₀ ρ₁ := by
    -- The lower branch is rewritten the same way, now using the reflected exact boundary value.
    refine IntervalIntegrable.congr ?_ hlowerInt
    intro x hx
    have hxIoc : x ∈ Set.Ioc ρ₀ ρ₁ := by
      simpa [Set.uIoc_of_le hρ₀ρ₁] using (hx : x ∈ Set.uIoc ρ₀ ρ₁)
    have hxpos : 0 < x := lt_trans hρ₀ hxIoc.1
    simp [g, positiveAxisAdjustedLowerLipKernel,
      positiveAxisAdjustedBranch_lowerLip_value (x := x) (α := α) hxpos hα, mul_assoc]
  -- Feed the exact upper/lower branch formulas into the generic upper-plus-lower radial bridge,
  -- then rewrite the paired kernel pointwise to its explicit adjusted-boundary form.
  have hbase :
      (∫ᶜ z in Path.segment (circleMap 0 ρ₁ (Real.pi - α)) (circleMap 0 ρ₀ (Real.pi - α)),
        (((fun z ↦
          toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
            (Complex.log (-z) + Real.pi * Complex.I)) dz) z)) +
        (∫ᶜ z in Path.segment (circleMap 0 ρ₀ (α - Real.pi)) (circleMap 0 ρ₁ (α - Real.pi)),
          (((fun z ↦
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
              (Complex.log (-z) + Real.pi * Complex.I)) dz) z)) =
        ∫ x in ρ₀..ρ₁,
          Complex.exp ((((α - Real.pi : ℝ) : ℂ) * Complex.I)) *
              g (circleMap 0 x (α - Real.pi)) -
            Complex.exp ((((Real.pi - α : ℝ) : ℂ) * Complex.I)) *
              g (circleMap 0 x (Real.pi - α)) := by
    simpa using
      positiveAxisUpperLower_curveIntegral_eq_lipPairInterval
        g ρ₁ ρ₀ (Real.pi - α) (α - Real.pi) hρ₁ hρ₀ hupperRaw hlowerRaw
  calc
    (∫ᶜ z in Path.segment (circleMap 0 ρ₁ (Real.pi - α)) (circleMap 0 ρ₀ (Real.pi - α)),
      (((fun z ↦
        toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
          (Complex.log (-z) + Real.pi * Complex.I)) dz) z)) +
      (∫ᶜ z in Path.segment (circleMap 0 ρ₀ (α - Real.pi)) (circleMap 0 ρ₁ (α - Real.pi)),
        (((fun z ↦
          toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
            (Complex.log (-z) + Real.pi * Complex.I)) dz) z)) =
      ∫ x in ρ₀..ρ₁,
        Complex.exp ((((α - Real.pi : ℝ) : ℂ) * Complex.I)) *
            g (circleMap 0 x (α - Real.pi)) -
          Complex.exp ((((Real.pi - α : ℝ) : ℂ) * Complex.I)) *
            g (circleMap 0 x (Real.pi - α)) := hbase
    _ = ∫ x in ρ₀..ρ₁, positiveAxisAdjustedLipPairKernel P Q α x := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        have hxIcc : x ∈ Set.Icc ρ₀ ρ₁ := by
          simpa [Set.uIcc_of_le hρ₀ρ₁] using (hx : x ∈ Set.uIcc ρ₀ ρ₁)
        have hxpos : 0 < x := lt_of_lt_of_le hρ₀ hxIcc.1
        simp [g, positiveAxisAdjustedLipPairKernel, positiveAxisAdjustedUpperLipKernel,
          positiveAxisAdjustedLowerLipKernel,
          positiveAxisAdjustedBranch_upperLip_value (x := x) (α := α) hxpos hα,
          positiveAxisAdjustedBranch_lowerLip_value (x := x) (α := α) hxpos hα,
          mul_assoc]

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the actual poles of `rationalEval P Q`
form the expected finite subfamily of the denominator roots. -/
private noncomputable def rationalEvalPoleFinset (P Q : Polynomial ℂ) : Finset ℂ :=
  Q.roots.toFinset.filter fun z ↦ meromorphicOrderAt (rationalEval P Q) z < 0

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: every genuine pole of the rational
kernel must lie among the roots of the denominator polynomial. -/
private lemma rationalEval_pole_mem_denominator_roots
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {z : ℂ}
    (hz : meromorphicOrderAt (rationalEval P Q) z < 0) :
    z ∈ Q.roots.toFinset := by
  by_contra hzRoot
  have hQz : Q.eval z ≠ 0 := by
    intro hQz
    exact hzRoot (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hQz))
  have hrat :
      AnalyticAt ℂ (rationalEval P Q) z := by
    -- Off the denominator roots, the rational quotient is an honest holomorphic function.
    have hPanalytic : AnalyticAt ℂ (fun w : ℂ ↦ P.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) P z (by simp))
    have hQanalytic : AnalyticAt ℂ (fun w : ℂ ↦ Q.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) Q z (by simp))
    simpa [rationalEval] using hPanalytic.div hQanalytic hQz
  exact (not_lt_of_ge hrat.meromorphicOrderAt_nonneg) hz

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: membership in the canonical pole
finset is definitionally equivalent to having negative meromorphic order. -/
private lemma rationalEval_pole_iff_mem_poleFinset
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ rationalEvalPoleFinset P Q := by
  intro z
  constructor
  · intro hz
    -- Record the pole in the filtered denominator-root finset using the previous root criterion.
    exact Finset.mem_filter.2 ⟨rationalEval_pole_mem_denominator_roots P Q hQ hz, hz⟩
  · intro hz
    -- The filter keeps exactly the negative-order points.
    exact (Finset.mem_filter.1 hz).2

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the canonical finite pole set already
lies in the shifted logarithm domain because the nonnegative real axis is pole-free. -/
private lemma rationalEvalPoleFinset_subset_shiftedLogDomain
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    (↑(rationalEvalPoleFinset P Q) : Set ℂ) ⊆ shiftedLogDomain := by
  -- Reuse the earlier source-faithful pole-domain package once the finite pole family is fixed.
  simpa [rationalEvalPoleFinset] using
    pole_finset_subset_shiftedLogDomain
      (rationalEval_pole_iff_mem_poleFinset P Q hQ) hcut'

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: every actual pole of the rational
kernel eventually lies strictly inside the large positive-axis wedge annulus. This packages the
geometric pole-avoidance frontier needed before the remaining lip and circle estimates. -/
private lemma eventually_rationalEvalPoleFinset_subset_interior_positiveAxisWedgeAnnulus
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∀ᶠ R : ℝ in atTop,
      let ε := 1 / R
      1 < R ∧
        ∀ z ∈ rationalEvalPoleFinset P Q,
          z ∈ interior (positiveAxisWedgeAnnulus R ε) := by
  classical
  let s : Finset ℂ := rationalEvalPoleFinset P Q
  let hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  have hsDomain :
      (↑s : Set ℂ) ⊆ shiftedLogDomain :=
    rationalEvalPoleFinset_subset_shiftedLogDomain P Q hQ hcut'
  let radius : ℂ → ℝ := fun z ↦
    if hz : z ∈ s then
      let data := Metric.mem_nhds_iff.1 (isOpen_shiftedLogDomain.mem_nhds (hsDomain hz))
      data.choose / 2
    else 1
  have hradius_pos : ∀ z ∈ s, 0 < radius z := by
    intro z hz
    dsimp [radius]
    simp [hz]
    let data := Metric.mem_nhds_iff.1 (isOpen_shiftedLogDomain.mem_nhds (hsDomain hz))
    have hdata : 0 < data.choose := data.choose_spec.1
    linarith
  have hradius_D : ∀ z ∈ s, Metric.closedBall z (radius z) ⊆ shiftedLogDomain := by
    intro z hz
    dsimp [radius]
    simp [hz]
    let data := Metric.mem_nhds_iff.1 (isOpen_shiftedLogDomain.mem_nhds (hsDomain hz))
    have hdata : 0 < data.choose := data.choose_spec.1
    exact (Metric.closedBall_subset_ball (by linarith)).trans data.choose_spec.2
  have hEventuallyInterior :
      ∀ᶠ R : ℝ in atTop,
        ∀ z ∈ s,
          Metric.closedBall z (radius z) ⊆ interior (positiveAxisWedgeAnnulus R (1 / R)) := by
    rw [Filter.eventually_all_finset]
    intro z hz
    filter_upwards
      [eventually_closedBall_subset_interior_positiveAxisWedgeAnnulus
        z (hρ := hradius_pos z hz) (hsubset := hradius_D z hz)]
      with R hR
    exact hR.2
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hEventuallyInterior] with R hRgt1 hInterior
  refine ⟨hRgt1, ?_⟩
  intro z hz
  exact hInterior z hz (Metric.mem_closedBall_self (hradius_pos z hz).le)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the original shifted-log upper and
lower slit lips grouped in the same orientation as the keyhole decomposition. -/
abbrev positiveAxisShiftedLogLipPairTerm
    (P Q : Polynomial ℂ) (R : ℝ) : ℂ :=
  (∫ᶜ z in Path.segment
      (circleMap 0 R (positiveAxisKeyholeUpperAngle R (1 / R)))
      (circleMap 0 (1 / R) (positiveAxisKeyholeUpperAngle R (1 / R))),
    (((shiftedLogRationalNormalForm P Q) dz) z)) +
    (∫ᶜ z in Path.segment
      (circleMap 0 (1 / R) (positiveAxisKeyholeLowerAngle R (1 / R)))
      (circleMap 0 R (positiveAxisKeyholeLowerAngle R (1 / R))),
      (((shiftedLogRationalNormalForm P Q) dz) z))

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the original shifted-log inner and
outer circular branches grouped in the same orientation as the keyhole decomposition. -/
abbrev positiveAxisShiftedLogArcPairTerm
    (P Q : Polynomial ℂ) (R : ℝ) : ℂ :=
  (∫ᶜ z in ((Path.segment
      (positiveAxisKeyholeUpperAngle R (1 / R))
      (positiveAxisKeyholeLowerAngle R (1 / R))).map
        (continuous_circleMap 0 (1 / R))),
    (((shiftedLogRationalNormalForm P Q) dz) z)) +
    (∫ᶜ z in ((Path.segment
      (positiveAxisKeyholeLowerAngle R (1 / R))
      (positiveAxisKeyholeUpperAngle R (1 / R))).map
        (continuous_circleMap 0 R)),
      (((shiftedLogRationalNormalForm P Q) dz) z))

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the explicit truncated real-axis term
subtracted from the keyhole contour integral. -/
abbrev positiveAxisShiftedLogTruncTargetTerm
    (P Q : Polynomial ℂ) (R : ℝ) : ℂ :=
  (-(2 * Real.pi * Complex.I : ℂ)) *
    ∫ x in (1 / R)..R, rationalEval P Q (x : ℂ)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: once the shifted-log keyhole contour
is grouped into its slit lips and circular arcs, the full remainder is exactly the lip remainder
plus the arc remainder. -/
lemma eventually_positiveAxisShiftedLogRemainder_eq_lipPair_add_arcPair
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∀ᶠ R : ℝ in atTop,
      ((∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((shiftedLogRationalNormalForm P Q) dz) z)) -
        positiveAxisShiftedLogTruncTargetTerm P Q R) =
        (positiveAxisShiftedLogLipPairTerm P Q R -
            positiveAxisShiftedLogTruncTargetTerm P Q R) +
          positiveAxisShiftedLogArcPairTerm P Q R := by
  -- Route correction: the contour bookkeeping is already stabilized, so the remaining work here is
  -- only to instantiate the grouped four-piece decomposition for the shifted-log kernel.
  let s : Finset ℂ := rationalEvalPoleFinset P Q
  let G : ℂ → ℂ := shiftedLogRationalNormalForm P Q
  let hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  have hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s :=
    rationalEval_pole_iff_mem_poleFinset P Q hQ
  have hscalarCont : ContinuousOn G (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- The shifted-log normal form is holomorphic away from the finite pole set, hence continuous.
    exact
      (shiftedLogRationalNF_differentiableOn_shiftedLogDomain_off_poles P Q hQ hpoles').continuousOn
  have hformCont : ContinuousOn ((G dz)) (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- Turn continuity of the scalar coefficient into continuity of the associated scalar `1`-form.
    simpa [G, Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ))).prodMk hscalarCont)
  filter_upwards
      [eventually_rationalEvalPoleFinset_subset_interior_positiveAxisWedgeAnnulus P Q hdeg hcut']
      with R hR
  rcases hR with ⟨hRgt1, hInterior⟩
  let ε : ℝ := 1 / R
  have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
  have hε : 0 < ε := by
    dsimp [ε]
    exact one_div_pos.mpr hRpos
  have hεR : ε < R := by
    dsimp [ε]
    exact (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
  have hfrontier :
      frontier (positiveAxisWedgeAnnulus R ε) = Set.range (positiveAxisKeyhole R ε) :=
    positiveAxisWedgeAnnulus_frontier_eq_range R ε hε hεR
  have hpathRange :
      Set.range (positiveAxisKeyhole R ε) ⊆ shiftedLogDomain \ (↑s : Set ℂ) := by
    intro z hz
    have hzFrontier : z ∈ frontier (positiveAxisWedgeAnnulus R ε) := by
      simpa [hfrontier] using hz
    have hzClosure : z ∈ closure (positiveAxisWedgeAnnulus R ε) :=
      frontier_subset_closure hzFrontier
    have hzWedge : z ∈ positiveAxisWedgeAnnulus R ε := by
      simpa [isClosed_positiveAxisWedgeAnnulus R ε |>.closure_eq] using hzClosure
    have hzNotPole : z ∉ (↑s : Set ℂ) := by
      intro hzPole
      have hzInterior : z ∈ interior (positiveAxisWedgeAnnulus R ε) := hInterior z hzPole
      have hzFrontier' := hzFrontier
      change z ∈ closure (positiveAxisWedgeAnnulus R ε) \ interior (positiveAxisWedgeAnnulus R ε)
        at hzFrontier'
      exact hzFrontier'.2 hzInterior
    exact ⟨positiveAxisWedgeAnnulus_subset_shiftedLogDomain hε hεR hzWedge, hzNotPole⟩
  have hupperRange :
      Set.range
          (Path.segment
            (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inl (Or.inl (Or.inl hz))
  have hinnerRange :
      Set.range
          (((Path.segment
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)).map
                (continuous_circleMap 0 ε))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inl (Or.inl (Or.inr hz))
  have hlowerRange :
      Set.range
          (Path.segment
            (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
            (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inl (Or.inr hz)
  have houterRange :
      Set.range
          (((Path.segment
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)).map
                (continuous_circleMap 0 R))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inr hz
  have hupper :
      CurveIntegrable
        (G dz)
        (Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))) := by
    -- The upper lip inherits curve integrability from continuity on the pole-free keyhole range.
    exact positiveAxis_curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
      (γ := Path.segment
        (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
        (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε)))
      (Path.segment_isPiecewiseDifferentiable _ _)
      hscalarCont (Set.Subset.trans hupperRange hpathRange)
  have hinner :
      CurveIntegrable
        (G dz)
        ((Path.segment
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)).map
              (continuous_circleMap 0 ε)) := by
    -- The inner arc is a smooth mapped angular segment staying on the same pole-free contour.
    exact positiveAxis_curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
      (γ := (Path.segment
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε)).map
            (continuous_circleMap 0 ε))
      ((positiveAxisKeyhole_circle_segment_isDifferentiable ε
        (positiveAxisKeyholeUpperAngle R ε)
        (positiveAxisKeyholeLowerAngle R ε)).isPiecewiseDifferentiable)
      hscalarCont (Set.Subset.trans hinnerRange hpathRange)
  have hlower :
      CurveIntegrable
        (G dz)
        (Path.segment
          (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))) := by
    -- The lower lip is the companion radial segment on the same eventual pole-free frontier.
    exact positiveAxis_curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
      (γ := Path.segment
        (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
        (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε)))
      (Path.segment_isPiecewiseDifferentiable _ _)
      hscalarCont (Set.Subset.trans hlowerRange hpathRange)
  have houter :
      CurveIntegrable
        (G dz)
        ((Path.segment
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)).map
              (continuous_circleMap 0 R)) := by
    -- The outer arc is handled exactly like the inner one, now at radius `R`.
    exact positiveAxis_curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
      (γ := (Path.segment
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε)).map
            (continuous_circleMap 0 R))
      ((positiveAxisKeyhole_circle_segment_isDifferentiable R
        (positiveAxisKeyholeLowerAngle R ε)
        (positiveAxisKeyholeUpperAngle R ε)).isPiecewiseDifferentiable)
      hscalarCont (Set.Subset.trans houterRange hpathRange)
  have hsplit :
      ∫ᶜ z in (positiveAxisKeyhole R ε).toClosedPath.toPath, ((G dz) z) =
        positiveAxisShiftedLogLipPairTerm P Q R + positiveAxisShiftedLogArcPairTerm P Q R := by
    -- With the four branch integrals now certified, the existing grouped contour theorem applies.
    simpa [G, ε, positiveAxisShiftedLogLipPairTerm, positiveAxisShiftedLogArcPairTerm,
      positiveAxisKeyholeLipPairIntegral, positiveAxisKeyholeArcPairIntegral] using
      positiveAxisKeyhole_curveIntegral_eq_lipPairIntegral_add_arcIntegrals G R ε
        hupper hinner hlower houter
  -- Subtract the same truncation term from the grouped contour identity and regroup the sum.
  calc
    (∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath, (((shiftedLogRationalNormalForm P Q) dz) z)) -
        positiveAxisShiftedLogTruncTargetTerm P Q R =
      (positiveAxisShiftedLogLipPairTerm P Q R + positiveAxisShiftedLogArcPairTerm P Q R) -
        positiveAxisShiftedLogTruncTargetTerm P Q R := by
          simpa [G, ε] using congrArg
            (fun w : ℂ ↦ w - positiveAxisShiftedLogTruncTargetTerm P Q R) hsplit
    _ =
      (positiveAxisShiftedLogLipPairTerm P Q R -
          positiveAxisShiftedLogTruncTargetTerm P Q R) +
        positiveAxisShiftedLogArcPairTerm P Q R := by
          abel
