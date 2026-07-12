import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0010_Proposition_4_1»
import DifferentialForms_Cartan_1970.II.section05.«0018_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

open scoped BigOperators unitInterval

universe u

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a primitive along a closed
piecewise differentiable path forces its contour integral to vanish once the primitive takes the
same value at the two endpoints. -/
theorem primitiveAlongClosedPath_integral_eq_zero_of_endpoint_eq
    {C : Set ℂ} {z : ℂ} {γ : Path z z} {ω : ℂ → ℂ →L[ℝ] ℂ} {f : C(I, ℂ)}
    (hγ_piece : γ.IsPiecewiseDifferentiable)
    (hendpoint : f 1 = f 0)
    (hf : IsPrimitiveAlongPath ω C γ f) :
    ∫ᶜ ζ in γ, ω ζ = 0 := by
  by_cases hγ_int : CurveIntegrable ω γ
  · calc
      ∫ᶜ ζ in γ, ω ζ = f 1 - f 0 := by
        simpa using hf.curveIntegral_eq_endpoint_sub hγ_piece hγ_int
      _ = 0 := by
        rw [hendpoint, sub_self]
  · rw [curveIntegral_def]
    simpa [CurveIntegrable] using
      (intervalIntegral.integral_undef (μ := MeasureTheory.volume)
        (f := curveIntegralFun ω γ) (a := (0 : ℝ)) (b := (1 : ℝ)) hγ_int)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: an exact stagewise decomposition of
the target contour into rectangle stages plus connector errors turns into the required rectangle
stage convergence once the connector errors tend to `0`. -/
theorem tendsto_rectangleStage_of_eq_target_add_error
    {target : ℂ} {N M : ℕ → ℕ} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (z w : ∀ n, Fin (N n) → ℂ) (ε : ∀ n, Fin (M n) → ClosedPath ℂ)
    (hstage :
      ∀ n,
        target =
          (∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) +
              ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ)
    (herror :
      Filter.Tendsto
        (fun n ↦ ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ)
        Filter.atTop
        (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ ∑ s : Fin (N n),
        ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ)
      Filter.atTop
      (nhds target) := by
  have htargetMinus :
      Filter.Tendsto
        (fun n ↦
          target - ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ)
        Filter.atTop
        (nhds (target - 0)) := by
    exact tendsto_const_nhds.sub herror
  have hrewrite :
      (fun n ↦ ∑ s : Fin (N n),
        ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) =
        (fun n ↦ target - ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ) := by
    funext n
    exact eq_sub_of_add_eq (hstage n).symm
  rw [hrewrite]
  simpa using htargetMinus

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a closed loop contained in one open
primitive domain already has zero contour integral. -/
theorem primitiveLoop_integral_eq_zero_of_hasPrimitiveOn
    {U : Set ℂ} (hU_open : IsOpen U) {z : ℂ} {γ : Path z z}
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hγ_piece : γ.IsPiecewiseDifferentiable)
    (hγU : Set.range γ ⊆ U) (hf : HasPrimitiveOn U ω) :
    ∫ᶜ ζ in γ, ω ζ = 0 := by
  rcases hf with ⟨primitive, hprimitive⟩
  have hprimitiveAlong :
      IsPrimitiveAlongPath ω U γ (hprimitive.alongPath γ hγU) :=
    hprimitive.isPrimitiveAlongPath hU_open γ hγU
  exact
    primitiveAlongClosedPath_integral_eq_zero_of_endpoint_eq
      hγ_piece
      (by simp [IsPrimitiveOn.alongPath_apply])
      hprimitiveAlong

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once each connector loop in a stage
family stays inside some open primitive neighborhood, every connector contour integral vanishes. -/
theorem connectorIntegrals_eq_zero_of_primitiveConnectorWitness
    {M : ℕ → ℕ} {ε : ∀ n, Fin (M n) → ClosedPath ℂ}
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hε_piece : ∀ n k, ((ε n k).toPath).IsPiecewiseDifferentiable)
    (hprimitive :
      ∀ n k, ∃ U : Set ℂ,
        IsOpen U ∧ Set.range (ε n k).toPath ⊆ U ∧ HasPrimitiveOn U ω) :
    ∀ n k, ∫ᶜ ζ in (ε n k).toPath, ω ζ = 0 := by
  intro n k
  rcases hprimitive n k with ⟨U, hU_open, hεU, hU_primitive⟩
  exact
    primitiveLoop_integral_eq_zero_of_hasPrimitiveOn
      hU_open (hε_piece n k) hεU hU_primitive

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: stagewise zero connector integrals
force the connector-error sequence to converge to `0`. -/
theorem connectorErrorTendstoZero_of_stagewiseIntegralZero
    {M : ℕ → ℕ} {ε : ∀ n, Fin (M n) → ClosedPath ℂ}
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hzero : ∀ n k, ∫ᶜ ζ in (ε n k).toPath, ω ζ = 0) :
    Filter.Tendsto
      (fun n ↦ ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ)
      Filter.atTop
      (nhds 0) := by
  have hsumZero :
      ∀ n, (∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ) = 0 := by
    intro n
    calc
      (∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ) =
          ∑ k : Fin (M n), 0 := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        exact hzero n k
      _ = 0 := by
        simp
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  exact Filter.Eventually.of_forall fun n ↦ (hsumZero n).symm

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the connected-case contour sum
is already known to vanish, the requested rectangle-stage package is a formal empty-stage
construction. -/
theorem rectangleStageDecompositionWithVanishingConnectorErrors_of_eq_zero
    {ι : Type u} [Fintype ι] {C : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (htarget : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ N : ℕ → ℕ, ∃ z w : ∀ n, Fin (N n) → ℂ,
      ∃ M : ℕ → ℕ, ∃ ε : ∀ n, Fin (M n) → ClosedPath ℂ,
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C) ∧
        (∀ n,
          (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) +
                ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ) ∧
        Filter.Tendsto
          (fun n ↦ ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ)
          Filter.atTop
          (nhds 0) := by
  let N : ℕ → ℕ := fun _ ↦ 0
  let z : ∀ n, Fin (N n) → ℂ := fun _ s ↦ nomatch s
  let w : ∀ n, Fin (N n) → ℂ := fun _ s ↦ nomatch s
  let M : ℕ → ℕ := fun _ ↦ 0
  let ε : ∀ n, Fin (M n) → ClosedPath ℂ := fun _ s ↦ nomatch s
  refine ⟨N, z, w, M, ε, ?_, ?_, ?_⟩
  · intro n s
    nomatch s
  · intro n
    simpa [N, M, z, w, ε] using htarget
  · exact
      connectorErrorTendstoZero_of_stagewiseIntegralZero
        (M := M) (ε := ε) (ω := ω) (hzero := by
          intro n k
          nomatch k)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the owner-level connected-open stage
package is only the formal empty-stage wrapper once the scalar contour sum is known to vanish. -/
theorem IsOrientedBoundaryOf.existsRectangleStageDecompositionWithVanishingConnectorErrors_of_sumZero
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (_hΓ : IsOrientedBoundaryOf K Γ)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hsumZero : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ N : ℕ → ℕ, ∃ z w : ∀ n, Fin (N n) → ℂ,
      ∃ M : ℕ → ℕ, ∃ ε : ∀ n, Fin (M n) → ClosedPath ℂ,
        (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C) ∧
        (∀ n,
          (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) =
            (∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) +
                ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ) ∧
        Filter.Tendsto
          (fun n ↦ ∑ k : Fin (M n), ∫ᶜ ζ in (ε n k).toPath, ω ζ)
          Filter.atTop
          (nhds 0) := by
  exact
    rectangleStageDecompositionWithVanishingConnectorErrors_of_eq_zero
      (C := C) (Γ := Γ) (ω := ω) hsumZero

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the total oriented-boundary
contour sum is already known to vanish, the requested asymptotic rectangle-stage package is the
formal empty-stage wrapper coming from the exact decomposition helper. -/
theorem asymptoticRectangleStages_of_sum_curveIntegral_eq_zero
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hsumZero : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ N : ℕ → ℕ, ∃ z w : ∀ n, Fin (N n) → ℂ,
      (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C) ∧
      Filter.Tendsto
        (fun n ↦ ∑ s : Fin (N n),
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ)) := by
  obtain ⟨N, z, w, M, ε, hrect, hstage, herror⟩ :=
    hΓ.existsRectangleStageDecompositionWithVanishingConnectorErrors_of_sumZero
      (C := C) (ω := ω) hsumZero
  refine ⟨N, z, w, hrect, ?_⟩
  -- Route correction: after the scalar contour sum is zero, only the formal exact-package to
  -- asymptotic-package transport remains.
  exact tendsto_rectangleStage_of_eq_target_add_error z w ε hstage herror
