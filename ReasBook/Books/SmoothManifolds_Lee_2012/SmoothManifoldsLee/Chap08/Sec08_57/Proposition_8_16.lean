import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.HahnBanach
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Definition_8_57_extra_1

open scoped ContDiff Manifold

noncomputable section

section

universe uE uE' uH uH' uM uN

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item uses
-- the local `VectorField.f_related` predicate together with mathlib's `ContMDiffAt` and
-- `mfderiv` APIs for local real-valued test functions.

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N]

/-- Helper for Proposition 8.16: composing the preferred chart at `F p` with a continuous linear
functional gives a smooth real-valued test function at `F p`. -/
lemma chartLinearTest_contMDiffAt
    {F : M → N} (p : M) (ℓ : E' →L[ℝ] ℝ) :
    ContMDiffAt J 𝓘(ℝ) (∞ : ℕ∞ω) (fun q : N ↦ ℓ (extChartAt J (F p) q)) (F p) := by
  -- The chart is smooth at its center, and continuous linear maps are smooth everywhere.
  simpa [Function.comp] using
    (ℓ.contMDiffAt.comp (F p) (contMDiffAt_extChartAt (I := J) (x := F p)))

/-- Helper for Proposition 8.16: differentiating a chart-linear test function evaluates the
chart pushforward of the input tangent vector under the chosen linear functional. -/
lemma chartLinearTest_mfderiv_apply
    {F : M → N} (p : M) (ℓ : E' →L[ℝ] ℝ) (v : TangentSpace J (F p)) :
    mfderiv% (fun q : N ↦ ℓ (extChartAt J (F p) q)) (F p) v =
      ℓ (mfderiv% (extChartAt J (F p)) (F p) v) := by
  -- Apply the chain rule to the chart-linear composition and simplify the linear derivative.
  simpa [Function.comp, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] using
    (mfderiv_comp_apply (x := F p)
      (g := ℓ)
      (f := extChartAt J (F p))
      (ℓ.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
      ((contMDiffAt_extChartAt (I := J) (x := F p)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0))
      v)

/-- Helper for Proposition 8.16: if two tangent vectors at `F p` have the same preferred-chart
pushforward, then the tangent vectors themselves are equal. -/
lemma pointwise_eq_of_chartPushforward_eq
    {F : M → N} (p : M) {v w : TangentSpace J (F p)}
    (hpush :
      mfderiv% (extChartAt J (F p)) (F p) v =
        mfderiv% (extChartAt J (F p)) (F p) w) :
    v = w := by
  -- Cancel the chart derivative using invertibility of the preferred chart derivative.
  exact
    (isInvertible_mfderiv_extChartAt (I := J) (x := F p) (y := F p)
      (mem_extChartAt_source (I := J) (F p))).injective hpush

/-- Helper for Proposition 8.16: the test-function identity forces equality of the preferred-chart
pushforwards of `mfderiv I J F p (X p)` and `Y (F p)`. -/
lemma chartPushforward_eq_of_testFunctions
    {F : M → N}
    (hF : ContMDiff I J (∞ : ℕ∞ω) F)
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q}
    (hTest :
      ∀ (p : M) (f : N → ℝ),
        ContMDiffAt J 𝓘(ℝ) (∞ : ℕ∞ω) f (F p) →
          mfderiv% (fun x ↦ f (F x)) p (X p) =
            mfderiv% f (F p) (Y (F p)))
    (p : M) :
    mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p)) =
      mfderiv% (extChartAt J (F p)) (F p) (Y (F p)) := by
  -- Separate the two chart-space vectors by continuous linear functionals.
  by_contra hne
  let w : E' :=
    mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p)) -
      mfderiv% (extChartAt J (F p)) (F p) (Y (F p))
  have hw_ne : w ≠ 0 := by
    intro hw
    apply hne
    simpa [w] using sub_eq_zero.mp hw
  obtain ⟨ℓ, -, hℓw⟩ := exists_dual_vector ℝ w (norm_ne_zero_iff.mpr hw_ne)
  have hchart :
      mfderiv% (fun q : N ↦ ℓ (extChartAt J (F p) q)) (F p) (mfderiv I J F p (X p)) =
        mfderiv% (fun q : N ↦ ℓ (extChartAt J (F p) q)) (F p) (Y (F p)) := by
    -- Apply the assumed test-function identity to the chart-linear test function.
    have htest :=
      hTest p (fun q : N ↦ ℓ (extChartAt J (F p) q)) (chartLinearTest_contMDiffAt (J := J) p ℓ)
    -- Rewrite the source derivative by the chain rule, then compare to the target side.
    have hleft :
        mfderiv% (fun x ↦ (fun q : N ↦ ℓ (extChartAt J (F p) q)) (F x)) p (X p) =
          mfderiv% (fun q : N ↦ ℓ (extChartAt J (F p) q)) (F p) (mfderiv I J F p (X p)) := by
      simpa [Function.comp] using
        (mfderiv_comp_apply (x := p)
          (g := fun q : N ↦ ℓ (extChartAt J (F p) q))
          (f := F)
          ((chartLinearTest_contMDiffAt (J := J) p ℓ).mdifferentiableAt
            (by simp : (∞ : ℕ∞ω) ≠ 0))
          (hF.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (X p))
    exact hleft.symm.trans htest
  have hzero :
      ℓ w = 0 := by
    -- Expand the chart derivatives into scalar evaluations of the same functional.
    have hEval := hchart
    rw [chartLinearTest_mfderiv_apply (J := J) (F := F) (p := p) (ℓ := ℓ)
          (v := mfderiv I J F p (X p)),
      chartLinearTest_mfderiv_apply (J := J) (F := F) (p := p) (ℓ := ℓ)
        (v := Y (F p))] at hEval
    have hSub :
        ℓ (mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p))) -
          ℓ (mfderiv% (extChartAt J (F p)) (F p) (Y (F p))) = 0 :=
      sub_eq_zero.mpr hEval
    change
      ℓ
          (mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p)) -
            mfderiv% (extChartAt J (F p)) (F p) (Y (F p))) = 0
    calc
      ℓ
          (mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p)) -
            mfderiv% (extChartAt J (F p)) (F p) (Y (F p)))
          =
            ℓ (mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p))) -
              ℓ (mfderiv% (extChartAt J (F p)) (F p) (Y (F p))) := by
                exact
                  ℓ.map_sub
                    (mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p)))
                    (mfderiv% (extChartAt J (F p)) (F p) (Y (F p)))
      _ = 0 := hSub
  rw [hℓw] at hzero
  exact hw_ne (norm_eq_zero.mp hzero)

/-- Proposition 8.16: suppose `F : M → N` is a smooth map between manifolds with or without
boundary. Then vector fields `X` on `M` and `Y` on `N` are `F`-related if and only if, for every
point `p : M` and every real-valued function that is smooth in a neighborhood of `F p`, the
derivative of `f ∘ F` along `X` at `p` agrees with the derivative of `f` along `Y` at `F p`. -/
theorem f_related_iff_mfderiv_comp_eq
    {F : M → N}
    (hF : ContMDiff I J (∞ : ℕ∞ω) F)
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q}
    : VectorField.f_related F X Y ↔
      ∀ (p : M) (f : N → ℝ),
        ContMDiffAt J 𝓘(ℝ) (∞ : ℕ∞ω) f (F p) →
          mfderiv% (fun x ↦ f (F x)) p (X p) =
            mfderiv% f (F p) (Y (F p)) := by
  constructor
  · intro hRelated p f hf
    -- Differentiate `f ∘ F` along `X p` and then rewrite the pushed-forward tangent vector.
    calc
      mfderiv% (fun x ↦ f (F x)) p (X p)
          = mfderiv% f (F p) (mfderiv I J F p (X p)) := by
              simpa [Function.comp] using
                mfderiv_comp_apply p (hf.mdifferentiableAt (by simp))
                  (hF.contMDiffAt.mdifferentiableAt (by simp)) (X p)
      _ = mfderiv% f (F p) (Y (F p)) := by
            rw [VectorField.f_related_apply hRelated p]
  · intro hTest
    -- Keep the given smoothness of `F`; the test functions determine the pointwise pushforward.
    refine ⟨hF, ?_⟩
    intro p
    have hpush :
        mfderiv% (extChartAt J (F p)) (F p) (mfderiv I J F p (X p)) =
          mfderiv% (extChartAt J (F p)) (F p) (Y (F p)) :=
      chartPushforward_eq_of_testFunctions (I := I) (J := J) hF hTest p
    -- Cancel the preferred-chart derivative to recover equality in the manifold tangent space.
    exact pointwise_eq_of_chartPushforward_eq (J := J) (F := F) p hpush

end
