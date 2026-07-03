import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_48 (from Chap06) -/
noncomputable section

open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

/- Definition 6.48 lies in Chapter 6's smoothed semidefinite / spectral optimization domain.

Mandatory domain-style sampling before refinement:
- `logSumExpMaxEigenvalueSmoothing` in `Definition_6_47`, the Chapter 6 owner of the
  positive-parameter spectral smoothing on `𝕊^n`;
- `logSumExpMaxEigenvalueSmoothing_eq` in `Definition_6_47`, the direct bridge to the textbook
  eigenvalue log-sum-exp formula;
- `SetConstrainedMinimizationProblem.optimalValue` in `Definition_1_3_7`, the project owner for
  the constrained optimal value of a feasible real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Definition_1_3_7`, the
  bridge expanding that owner to the `EReal` image infimum;
- `NonsmoothEigenvalueMinimizationProblem.toSetConstrainedMinimizationProblem` and
  `NonsmoothEigenvalueMinimizationProblem.optimalValue_eq` in `Definition_6_46`, the nearby
  Chapter 6 owner pattern for the same semidefinite optimization layer.

Best owner abstraction:
- source-facing: `smoothedSemidefiniteObjective`, the specialization `y ↦ f_μ(C + A y)`;
- core/canonical: `logSumExpMaxEigenvalueSmoothing` and
  `SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)`;
- bridge/view: `smoothedSemidefiniteObjective_apply` and the inherited optimal-value owner
  specialization at the end of the file.

Primitive data:
- the ambient real module `E`, with the textbook `ℝ^m` kept only as a specialization layer;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the symmetric matrix `C : 𝕊^n`;
- the continuous linear map `A : E →L[ℝ] 𝕊^n`;
- the feasible set `Q : Set E` only for the optimal-value surface.

Derived API:
- the source-facing objective specialization `smoothedSemidefiniteObjective`;
- its textbook pointwise expansion;
- the canonical optimal-value surface
  `(SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)).optimalValue`.

Source/core/bridge triage:
- source-facing: `smoothedSemidefiniteObjective`;
- core/canonical: `logSumExpMaxEigenvalueSmoothing`,
  `SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)`;
- bridge/view: the pointwise expansion theorem and the specialized owner checks below.

The previous version introduced a second public optimal-value definition that was only the Chapter
1 constrained-problem optimal-value owner under a new local name, and also fixed the ambient
decision space to the textbook coordinate model `ℝ^m`. This refinement keeps the source-facing
objective specialization, deletes that duplicate optimal-value wheel, and exposes the affine
composition through an arbitrary real module `E`, with `ℝ^m` available as the intended concrete
specialization.
-/

/-- Definition 6.48: for a symmetric matrix `C ∈ 𝕊^n`, a continuous linear map
`A : E →L[ℝ] 𝕊^n`, and
`μ > 0`, the smoothed semidefinite objective is the Definition 6.47 smoothing evaluated at
`C + A(y)`. The textbook case `E = ℝ^m` is the intended specialization. -/
abbrev smoothedSemidefiniteObjective
    (n : ℕ) (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) : E → ℝ :=
  fun y ↦ logSumExpMaxEigenvalueSmoothing μ (C + A y)

/-- Evaluating the smoothed semidefinite objective recovers the textbook formula
`f_μ(C + A(y))`. -/
theorem smoothedSemidefiniteObjective_apply
    (n : ℕ) (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y : E) :
    smoothedSemidefiniteObjective n μ C A y =
      (μ : ℝ) *
        Real.log (∑ i : Fin n, Real.exp (eigenvalues (C + A y) i / (μ : ℝ))) := by
  simpa [smoothedSemidefiniteObjective] using
    logSumExpMaxEigenvalueSmoothing_eq μ (C + A y)

variable (μ : {μ : ℝ // 0 < μ}) (Q : Set E) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)

/- Definition 6.48 uses the Chapter 1 constrained optimal-value owner directly for the notation
`φ_μ^*`. -/
recall SetConstrainedMinimizationProblem.optimalValue
recall SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

set_option linter.hashCommand false in
#check
  (SetConstrainedMinimizationProblem.mk Q (smoothedSemidefiniteObjective n μ C A)).optimalValue

set_option linter.hashCommand false in
#check
  (show
      (SetConstrainedMinimizationProblem.mk Q
        (smoothedSemidefiniteObjective n μ C A)).optimalValue =
      sInf ((fun y : E ↦ (smoothedSemidefiniteObjective n μ C A y : EReal)) '' Q) from
    (SetConstrainedMinimizationProblem.mk Q
      (smoothedSemidefiniteObjective n μ C A)).optimalValue_eq_sInf_image)

end

end

/-! ### Proposition_6_48 (from Chap06) -/
noncomputable section

open LinearEstimatingCertificate
open scoped BigOperators

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/- Proposition 6.48 lies in the chapter's averaged primal-dual gap / Fenchel-conjugacy domain.

Mandatory domain-style sampling before refinement:
- `Finset.centerMass`, the canonical owner for the averaged dual iterate `ν_t`;
- `linearEstimatingWeightSum`, `linearEstimatingWeightSum_def`, and
  `linearEstimatingAccuracyCertificate` in `Chap06/Definition_6_62`, the chapter owners for the
  shifted normalization factor and the source-facing certificate `\hat ℓ_t`;
- `fenchelConjugate` and `fenchelConjugate_apply` in `Chap06/Definition_6_1`, the chapter owner
  for `EReal`-valued Fenchel conjugates on the continuous dual;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the source-facing inner-product-space bridge
  built from `fenchelConjugate` via `innerₗ`;
- `StructuredObjectiveModel.adjointObjective_le_objective` in `Chap06/Proposition_6_4`, the
  chapter owner weak-duality pattern for primal/dual value functions.

Best owner abstraction:
- source-facing: Proposition 6.48's averaged-dual point
  `ν_t = (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (x_k))`, the source-facing
  certificate `\hat ℓ_t = linearEstimatingAccuracyCertificate ... t`, and the resulting gap
  bound;
- core/canonical: `Finset.centerMass`, `linearEstimatingAccuracyCertificate`,
  `linearEstimatingWeightSum`, `fenchelConjugate`, and `innerₗ`;
- bridge/view: the theorem-local dual value
  `ν ↦ inf_x (\bar f(x) + ⟪ν, u(x)⟫) - Φ*(ν)` written directly through `fenchelConjugate`.

Primitive data:
- the feasible set `Q`, certificate data `f`, `gradF`, `ψ`, `xSeq`, and `a`;
- the primal/dual data `barF`, `phi`, and `u`;
- the index `t` and error budget `Cv_t`.

Derived API:
- the source-facing theorem below.

Source/core/bridge triage:
- source-facing: `averaged_duality_gap_bound_of_lower_certificate`;
- core/canonical: `linearEstimatingAccuracyCertificate` and `fenchelConjugate`;
- bridge/view: evaluation at `innerₗ F νt`.

The previous version replaced the source-facing certificate `\hat ℓ_t` by a free scalar and
introduced a second public dual owner just to package the Fenchel formula. This refinement keeps
the actual Chapter 6 certificate on the theorem surface, deletes the duplicate owner, and uses
only theorem-local `let` bindings for the averaged dual point and the corresponding Fenchel dual
value. -/

-- Proof sketch: weak duality for the primal value `\bar f(x_t) + Φ(u(x_t))` and the dual
-- function `\bar g(ν) = inf_x (\bar f(x) + ⟪ν, u(x)⟫) - Φ*(ν)` gives
-- `0 ≤ \bar f(x_t) + Φ(u(x_t)) - \bar g(ν_t)`. The assumed lower bound
-- `\hat ℓ_t ≤ \bar g(ν_t)` then yields
-- `\bar f(x_t) + Φ(u(x_t)) - \bar g(ν_t) ≤ \bar f(x_t) + Φ(u(x_t)) - \hat ℓ_t`, and the
-- certificate
-- hypothesis bounds this by
-- `C_{v,t} / ∑_{k < t} a_{k+1}`.
/-- Proposition 6.48: let
`ν_t = (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (x_k))`.
If the Chapter 6 certificate `\hat ℓ_t = linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t`
is a lower bound for the dual value
`\bar g(ν_t) = inf_x (\bar f(x) + ⟪ν_t, u(x)⟫) - Φ*(ν_t)` and if the primal objective satisfies
`\bar f(x_t) + Φ(u(x_t)) - \hat ℓ_t ≤ C_{v,t} / linearEstimatingWeightSum a t`, then the
primal-dual gap at this averaged dual iterate lies in the canonical interval
`[0, C_{v,t} / linearEstimatingWeightSum a t]`. -/
theorem averaged_duality_gap_bound_of_lower_certificate
    (Q : Set E) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ)
    (barF : E → EReal) (phi : F → EReal) (u : E → F)
    (xSeq : ℕ → Q) (a : ℕ → ℝ) (t : ℕ) (Cv_t : ℝ)
    (hhatℓt :
      let νt := (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (xSeq k : E))
      let dualObj : F → EReal := fun ν ↦
        sInf (Set.range fun x : E ↦ barF x + ((inner ℝ ν (u x) : ℝ) : EReal)) -
          fenchelConjugate phi (innerₗ F ν)
      (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤ dualObj νt)
    (hcertificate :
      barF (xSeq t : E) + phi (u (xSeq t : E)) -
          (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤
        ((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal)) :
    let νt := (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (xSeq k : E))
    let dualObj : F → EReal := fun ν ↦
      sInf (Set.range fun x : E ↦ barF x + ((inner ℝ ν (u x) : ℝ) : EReal)) -
        fenchelConjugate phi (innerₗ F ν)
    barF (xSeq t : E) + phi (u (xSeq t : E)) - dualObj νt ∈
      Set.Icc 0 (((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal)) := by
  sorry
