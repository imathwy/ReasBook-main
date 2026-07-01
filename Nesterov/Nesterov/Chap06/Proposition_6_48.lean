import Nesterov.Chap06.Definition_6_1
import Nesterov.Chap06.Definition_6_62

-- Declarations for this item will be appended below by the statement pipeline.

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
