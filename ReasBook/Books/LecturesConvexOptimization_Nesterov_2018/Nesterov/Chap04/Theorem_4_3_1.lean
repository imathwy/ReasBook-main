import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_55
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Assumption_4_3_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 4.3.1 lies in the second-order oracle / lower-complexity domain on `ℝ^n`.

Sampled owner-style declarations:
* `IsSecondOrderSpanSequence` in `Assumption_4_3_1`, the chapter owner for the second-order
  affine-span restriction;
* `bestFunctionValueUpTo` in `Chap03/Definition_3_55`, the chapter owner for the best sampled
  objective value on a finite prefix;
* `HasLipschitzContinuousHessian` and the notation `C22[L]` in `Definition_4_2_7`, the chapter
  owner for globally Hessian-Lipschitz objectives;
* the project-standard positive-parameter owner `NNRealˣ`, used throughout the project whenever a
  displayed denominator is mathematically required to stay strictly positive;
* `SatisfiesSpanCondition` in `Chap02/Definition_2_9`, the earlier chapter pattern showing that a
  lower-complexity method should be modeled by its primitive iterate family, with the span
  restriction kept as a separate theorem-level hypothesis rather than as bundled data.

Source/core/bridge triage:
* source-facing: the cubic hard-instance lower bound for a second-order method complexity profile;
* core/canonical: `IsSecondOrderSpanSequence`, `bestFunctionValueUpTo`, and `f ∈ C22[L]`;
* bridge/view: the trajectory-value specialization `fun i ↦ f (testPoints f x0 i)` of the owner
  sampled-minimum API.

Primitive data:
* the iterate family `testPoints`;
* the strictly positive complexity profile `complexityConstant`.

Derived API:
* the initialization law `testPoints f x0 0 = x0`;
* the second-order span restriction on every `C²` objective;
* the uniform guarantee on `bestFunctionValueUpTo` for every Hessian-Lipschitz objective.

The previous file bundled the theorem hypotheses into a local `SecondOrderMethod` structure and
redefined the sampled-prefix minimum locally. The refinement keeps the source-facing theorem, but
uses the chapter owners `IsSecondOrderSpanSequence`, `bestFunctionValueUpTo`, and `C22[L]`
directly, leaving only the genuine primitive data as explicit inputs. The complexity denominator is
owned by `NNRealˣ`, so the displayed quantity `L_f ρ₀^3 / C_𝓜(k)` keeps its textbook
positive-denominator semantics instead of degenerating at `C_𝓜(k) = 0`.
-/

-- Proof sketch: apply the hard-instance family `f_t` with `t = 4m + 3` and start from `x₀ = 0`.
-- The span-sequence restriction keeps the first `k + 1` iterates in the coordinate subspaces
-- given by Corollary 4.3.1, so Lemma 4.3.2 identifies the best value among those iterates with
-- the hard-instance gap `f_k^* - f_t^* = (2 / 3) (m + 1)`. Proposition 4.3.2 supplies the
-- Hessian-Lipschitz constant on the canonical `C22[...]` surface, Proposition 4.3.1 controls the
-- distance from `0` to the minimizer, and rearranging the assumed estimate (4.3.7) yields the
-- displayed upper bound.
/-- Theorem 4.3.1: let the Hessian of the objective be Lipschitz continuous with constant `L_f`,
and let a second-order method satisfy the textbook second-order information restriction and the
guarantee
`min_{0 ≤ i ≤ k} f(x_i) - f(x^*) ≤ L_f ρ₀^3 / C_𝓜(k)` for every starting point
`x₀` with `‖x₀ - x^*‖ ≤ ρ₀`. Then, whenever `k = 3m + 2` with `m + 1 ≤ n / 4`
(equivalently `4 * (m + 1) ≤ n`), the strictly positive complexity quantity satisfies
`C_𝓜(k) ≤ 36 (k + 1)^{3.5}`. -/
theorem secondOrderMethod_complexityConstant_le_cubicHardInstance_bound
    (testPoints : (E → ℝ) → E → ℕ → E)
    (complexityConstant : ℕ → NNRealˣ)
    (htestPoints_zero :
      ∀ (f : E → ℝ) (x0 : E), testPoints f x0 0 = x0)
    (hspan :
      ∀ (f : E → ℝ) (_ : ContDiff ℝ 2 f) (x0 : E),
        IsSecondOrderSpanSequence f (testPoints f x0))
    (hguarantee :
      ∀ (f : E → ℝ) (Lf : NNReal) (_ : f ∈ C22[Lf])
        (xStar x0 : E) (rho0 : ℝ) (k : ℕ),
        IsMinOn f Set.univ xStar →
          ‖x0 - xStar‖ ≤ rho0 →
            bestFunctionValueUpTo (fun i ↦ f (testPoints f x0 i)) k - f xStar ≤
              (Lf : ℝ) * rho0 ^ 3 / (complexityConstant k : ℝ))
    {k m : ℕ} (hk : k = 3 * m + 2) (hm : m + 1 ≤ n / 4) :
    (complexityConstant k : ℝ) ≤
      36 * ((k + 1 : ℝ) ^ 3 * Real.sqrt (k + 1)) := sorry

end
