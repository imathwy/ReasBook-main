import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/-- Classical decidability for propositions, used to evaluate the interior-membership branch in
`universalBarrierAmbient`. -/
local instance {p : Prop} : Decidable p := Classical.propDecidable p

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.4.2.2 lies in the chapter's universal-barrier / finite-dimensional convex-geometry
domain.

Sampled owner-style declarations:
* `universalBarrierVolume` from `Definition_5_4_2_2`, the source-facing owner of the volume term
  `V(x)`;
* `polarSetAt` and `mem_polarSetAt_iff` from `Definition_5_4_2_1`, the geometric owner behind
  that volume term;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for self-concordant
  barriers on open convex domains;
* `polarSetAt_isCompact_convex` from `Theorem_5_4_2_1`, the preceding subsection's intrinsic
  finite-dimensional geometry theorem for the same based-polar construction.

Best owner abstraction:
* source-facing: the intrinsic universal barrier
  `universalBarrier c₁ Q : interior Q → ℝ`;
* core/canonical: `universalBarrierVolume Q x` together with
  `IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* bridge/view: the ambient totalization
  `universalBarrierAmbient c₁ Q : E → ℝ`, used only to feed the Chapter 5 barrier owner.

Primitive data:
* a finite-dimensional real inner-product space `E`;
* a set `Q : Set E`;
* the proper-convex regime on `Q`: convexity together with the absence of affine lines;
* a scaling constant `c₁`.

Derived API:
* the positivity bridge `universalBarrierVolume_pos`;
* the intrinsic barrier owner
  `universalBarrier c₁ Q : interior Q → ℝ`;
* the source-facing identity `universalBarrier_eq_log_volume`;
* the ambient bridge `universalBarrierAmbient c₁ Q : E → ℝ`;
* the Chapter 5 barrier owner
  `IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q)`;
* the intrinsic dimension factor `Module.finrank ℝ E`, which recovers the textbook dimension `n`
  on `EuclideanSpace ℝ (Fin n)`.

The previous version unnecessarily fixed the ambient space to `EuclideanSpace ℝ (Fin n)`. The
based-polar volume owner and the source formula `x ↦ c₁ log V(x)` are already intrinsic, so the
refined file keeps the same source mathematics while moving the public API to the canonical
finite-dimensional real inner-product owner level. The proper-convex/no-affine-line hypotheses are
kept only on the positivity bridge `universalBarrierVolume_pos` and on the final
self-concordance theorem, where they actually matter; the owner itself is just the source formula
`x ↦ c₁ log V(x)`. The ambient zero-extension is retained only as a thin bridge because
`IsSelfConcordantBarrierOnWith` is formulated for ambient maps `E → ℝ`. The theorem-level
positive constants are exposed on the canonical `NNRealˣ` surface rather than as ad hoc
positive-real subtypes. The main theorem still drops the redundant nonempty-interior and
positive-dimensional guards: the owner-level conclusion is already vacuous when `interior Q = ∅`
or `Module.finrank ℝ E = 0`, so those source-mirroring hypotheses do not belong in the public
API.
-/

-- Proof sketch: by Theorem 5.4.2.1 the based polar `polarSetAt Q x` is compact and has nonempty
-- interior under the proper-convex/no-affine-line hypotheses, so its finite-dimensional volume is
-- strictly positive.
/-- For a proper convex set `Q`, every interior based-polar body has strictly positive volume. This
positivity is the bridge that makes `log (universalBarrierVolume Q x)` the actual universal-barrier
formula rather than Lean's junk-value extension outside the proper-convex regime. -/
theorem universalBarrierVolume_pos
    (Q : Set E)
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (x : interior Q) :
    0 < universalBarrierVolume Q x := sorry

/-- The universal barrier attached to a proper convex set `Q` with scaling constant `c₁`, defined
on `interior Q` by the textbook formula `x ↦ c₁ * log V(x)`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the usual `ℝⁿ` formula. -/
def universalBarrier
    (c₁ : ℝ) (Q : Set E) :
    interior Q → ℝ :=
  fun x ↦ c₁ * Real.log (universalBarrierVolume Q x)

/- Evaluating `universalBarrier c₁ Q` gives the scaled logarithm of
`universalBarrierVolume Q`. -/
@[simp] theorem universalBarrier_eq_log_volume
    (c₁ : ℝ) (Q : Set E) (x : interior Q) :
    universalBarrier c₁ Q x =
      c₁ * Real.log (universalBarrierVolume Q x) := by
  simp [universalBarrier]

/-- The ambient zero-extension of `universalBarrier c₁ Q`, used only to
state the Chapter 5 self-concordant-barrier owner on the open set `interior Q`. -/
def universalBarrierAmbient
    (c₁ : ℝ) (Q : Set E) :
    E → ℝ :=
  fun x ↦
    if hx : x ∈ interior Q then
      universalBarrier c₁ Q ⟨x, hx⟩
    else
      0

/- On interior points of `Q`, the ambient bridge
`universalBarrierAmbient c₁ Q` agrees with the intrinsic owner `universalBarrier c₁ Q`. -/
@[simp] theorem universalBarrierAmbient_eq_universalBarrier
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) :
    universalBarrierAmbient c₁ Q x = universalBarrier c₁ Q ⟨x, hx⟩ := by
  simp [universalBarrierAmbient, hx]

-- Proof sketch: use the universal-barrier volume definition from Definition 5.4.2.2 and the
-- sharp one-dimensional marginal moment inequalities from the preceding subsection. These yield
-- standard self-concordance for `x ↦ c₁ log V(x)` on `interior Q` together with the barrier
-- gradient bound of order `n`, uniformly for absolute positive constants `c₁` and `c₂`. The
-- intrinsic formulation expresses this parameter as `c₂ * Module.finrank ℝ E`, which
-- specializes to the textbook `c₂ * n` on `EuclideanSpace ℝ (Fin n)`. Empty-interior and
-- zero-dimensional cases are already covered vacuously by the same owner-level statement, so
-- they do not need extra public guards.
/-- Theorem 5.4.2.2, stated with the intrinsic owner and its ambient bridge: there exist absolute
positive constants `c₁` and `c₂` such that for every proper convex set `Q` in a finite-dimensional
real inner-product space `E`, the ambient bridge of the universal barrier
`x ↦ c₁ * log (V(x))` is a `((c₂ : NNReal) * Module.finrank ℝ E)`-self-concordant barrier on
`interior Q`. Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook
`(c₂ * n)` parameter. The textbook nonempty-interior and `n ≥ 1` regime are the nonvacuous
special cases, but they are redundant for the intrinsic owner-level conclusion itself. -/
theorem exists_absolute_constants_universalBarrier_isSelfConcordantBarrierOnWith :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E}
        (hQ_convex : Convex ℝ Q)
        (hQ_noAffineLine :
          ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q),
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := sorry

end
