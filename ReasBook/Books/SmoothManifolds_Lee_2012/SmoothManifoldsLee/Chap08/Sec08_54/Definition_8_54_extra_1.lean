import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Support
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_54.Proposition_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe u_𝕜 u_E uH uM

-- Domain sampling pass: this file lies in the smooth-manifold vector-field API. Relevant owner
-- declarations checked before refinement:
-- `VectorField.mpullbackWithin` from mathlib for chart pullbacks of vector fields,
-- root `tsupport` / `HasCompactSupport` from `Topology.Algebra.Support` for generic support
--   terminology,
-- and the canonical tangent-bundle trivialization owners
--   `Bundle.Trivialization.contMDiffOn_section_baseSet_iff` and
--   `TangentBundle.trivializationAt_apply`.
-- Primitive data here is only the dependent section `X : ∀ p, TangentSpace I p`; there is no
-- upstream generic support owner directly on dependent sections, so the source-facing vector-field
-- support API stays local but is generalized to the actual model data it uses.

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}
variable (X : ∀ p : M, TangentSpace I p)

/- Definition 8.54-extra-1 (source-facing support layer): in Lean, a rough vector field on `M` is
the dependent section `X : ∀ p : M, TangentSpace I p`; the associated map into the tangent bundle
is `T% X`, and the support clause is the closure of the nonvanishing set. -/
#check (T% X : M → TangentBundle I M)

namespace VectorField

/-- Applying a rough vector field to a smooth scalar-valued function gives the pointwise
directional derivative function. -/
def apply (X : ∀ p : M, TangentSpace I p) (f : C^∞⟮I, M; 𝕜⟯) : M → 𝕜 :=
  fun p ↦ mfderiv% f p (X p)

/-- Unfolding of the pointwise application of a rough vector field to a smooth function. -/
theorem apply_def (X : ∀ p : M, TangentSpace I p) (f : C^∞⟮I, M; 𝕜⟯) :
    VectorField.apply X f = fun p ↦ mfderiv% f p (X p) := rfl

/-- Pointwise evaluation of the application of a rough vector field to a smooth function. -/
theorem apply_apply (X : ∀ p : M, TangentSpace I p) (f : C^∞⟮I, M; 𝕜⟯) (p : M) :
    VectorField.apply X f p = mfderiv% f p (X p) := rfl

/-- The support of a vector field is the closure of the set where it does not vanish. -/
def support (X : ∀ p : M, TangentSpace I p) : Set M :=
  closure { p | X p ≠ 0 }

/-- Unfolding of the support of a vector field. -/
theorem support_def (X : ∀ p : M, TangentSpace I p) :
    VectorField.support X = closure { p | X p ≠ 0 } := rfl

/-- A vector field is compactly supported if its support is compact. -/
def HasCompactSupport (X : ∀ p : M, TangentSpace I p) : Prop :=
  IsCompact (VectorField.support X)

/-- Unfolding of compact support for a vector field. -/
theorem hasCompactSupport_def (X : ∀ p : M, TangentSpace I p) :
    VectorField.HasCompactSupport X ↔ IsCompact (VectorField.support X) := Iff.rfl

end VectorField

end

section

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable [IsManifold I (∞ : ℕ∞ω) M]
variable (X : ∀ p : M, TangentSpace I p)

/- Definition 8.54-extra-1 (core/canonical chart-component owner): for a rough vector field, the
preferred chart-side Euclidean representative is obtained by applying the tangent-bundle
trivialization `trivializationAt` to the section `T% X`; the preferred base chart is `chartAt H p`,
whose extended chart is `extChartAt I p`.
-/
#check Bundle.Trivialization.contMDiffOn_section_baseSet_iff
#check TangentBundle.trivializationAt_apply

#check (Continuous (T% X))
#check (ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X))

/-- Helper for Definition 8.54-extra-1: the preferred tangent-bundle trivialization at `p`
expresses `X q` by the manifold derivative of the preferred chart at `q`. -/
private lemma preferredChartCoordinate_eq_mfderiv
    (X : ∀ p : M, TangentSpace I p) (p q : M) (hq : q ∈ (chartAt H p).source) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) p ⟨q, X q⟩).2 =
      NormedSpace.fromTangentSpace (extChartAt I p q)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (extChartAt I p) q (X q)) := by
  have hqBase :
      q ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) p).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hq
  -- Rewrite the fiber coordinate through the linear map carried by the tangent-bundle
  -- trivialization at `p`.
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := ℝ)
    (e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) p)
    hqBase (X q)]
  -- Replace that linear map with the manifold derivative of the preferred chart.
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (H := H) (x₀ := p)
    (x := q) hq]
  -- On the model space, `fromTangentSpace` is the canonical identity identification.
  rfl

/-- Specializing the canonical tangent-bundle trivialization to the preferred chart `chartAt H p`
recovers the usual preferred-chart component formula written with `extChartAt I p`. -/
theorem preferred_chart_component_apply
    (p q : M) (hq : q ∈ (chartAt H p).source) (i : Fin n) :
    ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) p ⟨q, X q⟩).2).ofLp i =
      (NormedSpace.fromTangentSpace (extChartAt I p q)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (extChartAt I p) q (X q))).ofLp i := by
  -- First identify the full Euclidean chart-coordinate vector.
  have hcoord := preferredChartCoordinate_eq_mfderiv (I := I) X p q hq
  -- Then read off the requested scalar component.
  exact congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v.ofLp i) hcoord

end
