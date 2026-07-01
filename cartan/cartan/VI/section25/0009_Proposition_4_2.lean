import cartan.VI.section25.«0007_Theorem_VI_4_extra_7»
import cartan.VI.section25.«0008_Proposition_4_I»

open scoped Manifold Topology

universe u v w

-- Semantic recall tool unavailable in this session; this statement is aligned with
-- `Mathlib.Geometry.Manifold.Complex`.

-- Declarations for this item will be appended below by the statement pipeline.

/-- Proposition 4.2. If a holomorphic function on a preconnected complex manifold has a relative
maximum of `|f|` at a point `a`, then the function is constant. -/
theorem eq_const_of_mdifferentiable_of_isLocalMax_norm
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {X : Type w} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X] [PreconnectedSpace X]
    {f : X → ℂ} {a : X} (hf : MDiff f) (hmax : IsLocalMax (norm ∘ f) a) :
    f = Function.const X (f a) := by
  have hnorm : ∀ᶠ y in 𝓝 a, ‖f y‖ = ‖f a‖ :=
    Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax
      (Filter.Eventually.of_forall fun y ↦ hf y) hmax
  have hnorm_add : ∀ᶠ y in 𝓝 a, ‖f y + f a‖ = ‖f a + f a‖ :=
    Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax
      (Filter.Eventually.of_forall fun y ↦ (hf.add mdifferentiable_const) y) hmax.norm_add_self
  have heq : f =ᶠ[𝓝 a] Function.const X (f a) := by
    filter_upwards [hnorm, hnorm_add] with y hy hy_add
    exact eq_of_norm_eq_of_norm_add_eq hy <| by
      simpa only [hy, SameRay.rfl.norm_add] using hy_add
  rcases eventually_nhds_iff.mp heq with ⟨U, hU, hU_open, haU⟩
  have hU_eq : Set.EqOn f (Function.const X (f a)) U := fun y hy ↦ hU y hy
  exact eq_of_eqOn_nonempty_open_of_mdifferentiable hU_open ⟨a, haU⟩ hf mdifferentiable_const hU_eq
