import Mathlib
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_5
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_8
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_9
import SmoothManifolds_Lee_2012.Chap01.Sec01_04.Example_1_33

open Projectivization
open scoped ContDiff LinearAlgebra.Projectivization Manifold Torus

-- Domain sampling pass: the primary domain here is smooth-manifold `ContMDiff`.
-- Sampled owner declarations:
-- * mathlib: `contMDiff_circleExp`
-- * mathlib: `contMDiff_coe_sphere`
-- * mathlib: `contMDiffAt_pi_space`
-- * project: `contMDiff_pi_iff` from `Ch2/Proposition_2_12`
-- The owner abstraction for finite products is `ContMDiff ... (ModelWithCorners.pi I) ...`.
-- The family `I` of models and the family `M` of manifolds are primitive data; coordinate
-- projections are derived `bridge/view` API and should therefore reuse `contMDiff_pi_iff`
-- instead of keeping a parallel `Fin`-indexed owner.

universe u𝕜 uι uE uM uN uH

/-- Example 2.13 (1): any map from a zero-dimensional smooth manifold to a smooth manifold without
boundary is smooth. -/
theorem zero_dimensional_manifold_to_boundaryless_contMDiff
    {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [IsManifold (𝓡 0) ∞ M]
    {n : ℕ} {N : Type uN} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (f : M → N) :
    ContMDiff (𝓡 0) (𝓡 n) ∞ f := by
  let _ : DiscreteTopology M :=
    ChartedSpace.discreteTopology (H := EuclideanSpace ℝ (Fin 0)) (M := M)
  -- A zero-dimensional modeled manifold is discrete, so every map out of it is smooth.
  simpa using
    (contMDiff_of_discreteTopology (I := 𝓡 0) (I' := 𝓡 n)
      (n := (∞ : WithTop ℕ∞)) (f := f))

/-- Example 2.13 (2): any map from a zero-dimensional smooth manifold to a smooth manifold with
boundary is smooth. -/
theorem zero_dimensional_manifold_to_boundary_contMDiff
    {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [IsManifold (𝓡 0) ∞ M]
    {n : ℕ} {N : Type uN} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) N] [IsManifold (𝓡∂ (n + 1)) ∞ N]
    (f : M → N) :
    ContMDiff (𝓡 0) (𝓡∂ (n + 1)) ∞ f := by
  let _ : DiscreteTopology M :=
    ChartedSpace.discreteTopology (H := EuclideanSpace ℝ (Fin 0)) (M := M)
  -- The same discrete-source argument applies for manifolds with boundary.
  simpa using
    (contMDiff_of_discreteTopology (I := 𝓡 0) (I' := 𝓡∂ (n + 1))
      (n := (∞ : WithTop ℕ∞)) (f := f))

/-- Example 2.13 (3): the standard map `ε : ℝ → S¹`, `t ↦ e^{2π i t}`, is smooth. -/
theorem circle_fourier_exp_contMDiff :
    ContMDiff (𝓘(ℝ)) (𝓡 1) ∞ (fun t : ℝ ↦ Circle.exp (2 * Real.pi * t)) := by
  have hmul : ContMDiff (𝓘(ℝ)) 𝓘(ℝ) ∞ (fun t : ℝ ↦ (2 * Real.pi) * t) := by
    -- The phase function is an affine real map, hence smooth.
    simpa using (contMDiff_const.mul contMDiff_id)
  -- Compose the smooth exponential parametrization of the circle with the smooth phase map.
  simpa [Function.comp] using contMDiff_circleExp.comp hmul

/-- Helper for Example 2.13: smoothness of a map into the `n`-torus is equivalent to smoothness
of all of its circle-valued coordinate functions. -/
theorem torus_contMDiff_pi_bridge (n : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → 𝕋^{n}} :
    ContMDiff (𝓡 n) (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1) ∞ f ↔
      ∀ i : Fin n, ContMDiff (𝓡 n) (𝓡 1) ∞ (fun x ↦ f x i) := by
  constructor
  · intro h i x
    have hx := h x
    rw [contMDiffAt_iff_target] at hx ⊢
    constructor
    · exact (continuous_apply i).continuousAt.comp hx.1
    · exact contMDiffAt_pi_space.1 hx.2 i
  · intro h x
    rw [contMDiffAt_iff_target]
    constructor
    · exact continuousAt_pi.2 fun i ↦ (h i x).continuousAt
    · refine contMDiffAt_pi_space.2 ?_
      intro i
      exact (contMDiffAt_iff_target.1 (h i x)).2

/-- Example 2.13 (4): the coordinatewise map `εⁿ : ℝⁿ → 𝕋ⁿ`,
`x ↦ (e^{2π i x¹}, …, e^{2π i xⁿ})`, is smooth. -/
theorem torus_coordinatewise_fourier_exp_contMDiff (n : ℕ) :
    ContMDiff
      (𝓡 n)
      (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1)
      ∞
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        (fun i ↦ Circle.exp (2 * Real.pi * x i) : 𝕋^{n})) := by
  -- Smoothness into a finite product manifold reduces to smoothness of each component.
  rw [torus_contMDiff_pi_bridge]
  intro i
  have hproj :
      ContMDiff (𝓡 n) (𝓘(ℝ)) ∞
        (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) := by
    -- Each Euclidean coordinate projection is a smooth map.
    simpa using
      (((contDiff_piLp_apply (p := (2 : ENNReal)) (i := i)) :
          ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) ↦ x i)).contMDiff :
        ContMDiff (𝓡 n) (𝓘(ℝ)) ∞
          (fun x : EuclideanSpace ℝ (Fin n) ↦ x i))
  -- Compose the one-dimensional Fourier exponential with the chosen coordinate projection.
  simpa [Function.comp] using circle_fourier_exp_contMDiff.comp hproj

/- Example 2.13 (5): the inclusion `ι : Sⁿ ↪ ℝ^(n+1)` is smooth; this is exactly the canonical
mathlib owner `contMDiff_coe_sphere` specialized to the Euclidean sphere model. -/
recall contMDiff_coe_sphere {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ∞ω} {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) m ((↑) : Metric.sphere (0 : E) 1 → E)

/-- Helper for Example 2.13: the punctured Euclidean space `ℝ^(n+1) \ {0}` viewed as the canonical
open submanifold of `ℝ^(n+1)`. -/
def puncturedRealEuclidean (n : ℕ) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨{ x | x ≠ 0 }, isOpen_ne⟩

/-- Helper for Example 2.13: membership in the punctured Euclidean open subset is exactly
nonvanishing. -/
@[simp] theorem mem_puncturedRealEuclidean_iff {n : ℕ}
    {x : EuclideanSpace ℝ (Fin (n + 1))} :
    x ∈ puncturedRealEuclidean n ↔ x ≠ 0 :=
  Iff.rfl

/-- Helper for Example 2.13: every standard affine chart on `ℝPⁿ` already belongs to the smooth
maximal atlas. -/
theorem real_projective_chart_mem_maximal_atlas (n : ℕ) (i : Fin (n + 1)) :
    realProjectiveChart n i ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) := by
  have hAtlas : realProjectiveChart n i ∈ atlas (EuclideanSpace ℝ (Fin n)) (ℝP[n]) := by
    change realProjectiveChart n i ∈ { e | ∃ j : Fin (n + 1), e = realProjectiveChart n j }
    exact ⟨i, rfl⟩
  -- Standard projective charts are chart members first, hence smooth maximal-atlas members.
  exact IsManifold.subset_maximalAtlas hAtlas

/-- Helper for Example 2.13: if the `i`th homogeneous coordinate of a punctured vector is nonzero,
then its projective class lies in the `i`th affine chart domain. -/
theorem real_projective_quotient_mem_chart_domain (n : ℕ) (i : Fin (n + 1))
    (z : { x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0 })
    (hzi : (z : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0) :
    mk' ℝ z ∈ realProjectiveChartDomain n i := by
  -- Rewrite the projective point using its chosen punctured representative.
  simpa [Projectivization.mk'_eq_mk] using
    (realProjectiveChartDomain_mk n i (z : EuclideanSpace ℝ (Fin (n + 1))) z.2).2 hzi

/-- Helper for Example 2.13: on a punctured representative, the standard affine chart is the usual
coordinate ratio map. -/
theorem real_projective_quotient_map_restricted_chart_formula (n : ℕ) (i : Fin (n + 1))
    (z : { x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0 })
    (_hzi : (z : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0) :
    realProjectiveChart n i (mk' ℝ z) =
      WithLp.toLp 2 (fun j ↦
        (z : EuclideanSpace ℝ (Fin (n + 1))) (i.succAbove j) /
          (z : EuclideanSpace ℝ (Fin (n + 1))) i) := by
  -- The chart formula is exactly the textbook homogeneous-coordinate quotient formula.
  simpa [Projectivization.mk'_eq_mk] using
    (realProjectiveChart_mk n i (z : EuclideanSpace ℝ (Fin (n + 1))) z.2)

/-- Helper for Example 2.13: every punctured real homogeneous vector has a nonzero coordinate. -/
theorem punctured_real_euclidean_exists_nonzero_coord (n : ℕ)
    (z : { x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0 }) :
    ∃ i : Fin (n + 1), (z : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0 := by
  classical
  by_contra h
  apply z.2
  ext i
  by_contra hzi
  exact h ⟨i, hzi⟩

/-- Helper for Example 2.13: on the locus where the `i`th homogeneous coordinate is nonzero, the
affine ratio map is smooth. -/
theorem real_projective_ratio_map_contDiffOn (n : ℕ) (i : Fin (n + 1)) :
    ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        WithLp.toLp 2 (fun j ↦ z (i.succAbove j) / z i))
      { z : EuclideanSpace ℝ (Fin (n + 1)) | z i ≠ 0 } := by
  refine contDiffOn_piLp' (p := (2 : ENNReal)) ?_
  intro j
  -- Each affine coordinate is a quotient of two smooth ambient coordinate projections.
  exact
    (((contDiff_piLp_apply (p := (2 : ENNReal)) (i := i.succAbove j)) :
        ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z (i.succAbove j))).contDiffOn).div
      (((contDiff_piLp_apply (p := (2 : ENNReal)) (i := i)) :
          ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i)).contDiffOn)
      (fun z hz ↦ hz)

/-- Helper for Example 2.13: if one homogeneous coordinate is nonzero at a punctured vector, then
the quotient map is smooth there through the corresponding standard affine chart. -/
theorem real_projective_quotient_map_contMDiffAt_of_nonzero_coord (n : ℕ)
    (i : Fin (n + 1))
    (z : puncturedRealEuclidean n)
    (hzi : (z : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0) :
    ContMDiffAt (𝓡 (n + 1)) (𝓡 n) ∞
      (fun w : puncturedRealEuclidean n ↦ mk' ℝ w) z := by
  let ratio : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
    fun w ↦
      WithLp.toLp 2 (fun j ↦ w (i.succAbove j) / w i)
  have hratio_at :
      ContDiffAt ℝ ∞ ratio (z : EuclideanSpace ℝ (Fin (n + 1))) := by
    -- The chartwise ratio map is smooth on the open nonvanishing-coordinate locus.
    exact (real_projective_ratio_map_contDiffOn n i).contDiffAt <| by
      have hsOpen : IsOpen { w : EuclideanSpace ℝ (Fin (n + 1)) | w i ≠ 0 } := by
        simpa using
          isOpen_ne_fun
            ((PiLp.continuous_apply 2 _ i) :
              Continuous fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w i)
            continuous_const
      exact hsOpen.mem_nhds hzi
  have hratio_subtype :
      ContMDiffAt (𝓡 (n + 1)) (𝓡 n) ∞
        (fun w : puncturedRealEuclidean n ↦ ratio w) z := by
    -- Passing to the punctured open subtype preserves this ambient smoothness statement.
    rw [contMDiffAt_subtype_iff (U := puncturedRealEuclidean n) (f := ratio) (x := z)]
    exact hratio_at.contMDiffAt
  have hsymm :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞
        (realProjectiveChart n i).symm (ratio (z : EuclideanSpace ℝ (Fin (n + 1)))) := by
    have hmax := real_projective_chart_mem_maximal_atlas n i
    -- The inverse affine chart is smooth on its Euclidean target.
    simpa [ratio] using
      contMDiffAt_symm_of_mem_maximalAtlas hmax
        (by simp : ratio (z : EuclideanSpace ℝ (Fin (n + 1))) ∈ Set.univ)
  have hcomp :
      ContMDiffAt (𝓡 (n + 1)) (𝓡 n) ∞
        ((realProjectiveChart n i).symm ∘ fun w : puncturedRealEuclidean n ↦ ratio w) z := by
    -- Compose the smooth ratio map with the smooth inverse affine chart.
    exact hsymm.comp z hratio_subtype
  have hEq :
      (fun w : puncturedRealEuclidean n ↦ mk' ℝ w) =ᶠ[nhds z]
        ((realProjectiveChart n i).symm ∘ fun w : puncturedRealEuclidean n ↦ ratio w) := by
    have hsOpen : IsOpen { w : puncturedRealEuclidean n | (w : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0 } := by
      simpa using
        isOpen_ne_fun
          (((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val) :
            Continuous fun w : puncturedRealEuclidean n ↦
              (w : EuclideanSpace ℝ (Fin (n + 1))) i)
          continuous_const
    have hsNhds :
        { w : puncturedRealEuclidean n | (w : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0 } ∈ nhds z :=
      hsOpen.mem_nhds hzi
    filter_upwards [hsNhds] with w hw
    have hwDomain : mk' ℝ w ∈ realProjectiveChartDomain n i :=
      real_projective_quotient_mem_chart_domain n i w hw
    have hleft := OpenPartialHomeomorph.left_inv (realProjectiveChart n i) hwDomain
    -- Route correction: identify the quotient map locally with the inverse affine chart applied to
    -- the explicit homogeneous-coordinate ratio map.
    rw [real_projective_quotient_map_restricted_chart_formula n i w hw] at hleft
    simpa [Function.comp, ratio] using hleft.symm
  exact hcomp.congr_of_eventuallyEq hEq

/-- Helper for Example 2.13: the projective quotient map is smooth on the canonical punctured
Euclidean open submanifold. -/
theorem real_projective_quotient_map_on_punctured_open_contMDiff (n : ℕ) :
    ContMDiff
      (𝓡 (n + 1))
      (𝓡 n)
      ∞
      (fun z : puncturedRealEuclidean n ↦ mk' ℝ z) := by
  intro z
  -- Choose a nonzero homogeneous coordinate and use the corresponding affine chart.
  rcases punctured_real_euclidean_exists_nonzero_coord n z with ⟨i, hzi⟩
  exact real_projective_quotient_map_contMDiffAt_of_nonzero_coord n i z hzi

/-- Example 2.13 (6): the quotient map `π : ℝ^(n+1) \ {0} → ℝPⁿ` is smooth. -/
theorem real_projectivization_quotient_contMDiff (n : ℕ) :
    ContMDiff
      (𝓡 (n + 1))
      (𝓡 n)
      ∞
      (fun z : puncturedRealEuclidean n ↦ mk' ℝ z) := by
  exact real_projective_quotient_map_on_punctured_open_contMDiff n

/-- Helper for Example 2.13: the sphere inclusion lifts smoothly into the punctured Euclidean open
submanifold. -/
theorem sphere_lift_to_punctured_open_contMDiff (n : ℕ) :
    ContMDiff
      (𝓡 n)
      (𝓡 (n + 1))
      ∞
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        (⟨(x : EuclideanSpace ℝ (Fin (n + 1))),
          Metric.ne_of_mem_sphere x.property one_ne_zero⟩ : puncturedRealEuclidean n)) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  let lift :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        puncturedRealEuclidean n :=
    fun x ↦
      ⟨(x : EuclideanSpace ℝ (Fin (n + 1))),
        Metric.ne_of_mem_sphere x.property one_ne_zero⟩
  have hambient :
      ContMDiff
        (𝓡 n)
        (𝓡 (n + 1))
        ∞
        (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
          ((lift x : puncturedRealEuclidean n) : EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The lifted map has the usual sphere inclusion as its ambient-value composition.
    simpa [lift] using
      (contMDiff_coe_sphere :
        ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
          ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
            EuclideanSpace ℝ (Fin (n + 1))))
  -- Recover smoothness of the lift itself from smoothness of its ambient-value composition.
  exact (ContMDiff.subtypeVal_comp_iff (puncturedRealEuclidean n) lift).1 hambient

/-- Example 2.13 (7): the restriction `q : Sⁿ → ℝPⁿ` of the projective quotient map to the sphere
is smooth. -/
theorem sphere_to_realProjectiveSpace_contMDiff (n : ℕ) :
    ContMDiff
      (𝓡 n)
      (𝓡 n)
      ∞
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        mk ℝ (x : EuclideanSpace ℝ (Fin (n + 1)))
          (Metric.ne_of_mem_sphere x.property one_ne_zero)) := by
  let lift :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        puncturedRealEuclidean n :=
    fun x ↦
      ⟨(x : EuclideanSpace ℝ (Fin (n + 1))),
        Metric.ne_of_mem_sphere x.property one_ne_zero⟩
  have hlift : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ lift :=
    sphere_lift_to_punctured_open_contMDiff n
  have hquot :
      ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞
        (fun z : puncturedRealEuclidean n ↦ mk' ℝ z) :=
    real_projective_quotient_map_on_punctured_open_contMDiff n
  -- Compose the sphere lift into the punctured ambient space with the canonical quotient map.
  simpa [lift, Function.comp, Projectivization.mk'_eq_mk] using hquot.comp hlift

/-- Example 2.13 (8): for a finite product of smooth manifolds, each coordinate projection is
smooth. -/
theorem manifold_pi_projection_contMDiff
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {ι : Type uι} [Fintype ι]
    {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {H : ι → Type uH} [∀ i, TopologicalSpace (H i)]
    {I : (i : ι) → ModelWithCorners 𝕜 (E i) (H i)}
    {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
    [∀ i, IsManifold (I i) ∞ (M i)]
    (i : ι) :
    ContMDiff (ModelWithCorners.pi I) (I i) ∞ (fun x : ∀ j, M j ↦ x i) := by
  have hId : ContMDiff (ModelWithCorners.pi I) (ModelWithCorners.pi I) ∞
      (id : (∀ j, M j) → ∀ j, M j) := contMDiff_id
  intro x
  have hx := hId x
  rw [contMDiffAt_iff_target] at hx ⊢
  constructor
  · exact (continuous_apply i).continuousAt.comp hx.1
  · exact (contMDiffAt_pi_space.1 hx.2) i
