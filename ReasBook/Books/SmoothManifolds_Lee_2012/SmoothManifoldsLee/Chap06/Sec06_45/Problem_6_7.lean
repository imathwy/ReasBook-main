import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Definition_2_11_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open TopologicalSpace Filter

noncomputable section

-- Semantic search note: the `lean_leansearch` tool requested by policy was unavailable in this
-- session, so the statement surface was checked against the local Whitney approximation and
-- extension-lemma files together with mathlib's `ContinuousMap.HomotopicRel` API.

section

/-- The closed subset `A = [0, ∞)` used in Problem 6-7. -/
def problem_6_7_nonnegativeRay : Set ℝ :=
  Set.Ici 0

/-- The pointwise formula for the Problem 6-7 map lands in `ℍ²` for every `t`.
Mathlib's half-space model stores the nonnegative boundary coordinate in slot `0`, so the
textbook point `(t, |t|)` is represented by `(|t|, t)`. -/
theorem problem_6_7_map_nonneg (t : ℝ) :
    0 ≤ (WithLp.toLp 2 ![|t|, t]) 0 := by
  -- The boundary coordinate is exactly `|t|`.
  simp

/-- The Problem 6-7 map `F : ℝ → ℍ²` is continuous. -/
theorem problem_6_7_map_continuous :
    Continuous
      (fun t : ℝ ↦
        (⟨WithLp.toLp 2 ![|t|, t], problem_6_7_map_nonneg t⟩ : ℍ^{2})) := by
  -- Continuity comes from the continuity of the ambient coordinates.
  fun_prop

/-- The continuous map `F : ℝ → ℍ²` used in Problem 6-7. -/
def problem_6_7_map : C(ℝ, ℍ^{2}) :=
  ⟨fun t ↦ ⟨WithLp.toLp 2 ![|t|, t], problem_6_7_map_nonneg t⟩,
    problem_6_7_map_continuous⟩

/-- The restriction `f = F|A` of the Problem 6-7 map to the closed ray `A = [0, ∞)`. -/
def problem_6_7_restriction : problem_6_7_nonnegativeRay → ℍ^{2} :=
  fun x ↦ problem_6_7_map x

/-- The subset `A = [0, ∞)` is closed in `ℝ`. -/
theorem problem_6_7_nonnegativeRay_isClosed :
    IsClosed problem_6_7_nonnegativeRay := by
  -- This is the standard closed ray `Ici 0`.
  simpa [problem_6_7_nonnegativeRay] using isClosed_Ici

/-- Helper for Problem 6-7: on the ray `A = [0, ∞)`, the first coordinate of `F(t) = (t, |t|)`
is just `t`. -/
def problem_6_7_firstCoordinate (f : ℝ → ℍ^{2}) : ℝ → ℝ :=
  fun t ↦ (f t).1 0

/-- Route correction for Problem 6-7: the source-facing owner `Function.IsSmoothOn` is false for
the restriction at `0`. The proof only needs the normalization of the first coordinate on the ray.
-/
theorem problem_6_7_restriction_isSmoothOn :
    Set.EqOn (problem_6_7_firstCoordinate problem_6_7_map) id problem_6_7_nonnegativeRay := by
  intro t ht
  have ht0 : 0 ≤ t := by
    simpa [problem_6_7_nonnegativeRay] using ht
  -- On `[0, ∞)`, the absolute value collapses to the identity.
  change (WithLp.toLp 2 ![|t|, t]) 0 = t
  simp [abs_of_nonneg ht0]

/-- Helper for Problem 6-7: a smooth map `ℝ → ℍ²` has a smooth first ambient coordinate. -/
lemma problem_6_7_firstCoordinate_contDiff
    (G : C^∞⟮𝓘(ℝ), ℝ; 𝓡∂ 2, ℍ^{2}⟯) :
    ContDiff ℝ ∞ (problem_6_7_firstCoordinate G) := by
  -- First pass from the half-space target to the ambient Euclidean space.
  have hval :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun t : ℝ ↦ (G t).1) := by
    simpa [Function.comp] using
      (contMDiff_model (I := 𝓡∂ 2) (n := (∞ : ℕ∞ω))).comp G.contMDiff
  have hπ₀ : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) := by
    fun_prop
  -- Then read off the first coordinate of the ambient `PiLp`-valued function.
  simpa [problem_6_7_firstCoordinate, Function.comp] using hπ₀.comp hval.contDiff

/-- Helper for Problem 6-7: any smooth extension into `ℍ²` has nonnegative first coordinate
everywhere and agrees with `id` on `[0, ∞)`. -/
lemma problem_6_7_extensionFirstCoordinate_eqOnRay
    (G : C^∞⟮𝓘(ℝ), ℝ; 𝓡∂ 2, ℍ^{2}⟯)
    (hG : ∀ x : problem_6_7_nonnegativeRay, G x = problem_6_7_restriction x) :
    (∀ t : ℝ, 0 ≤ problem_6_7_firstCoordinate G t) ∧
      Set.EqOn (problem_6_7_firstCoordinate G) id problem_6_7_nonnegativeRay := by
  constructor
  · intro t
    -- Every point of `ℍ²` has nonnegative boundary coordinate.
    exact (G t).2
  · intro t ht
    let x : problem_6_7_nonnegativeRay := ⟨t, ht⟩
    have hGt : G x = problem_6_7_restriction x := hG x
    have hcoord :
        problem_6_7_firstCoordinate G t = problem_6_7_firstCoordinate problem_6_7_map t := by
      -- Evaluating the extension equality at the first coordinate identifies the scalar traces.
      simpa [problem_6_7_firstCoordinate, problem_6_7_restriction] using
        congrArg (fun z : ℍ^{2} ↦ z.1 0) hGt
    calc
      problem_6_7_firstCoordinate G t = problem_6_7_firstCoordinate problem_6_7_map t := hcoord
      _ = t := problem_6_7_restriction_isSmoothOn ht

/-- Helper for Problem 6-7: there is no smooth real-valued function on `ℝ` that is everywhere
nonnegative and restricts to `id` on `[0, ∞)`. -/
lemma problem_6_7_noSmoothNonnegativeRealExtension :
    ¬ ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
        (∀ t : ℝ, 0 ≤ g t) ∧
        Set.EqOn g id problem_6_7_nonnegativeRay := by
  rintro ⟨g, hg, hnonneg, hEq⟩
  have hZero : g 0 = 0 := by
    -- The ray agreement pins down the value at the boundary point.
    have h0mem : (0 : ℝ) ∈ problem_6_7_nonnegativeRay := by
      simp [problem_6_7_nonnegativeRay]
    simpa using hEq h0mem
  have hLocalMin : IsLocalMin g 0 := by
    have hle : (fun _ : ℝ ↦ (0 : ℝ)) ≤ᶠ[nhds 0] g :=
      Filter.Eventually.of_forall hnonneg
    -- Global nonnegativity makes `0` a local minimum once we know `g 0 = 0`.
    exact hle.isLocalMin hZero.symm isLocalMin_const
  have hDerivZero : deriv g 0 = 0 := hLocalMin.deriv_eq_zero
  have hHasDerivAt : HasDerivAt g (deriv g 0) 0 :=
    ((hg.contDiffAt : ContDiffAt ℝ ∞ g 0).differentiableAt (by simp)).hasDerivAt
  have hDerivWithinZero : derivWithin g (Set.Ici 0) 0 = 0 := by
    -- The ambient derivative controls the right derivative because `[0, ∞)` has unique tangent.
    rw [hHasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0), hDerivZero]
  have hEqWithin : g =ᶠ[nhdsWithin 0 (Set.Ici 0)] id := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro x hx
    exact hEq hx
  have hHasDerivWithinId : HasDerivWithinAt g 1 (Set.Ici 0) 0 := by
    -- On the ray, `g` agrees with the identity, so its right derivative there is `1`.
    exact (hasDerivAt_id 0).hasDerivWithinAt.congr_of_eventuallyEq_of_mem hEqWithin (by simp)
  have hDerivWithinOne : derivWithin g (Set.Ici 0) 0 = 1 :=
    hHasDerivWithinId.derivWithin (uniqueDiffWithinAt_Ici 0)
  rw [hDerivWithinOne] at hDerivWithinZero
  norm_num at hDerivWithinZero

/-- Helper for Problem 6-7: the restriction `f = F|A` has no smooth extension `ℝ → ℍ²`. -/
lemma problem_6_7_noSmoothExtension :
    ¬ ∃ G : C^∞⟮𝓘(ℝ), ℝ; 𝓡∂ 2, ℍ^{2}⟯,
        ∀ x : problem_6_7_nonnegativeRay, G x = problem_6_7_restriction x := by
  rintro ⟨G, hG⟩
  rcases problem_6_7_extensionFirstCoordinate_eqOnRay G hG with ⟨hnonneg, hEq⟩
  -- The first coordinate of any putative extension would contradict the scalar obstruction.
  exact problem_6_7_noSmoothNonnegativeRealExtension
    ⟨problem_6_7_firstCoordinate G, problem_6_7_firstCoordinate_contDiff G, hnonneg, hEq⟩

/-- Problem 6-7 (1): for the map `F(t) = (t, |t|)` and `A = [0, ∞)`, the relative Whitney
approximation conclusion of Theorem 6.26 can fail when the target manifold has nonempty boundary;
there is no smooth map `G : ℝ → ℍ²` homotopic to `F` relative to `A`. -/
theorem problem_6_7_no_homotopicRel_to_smooth_map :
    ¬ ∃ G : C^∞⟮𝓘(ℝ), ℝ; 𝓡∂ 2, ℍ^{2}⟯,
        problem_6_7_map.HomotopicRel (G : C(ℝ, ℍ^{2})) problem_6_7_nonnegativeRay := by
  rintro ⟨G, hG⟩
  have hExt : ∀ x : problem_6_7_nonnegativeRay, G x = problem_6_7_restriction x := by
    intro x
    -- A relative homotopy forces the two maps to agree pointwise on the ray.
    calc
      G x = problem_6_7_map x := by
        simpa using (ContinuousMap.HomotopicRel.fst_eq_snd hG x.2).symm
      _ = problem_6_7_restriction x := rfl
  exact problem_6_7_noSmoothExtension ⟨G, hExt⟩

/-- Problem 6-7 (2): for the same closed subset `A = [0, ∞)` and smooth map `f = F|A`,
Corollary 6.27 can fail when the target manifold has nonempty boundary: `f` has a continuous
extension to `ℝ`, but it has no smooth extension to `ℝ`. -/
theorem problem_6_7_continuous_but_no_smooth_extension :
    (∃ F : C(ℝ, ℍ^{2}),
      ∀ x : problem_6_7_nonnegativeRay, F x = problem_6_7_restriction x) ∧
      ¬ ∃ G : C^∞⟮𝓘(ℝ), ℝ; 𝓡∂ 2, ℍ^{2}⟯,
          ∀ x : problem_6_7_nonnegativeRay, G x = problem_6_7_restriction x := by
  constructor
  · -- The original map `F` is already a continuous extension of its restriction.
    exact ⟨problem_6_7_map, fun x ↦ rfl⟩
  · -- The second half is exactly the extension obstruction proved above.
    exact problem_6_7_noSmoothExtension

end
