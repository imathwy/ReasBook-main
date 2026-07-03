import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order.Compact

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_8 (from Chap01/Sec01) -/
universe u v w x

open scoped ContDiff Manifold

section Pi

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type u} [Fintype ι] {r : WithTop ℕ∞}
variable {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {H : ι → Type w} [∀ i, TopologicalSpace (H i)]
variable {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
variable {M : ι → Type x} [∀ i, TopologicalSpace (M i)]

omit [Fintype ι] in
/-- Helper for Example 1.8: the transition map between product charts is the product of the
factorwise transition maps. -/
lemma openPartialHomeomorph_pi_symm_trans_pi [Finite ι]
    (e e' : ∀ i, OpenPartialHomeomorph (M i) (H i)) :
    (OpenPartialHomeomorph.pi e).symm.trans (OpenPartialHomeomorph.pi e') =
      OpenPartialHomeomorph.pi (fun i ↦ (e i).symm.trans (e' i)) := by
  -- Compare the transition maps coordinatewise.
  apply OpenPartialHomeomorph.ext
  · intro x
    funext i
    rfl
  · intro x
    funext i
    rfl
  · ext x
    simp [Set.mem_pi]

/-- Helper for Example 1.8: membership in the product-source condition is equivalent to the
corresponding coordinatewise source conditions. -/
lemma mem_modelWithCorners_pi_source_iff
    {e : ∀ i, OpenPartialHomeomorph (H i) (H i)} {x : ∀ i, E i} :
    x ∈ (ModelWithCorners.pi I).symm ⁻¹' (OpenPartialHomeomorph.pi e).source ∩
        Set.range (ModelWithCorners.pi I) ↔
      ∀ i, x i ∈ (I i).symm ⁻¹' (e i).source ∩ Set.range (I i) := by
  -- Unfold the finite-product structures so the source condition separates by coordinates.
  have hrange :
      Set.range (ModelWithCorners.pi I) = Set.pi Set.univ (fun i ↦ Set.range (I i)) := by
    change Set.range (Pi.map fun i ↦ (I i)) = _
    simp
  rw [hrange]
  constructor
  · intro hx i
    have hx_source_mem :
        (ModelWithCorners.pi I).symm x ∈ Set.pi Set.univ (fun i ↦ (e i).source) := by
      simpa [OpenPartialHomeomorph.pi] using hx.1
    have hx_source_mem' :
        ∀ i ∈ Set.univ, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
      dsimp [ModelPi] at hx_source_mem ⊢
      rw [Set.mem_pi] at hx_source_mem
      exact hx_source_mem
    have hx_source_pi : ∀ i, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
      exact fun i ↦ hx_source_mem' i (by simp)
    have hx_source : ∀ i, (I i).symm (x i) ∈ (e i).source := by
      simpa [ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using hx_source_pi
    have hx_range_mem : x ∈ Set.pi Set.univ (fun i ↦ Set.range (I i)) := hx.2
    have hx_range : ∀ i, x i ∈ Set.range (I i) := by
      rw [Set.mem_pi] at hx_range_mem
      exact fun i ↦ hx_range_mem i (by simp)
    exact ⟨hx_source i, hx_range i⟩
  · intro hx
    constructor
    · have hx_source : ∀ i, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
        simpa [ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using fun i ↦ (hx i).1
      have hx_source_mem' :
          ∀ i ∈ Set.univ, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
        exact fun i _ ↦ hx_source i
      have hx_source_mem :
          (ModelWithCorners.pi I).symm x ∈ Set.pi Set.univ (fun i ↦ (e i).source) := by
        dsimp [ModelPi] at ⊢
        rw [Set.mem_pi]
        exact hx_source_mem'
      simpa [OpenPartialHomeomorph.pi] using hx_source_mem
    · rw [Set.mem_pi]
      exact fun i _ ↦ (hx i).2

/-- Helper for Example 1.8: each coordinate projection on a finite product model space is `C^r`. -/
lemma contDiffOn_pi_proj (i : ι) (s : Set (∀ i, E i)) :
    ContDiffOn 𝕜 r (fun x : ∀ i, E i ↦ x i) s := by
  -- Coordinate projections are continuous linear, hence `C^r`.
  simpa using
    ((((ContinuousLinearMap.proj (R := 𝕜) i) : (∀ i, E i) →L[𝕜] E i).contDiff).contDiffOn :
      ContDiffOn 𝕜 r ((ContinuousLinearMap.proj (R := 𝕜) i) : (∀ i, E i) → E i) s)

/-- Helper for Example 1.8: a finite product of `C^r` coordinate changes is again `C^r`. -/
lemma contDiffGroupoid_pi {e : ∀ i, OpenPartialHomeomorph (H i) (H i)}
    (he : ∀ i, e i ∈ contDiffGroupoid r (I i)) :
    OpenPartialHomeomorph.pi e ∈ contDiffGroupoid r (ModelWithCorners.pi I) := by
  refine (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (ModelWithCorners.pi I))).2 ?_
  constructor
  · -- Prove the forward map is `C^r` by checking each coordinate separately.
    refine contDiffOn_pi.2 ?_
    intro i
    have hi :=
      (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (I i))).1 (he i)
    simpa [Function.comp] using
      (show ContDiffOn 𝕜 r ((I i) ∘ e i ∘ (I i).symm)
          ((I i).symm ⁻¹' (e i).source ∩ Set.range (I i)) from by
            simpa [contDiffPregroupoid] using hi.1).comp
          (contDiffOn_pi_proj (𝕜 := 𝕜) (r := r) i _)
          fun x hx =>
        (mem_modelWithCorners_pi_source_iff (I := I) (e := e) (x := x)).1 hx i
  · -- Apply the same coordinatewise argument to the inverse product chart.
    refine contDiffOn_pi.2 ?_
    intro i
    have hi :=
      (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (I i))).1 (he i)
    simpa [Function.comp] using
      (show ContDiffOn 𝕜 r ((I i) ∘ (e i).symm ∘ (I i).symm)
          ((I i).symm ⁻¹' ((e i).symm).source ∩ Set.range (I i)) from by
            simpa [contDiffPregroupoid] using hi.2).comp
          (contDiffOn_pi_proj (𝕜 := 𝕜) (r := r) i _)
          fun x hx =>
        (mem_modelWithCorners_pi_source_iff (I := I) (e := fun i ↦ (e i).symm) (x := x)).1
          (by simpa [OpenPartialHomeomorph.pi] using hx) i

variable [∀ i, ChartedSpace (H i) (M i)]

-- Primitive data are the factorwise charted-space and manifold structures; the finite product
-- manifold structure is the canonical owner instance over `ModelWithCorners.pi`.
set_option backward.isDefEq.respectTransparency false in
instance instIsManifoldPi [∀ i, IsManifold (I i) r (M i)] :
    IsManifold (ModelWithCorners.pi I) r (∀ i, M i) := by
  refine isManifold_of_contDiffOn (I := ModelWithCorners.pi I) r (∀ i, M i) ?_
  intro f g hf hg
  rcases hf with ⟨f', hf', rfl⟩
  rcases hg with ⟨g', hg', rfl⟩
  have hf_atlas : ∀ i, f' i ∈ atlas (H i) (M i) := by
    simpa [Set.mem_pi] using hf'
  have hg_atlas : ∀ i, g' i ∈ atlas (H i) (M i) := by
    simpa [Set.mem_pi] using hg'
  -- Rewrite the product transition map into its factorwise coordinate changes.
  rw [openPartialHomeomorph_pi_symm_trans_pi]
  -- Each factor transition is `C^r`, so the whole product transition is `C^r`.
  exact ((mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (ModelWithCorners.pi I))).1 <|
    contDiffGroupoid_pi (I := I) (r := r) fun i =>
      (contDiffGroupoid r (I i)).compatible (hf_atlas i) (hg_atlas i)).1

end Pi

/-- Example 1.8 (Product Manifolds): a finite product of topological manifolds carries the
canonical topological manifold structure modeled on the finite product of the factor Euclidean
spaces. -/
theorem isManifold_pi
    {ι : Type u} [Fintype ι] {n : ι → ℕ}
    {M : ι → Type v} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin (n i))) (M i)]
    [∀ i, IsManifold (𝓡 (n i)) 0 (M i)] :
    IsManifold (ModelWithCorners.pi fun i ↦ 𝓡 (n i)) 0 (∀ i, M i) := by
  -- This is exactly the canonical finite-product manifold instance specialized to Euclidean models.
  infer_instance

/-! ### Problem_1_8 (from Chap01/Sec01_07) -/
noncomputable section

open scoped Manifold ContDiff

/-- A function `θ : U → ℝ` is an angle function if it is continuous and exponentiates to the
inclusion `U ↪ S¹`. -/
def IsAngleFunction {U : TopologicalSpace.Opens Circle} (θ : U → ℝ) : Prop :=
  Continuous θ ∧ ∀ z : U, Circle.exp (θ z) = z

/-- Helper for Problem 1-8: a point of the unit circle lies in the complex slit plane exactly when
it is not the branch point `-1`. -/
lemma circle_mem_slitPlane_iff_ne_neg_one (z : Circle) :
    ((z : ℂ) ∈ Complex.slitPlane) ↔ z ≠ -1 := by
  -- Reduce the slit-plane condition to a singleton subset of the unit sphere.
  have hs : ({(z : ℂ)} : Set ℂ) ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact z.2
  have hsubset := Complex.subset_slitPlane_iff_of_subset_sphere (r := 1) hs
  calc
    ((z : ℂ) ∈ Complex.slitPlane) ↔ ({(z : ℂ)} : Set ℂ) ⊆ Complex.slitPlane := by
      constructor
      · intro hz
        intro w hw
        rcases Set.mem_singleton_iff.mp hw with rfl
        exact hz
      · intro hz
        exact hz (by simp)
    _ ↔ (-1 : ℂ) ∉ ({(z : ℂ)} : Set ℂ) := hsubset
    _ ↔ z ≠ -1 := by
      constructor
      · intro hz h
        apply hz
        simpa [h]
      · intro hz h
        apply hz
        exact Circle.ext <| by simpa using h.symm

/-- Helper for Problem 1-8: if an open subset of the circle misses one point, then rotating that
point to `-1` lets `Complex.arg` define an angle function on the open subset. -/
lemma exists_angleFunction_of_missing_point {U : TopologicalSpace.Opens Circle} {c : Circle}
    (hc : c ∉ U) : ∃ θ : U → ℝ, IsAngleFunction θ := by
  let u : Circle := -c⁻¹
  let θ : U → ℝ := fun z ↦ Complex.arg (((u * z : Circle) : ℂ)) - Complex.arg (u : ℂ)
  refine ⟨θ, ?_⟩
  constructor
  · -- Continuity comes from the continuity of `arg` away from the rotated missing point.
    let g : U → ℂ := fun z ↦ (((u * z : Circle) : ℂ))
    have hg : Continuous g := by
      simpa [g] using
        (continuous_subtype_val.comp (continuous_const.mul continuous_subtype_val))
    have hslit : ∀ z : U, (((u * z : Circle) : ℂ)) ∈ Complex.slitPlane := by
      intro z
      rw [circle_mem_slitPlane_iff_ne_neg_one]
      intro hz
      have hz' : (z : Circle) = c := by
        have hz_mul := congrArg (fun w : Circle ↦ u⁻¹ * w) hz
        simpa [u, mul_assoc] using hz_mul
      exact hc (hz' ▸ z.2)
    have harg : Continuous fun z : U ↦ Complex.arg (g z) := by
      rw [continuous_iff_continuousAt]
      intro z
      have hgz : ContinuousAt g z := hg.continuousAt
      exact (Complex.continuousAt_arg (by simpa [g] using hslit z)).comp hgz
    simpa [g] using harg.sub continuous_const
  · intro z
    -- Exponentiating the rotated argument undoes the rotation and recovers the original point.
    have hexp_mul : Circle.exp (Complex.arg (((u * z : Circle) : ℂ))) = (u * z : Circle) := by
      simpa using Circle.exp_arg (u * z)
    have hexp_u : Circle.exp (Complex.arg (u : ℂ)) = u := by
      simpa using Circle.exp_arg u
    calc
      Circle.exp (θ z)
          = Circle.exp (Complex.arg (((u * z : Circle) : ℂ))) /
              Circle.exp (Complex.arg (u : ℂ)) := by
            rw [show θ z = Complex.arg (((u * z : Circle) : ℂ)) - Complex.arg (u : ℂ) by rfl,
              Circle.exp_sub]
      _ = (u * z : Circle) / u := by rw [hexp_mul, hexp_u]
      _ = z := by
        simp [u, mul_assoc]

/-- Problem 1-8 (1): an open subset of `S¹` admits an angle function exactly when it is not all of
`S¹`. -/
-- Proof sketch: if `U = S¹`, a continuous lift of the exponential map would give a global branch
-- of argument on the circle, contradicting the winding of `Circle.exp`. Conversely, if `U ≠ S¹`,
-- remove a point of the circle outside `U` and use the corresponding branch of argument obtained
-- from stereographic projection or the standard cut-open parametrization of the circle.
theorem exists_angleFunction_iff_ne_univ (U : TopologicalSpace.Opens Circle) :
    (∃ θ : U → ℝ, IsAngleFunction θ) ↔ U ≠ ⊤ := by
  constructor
  · rintro ⟨θ, hθ⟩ hU
    subst hU
    let θ' : Circle → ℝ := fun z ↦ θ ⟨z, by simp⟩
    have hθ' : Continuous θ' := by
      have hincl : Continuous fun z : Circle ↦ (⟨z, by simp⟩ : (⊤ : TopologicalSpace.Opens Circle)) := by
        simpa using (Homeomorph.Set.univ Circle).symm.continuous
      exact hθ.1.comp hincl
    have hrange : Set.range θ' = Set.range θ := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨⟨z, by simp⟩, rfl⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z, rfl⟩
    -- A global angle function would be an open embedding of the compact circle into `ℝ`.
    have hcomp : Circle.exp ∘ θ = Subtype.val := by
      funext z
      exact hθ.2 z
    have hsection : Topology.IsOpenEmbedding (Circle.exp ∘ θ) := by
      rw [hcomp]
      exact isOpen_univ.isOpenEmbedding_subtypeVal
    have hθemb : Topology.IsOpenEmbedding θ :=
      isLocalHomeomorph_circleExp.isOpenEmbedding_of_comp hsection hθ.1
    have hopen : IsOpen (Set.range θ) := hθemb.isOpen_range
    have hcompact : IsCompact (Set.range θ) := by
      rw [← hrange]
      exact isCompact_range hθ'
    have hnonempty : (Set.range θ).Nonempty := by
      rw [← hrange]
      exact Set.range_nonempty _
    obtain ⟨x, hx⟩ := hcompact.exists_isGreatest hnonempty
    -- An open subset of `ℝ` cannot contain a greatest element.
    obtain ⟨a, b, hxab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hx.1)
    have hax : a < x := hxab.1
    have hxb : x < b := hxab.2
    have hy_left : a < (x + b) / 2 := by linarith
    have hy_right : (x + b) / 2 < b := by linarith
    have hy_mem : (x + b) / 2 ∈ Set.range θ := hab ⟨hy_left, hy_right⟩
    have hx_lt_mid : x < (x + b) / 2 := by linarith
    exact (not_lt_of_ge (hx.2 hy_mem)) hx_lt_mid
  · intro hU
    classical
    -- A proper open subset misses some point of the circle, so we use the branch-cut construction.
    have hnotall : ¬ ∀ z : Circle, z ∈ U := by
      intro hall
      apply hU
      ext z
      simp [TopologicalSpace.Opens.coe_top, hall z]
    obtain ⟨c, hc⟩ := not_forall.mp hnotall
    exact exists_angleFunction_of_missing_point hc

/-- Problem 1-8 (2): an angle function identifies its domain with an open subset of `ℝ`. -/
-- Proof sketch: `Circle.exp ∘ θ = id` on `U`, so `θ` is injective and `Circle.exp` restricts to a
-- continuous inverse on `Set.range θ`. The openness of `U` and the local homeomorphism property of
-- the exponential parametrization then show that `θ` is an open embedding.
theorem IsAngleFunction.isOpenEmbedding {U : TopologicalSpace.Opens Circle} {θ : U → ℝ}
    (hθ : IsAngleFunction θ) :
    Topology.IsOpenEmbedding θ := by
  -- The inclusion `U ↪ Circle` factors as `Circle.exp ∘ θ`, so `θ` is a continuous local section.
  have hcomp : Circle.exp ∘ θ = Subtype.val := by
    funext z
    exact hθ.2 z
  have hsection : Topology.IsOpenEmbedding (Circle.exp ∘ θ) := by
    rw [hcomp]
    exact U.2.isOpenEmbedding_subtypeVal
  exact isLocalHomeomorph_circleExp.isOpenEmbedding_of_comp hsection hθ.1

/-- Helper for Problem 1-8: the polar-coordinate chart on the slit plane is smooth because its
inverse is the explicit smooth map `(r, θ) ↦ (r cos θ, r sin θ)`. -/
lemma polarCoord_contDiffAt (q : ℝ × ℝ) (hq : q ∈ polarCoord.source) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) polarCoord q := by
  -- First record that the inverse polar-coordinate map is smooth by its explicit formula.
  have hsymm : ContDiff ℝ (⊤ : WithTop ℕ∞) polarCoord.symm := by
    change ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun p : ℝ × ℝ ↦ (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    fun_prop
  have hq_target : q ∈ polarCoord.symm.target := hq
  -- Then the easy inverse-function theorem upgrades the local inverse to a smooth map.
  exact polarCoord.symm.contDiffAt_symm hq_target
    (f₀' := (fderivPolarCoordSymm (polarCoord q)).toContinuousLinearEquivOfDetNeZero (by
      rw [det_fderivPolarCoordSymm]
      exact (polarCoord.map_source hq).1.ne'))
    (by
      simpa using hasFDerivAt_polarCoord_symm (polarCoord q))
    hsymm.contDiffAt

/-- Helper for Problem 1-8: `Complex.arg` is smooth at every point of the slit plane. -/
lemma Complex.arg_contDiffAt_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) Complex.arg z := by
  -- Rewrite the complex slit-plane chart through the real polar-coordinate chart.
  have hreal : ContDiffAt ℝ (⊤ : WithTop ℕ∞) polarCoord (Complex.equivRealProd z) := by
    simpa [Complex.polarCoord, Complex.polarCoord_source] using
      polarCoord_contDiffAt (Complex.equivRealProd z) hz
  have hcomplex : ContDiffAt ℝ (⊤ : WithTop ℕ∞) Complex.polarCoord z := by
    simpa [Complex.polarCoord] using hreal.comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  -- The argument is the second polar-coordinate component.
  have hEq : Complex.arg = fun w : ℂ ↦ (Complex.polarCoord w).2 := by
    funext w
    simp [Complex.polarCoord_apply]
  rw [hEq]
  simpa using contDiff_snd.contDiffAt.comp z hcomplex

/-- Helper for Problem 1-8: the explicit branch-cut formula is smooth at each circle point whose
rotated image avoids the branch point `-1`. -/
lemma explicit_branch_contMDiffAt {u : Circle} {z : Circle}
    (hz : (((u * z : Circle) : ℂ)) ∈ Complex.slitPlane) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ) ∞ (fun y : Circle ↦ Complex.arg (((u * y : Circle) : ℂ))) z := by
  letI : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  -- Smoothness of the inner rotation map comes from the smooth sphere inclusion into `ℂ`.
  have hmulAmbient : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w : ℂ ↦ (u : ℂ) * w) := by
    simpa using contDiff_const.mul contDiff_id
  have hcoe : ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (fun y : Circle ↦ (y : ℂ)) := by
    exact contMDiff_coe_sphere (n := 1)
  have hmul : ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (fun y : Circle ↦ ((u : ℂ) * (y : ℂ))) := by
    exact (hmulAmbient.contMDiff.of_le le_top).comp hcoe
  -- Compose the smooth ambient branch `arg` with that smooth rotation.
  have harg : ContMDiffAt (𝓘(ℝ, ℂ)) 𝓘(ℝ) ∞ Complex.arg (((u * z : Circle) : ℂ)) :=
    (Complex.arg_contDiffAt_of_mem_slitPlane hz).contMDiffAt.of_le le_top
  simpa [mul_comm, mul_left_comm, mul_assoc] using harg.comp z hmul.contMDiffAt

/-- Helper for Problem 1-8: if an open circle subset misses one point, then the standard branch-cut
angle function on that subset is smooth. -/
lemma smooth_branch_of_missing_point {U : TopologicalSpace.Opens Circle} {c : Circle}
    (hc : c ∉ U) :
    ∃ θ : U → ℝ, IsAngleFunction θ ∧ ContMDiff (𝓡 1) 𝓘(ℝ) ∞ θ := by
  refine ⟨
    fun z : U ↦ Complex.arg ((((-c⁻¹) * z : Circle) : ℂ)) - Complex.arg ((-c⁻¹ : Circle) : ℂ),
    ?_, ?_⟩
  · -- This is exactly the standard branch-cut angle function from the topological half.
    constructor
    · let u : Circle := -c⁻¹
      let g : U → ℂ := fun z ↦ (((u * z : Circle) : ℂ))
      have hg : Continuous g := by
        simpa [g] using
          (continuous_subtype_val.comp (continuous_const.mul continuous_subtype_val))
      have hslit : ∀ z : U, (((u * z : Circle) : ℂ)) ∈ Complex.slitPlane := by
        intro z
        rw [circle_mem_slitPlane_iff_ne_neg_one]
        intro hz
        have hz' : (z : Circle) = c := by
          have hz_mul := congrArg (fun w : Circle ↦ u⁻¹ * w) hz
          simpa [u, mul_assoc] using hz_mul
        exact hc (hz' ▸ z.2)
      have harg : Continuous fun z : U ↦ Complex.arg (g z) := by
        rw [continuous_iff_continuousAt]
        intro z
        have hgz : ContinuousAt g z := hg.continuousAt
        exact (Complex.continuousAt_arg (by simpa [g] using hslit z)).comp hgz
      simpa [u, g] using harg.sub continuous_const
    · intro z
      -- Exponentiating cancels the branch-cut formula and recovers the original circle point.
      have hexp_mul :
          Circle.exp (Complex.arg ((((-c⁻¹) * z : Circle) : ℂ))) = ((-c⁻¹) * z : Circle) := by
        simpa using Circle.exp_arg ((-c⁻¹ : Circle) * z)
      have hexp_u : Circle.exp (Complex.arg ((-c⁻¹ : Circle) : ℂ)) = (-c⁻¹ : Circle) := by
        simpa using Circle.exp_arg (-c⁻¹ : Circle)
      calc
        Circle.exp
            (Complex.arg ((((-c⁻¹) * z : Circle) : ℂ)) - Complex.arg ((-c⁻¹ : Circle) : ℂ))
            =
              Circle.exp (Complex.arg ((((-c⁻¹) * z : Circle) : ℂ))) /
                Circle.exp (Complex.arg ((-c⁻¹ : Circle) : ℂ)) := by
              rw [Circle.exp_sub]
        _ = (((-c⁻¹ : Circle) * z : Circle)) / (-c⁻¹ : Circle) := by rw [hexp_mul, hexp_u]
        _ = z := by simp [mul_assoc]
  · intro z
    -- Smoothness on the open subtype reduces to smoothness of the ambient branch formula.
    refine (contMDiffAt_subtype_iff
      (f := fun y : Circle ↦
        Complex.arg ((((-c⁻¹) * y : Circle) : ℂ)) - Complex.arg ((-c⁻¹ : Circle) : ℂ))
      (x := z)).2 ?_
    have hslit : ((((-c⁻¹) * z : Circle) : ℂ)) ∈ Complex.slitPlane := by
      rw [circle_mem_slitPlane_iff_ne_neg_one]
      intro hz
      have hz' : (z : Circle) = c := by
        have hz_mul := congrArg (fun w : Circle ↦ (-c⁻¹ : Circle)⁻¹ * w) hz
        simpa [mul_assoc] using hz_mul
      exact hc (hz' ▸ z.2)
    exact (explicit_branch_contMDiffAt hslit).sub contMDiffAt_const

section

variable {U : TopologicalSpace.Opens Circle} {θ : U → ℝ}

/-- Problem 1-8 (3): an angle function is a smooth local coordinate on `S¹`. -/
-- Proof sketch: compare the chart `θ` with the standard smooth structure on `Circle`, using that
-- `Circle.exp` is smooth and that `θ` is its local inverse on `U`. Smoothness of a local inverse
-- follows from the manifold chart criterion for mutually inverse smooth maps between open sets.
theorem IsAngleFunction.contMDiff (hθ : IsAngleFunction θ) :
    ContMDiff (𝓡 1) 𝓘(ℝ) ∞ θ := by
  -- Route correction: the old local-diffeomorphism transport route was too abstract here.
  -- The source-faithful route is to compare `θ` near each point with a smooth branch-cut angle
  -- function coming from `Complex.arg` on a slit neighborhood of the circle.
  have hU : U ≠ ⊤ := (exists_angleFunction_iff_ne_univ U).mp ⟨θ, hθ⟩
  have hnotall : ¬ ∀ z : Circle, z ∈ U := by
    intro hall
    apply hU
    ext z
    simp [hall z]
  obtain ⟨c, hc⟩ := not_forall.mp hnotall
  obtain ⟨η, hη, hη_smooth⟩ := smooth_branch_of_missing_point hc
  intro z
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp ((hθ.2 z).trans (hη.2 z).symm)
  let g : U → ℝ := fun y ↦ η y + m * (2 * Real.pi)
  have hg_eq : g z = θ z := by
    simpa [g] using hm.symm
  have hg_exp : ∀ y : U, Circle.exp (g y) = y := by
    intro y
    -- The shifted branch is still an angle function because `Circle.exp` is `2π`-periodic.
    calc
      Circle.exp (g y)
          = Circle.exp (η y) * Circle.exp (m * (2 * Real.pi)) := by
              simp [g, Circle.exp_add]
      _ = Circle.exp (η y) := by rw [Circle.exp_int_mul_two_pi, mul_one]
      _ = y := hη.2 y
  have hg_smooth : ContMDiffAt (𝓡 1) 𝓘(ℝ) ∞ g z := by
    -- Shifting a smooth branch by a constant preserves smoothness.
    simpa [g] using (hη_smooth z).add contMDiffAt_const
  have hwindow_mem : Set.Ioo (θ z - Real.pi / 2) (θ z + Real.pi / 2) ∈ nhds (θ z) := by
    refine IsOpen.mem_nhds isOpen_Ioo ?_
    constructor <;> linarith [Real.pi_pos]
  have hθ_window :
      ∀ᶠ y in nhds z, θ y ∈ Set.Ioo (θ z - Real.pi / 2) (θ z + Real.pi / 2) :=
    hθ.1.continuousAt.preimage_mem_nhds hwindow_mem
  have hg_window :
      ∀ᶠ y in nhds z, g y ∈ Set.Ioo (θ z - Real.pi / 2) (θ z + Real.pi / 2) := by
    have : Set.Ioo (θ z - Real.pi / 2) (θ z + Real.pi / 2) ∈ nhds (g z) := by
      simpa [hg_eq] using hwindow_mem
    exact (hη.1.add continuous_const).continuousAt.preimage_mem_nhds this
  have hwidth : (θ z + Real.pi / 2) - (θ z - Real.pi / 2) < 2 * Real.pi := by
    linarith [Real.pi_pos]
  have hlocal_eq : θ =ᶠ[nhds z] g := by
    -- On a small interval of width `π`, the exponential map on the circle is injective.
    filter_upwards [hθ_window, hg_window] with y hyθ hyg
    have hyθ' : θ y ∈ Set.Icc (θ z - Real.pi / 2) (θ z + Real.pi / 2) :=
      ⟨le_of_lt hyθ.1, le_of_lt hyθ.2⟩
    have hyg' : g y ∈ Set.Icc (θ z - Real.pi / 2) (θ z + Real.pi / 2) :=
      ⟨le_of_lt hyg.1, le_of_lt hyg.2⟩
    have hEqExp : Circle.exp (θ y) = Circle.exp (g y) := by
      calc
        Circle.exp (θ y) = y := hθ.2 y
        _ = Circle.exp (g y) := (hg_exp y).symm
    exact (Circle.exp_injOn_Icc (a := θ z - Real.pi / 2) (b := θ z + Real.pi / 2) hwidth) hyθ'
      hyg'
      hEqExp
  -- The original angle function is eventually equal to the shifted smooth branch.
  exact hg_smooth.congr_of_eventuallyEq hlocal_eq

/-- The open image of an angle function in `ℝ`. -/
def IsAngleFunction.openImage (hθ : IsAngleFunction θ) : TopologicalSpace.Opens ℝ :=
  ⟨Set.range θ, hθ.isOpenEmbedding.isOpen_range⟩

theorem IsAngleFunction.mapsTo_circleExp_openImage (hθ : IsAngleFunction θ) :
    Set.MapsTo Circle.exp (hθ.openImage : Set ℝ) U := by
  rintro _ ⟨z, rfl⟩
  exact (hθ.2 z).symm ▸ z.2

/-- The inverse parametrization attached to an angle function, defined on its open image. -/
def IsAngleFunction.circleExpOpenImage (hθ : IsAngleFunction θ) : hθ.openImage → U :=
  Set.MapsTo.restrict Circle.exp (hθ.openImage : Set ℝ) U (hθ.mapsTo_circleExp_openImage)

theorem IsAngleFunction.leftInverse_circleExpOpenImage (hθ : IsAngleFunction θ) :
    Function.LeftInverse hθ.circleExpOpenImage (Set.rangeFactorization θ) := by
  intro z
  apply Subtype.ext
  exact hθ.2 z

theorem IsAngleFunction.rightInverse_circleExpOpenImage (hθ : IsAngleFunction θ) :
    Function.RightInverse hθ.circleExpOpenImage (Set.rangeFactorization θ) := by
  rintro ⟨x, ⟨z, rfl⟩⟩
  apply Subtype.ext
  simpa using congrArg θ (hθ.leftInverse_circleExpOpenImage z)

/-- Helper for Problem 1-8: the inverse parametrization followed by the angle function is the
inclusion of the open image into `ℝ`. -/
theorem IsAngleFunction.theta_comp_circleExpOpenImage (hθ : IsAngleFunction θ) :
    θ ∘ hθ.circleExpOpenImage = Subtype.val := by
  -- This is the right-inverse statement with the range subtype forgotten.
  funext x
  exact congrArg Subtype.val (hθ.rightInverse_circleExpOpenImage x)

/-- Helper for Problem 1-8: after forgetting the codomain restriction, the inverse
parametrization is just `Circle.exp` on the open image of the angle function. -/
theorem IsAngleFunction.subtypeVal_comp_circleExpOpenImage (hθ : IsAngleFunction θ) :
    (Subtype.val : U → Circle) ∘ hθ.circleExpOpenImage =
      Circle.exp ∘ (Subtype.val : hθ.openImage → ℝ) := by
  -- Both sides are the ambient circle exponential evaluated on the chosen angle value.
  funext x
  rfl

/-- Problem 1-8 (4): the inverse parametrization attached to an angle function is a smooth map
from the open image of `θ` back to `U`. -/
-- Proof sketch: `Circle.exp` is globally smooth on `ℝ`, hence smooth on the open image of `θ`.
-- The angle function identity `Circle.exp (θ z) = z` shows that this restriction lands in `U`
-- and inverts `θ` on both sides, giving the smooth inverse parametrization required for
-- `(U, θ)` to be a smooth coordinate chart.
theorem IsAngleFunction.contMDiff_circleExpOpenImage (hθ : IsAngleFunction θ) :
    ContMDiff (𝓘(ℝ)) (𝓡 1) ∞ hθ.circleExpOpenImage := by
  -- It suffices to check smoothness after composing with the open-submanifold inclusion `U ↪ S¹`.
  rw [← ContMDiff.subtypeVal_comp_iff U hθ.circleExpOpenImage]
  -- After forgetting the codomain restriction, this is just the smooth circle exponential.
  rw [hθ.subtypeVal_comp_circleExpOpenImage]
  exact contMDiff_circleExp.comp contMDiff_subtype_val

end
