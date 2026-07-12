import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».BoundaryFrontier

open Set
open scoped UpperHalfPlane

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: once the Abel integral is known to be bijective
from the upper half-plane onto the fundamental rectangle, `Function.invFunOn` packages the
source-facing inverse owner without reopening the analytic argument. -/
lemma exercise8_rectangleInverseOfBijOn
    (k : Exercise8Modulus)
    (hbij :
      Set.BijOn (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane)
        (exercise8_open_rectangle k)) :
    ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  classical
  let G : exercise8_open_rectangle k → UpperHalfPlane :=
    fun u ↦ Function.invFunOn (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane) u
  rcases hbij with ⟨hmap, hinj, hsurj⟩
  refine ⟨G, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u
    -- The surjective half of `BijOn` makes `invFunOn` a right inverse on the rectangle.
    simpa [G] using hsurj.rightInvOn_invFunOn u.2
  · intro z
    -- The same owner theorem already records that every upper-half-plane point lands in the
    -- rectangle.
    exact hmap (by trivial)
  · intro z hz
    -- Injectivity on the source turns `invFunOn` into the required left inverse on `univ`.
    simpa [G] using hinj.leftInvOn_invFunOn (show z ∈ (Set.univ : Set UpperHalfPlane) by trivial)

/-- Helper for Cartan section26 0018_Exercise_8: the Abel integral is continuous on the strict
upper half-plane subtype. -/
lemma exercise8_abel_integral_continuous
    (k : Exercise8Modulus) :
    Continuous (exercise8_abel_integral k) := by
  -- The pointwise continuity owner already proves global continuity on the subtype domain.
  rw [continuous_iff_continuousAt]
  intro z
  exact exercise8_abel_integral_continuousAt k z

/-- Helper for Cartan section26 0018_Exercise_8: the Abel image is nonempty because the source
upper half-plane already contains the standard point `i`. -/
lemma exercise8_abelImage_nonempty
    (k : Exercise8Modulus) :
    (Set.range (exercise8_abel_integral k)).Nonempty := by
  -- Evaluating at `i` gives one explicit point of the image.
  exact ⟨exercise8_abel_integral k UpperHalfPlane.I, ⟨UpperHalfPlane.I, rfl⟩⟩

/-- Helper for Cartan section26 0018_Exercise_8: the Abel image is connected because it is the
continuous image of the connected upper half-plane. -/
lemma exercise8_abelImage_isConnected
    (k : Exercise8Modulus) :
    IsConnected (Set.range (exercise8_abel_integral k)) := by
  have hrange :
      Set.range (exercise8_abel_integral k) =
        (exercise8_abel_integral k) '' (Set.univ : Set UpperHalfPlane) := by
    -- Rewrite the range as an image of `univ` so that connectedness transports directly.
    ext u
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by trivial, rfl⟩
    · rintro ⟨z, -, rfl⟩
      exact ⟨z, rfl⟩
  -- Continuous images of connected sets remain connected.
  rw [hrange]
  exact isConnected_univ.image (exercise8_abel_integral k)
    (exercise8_abel_integral_continuous k).continuousOn

/-- Helper for Cartan section26 0018_Exercise_8: the strict upper half-plane is preconnected, so
the complex open-mapping theorem applies to ambient aliases of the Abel integral on this source
domain. -/
lemma exercise8_upperHalfPlaneSet_isPreconnected :
    IsPreconnected UpperHalfPlane.upperHalfPlaneSet := by
  -- The strict upper half-plane is the convex half-space `Im z > 0`.
  exact exercise8_convex_upperHalfPlaneSet.isPreconnected

/-- Helper for Cartan section26 0018_Exercise_8: the Abel image can be rewritten as the image of
the ambient alias `w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)` on `Im w > 0`. -/
lemma exercise8_abelImage_eq_ambientImage
    (k : Exercise8Modulus) :
    Set.range (exercise8_abel_integral k) =
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) ''
        UpperHalfPlane.upperHalfPlaneSet := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(z : ℂ), z.2, ?_⟩
    -- On strict upper-half-plane points, the ambient alias is exactly the subtype map.
    simpa using congrArg (exercise8_abel_integral k) (UpperHalfPlane.ofComplex_apply z)
  · rintro ⟨w, hw, rfl⟩
    -- Any ambient upper-half-plane input is already a genuine source point for the Abel map.
    exact ⟨UpperHalfPlane.ofComplex w, rfl⟩

/-- Helper for Cartan section26 0018_Exercise_8: the ambient Abel alias is differentiable on the
strict upper half-plane. This isolates the segment-primitive calculation so later rectangle-image
theorems can consume a named analytic owner instead of rebuilding the same congruence locally. -/
lemma exercise8_abelIntegral_differentiableOn_ambient
    (k : Exercise8Modulus) :
    DifferentiableOn ℂ
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      UpperHalfPlane.upperHalfPlaneSet := by
  have hprimitive :
      DifferentiableOn ℂ
        (fun w : ℂ ↦
          exercise8_abel_integral k UpperHalfPlane.I +
            ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ) w, (exercise8_integrand k dz) t)
        UpperHalfPlane.upperHalfPlaneSet := by
    -- The segment primitive is already holomorphic; adding the fixed anchor value preserves
    -- differentiability on the ambient upper-half-plane set.
    simpa using
      (exercise8_segmentPrimitive_differentiableAmbient k UpperHalfPlane.I).const_add
        (exercise8_abel_integral k UpperHalfPlane.I)
  refine DifferentiableOn.congr hprimitive ?_
  intro w hw
  have hw_im : 0 < w.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hw
  have hcoerce :
      (((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)) = w := by
    simpa using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply_of_im_pos hw_im)
  -- Rewrite the ambient alias through the fixed-anchor identity against the interior point `i`.
  calc
    exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
        = exercise8_abel_integral k UpperHalfPlane.I +
            ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ)
                ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ),
              (exercise8_integrand k dz) t := by
            exact exercise8_abelIntegral_eq_anchor_add_segment k UpperHalfPlane.I
              (UpperHalfPlane.ofComplex w)
    _ =
        exercise8_abel_integral k UpperHalfPlane.I +
          ∫ᶜ t in Path.segment (UpperHalfPlane.I : ℂ) w, (exercise8_integrand k dz) t := by
            rw [hcoerce]

/-- Helper for Cartan section26 0018_Exercise_8: the ambient Abel alias is holomorphic on the
strict upper half-plane. This is the analytic owner consumed by the rectangle-image package. -/
lemma exercise8_abelIntegral_analyticOnNhd_ambient
    (k : Exercise8Modulus) :
    AnalyticOnNhd ℂ
      (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      UpperHalfPlane.upperHalfPlaneSet := by
  -- The upper half-plane is open, so ambient differentiability upgrades to ambient analyticity.
  exact
    (Complex.analyticOnNhd_iff_differentiableOn UpperHalfPlane.isOpen_upperHalfPlaneSet).2
      (exercise8_abelIntegral_differentiableOn_ambient k)

/-- Helper for Cartan section26 0018_Exercise_8: once the ambient alias of the Abel integral is
known to be analytic and nonconstant on `Im z > 0`, the global complex open-mapping theorem
packages the Abel image as an open subset of `ℂ`. -/
lemma exercise8_abelImage_isOpen_of_analyticAmbient
    (k : Exercise8Modulus)
    (hanalytic :
      AnalyticOnNhd ℂ
        (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        UpperHalfPlane.upperHalfPlaneSet)
    (hnonconst :
      ¬ ∃ c : ℂ,
        ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
          exercise8_abel_integral k (UpperHalfPlane.ofComplex z) = c) :
    IsOpen (Set.range (exercise8_abel_integral k)) := by
  have hopen :
      ∀ s ⊆ UpperHalfPlane.upperHalfPlaneSet,
        IsOpen s →
          IsOpen
            ((fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) '' s) := by
    -- Route correction: this isolates the open-image package so the rectangle theorem no longer
    -- has to rediscover the open-mapping step inline.
    exact
      (hanalytic.is_constant_or_isOpen exercise8_upperHalfPlaneSet_isPreconnected).resolve_left
        hnonconst
  -- Apply the packaged open-mapping theorem to the whole strict upper half-plane.
  rw [exercise8_abelImage_eq_ambientImage k]
  exact hopen UpperHalfPlane.upperHalfPlaneSet Subset.rfl UpperHalfPlane.isOpen_upperHalfPlaneSet

/-- Helper for Cartan section26 0018_Exercise_8: once the ambient analyticity and nonconstancy
inputs are supplied, the Abel image already has the full topological package needed by the global
rectangle theorem: it is open, connected, and nonempty. -/
lemma exercise8_abelImage_topology_of_analyticAmbient
    (k : Exercise8Modulus)
    (hanalytic :
      AnalyticOnNhd ℂ
        (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        UpperHalfPlane.upperHalfPlaneSet)
    (hnonconst :
      ¬ ∃ c : ℂ,
        ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
          exercise8_abel_integral k (UpperHalfPlane.ofComplex z) = c) :
    IsOpen (Set.range (exercise8_abel_integral k)) ∧
      IsConnected (Set.range (exercise8_abel_integral k)) ∧
      (Set.range (exercise8_abel_integral k)).Nonempty := by
  -- The open-mapping theorem gives the openness input for the eventual image-equality step.
  refine ⟨exercise8_abelImage_isOpen_of_analyticAmbient k hanalytic hnonconst, ?_, ?_⟩
  · -- Connectedness was proved independently from continuity on the upper half-plane subtype.
    exact exercise8_abelImage_isConnected k
  · -- Nonemptiness comes from evaluating the Abel integral at the standard point `i`.
    exact exercise8_abelImage_nonempty k

/-- Helper for Cartan section26 0018_Exercise_8: the ambient upper-half-plane alias of the Abel
integral is nonconstant because its from-above limits at `0` and `1` are different boundary
vertices of the rectangle. -/
lemma exercise8_abelIntegral_not_constantAmbient
    (k : Exercise8Modulus) :
    ¬ ∃ c : ℂ,
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        exercise8_abel_integral k (UpperHalfPlane.ofComplex z) = c := by
  intro hconst
  rcases hconst with ⟨c, hc⟩
  have hupper_closure (x : ℝ) : (x : ℂ) ∈ closure UpperHalfPlane.upperHalfPlaneSet := by
    -- Every real boundary point is accumulated by a short vertical segment from above.
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · have him_pos : 0 < ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I).im := by
        simp
        linarith
      simpa [UpperHalfPlane.upperHalfPlaneSet] using him_pos
    · have hhalf_nonneg : 0 ≤ ε / 2 := by
        linarith
      have hnormOfReal : ‖((ε / 2 : ℝ) : ℂ)‖ = |ε / 2| := by
        simpa using (RCLike.norm_ofReal (K := ℂ) (ε / 2))
      calc
        dist (x : ℂ) ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I)
            = ‖(x : ℂ) - ((x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by
              rw [dist_eq_norm]
        _ = ‖-(((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by ring_nf
        _ = ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ := by rw [norm_neg]
        _ = ‖((ε / 2 : ℝ) : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
        _ = |ε / 2| * ‖Complex.I‖ := by rw [hnormOfReal]
        _ = |ε / 2| * 1 := by rw [Complex.norm_I]
        _ = ε / 2 := by rw [abs_of_nonneg hhalf_nonneg]; ring
        _ < ε := by linarith
  have hEq_zero :
      Filter.EventuallyEq
        (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet)
        (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (fun _ : ℂ ↦ c) := by
    -- On the source filter, the ambient alias agrees pointwise with the constant value `c`.
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun z hz ↦ hc z hz)
  have hEq_one :
      Filter.EventuallyEq
        (nhdsWithin (1 : ℂ) UpperHalfPlane.upperHalfPlaneSet)
        (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (fun _ : ℂ ↦ c) := by
    -- The same pointwise constancy holds near the second boundary vertex.
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun z hz ↦ hc z hz)
  have hconst_zero :
      Filter.Tendsto (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet) (nhds c) := by
    -- Eventual equality with a constant function forces the same limit.
    exact Filter.Tendsto.congr' hEq_zero.symm tendsto_const_nhds
  have hconst_one :
      Filter.Tendsto (fun z : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex z))
        (nhdsWithin (1 : ℂ) UpperHalfPlane.upperHalfPlaneSet) (nhds c) := by
    -- The identical argument applies at the neighborhood filter above `1`.
    exact Filter.Tendsto.congr' hEq_one.symm tendsto_const_nhds
  have htrace_zero : exercise8_boundary_trace k 0 = c := by
    -- The from-above limit at the origin is unique in the Hausdorff target `ℂ`.
    letI : (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (hupper_closure 0)
    exact tendsto_nhds_unique (exercise8_abel_integral_tendsto_boundary_trace_zero k) hconst_zero
  have htrace_one : exercise8_boundary_trace k 1 = c := by
    -- The same uniqueness argument identifies the limit above `1` with the same constant `c`.
    letI : (nhdsWithin (1 : ℂ) UpperHalfPlane.upperHalfPlaneSet).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (hupper_closure 1)
    exact
      tendsto_nhds_unique
        (exercise8_abel_integral_tendsto_boundary_trace_nonzero_real k (by norm_num))
        hconst_one
  have hzero : exercise8_boundary_trace k 0 = 0 := by
    -- The repaired boundary trace is normalized to vanish at the origin.
    simpa using exercise8_boundary_value_zero k
  have hone :
      exercise8_boundary_trace k 1 = exercise8_complete_real_period k := by
    -- The right endpoint of the bottom edge is the real period vertex `K`.
    simpa using exercise8_boundary_value_one k
  have hperiod_ne :
      (exercise8_complete_real_period k : ℂ) ≠ 0 := by
    -- The complete real period is strictly positive, hence nonzero.
    exact_mod_cast (exercise8_complete_real_period_pos k).ne'
  have hzero_eq_period :
      (0 : ℂ) = exercise8_complete_real_period k := by
    calc
      (0 : ℂ) = exercise8_boundary_trace k 0 := hzero.symm
      _ = c := htrace_zero
      _ = exercise8_boundary_trace k 1 := htrace_one.symm
      _ = exercise8_complete_real_period k := hone
  exact hperiod_ne hzero_eq_period.symm

/-- Helper for Cartan section26 0018_Exercise_8: the Abel image already carries the full
topological package needed by the rectangle-owner theorem without any extra hypotheses. -/
lemma exercise8_abelImage_topology
    (k : Exercise8Modulus) :
    IsOpen (Set.range (exercise8_abel_integral k)) ∧
      IsConnected (Set.range (exercise8_abel_integral k)) ∧
      (Set.range (exercise8_abel_integral k)).Nonempty := by
  -- The ambient analyticity and nonconstancy owners now live in this support layer, so the public
  -- topology package is a direct specialization of the parameterized theorem above.
  exact exercise8_abelImage_topology_of_analyticAmbient k
    (exercise8_abelIntegral_analyticOnNhd_ambient k)
    (exercise8_abelIntegral_not_constantAmbient k)

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is open in `ℂ` because it is
the product of two open real intervals under the `re`/`im` identification. -/
lemma exercise8_open_rectangle_isOpen
    (k : Exercise8Modulus) :
    IsOpen (exercise8_open_rectangle k) := by
  -- The target is literally `Ioo (-K, K) × Ioo (0, K')`.
  simpa [exercise8_open_rectangle] using
    (isOpen_Ioo.reProdIm isOpen_Ioo :
      IsOpen
        (Set.Ioo (-exercise8_complete_real_period k) (exercise8_complete_real_period k) ×ℂ
          Set.Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)))

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is convex because it is the
intersection of four real and imaginary open half-spaces. -/
lemma exercise8_open_rectangle_convex
    (k : Exercise8Modulus) :
    Convex ℝ (exercise8_open_rectangle k) := by
  let K := exercise8_complete_real_period k
  let K' := exercise8_complete_imaginary_period k
  have hrect :
      exercise8_open_rectangle k =
        {z : ℂ | -K < z.re} ∩
          ({z : ℂ | z.re < K} ∩ ({z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < K'})) := by
    ext z
    rw [exercise8_open_rectangle, Complex.mem_reProdIm]
    simpa [K, K', and_assoc]
  -- Repackage the rectangle as a finite intersection of convex half-spaces.
  rw [hrect]
  exact
    (convex_halfSpace_re_gt (-K)).inter
      ((convex_halfSpace_re_lt K).inter
        ((convex_halfSpace_im_gt (0 : ℝ)).inter (convex_halfSpace_im_lt K')))

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is nonempty, witnessed by
its vertical midpoint. -/
lemma exercise8_open_rectangle_nonempty
    (k : Exercise8Modulus) :
    (exercise8_open_rectangle k).Nonempty := by
  let center : ℂ := ((exercise8_complete_imaginary_period k / 2 : ℝ) : ℂ) * Complex.I
  refine ⟨center, ?_⟩
  rw [mem_exercise8_open_rectangle_iff]
  constructor
  · constructor <;> simp [center]
    · linarith [exercise8_complete_real_period_pos k]
    · linarith [exercise8_complete_real_period_pos k]
  · constructor <;> simp [center]
    · linarith [exercise8_complete_imaginary_period_pos k]
    · linarith [exercise8_complete_imaginary_period_pos k]

/-- Helper for Cartan section26 0018_Exercise_8: the target rectangle is connected because any
nonempty convex subset of `ℂ` is connected. -/
lemma exercise8_open_rectangle_isConnected
    (k : Exercise8Modulus) :
    IsConnected (exercise8_open_rectangle k) := by
  -- Convexity plus the midpoint witness gives the source-facing connectedness owner.
  exact (exercise8_open_rectangle_convex k).isConnected (exercise8_open_rectangle_nonempty k)

/-- Helper for Exercise 8: the inverse branch coming from the biholomorphic Abel map is itself a
source-facing rectangle inverse. -/
lemma exercise8_biholomorphicInverse_isRectangleInverse
    (k : Exercise8Modulus)
    {e : HolomorphicIsomorph UpperHalfPlane.upperHalfPlaneSet (exercise8_open_rectangle k)}
    (he : ∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z) :
    IsExercise8RectangleInverse k
      (fun u : exercise8_open_rectangle k ↦
        UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have hu_target : (u : ℂ) ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
      simpa [e.target_eq] using u.2
    have hu_source :
        ((e : OpenPartialHomeomorph ℂ ℂ).symm u : ℂ) ∈
          (e : OpenPartialHomeomorph ℂ ℂ).source := by
      exact (e : OpenPartialHomeomorph ℂ ℂ).map_target hu_target
    have hu_im : 0 < (((e : OpenPartialHomeomorph ℂ ℂ).symm u : ℂ)).im := by
      simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using hu_source
    have hu_coe :
        (((UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u) : UpperHalfPlane) :
            ℂ)) =
          (e : OpenPartialHomeomorph ℂ ℂ).symm u := by
      simpa using
        congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
          (UpperHalfPlane.ofComplex_apply_of_im_pos hu_im)
    -- Reinterpret the biholomorphic inverse value as an element of `UpperHalfPlane`.
    calc
      exercise8_abel_integral k
          (UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u))
          = e (UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u)) := by
              simpa using
                (he (UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u))).symm
      _ = (e : OpenPartialHomeomorph ℂ ℂ) ((e : OpenPartialHomeomorph ℂ ℂ).symm u) := by
            rw [hu_coe]
      _ = u := by
            simpa using (e : OpenPartialHomeomorph ℂ ℂ).right_inv hu_target
  · intro z
    have hz_source : ((z : UpperHalfPlane) : ℂ) ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
      simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using z.2
    -- The biholomorphic forward map lands in the prescribed rectangle.
    simpa [e.target_eq, he z] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source
  · intro z hz
    have hz_target :
        exercise8_abel_integral k z ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
      simpa [e.target_eq] using hz
    have hz_source :
        ((e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z) : ℂ) ∈
          (e : OpenPartialHomeomorph ℂ ℂ).source := by
      exact (e : OpenPartialHomeomorph ℂ ℂ).map_target hz_target
    have hz_im :
        0 < (((e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z) : ℂ)).im := by
      simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using hz_source
    -- Apply the inverse branch to the Abel image and then coerce back to `UpperHalfPlane`.
    simpa using
      (calc
        (((UpperHalfPlane.ofComplex
              ((e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z)) :
              UpperHalfPlane) : ℂ))
            = (e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z) := by
                simpa using
                  congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
                    (UpperHalfPlane.ofComplex_apply_of_im_pos hz_im)
        _ = (z : ℂ) := by
              calc
                (e : OpenPartialHomeomorph ℂ ℂ).symm (exercise8_abel_integral k z)
                    = (e : OpenPartialHomeomorph ℂ ℂ).symm (e z) := by
                        rw [(he z).symm]
                _ = z := by
                      simpa using
                        (e : OpenPartialHomeomorph ℂ ℂ).left_inv
                          (by simpa [e.source_eq, UpperHalfPlane.upperHalfPlaneSet] using z.2))

/-- Helper for Cartan section26 0018_Exercise_8: the single-sheet inverse branch on the
fundamental rectangle is the structural owner that the public bijection theorem should consume. -/
lemma exercise8_rectangleInverse_exists_support
    (k : Exercise8Modulus) :
    ∃ G : exercise8_open_rectangle k → UpperHalfPlane, IsExercise8RectangleInverse k G := by
  -- Route correction: isolate the global inverse owner first, so the public `BijOn` theorem
  -- becomes a short unpacking lemma rather than the first place where the inverse is constructed.
  rcases exercise_8_abel_integral_bijective k with ⟨e, he, _G, _hG⟩
  let G : exercise8_open_rectangle k → UpperHalfPlane :=
    fun u ↦ UpperHalfPlane.ofComplex ((e : OpenPartialHomeomorph ℂ ℂ).symm u)
  have heUpper : ∀ z : UpperHalfPlane, e z = exercise8_abel_integral k z := by
    intro z
    simpa using he z
  have hG : IsExercise8RectangleInverse k G :=
    exercise8_biholomorphicInverse_isRectangleInverse k (e := e) heUpper
  -- The public biholomorphic owner already comes with the required rectangle inverse branch.
  exact ⟨G, hG⟩

/-- Helper for Cartan section26 0018_Exercise_8: the missing global owner theorem should identify
the Abel integral as the unique sheet over the fundamental rectangle. -/
lemma exercise8_abel_integral_bijOn_open_rectangle
    (k : Exercise8Modulus) :
    Set.BijOn (exercise8_abel_integral k) (Set.univ : Set UpperHalfPlane)
      (exercise8_open_rectangle k) := by
  rcases exercise8_rectangleInverse_exists_support k with ⟨G, hG⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    -- The support theorem already records that every upper-half-plane point lands in the
    -- fundamental rectangle.
    exact hG.2.1 z
  · intro z₁ hz₁ z₂ hz₂ hzEq
    have hz₁_rect : exercise8_abel_integral k z₁ ∈ exercise8_open_rectangle k := hG.2.1 z₁
    have hz₂_rect : exercise8_abel_integral k z₂ ∈ exercise8_open_rectangle k := hG.2.1 z₂
    have hsub :
        (⟨exercise8_abel_integral k z₁, hz₁_rect⟩ : exercise8_open_rectangle k) =
          ⟨exercise8_abel_integral k z₂, hz₂_rect⟩ := by
      apply Subtype.ext
      simpa using hzEq
    -- The left-inverse field of `G` turns equality of Abel images back into equality upstairs.
    calc
      z₁ = G ⟨exercise8_abel_integral k z₁, hz₁_rect⟩ := by
            simpa using (hG.2.2 z₁ hz₁_rect).symm
      _ = G ⟨exercise8_abel_integral k z₂, hz₂_rect⟩ := by simpa [hsub]
      _ = z₂ := by
            simpa using hG.2.2 z₂ hz₂_rect
  · intro u hu
    refine ⟨G ⟨u, hu⟩, ?_, ?_⟩
    · trivial
    · -- The right-inverse field of `G` makes surjectivity onto the rectangle immediate.
      exact hG.1 ⟨u, hu⟩
