import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0010_Proposition_4_1»
import DifferentialForms_Cartan_1970.II.section05.«0018_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».RectangleStageReduction

open scoped BigOperators Interval unitInterval

universe u

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: if `K ⊆ D`, then the frontier of the
compact region bounded by `Γ` also lies in `D`. -/
theorem frontier_subset_domain_of_orientedBoundary
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) :
    frontier K ⊆ D := by
  -- A compact set contains its frontier, so the ambient-domain inclusion extends to the frontier.
  intro z hz
  exact hKD (hΓ.isCompact.isClosed.frontier_subset hz)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: each boundary component of an
oriented boundary stays inside the ambient domain `D`. -/
theorem range_toPath_subset_domain_of_orientedBoundary
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (i : ι) :
    Set.range (Γ i).toPath ⊆ D := by
  -- The image of each boundary path sits on `frontier K`, which the previous helper sends into
  -- `D`.
  intro z hz
  exact frontier_subset_domain_of_orientedBoundary hΓ hKD (hΓ.range_toPath_subset_frontier i hz)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a closed-path homotopy from `γ` to
a constant loop already forces the contour integral of `γ` to vanish on a closed-form domain. -/
theorem curveIntegral_eq_zero_of_closedPathHomotopicIn_const
    {D : Set ℂ} {z x : ℂ} {γ : Path z z} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hγ_homotopic : ClosedPathHomotopicIn D γ (Path.refl x))
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_integrable : CurveIntegrable ω γ)
    (hω : IsClosedOn ω D) :
    ∫ᶜ ζ in γ, ω ζ = 0 := by
  have hEq : ∫ᶜ ζ in γ, ω ζ = ∫ᶜ ζ in Path.refl x, ω ζ :=
    Path.curveIntegral_eq_of_homotopic_closed_paths_of_closed_form
      hγ_homotopic hγ_piecewise (Path.isPiecewiseDifferentiable_refl x)
      hγ_integrable (CurveIntegrable.refl ω x) hω
  calc
    ∫ᶜ ζ in γ, ω ζ = ∫ᶜ ζ in Path.refl x, ω ζ := hEq
    _ = 0 := by simp

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a closed form has zero integral
around any axis-parallel rectangle contained in the domain. -/
theorem rectangleBoundaryIntegral_eq_zero_of_isClosedOn
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) {z w : ℂ}
    (hrect : Complex.Rectangle z w ⊆ D)
    (hrect_integrable : CurveIntegrable ω (axisParallelRectangleBoundaryPath z w)) :
    ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, ω ζ = 0 := by
  let γ : Path z z := axisParallelRectangleBoundaryPath z w
  have hzRect : z ∈ Complex.Rectangle z w := by
    simp [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc]
  have hconvRect : Convex ℝ (Complex.Rectangle z w) := by
    rw [Complex.rectangle_eq_convexHull]
    exact convex_convexHull (𝕜 := ℝ)
      ({z, z.re + w.im * Complex.I, w.re + z.im * Complex.I, w} : Set ℂ)
  have hFcont : Continuous fun p : I × I ↦ AffineMap.lineMap (γ p.2) z (p.1 : ℝ) := by
    fun_prop
  let F : γ.Homotopy (Path.refl z) :=
    { toHomotopy :=
        { toFun := fun p ↦ AffineMap.lineMap (γ p.2) z (p.1 : ℝ)
          continuous_toFun := hFcont
          map_zero_left := by
            intro t
            simp [AffineMap.lineMap_apply]
          map_one_left := by
            intro t
            simp [AffineMap.lineMap_apply] }
      prop' := by
        intro s t ht
        rcases ht with rfl | rfl <;> simp [γ, AffineMap.lineMap_apply] }
  have hFmaps : Set.range F ⊆ D := by
    rintro _ ⟨p, rfl⟩
    have hγRect : γ p.2 ∈ Complex.Rectangle z w := by
      exact axisParallelRectangleBoundaryPath_range_subset_rectangle z w ⟨p.2, rfl⟩
    have hs : (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := p.1.2
    exact hrect (hconvRect.lineMap_mem hγRect hzRect hs)
  calc
    ∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, ω ζ =
        ∫ᶜ ζ in Path.refl z, ω ζ := by
      simpa [γ] using
        Path.curveIntegral_eq_of_homotopy_in_domain
          hω
          (axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable z w)
          (Path.isPiecewiseDifferentiable_refl z)
          hrect_integrable
          (CurveIntegrable.refl ω z)
          F hFmaps
    _ = 0 := by simp

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: an axis-parallel rectangle boundary
contracts inside every ambient domain containing that rectangle. -/
theorem axisParallelRectangleBoundaryPath_nullHomotopicIn_domain
    {C : Set ℂ} {z w : ℂ} (hrect : Complex.Rectangle z w ⊆ C) :
    IsNullHomotopicClosedPathIn C (axisParallelRectangleBoundaryPath z w) := by
  let γ : Path z z := axisParallelRectangleBoundaryPath z w
  have hzRect : z ∈ Complex.Rectangle z w := by
    simp [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc]
  have hconvRect : Convex ℝ (Complex.Rectangle z w) := by
    rw [Complex.rectangle_eq_convexHull]
    exact convex_convexHull (𝕜 := ℝ)
      ({z, z.re + w.im * Complex.I, w.re + z.im * Complex.I, w} : Set ℂ)
  have hFcont : Continuous fun p : I × I ↦ AffineMap.lineMap (γ p.2) z (p.1 : ℝ) := by
    fun_prop
  let F : γ.Homotopy (Path.refl z) :=
    { toHomotopy :=
        { toFun := fun p ↦ AffineMap.lineMap (γ p.2) z (p.1 : ℝ)
          continuous_toFun := hFcont
          map_zero_left := by
            -- At homotopy time `0`, the contraction is the original rectangle boundary loop.
            intro t
            simp [AffineMap.lineMap_apply]
          map_one_left := by
            -- At homotopy time `1`, the contraction collapses the loop to the corner `z`.
            intro t
            simp [AffineMap.lineMap_apply] }
      prop' := by
        -- The contraction fixes the common start and end point throughout the homotopy.
        intro s t ht
        rcases ht with rfl | rfl <;> simp [γ, AffineMap.lineMap_apply] }
  have hFmaps : Set.range F ⊆ C := by
    rintro _ ⟨p, rfl⟩
    have hγRect : γ p.2 ∈ Complex.Rectangle z w := by
      exact axisParallelRectangleBoundaryPath_range_subset_rectangle z w ⟨p.2, rfl⟩
    have hs : (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := p.1.2
    -- Convexity keeps the straight-line contraction inside the same rectangle.
    exact hrect (hconvRect.lineMap_mem hγRect hzRect hs)
  refine ⟨z, hrect hzRect, ?_⟩
  refine ⟨{ toHomotopy := F.toHomotopy, prop' := ?_ }⟩
  intro t
  change IsClosedPathIn C (((F.eval t : Path z z) : C(I, ℂ)))
  refine ⟨(F.eval t).isClosedPath, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact hFmaps ⟨(t, s), rfl⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the oriented-boundary contour
sum has been rewritten as a finite sum of rectangle-boundary integrals inside `D`, the existing
rectangle vanishing lemma collapses the whole sum to zero. -/
theorem rectangleStage_sum_curveIntegral_eq_zero_of_isClosedOn
    {S : Type u} [Fintype S] {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hω : IsClosedOn ω D) (z w : S → ℂ)
    (hrect : ∀ s, Complex.Rectangle (z s) (w s) ⊆ D)
    (hrect_integrable : ∀ s, CurveIntegrable ω (axisParallelRectangleBoundaryPath (z s) (w s))) :
    (∑ s, ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z s) (w s), ω ζ) = 0 := by
  -- Kill the rectangle stage termwise before any global boundary transport is used.
  calc
    (∑ s, ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z s) (w s), ω ζ) = ∑ s, 0 := by
      -- Every stage rectangle lies in `D`, so the rectangle vanishing lemma applies to each
      -- summand independently.
      refine Finset.sum_congr rfl ?_
      intro s hs
      exact rectangleBoundaryIntegral_eq_zero_of_isClosedOn hω (hrect s) (hrect_integrable s)
    _ = 0 := by
      simp

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the oriented-boundary contour
sum has been rewritten as a finite sum of rectangle-boundary integrals inside `D`, the existing
rectangle vanishing lemma collapses the whole sum to zero. -/
theorem sum_curveIntegral_eq_zero_of_rectangleBoundaryDecomposition
    {ι : Type u} [Fintype ι] {S : Type u} [Fintype S] {D : Set ℂ}
    {Γ : ι → ClosedPath ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D)
    (z w : S → ℂ) (hrect : ∀ s, Complex.Rectangle (z s) (w s) ⊆ D)
    (hrect_integrable : ∀ s, CurveIntegrable ω (axisParallelRectangleBoundaryPath (z s) (w s)))
    (hdecomp :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) =
        (∑ s, ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z s) (w s), ω ζ)) :
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  -- Rewrite the global boundary sum through the rectangle decomposition supplied by geometry.
  calc
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) =
        ∑ s, ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z s) (w s), ω ζ := hdecomp
    _ = 0 := rectangleStage_sum_curveIntegral_eq_zero_of_isClosedOn hω z w hrect hrect_integrable

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a null-homotopic closed loop in `D`
has zero contour integral against a closed form. -/
theorem curveIntegral_eq_zero_of_nullHomotopicClosedPathIn_domain
    {D : Set ℂ} {z : ℂ} {γ : Path z z} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hγ : IsNullHomotopicClosedPathIn D γ) (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_integrable : CurveIntegrable ω γ)
    (hω : IsClosedOn ω D) :
    ∫ᶜ ζ in γ, ω ζ = 0 := by
  rcases hγ with ⟨x, hxD, hhom⟩
  -- The null-homotopy already contracts `γ` to a constant loop in `D`.
  simpa using
    curveIntegral_eq_zero_of_closedPathHomotopicIn_const
      (γ := γ) (x := x) hhom hγ_piecewise hγ_integrable hω

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the local-primitive hypothesis
already forces the ambient domain to be open. -/
theorem isOpen_domain_of_isClosedOn
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) :
    IsOpen D := by
  -- Read openness off the neighborhood appearing in the local primitive witness at each point.
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases hω z hz with ⟨U, hU_open, hzU, hUD, -⟩
  exact Filter.mem_of_superset (hU_open.mem_nhds hzU) hUD

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the image of a closed path lies in
the connected component of the ambient domain containing its base point. -/
theorem range_toPath_subset_connectedComponent_domain
    {D : Set ℂ} {z : ℂ} {γ : Path z z} (hγD : Set.range γ ⊆ D) :
    Set.range γ ⊆ connectedComponentIn D z := by
  let S : Set ℂ := γ '' (Set.univ : Set I)
  have hS_preconnected : IsPreconnected S := by
    -- The image of the unit interval under a continuous path is preconnected.
    simpa [S, Set.image_univ] using isPreconnected_range γ.continuous
  have hzS : z ∈ S := by
    -- The base point is realized at parameter `0`.
    refine ⟨0, Set.mem_univ _, ?_⟩
    simp
  have hSD : S ⊆ D := by
    -- The whole path image stays in the ambient domain by hypothesis.
    rintro w ⟨t, -, rfl⟩
    exact hγD ⟨t, rfl⟩
  have hS_component : S ⊆ connectedComponentIn D z :=
    hS_preconnected.subset_connectedComponentIn hzS hSD
  -- Rewrite the image set back to the usual `Set.range` notation.
  intro w hw
  rcases hw with ⟨t, rfl⟩
  exact hS_component ⟨t, Set.mem_univ _, rfl⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a connected component of `D`
selected by one boundary loop is itself an open connected subset of `D`. -/
theorem boundaryComponent_isOpen_isConnected
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsOpen C ∧ IsConnected C := by
  rcases Finset.mem_image.mp hC with ⟨i, -, rfl⟩
  have hiD : (Γ i).toPath 0 ∈ D := by
    exact range_toPath_subset_domain_of_orientedBoundary hΓ hKD i ⟨0, by simp⟩
  constructor
  · -- The component of an open planar domain is again open.
    simpa using hD_open.connectedComponentIn (x := (Γ i).toPath 0)
  · -- A nonempty connected component is connected by definition.
    simpa using
      (isConnected_connectedComponentIn_iff
        (F := D) (x := (Γ i).toPath 0)).2 hiD

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: every boundary component selected by
the connected-component key lies in the ambient domain `D`. -/
theorem boundaryComponent_subset_domain
    {ι : Type u} [Fintype ι] {D : Set ℂ} {Γ : ι → ClosedPath ℂ} {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    C ⊆ D := by
  rcases Finset.mem_image.mp hC with ⟨i, -, hiC⟩
  -- A connected component of `D` is contained in `D` by construction.
  intro z hz
  exact connectedComponentIn_subset D ((Γ i).toPath 0) (hiC ▸ hz)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a closed form on `C` admits a
primitive along every path whose image stays in `C`. -/
theorem IsClosedOn.existsPrimitiveAlongPath_of_path_in_domain
    {C : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    {x y : ℂ} {γ : Path x y} (hγC : Set.range γ ⊆ C) :
    ∃ f : C(I, ℂ), IsPrimitiveAlongPath ω C γ f := by
  have hδ_cont : Continuous fun p : Path.unitSquare ↦
      γ (⟨p.1.1, (Path.unitSquare_bounds p).1.1, (Path.unitSquare_bounds p).2.1⟩ : I) := by
    fun_prop
  let δ : C(Path.unitSquare, ℂ) := ⟨fun p ↦
    γ (⟨p.1.1, (Path.unitSquare_bounds p).1.1, (Path.unitSquare_bounds p).2.1⟩ : I), hδ_cont⟩
  have hlocal : ∀ p : Path.unitSquare, HasPrimitiveWithinAt C ω (δ p) := by
    intro p
    apply hω
    exact hγC ⟨⟨p.1.1, (Path.unitSquare_bounds p).1.1, (Path.unitSquare_bounds p).2.1⟩, by
      simp [δ]⟩
  obtain ⟨f, hf, -⟩ :=
    primitive_following_on_rectangle_exists_and_unique_up_to_constant
      (ω := ω) (D := C) (a := 0) (a' := 0) (b := 1) (b' := 1) (δ := δ) hlocal
  have isPrimitiveAlongEdge
      {x y : ℂ} {η : Path x y} {e : C(I, Path.unitSquare)}
      (hedge : ∀ t : I, δ (e t) = η t) :
      IsPrimitiveAlongPath ω C η (f.comp e) := by
    intro τ
    rcases hf (e τ) with
      ⟨s, hs_open, hs_mem, U, hU_open, hδU, hUC, hmaps, primitive, hprimitive, hEq⟩
    refine ⟨e ⁻¹' s, hs_open.preimage e.continuous, hs_mem, U, hU_open, ?_, hUC, ?_,
      primitive, hprimitive, ?_⟩
    · simpa [hedge τ] using hδU
    · intro t ht
      simpa [hedge t] using hmaps ht
    · intro t ht
      have hEqt := hEq ht
      simpa [ContinuousMap.comp_apply, hedge t] using hEqt
  have hbottom_mem :
      ∀ t : I, (((t : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈
        Set.uIcc (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) ((1 : ℝ), (1 : ℝ)) := by
    intro t
    simp [t.2.1, t.2.2]
  have hbottom_cont :
      Continuous fun t : I ↦ (⟨((t : ℝ), (0 : ℝ)), hbottom_mem t⟩ : Path.unitSquare) := by
    fun_prop
  let bottomEdge : C(I, Path.unitSquare) :=
    ⟨fun t ↦ ⟨((t : ℝ), (0 : ℝ)), hbottom_mem t⟩, hbottom_cont⟩
  have hbottom_edge : ∀ t : I, δ (bottomEdge t) = γ t := by
    intro t
    simp [δ, bottomEdge]
  refine ⟨f.comp bottomEdge, ?_⟩
  -- Restrict the rectangle primitive to the bottom edge, which is exactly the original path.
  exact isPrimitiveAlongEdge hbottom_edge

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the frontier of a connected
component inside an open set stays on the frontier of the ambient open set. -/
theorem frontier_connectedComponentIn_subset_frontier
    {D : Set ℂ} (hD_open : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    frontier (connectedComponentIn D z) ⊆ frontier D := by
  let C : Set ℂ := connectedComponentIn D z
  have hC_subset : C ⊆ D := connectedComponentIn_subset D z
  have hC_open : IsOpen C := hD_open.connectedComponentIn
  have hcomp_closed : IsClosed (connectedComponent (⟨z, hz⟩ : D)) := isClosed_connectedComponent
  obtain ⟨t, ht_closed, ht_image⟩ := hcomp_closed.image_val
  have hC_eq : C = t ∩ D := by
    simpa [C, connectedComponentIn_eq_image hz] using ht_image
  have hclosureC_subset_t : closure C ⊆ t := by
    rw [hC_eq]
    exact closure_minimal Set.inter_subset_left ht_closed
  intro x hx
  have hxC : x ∈ frontier C := by
    simpa [C] using hx
  have hx' : x ∈ closure C ∧ x ∉ C := by
    rw [hC_open.frontier_eq] at hxC
    simpa using hxC
  have hx_not_memD : x ∉ D := by
    intro hxD
    have hxt : x ∈ t := hclosureC_subset_t hx'.1
    have hxC' : x ∈ C := by
      rw [hC_eq]
      exact ⟨hxt, hxD⟩
    exact hx'.2 hxC'
  refine ⟨closure_mono hC_subset hx'.1, ?_⟩
  simpa [hD_open.interior_eq] using hx_not_memD

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the compact region `K` does not meet
the frontier of a boundary component of the ambient open set. -/
theorem boundaryComponent_frontier_disjoint_compactRegion
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    frontier C ∩ K = ∅ := by
  rcases Finset.mem_image.mp hC with ⟨i, -, rfl⟩
  have hizD : (Γ i).toPath 0 ∈ D := by
    exact range_toPath_subset_domain_of_orientedBoundary hΓ hKD i ⟨0, by simp⟩
  have hfrontierCD :
      frontier (connectedComponentIn D ((Γ i).toPath 0)) ⊆ frontier D :=
    frontier_connectedComponentIn_subset_frontier hD_open hizD
  apply Set.not_nonempty_iff_eq_empty.1
  rintro ⟨x, hx⟩
  rcases hx with ⟨hxFront, hxK⟩
  have hxD : x ∈ D := hKD hxK
  have hxFrontD : x ∈ frontier D := hfrontierCD hxFront
  have hdisj : Disjoint D (frontier D) := by
    simpa [hD_open.interior_eq] using (disjoint_interior_frontier (s := D))
  exact hdisj.le_bot ⟨hxD, hxFrontD⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: if a boundary loop is assigned to
the component `C`, then its entire image lies in `C`. -/
theorem range_toPath_subset_component_of_boundaryKey
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ} {i : ι}
    (hiC : connectedComponentIn D ((Γ i).toPath 0) = C) :
    Set.range (Γ i).toPath ⊆ C := by
  have hpathD : Set.range (Γ i).toPath ⊆ D :=
    range_toPath_subset_domain_of_orientedBoundary hΓ hKD i
  have hpathC :
      Set.range (Γ i).toPath ⊆ connectedComponentIn D ((Γ i).toPath 0) :=
    range_toPath_subset_connectedComponent_domain hpathD
  exact hiC ▸ hpathC

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: if the ambient domain `C` is
connected, every boundary-loop base point already has connected-component key `C`. -/
theorem boundaryComponentKey_eq_ambient_of_connectedAmbient
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C) (i : ι) :
    connectedComponentIn C ((Γ i).toPath 0) = C := by
  have hiC : (Γ i).toPath 0 ∈ C := by
    -- The boundary-loop base point is one point on the path image, so `K ⊆ C` already places it
    -- in the connected ambient set.
    exact range_toPath_subset_domain_of_orientedBoundary hΓ hKC i ⟨0, by simp⟩
  -- In a connected ambient set, the connected component of any point is the whole set.
  exact hC_connected.isPreconnected.connectedComponentIn hiC

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the ambient domain `C` is
connected, filtering the boundary index family by the component key `C` leaves all indices. -/
theorem boundaryComponentFilter_eq_univ_of_connectedAmbient
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C) :
    (Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C) =
      Finset.univ := by
  classical
  -- Each boundary-loop key is definitionally `C` after the connected-ambient normalization.
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro _
    simp
  · intro _
    exact boundaryComponentKey_eq_ambient_of_connectedAmbient hΓ hKC hC_connected i

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected ambient domain, a
component-filtered boundary contour sum is already the total contour sum. -/
theorem connectedAmbient_componentFilter_sum_eq_total
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C)
    {β : Type*} [AddCommMonoid β] (f : ι → β) :
    ((Finset.univ.filter fun i : ι => connectedComponentIn C ((Γ i).toPath 0) = C).sum f) =
      ∑ i, f i := by
  -- Rewrite the filtered index family to `Finset.univ`; connectedness makes every key equal `C`.
  rw [boundaryComponentFilter_eq_univ_of_connectedAmbient hΓ hKC hC_connected]

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the component-restricted boundary
family inherits piecewise differentiability from the original oriented boundary. -/
theorem subtypeBoundaryPaths_piecewiseDifferentiable
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) {C : Set ℂ} :
    ∀ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C},
      ((Γ i.1).toPath).IsPiecewiseDifferentiable := by
  intro i
  -- Restricting the index type does not change the underlying boundary loop.
  simpa using hΓ.piecewiseDifferentiable i.1

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: every loop in the
component-restricted boundary family stays inside that component. -/
theorem subtypeBoundaryPaths_subset_component
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ} :
    ∀ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C},
      Set.range (Γ i.1).toPath ⊆ C := by
  intro i
  -- The subtype equality stores exactly the connected-component key we need.
  exact range_toPath_subset_component_of_boundaryKey hΓ hKD i.2

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: restricting a local curve
straightening chart to a smaller open subset containing the base point preserves the straightening
data. -/
theorem IsLocalCurveStraighteningAt.restrOpen
    {γ : ℝ → Plane} {a b t₀ : ℝ} {δ : OpenPartialHomeomorph Plane Plane}
    (hδ : IsLocalCurveStraighteningAt γ a b t₀ δ)
    {s : Set Plane} (hs : IsOpen s) (ht : (t₀, 0) ∈ s) :
    IsLocalCurveStraighteningAt γ a b t₀ (δ.restrOpen s hs) := by
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_ }
  · -- The restricted chart keeps the same base point because the new source still contains it.
    simpa using And.intro hδ.basePoint_mem_source ht
  · -- The new source is a subset of the old source, so the original strip control persists.
    intro p hp
    exact hδ.source_subset hp.1
  · -- The original `C¹` regularity simply restricts to the smaller open source.
    exact hδ.contDiffOn.mono fun _ hx ↦ hx.1
  · -- The same restriction argument applies to the inverse chart on the smaller target.
    exact hδ.contDiffOn_symm.mono fun _ hy ↦ hy.1
  · -- On the horizontal axis the restricted chart is literally the original chart.
    intro t ht₀
    exact hδ.map_horizontal_axis ht₀.1
  · -- The image of the horizontal axis is still characterized by the vanishing second coordinate.
    exact
      curve_image_is_horizontal_axis
        (fun {t} ht₀ ↦ hδ.map_horizontal_axis ht₀.1)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: every interior parameter value on a
boundary loop assigned to the component `C` lands in that component. -/
theorem realCurve_mem_component_of_boundaryKey
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ} {i : ι}
    (hiC : connectedComponentIn D ((Γ i).toPath 0) = C)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.equivRealProdCLM.symm ((Γ i).realCurve t) ∈ C := by
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrange :
      Complex.equivRealProdCLM.symm ((Γ i).realCurve t) ∈ Set.range (Γ i).toPath := by
    refine ⟨⟨t, htIcc⟩, ?_⟩
    refine Complex.ext ?_ ?_
    · simp [ClosedPath.realCurve, Path.extend_apply, htIcc]
    · simp [ClosedPath.realCurve, Path.extend_apply, htIcc]
  -- Reinterpret the real-plane chart point as an actual point of the underlying closed path.
  exact range_toPath_subset_component_of_boundaryKey hΓ hKD hiC hrange

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: restricting a boundary
straightening chart to ambient points lying in an open set `C` keeps the same boundary
straightening data for the intersected compact region. -/
theorem IsBoundaryStraighteningAt.inter_boundaryComponent
    {K C : Set ℂ} {γ : ℝ → Plane} {t₀ : ℝ}
    {δ : OpenPartialHomeomorph Plane Plane}
    (hδ : IsBoundaryStraighteningAt K γ t₀ δ)
    (hC_open : IsOpen C)
    (hγC : Complex.equivRealProdCLM.symm (γ t₀) ∈ C) :
    ∃ δ' : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (K ∩ C) γ t₀ δ' := by
  let Cplane : Set Plane := Complex.equivRealProdCLM '' C
  have hCplane_open : IsOpen Cplane := by
    exact Complex.equivRealProdCLM.isOpenMap _ hC_open
  have hs_target_open : IsOpen (Cplane ∩ δ.target) := hCplane_open.inter δ.open_target
  have hs_target_subset : Cplane ∩ δ.target ⊆ δ.target := Set.inter_subset_right
  have hs_open_image : IsOpen (δ.symm '' (Cplane ∩ δ.target)) :=
    δ.symm.isOpen_image_of_subset_source hs_target_open hs_target_subset
  have hs_eq :
      δ.symm '' (Cplane ∩ δ.target) = δ.source ∩ δ ⁻¹' Cplane := by
    rw [δ.symm.image_eq_target_inter_inv_preimage hs_target_subset]
    ext p
    constructor
    · rintro ⟨hp_source, hpCplane_target⟩
      exact ⟨hp_source, hpCplane_target.1⟩
    · intro hp
      exact ⟨hp.1, hp.2, δ.map_source hp.1⟩
  have hs_open : IsOpen (δ.source ∩ δ ⁻¹' Cplane) := by
    rw [← hs_eq]
    exact hs_open_image
  let δ' := δ.restrOpen (δ.source ∩ δ ⁻¹' Cplane) hs_open
  have hbase_mem : (t₀, 0) ∈ δ.source ∩ δ ⁻¹' Cplane := by
    refine ⟨hδ.basePoint_mem_source, ?_⟩
    refine ⟨Complex.equivRealProdCLM.symm (γ t₀), hγC, ?_⟩
    exact (hδ.map_horizontal_axis hδ.basePoint_mem_horizontalAxisDomain).symm
  have hlocal : IsLocalCurveStraighteningAt γ 0 1 t₀ δ' :=
    hδ.toIsLocalCurveStraighteningAt.restrOpen hs_open hbase_mem
  refine ⟨δ', ?_⟩
  refine
    { toIsLocalCurveStraighteningAt := hlocal
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The restricted chart uses fewer right-side points, so the original exterior condition
    -- still rules out the intersection with `K ∩ C`.
    apply Set.not_nonempty_iff_eq_empty.1
    rintro ⟨z, hz⟩
    rcases hz with ⟨hz_image, hzKC⟩
    have hzK : z ∈ K := hzKC.1
    have hz_old :
        z ∈ Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p : Plane | p.2 < 0})) := by
      rcases hz_image with ⟨q, hq, rfl⟩
      rcases hq with ⟨p, hp, rfl⟩
      refine ⟨δ p, ?_, rfl⟩
      exact ⟨p, ⟨hp.1.1, hp.2⟩, rfl⟩
    have hz_oldK :
        z ∈ (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p : Plane | p.2 < 0}))) ∩ K :=
      ⟨hz_old, hzK⟩
    have : False := by
      simp [hδ.exterior_on_right] at hz_oldK
    exact this
  · -- On the left side, the restricted chart lands both in `interior K` and in the open set `C`.
    intro z hz
    rcases hz with ⟨q, hq, rfl⟩
    rcases hq with ⟨p, hp, rfl⟩
    have hp' : p ∈ (δ.source ∩ δ ⁻¹' Cplane) ∩ {p : Plane | 0 < p.2} := by
      simpa [δ'] using hp
    have hzInteriorK :
        Complex.equivRealProdCLM.symm (δ p) ∈ interior K := by
      exact hδ.interior_on_left ⟨δ p, ⟨p, ⟨hp'.1.1, hp'.2⟩, rfl⟩, rfl⟩
    have hzCplane : δ p ∈ Cplane := hp'.1.2
    rcases hzCplane with ⟨w, hwC, hwEq⟩
    have hzC : Complex.equivRealProdCLM.symm (δ p) ∈ C := by
      rw [← hwEq]
      simpa using hwC
    rw [interior_inter, hC_open.interior_eq]
    exact ⟨hzInteriorK, hzC⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: intersecting the compact owner with
one boundary component remains compact because `K` misses the frontier of that component. -/
theorem compact_inter_boundaryComponent
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsCompact (K ∩ C) := by
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  have hfrontierEmpty :
      frontier C ∩ K = ∅ :=
    boundaryComponent_frontier_disjoint_compactRegion hΓ hKD hD_open hC
  have hKC_eq : K ∩ C = K ∩ closure C := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, subset_closure hx.2⟩
    · intro hx
      by_cases hxC : x ∈ C
      · exact ⟨hx.1, hxC⟩
      · have hxFront : x ∈ frontier C := by
          rw [hC_open.frontier_eq]
          exact ⟨hx.2, hxC⟩
        have hnonempty : (frontier C ∩ K).Nonempty := ⟨x, ⟨hxFront, hx.1⟩⟩
        have hfalse : False := by
          simp [hfrontierEmpty] at hnonempty
        exact False.elim hfalse
  -- Rewrite the intersection against the closed set `closure C`, then use compactness of `K`.
  rw [hKC_eq]
  exact hΓ.isCompact.inter_right isClosed_closure

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: intersecting the compact region
with one boundary component does not create new frontier points outside that component. -/
theorem frontier_inter_boundaryComponent_eq
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    frontier (K ∩ C) = frontier K ∩ C := by
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  have hfrontierKC_subset_C : frontier (K ∩ C) ⊆ C := by
    intro x hx
    rw [frontier_eq_closure_inter_closure] at hx
    have hxClosure : x ∈ closure (K ∩ C) := hx.1
    have hxK : x ∈ K :=
      (closure_minimal Set.inter_subset_left hΓ.isCompact.isClosed) hxClosure
    by_contra hx_notC
    have hxFrontC : x ∈ frontier C := by
      rw [hC_open.frontier_eq]
      exact ⟨closure_mono Set.inter_subset_right hxClosure, hx_notC⟩
    have hfrontierEmpty :=
      boundaryComponent_frontier_disjoint_compactRegion hΓ hKD hD_open hC
    have hnonempty : (frontier C ∩ K).Nonempty := ⟨x, ⟨hxFrontC, hxK⟩⟩
    have hfalse : False := by
      simp [hfrontierEmpty] at hnonempty
    exact False.elim hfalse
  -- The frontier stays inside `C`, so the standard open-intersection formula becomes an equality.
  calc
    frontier (K ∩ C) = frontier (K ∩ C) ∩ C := by
      symm
      exact Set.inter_eq_left.mpr hfrontierKC_subset_C
    _ = frontier K ∩ C := frontier_inter_open_inter hC_open

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: restricting the boundary family to
one connected component cuts the global frontier down to `frontier K ∩ C`. -/
theorem iUnion_subtypeBoundaryPaths_eq_frontier_inter_boundaryComponent
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    (⋃ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C}, Set.range (Γ i.1).toPath) =
      frontier K ∩ C := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hix⟩
    exact
      ⟨hΓ.range_toPath_subset_frontier i.1 hix,
        (subtypeBoundaryPaths_subset_component hΓ hKD i) hix⟩
  · rintro ⟨hxFront, hxC⟩
    rcases Finset.mem_image.mp hC with ⟨i0, -, hi0C⟩
    rw [← hΓ.iUnion_range_eq_frontier] at hxFront
    rcases Set.mem_iUnion.mp hxFront with ⟨i, hix⟩
    have hxKey :
        x ∈ connectedComponentIn D ((Γ i).toPath 0) := by
      exact
        (range_toPath_subset_connectedComponent_domain
          (range_toPath_subset_domain_of_orientedBoundary hΓ hKD i)) hix
    have hCx : C = connectedComponentIn D x := by
      calc
        C = connectedComponentIn D ((Γ i0).toPath 0) := hi0C.symm
        _ = connectedComponentIn D x := connectedComponentIn_eq (hi0C.symm ▸ hxC)
    have hiC : connectedComponentIn D ((Γ i).toPath 0) = C := by
      exact (connectedComponentIn_eq hxKey).trans hCx.symm
    exact Set.mem_iUnion.mpr ⟨⟨i, hiC⟩, hix⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the total contour sum splits into
the finite block sums indexed by the connected components of `D` hit by the boundary family. -/
theorem sum_curveIntegral_eq_sum_component_blocks
    {ι : Type u} [Fintype ι] {D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {ω : ℂ → ℂ →L[ℝ] ℂ} :
    (∑ i, ∫ᶜ z in (Γ i).toPath, ω z) =
      (Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))).sum
        (fun c =>
          (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = c).sum
            (fun i => ∫ᶜ z in (Γ i).toPath, ω z)) := by
  classical
  let key : ι → Set ℂ := fun i => connectedComponentIn D ((Γ i).toPath 0)
  let value : ι → ℂ := fun i => ∫ᶜ z in (Γ i).toPath, ω z
  have hkey_mem : ∀ i : ι, key i ∈ Finset.univ.image key := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  -- Group the finite sum fiberwise by the connected-component key.
  calc
    ∑ i, value i =
        Finset.univ.sum fun i => if key i ∈ Finset.univ.image key then value i else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [hkey_mem i]
    _ =
        (Finset.univ.image key).sum
          (fun c => (Finset.univ.filter fun i => key i = c).sum value) := by
      symm
      simpa [Finset.sum_filter] using
        (Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.univ.image key) key value)
    _ =
        (Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))).sum
          (fun c =>
            (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = c).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, ω z)) := by
      simp [key, value]
