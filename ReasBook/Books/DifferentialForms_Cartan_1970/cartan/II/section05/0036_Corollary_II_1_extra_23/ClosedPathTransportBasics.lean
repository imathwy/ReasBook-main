import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0017_Definition_II_1_extra_10»
import DifferentialForms_Cartan_1970.II.section05.«0010_Proposition_4_1»

open scoped unitInterval

universe u

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a trivial endpoint cast does not
change piecewise differentiability of a path. -/
theorem Path.IsPiecewiseDifferentiable.castEndpoints
    {z0 z1 w0 w1 : ℂ} {γ : Path z0 z1}
    (hγ : γ.IsPiecewiseDifferentiable) (hz0 : w0 = z0) (hz1 : w1 = z1) :
    (γ.cast hz0 hz1).IsPiecewiseDifferentiable := by
  -- Endpoint casts only change the path indices, not the underlying map or its regularity.
  cases hz0
  cases hz1
  simpa using hγ

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a trivial endpoint cast does not
change null-homotopy of a closed path. -/
theorem isNullHomotopicClosedPathIn_castEndpoints
    {C : Set ℂ} {z0 w0 : ℂ} {γ : Path z0 z0}
    (hγ : IsNullHomotopicClosedPathIn C γ) (hz0 : w0 = z0) :
    IsNullHomotopicClosedPathIn C (γ.cast hz0 hz0) := by
  -- The casted closed path is propositionally the same loop, so the old contraction still works.
  cases hz0
  simpa using hγ

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a path homotopy whose every point
stays in `C` is automatically a closed-path homotopy in `C`. -/
theorem closedPathHomotopicIn_of_pathHomotopyIn
    {C : Set ℂ} {z0 : ℂ} {γ0 γ1 : Path z0 z0}
    (F : γ0.Homotopy γ1)
    (hF : ∀ p : I × I, F p ∈ C) :
    ClosedPathHomotopicIn C γ0 γ1 := by
  -- Package the path homotopy as a homotopy through closed paths, keeping the ambient-membership
  -- witness explicit at each time slice.
  refine ⟨{ toHomotopy := F.toHomotopy, prop' := ?_ }⟩
  intro t
  change IsClosedPathIn C ((F.eval t : Path z0 z0) : C(I, ℂ))
  refine ⟨(F.eval t).isClosedPath, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact hF (t, s)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: an axis-parallel rectangle boundary
has an explicit path homotopy in `C` to the constant loop at its initial vertex. -/
theorem axisParallelRectangleBoundaryPath_pathHomotopyConstIn_domain
    {C : Set ℂ} {z w : ℂ} (hrect : Complex.Rectangle z w ⊆ C) :
    ∃ F : (axisParallelRectangleBoundaryPath z w).Homotopy (Path.refl z),
      ∀ p : I × I, F p ∈ C := by
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
            -- At homotopy time `0`, this is the original rectangle boundary loop.
            intro t
            simp [AffineMap.lineMap_apply]
          map_one_left := by
            -- At homotopy time `1`, the whole loop has collapsed to the corner `z`.
            intro t
            simp [AffineMap.lineMap_apply] }
      prop' := by
        -- The contraction keeps the common start and end point fixed throughout.
        intro s t ht
        rcases ht with rfl | rfl <;> simp [γ, AffineMap.lineMap_apply] }
  have hFmaps : ∀ p : I × I, F p ∈ C := by
    intro p
    have hγRect : γ p.2 ∈ Complex.Rectangle z w := by
      exact axisParallelRectangleBoundaryPath_range_subset_rectangle z w ⟨p.2, rfl⟩
    have hs : (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := p.1.2
    -- Convexity keeps the straight-line contraction inside the same rectangle at every time.
    exact hrect (hconvRect.lineMap_mem hγRect hzRect hs)
  exact ⟨F, hFmaps⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: an axis-parallel rectangle boundary
is already closed-path homotopic in `C` to the constant loop at its initial vertex. -/
theorem axisParallelRectangleBoundaryPath_closedPathHomotopicIn_constIn_domain
    {C : Set ℂ} {z w : ℂ} (hrect : Complex.Rectangle z w ⊆ C) :
    ClosedPathHomotopicIn C (axisParallelRectangleBoundaryPath z w) (Path.refl z) := by
  -- Repackage the explicit rectangle contraction as a homotopy through closed paths in `C`.
  rcases axisParallelRectangleBoundaryPath_pathHomotopyConstIn_domain hrect with ⟨F, hFmaps⟩
  exact closedPathHomotopicIn_of_pathHomotopyIn F hFmaps

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a closed-path homotopy to a constant
loop is already the required null-homotopy in the same ambient domain. -/
theorem isNullHomotopicClosedPathIn_of_closedPathHomotopicIn_const
    {C : Set ℂ} {z0 x : ℂ} {γ : Path z0 z0}
    (hhom : ClosedPathHomotopicIn C γ (Path.refl x))
    (hxC : x ∈ C) :
    IsNullHomotopicClosedPathIn C γ := by
  -- Unpack the definition: null-homotopy in `C` is exactly a closed-path homotopy to some
  -- constant loop with value in `C`.
  exact ⟨x, hxC, hhom⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: unpacking `toClosedPath.toPath`
only inserts the trivial endpoint cast on a loop. -/
theorem loopToClosedPath_toPath_eq_cast {z : ℂ} (γ : Path z z) :
    γ.toClosedPath.toPath = γ.cast γ.source γ.source := by
  cases γ
  rfl

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: sending a loop through
`toClosedPath.toPath` does not change its contour integral. -/
theorem curveIntegral_toClosedPath_toPath_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {z : ℂ} (ω : ℂ → ℂ →L[ℝ] F) (γ : Path z z) :
    ∫ᶜ x in γ.toClosedPath.toPath, ω x = ∫ᶜ x in γ, ω x := by
  -- Push the endpoint cast down to the curve-integrand level before comparing the two integrals.
  rw [loopToClosedPath_toPath_eq_cast, curveIntegral_def', curveIntegral_def']
  change
    ∫ t in (0 : ℝ)..1, curveIntegralFun (fun x ↦ ω x) (γ.cast γ.source γ.source) t =
      ∫ t in (0 : ℝ)..1, curveIntegralFun (fun x ↦ ω x) γ t
  simpa using
    congrArg
      (fun f : ℝ → F ↦ ∫ t in (0 : ℝ)..1, f t)
      (curveIntegralFun_cast (fun x ↦ ω x) γ γ.source γ.source)
