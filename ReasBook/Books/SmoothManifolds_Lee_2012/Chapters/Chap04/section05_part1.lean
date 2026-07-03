import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_4_5 (from Chap04/Sec04_27) -/
noncomputable section

open Projectivization
open scoped LinearAlgebra.Projectivization Manifold ContDiff

-- Local API note: this file reuses the chapter's `ComplexProjectiveSpace` owner together with the
-- canonical projectivization constructor `Projectivization.mk'` on the punctured subtype.
attribute [local instance] Classical.propDecidable

local notation "CVec" n => EuclideanSpace ℂ (Fin (n + 1))
local notation "Ipunct" n => 𝓘(ℝ, CVec n)
local notation "Icp" n => 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
local notation "unitSphere2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The punctured complex Euclidean space `ℂ^(n+1) \ {0}` as an open submanifold of `ℂ^(n+1)`. -/
def puncturedComplexEuclidean (n : ℕ) : TopologicalSpace.Opens (CVec n) :=
  ⟨{ z | z ≠ 0 }, isOpen_ne⟩

/-- Membership in `puncturedComplexEuclidean n` is exactly nonvanishing. -/
@[simp] theorem mem_puncturedComplexEuclidean_iff {n : ℕ} {z : CVec n} :
    z ∈ puncturedComplexEuclidean n ↔ z ≠ 0 :=
  Iff.rfl

/-- Helper for Problem 4-5: every standard affine chart of `ℂPⁿ` already belongs to the smooth
maximal atlas. -/
theorem complex_projective_chart_mem_maximal_atlas (n : ℕ) (i : Fin (n + 1)) :
    complexProjectiveChart n i ∈ IsManifold.maximalAtlas (Icp n) ∞ (ℂP[n]) := by
  have hAtlas : complexProjectiveChart n i ∈ atlas (EuclideanSpace ℂ (Fin n)) (ℂP[n]) := by
    change complexProjectiveChart n i ∈ { e | ∃ j : Fin (n + 1), e = complexProjectiveChart n j }
    exact ⟨i, rfl⟩
  exact IsManifold.subset_maximalAtlas hAtlas

/-- Helper for Problem 4-5: the inserted homogeneous representative has distinguished coordinate
equal to `1`. -/
theorem complex_projective_chart_inv_vector_apply_self (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    complexProjectiveChartInvVector n i u i = 1 := by
  simp [complexProjectiveChartInvVector]

/-- Helper for Problem 4-5: away from the distinguished slot, the inserted homogeneous
representative recovers the affine coordinates. -/
theorem complex_projective_chart_inv_vector_apply_succAbove (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    complexProjectiveChartInvVector n i u (i.succAbove j) = u j := by
  simp [complexProjectiveChartInvVector]

/-- Helper for Problem 4-5: if the `i`th homogeneous coordinate of a punctured vector is nonzero,
then its projective class lies in the `i`th affine chart domain. -/
theorem complex_projective_quotient_mem_chart_domain (n : ℕ) (i : Fin (n + 1))
    (z : puncturedComplexEuclidean n) (hzi : (z : CVec n) i ≠ 0) :
    mk' ℂ z ∈ complexProjectiveChartDomain n i := by
  -- Rewrite the quotient point using its explicit nonzero representative.
  simpa [Projectivization.mk'_eq_mk] using
    (complexProjectiveChartDomain_mk n i (z : CVec n) z.2).2 hzi

/-- Helper for Problem 4-5: scaling the standard inserted representative by a nonzero scalar keeps
it in the punctured ambient space. -/
theorem complex_projective_scaled_chart_lift_ne_zero (n : ℕ) (i : Fin (n + 1))
    (c : ℂ) (hc : c ≠ 0) (u : EuclideanSpace ℂ (Fin n)) :
    c • complexProjectiveChartInvVector n i u ≠ 0 := by
  exact smul_ne_zero hc (complexProjectiveChartInvVector_ne_zero n i u)

/-- Helper for Problem 4-5: over the `i`th affine chart, rescale the standard inserted
representative by a fixed nonzero complex scalar. -/
def complexProjectiveScaledChartSection (n : ℕ) (i : Fin (n + 1)) (c : ℂ) (hc : c ≠ 0) :
    (⟨complexProjectiveChartDomain n i, complexProjectiveChartDomain_isOpen n i⟩ :
      TopologicalSpace.Opens (ℂP[n])) → puncturedComplexEuclidean n :=
  fun x ↦
    ⟨c • complexProjectiveChartInvVector n i (complexProjectiveChart n i x.1),
      complex_projective_scaled_chart_lift_ne_zero n i c hc (complexProjectiveChart n i x.1)⟩

/-- Helper for Problem 4-5: every scaled affine-chart representative projects back to the original
point of the chart domain. -/
theorem complex_projective_scaled_chart_section_apply_eq (n : ℕ) (i : Fin (n + 1))
    (c : ℂ) (hc : c ≠ 0)
    (x : (⟨complexProjectiveChartDomain n i, complexProjectiveChartDomain_isOpen n i⟩ :
      TopologicalSpace.Opens (ℂP[n]))) :
    mk' ℂ (complexProjectiveScaledChartSection n i c hc x) = x.1 := by
  have hscaled :
      mk' ℂ (complexProjectiveScaledChartSection n i c hc x) =
        mk ℂ
          (complexProjectiveChartInvVector n i (complexProjectiveChart n i x.1))
          (complexProjectiveChartInvVector_ne_zero n i (complexProjectiveChart n i x.1)) := by
    -- Scaling by a nonzero complex number does not change the projective class.
    rw [Projectivization.mk'_eq_mk]
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _
      (complex_projective_scaled_chart_lift_ne_zero n i c hc (complexProjectiveChart n i x.1))
      (complexProjectiveChartInvVector_ne_zero n i (complexProjectiveChart n i x.1))).2 ?_
    exact ⟨c, rfl⟩
  have hinv :
      mk ℂ
          (complexProjectiveChartInvVector n i (complexProjectiveChart n i x.1))
          (complexProjectiveChartInvVector_ne_zero n i (complexProjectiveChart n i x.1)) = x.1 := by
    -- The unscaled inserted representative is exactly the inverse branch of the affine chart.
    change (complexProjectiveChart n i).symm ((complexProjectiveChart n i) x.1) = x.1
    exact (complexProjectiveChart n i).left_inv x.2
  exact hscaled.trans hinv

/-- Helper for Problem 4-5: on the `i`th affine chart, the quotient map is the usual coordinate
ratio map. -/
theorem complex_projective_quotient_map_restricted_chart_formula (n : ℕ) (i : Fin (n + 1))
    (z : puncturedComplexEuclidean n) (_hzi : (z : CVec n) i ≠ 0) :
    complexProjectiveChart n i (mk' ℂ z) =
      (EuclideanSpace.equiv (Fin n) ℂ).symm
        (fun j ↦ (z : CVec n) (i.succAbove j) / (z : CVec n) i) := by
  -- Rewrite the quotient point by its explicit nonzero representative and apply the chart formula.
  simpa [Projectivization.mk'_eq_mk] using
    (complexProjectiveChart_mk n i (z : CVec n) z.2)

/-- Helper for Problem 4-5: choosing the scale factor from a punctured vector recovers that exact
vector at its own projective class. -/
theorem complex_projective_scaled_chart_section_through_point (n : ℕ) (i : Fin (n + 1))
    (z : puncturedComplexEuclidean n) (hzi : (z : CVec n) i ≠ 0) :
    complexProjectiveScaledChartSection n i ((z : CVec n) i) hzi
      ⟨mk' ℂ z, complex_projective_quotient_mem_chart_domain n i z hzi⟩ = z := by
  apply Subtype.ext
  ext k
  cases k using i.succAboveCases with
  | x =>
      -- At the distinguished slot, the chosen scaling factor reproduces the original coordinate.
      simp [complexProjectiveScaledChartSection,
        complex_projective_chart_inv_vector_apply_self]
  | p j =>
      -- Away from the distinguished slot, the chart coordinate is `z (i.succAbove j) / z i`.
      simp [complexProjectiveScaledChartSection,
        complex_projective_chart_inv_vector_apply_succAbove, hzi, div_eq_mul_inv, mul_comm]

/-- Helper for Problem 4-5: the rescaled homogeneous insertion map is smooth in affine
coordinates. -/
theorem complex_projective_scaled_inv_vector_cont_mdiff (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    ContMDiff (Icp n) (𝓘(ℝ, CVec n)) ∞
      (fun u : EuclideanSpace ℂ (Fin n) ↦ c • complexProjectiveChartInvVector n i u) := by
  rw [contMDiff_iff_contDiff, contDiff_piLp]
  intro j
  cases j using i.succAboveCases with
  | x =>
      -- At the distinguished coordinate, the scaled inserted vector is the constant map `c`.
      have hcoord :
          (fun u : EuclideanSpace ℂ (Fin n) ↦ (c • complexProjectiveChartInvVector n i u) i) =
            fun _ : EuclideanSpace ℂ (Fin n) ↦ c := by
        funext u
        simpa [complexProjectiveChartInvVector]
      rw [hcoord]
      exact contDiff_const
  | p k =>
      -- Every other coordinate is the scalar multiple `c * u k` of the corresponding affine
      -- coordinate projection.
      have hcoord :
          (fun u : EuclideanSpace ℂ (Fin n) ↦
            (c • complexProjectiveChartInvVector n i u) (i.succAbove k)) =
              fun u : EuclideanSpace ℂ (Fin n) ↦ c * u k := by
        funext u
        simpa [complexProjectiveChartInvVector]
      rw [hcoord]
      exact contDiff_const.mul
        ((contDiff_piLp_apply (p := 2) (i := k)) :
          ContDiff ℝ ∞ (fun u : EuclideanSpace ℂ (Fin n) ↦ u k))

/-- Helper for Problem 4-5: the scaled affine-chart section is smooth as a map into the punctured
ambient space. -/
theorem complex_projective_scaled_chart_section_cont_mdiff (n : ℕ) (i : Fin (n + 1))
    (c : ℂ) (hc : c ≠ 0) :
    ContMDiff (Icp n) (Ipunct n) ∞ (complexProjectiveScaledChartSection n i c hc) := by
  let U : TopologicalSpace.Opens (ℂP[n]) :=
    ⟨complexProjectiveChartDomain n i, complexProjectiveChartDomain_isOpen n i⟩
  let f : U → (⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))) :=
    fun x ↦
      show (⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))) from
        (complexProjectiveChart n i).toHomeomorphSourceTarget x
  have hmemω :
      complexProjectiveChart n i ∈ IsManifold.maximalAtlas (Icp n) ω (ℂP[n]) := by
    have hAtlas : complexProjectiveChart n i ∈ atlas (EuclideanSpace ℂ (Fin n)) (ℂP[n]) := by
      change complexProjectiveChart n i ∈ { e | ∃ j : Fin (n + 1), e = complexProjectiveChart n j }
      exact ⟨i, rfl⟩
    exact IsManifold.subset_maximalAtlas hAtlas
  have hf :
      ContMDiff (Icp n) (Icp n) ∞ f := by
    -- The projective chart is smooth as a map from its source subtype to the Euclidean target.
    simpa [f] using
      smoothChart_contMDiff_toHomeomorphSourceTarget
        (e := complexProjectiveChart n i)
        (he := hmemω)
  have hchart :
      ContMDiff (Icp n) (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
        (fun x : U ↦ complexProjectiveChart n i x.1) := by
    have hchartHomeo :
        ContMDiff (Icp n) (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
          (fun x : U ↦
            ((complexProjectiveChart n i).toHomeomorphSourceTarget x :
              EuclideanSpace ℂ (Fin n))) := by
      exact
        (contMDiff_subtype_val
          (I := Icp n)
          (U := (⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))))).comp
          hf
    exact hchartHomeo.congr fun x ↦ rfl
  have hambient :
      ContMDiff (Icp n) (𝓘(ℝ, CVec n)) ∞
        (fun x : U ↦ c • complexProjectiveChartInvVector n i (complexProjectiveChart n i x.1)) := by
    -- Compose the smooth affine chart with the smooth inserted-representative map.
    exact (complex_projective_scaled_inv_vector_cont_mdiff n i c).comp hchart
  have hambientSection :
      ContMDiff (Icp n) (𝓘(ℝ, CVec n)) ∞
        (fun x : U ↦
          ((complexProjectiveScaledChartSection n i c hc x : puncturedComplexEuclidean n) : CVec n)) := by
    exact hambient.congr fun x ↦ rfl
  exact
    (ContMDiff.subtypeVal_comp_iff (puncturedComplexEuclidean n)
      (complexProjectiveScaledChartSection n i c hc)).1 hambientSection

/-- Helper for Problem 4-5: over each affine chart, the scaled representative map is a smooth local
section of the quotient map. -/
theorem complex_projective_scaled_chart_section_is_smooth_local_section (n : ℕ)
    (i : Fin (n + 1)) (c : ℂ) (hc : c ≠ 0) :
    Manifold.IsSmoothLocalSection (Ipunct n) (Icp n)
      (fun z : puncturedComplexEuclidean n ↦ mk' ℂ z)
      (⟨complexProjectiveChartDomain n i, complexProjectiveChartDomain_isOpen n i⟩ :
        TopologicalSpace.Opens (ℂP[n]))
      (complexProjectiveScaledChartSection n i c hc) := by
  constructor
  · -- Smoothness is the chartwise smoothness already established for the scaled section.
    exact complex_projective_scaled_chart_section_cont_mdiff n i c hc
  · -- The section equation is exactly the projective-class identity proved above.
    intro x
    exact complex_projective_scaled_chart_section_apply_eq n i c hc x

/-- Problem 4-5 (1): the canonical quotient map `π : ℂ^(n+1) \ {0} → ℂPⁿ` is surjective. -/
theorem complexProjectiveQuotientMap_surjective (n : ℕ) :
    Function.Surjective (fun z : puncturedComplexEuclidean n ↦ mk' ℂ z) := by
  intro x
  -- Use the canonical nonzero representative chosen by the projectivization API.
  refine ⟨⟨x.rep, x.rep_nonzero⟩, ?_⟩
  simpa [Projectivization.mk'_eq_mk, x.mk_rep]

/-- Helper for Problem 4-5: a punctured homogeneous vector has some nonzero coordinate. -/
theorem punctured_complex_euclidean_exists_nonzero_coord (n : ℕ)
    (z : puncturedComplexEuclidean n) :
    ∃ i : Fin (n + 1), (z : CVec n) i ≠ 0 := by
  by_contra h
  apply z.2
  ext i
  by_contra hzi
  exact h ⟨i, hzi⟩

-- The remaining smoothness proof first isolates the explicit affine ratio map on a standard chart.
/-- Helper for Problem 4-5: on the open locus where the `i`th homogeneous coordinate does not
vanish, the affine ratio map is smooth. -/
theorem complex_projective_ratio_map_contDiffOn (n : ℕ) (i : Fin (n + 1)) :
    ContDiffOn ℝ ∞
      (fun z : CVec n ↦
        (EuclideanSpace.equiv (Fin n) ℂ).symm (fun j ↦ z (i.succAbove j) / z i))
      { z : CVec n | z i ≠ 0 } := by
  rw [contDiffOn_piLp]
  intro j
  -- Each affine coordinate is a quotient of two smooth coordinate projections on the nonvanishing
  -- denominator locus.
  exact
    (((contDiff_piLp_apply (p := 2) (i := i.succAbove j)) :
        ContDiff ℝ ∞ (fun z : CVec n ↦ z (i.succAbove j))).contDiffOn).mul
      ((((contDiff_piLp_apply (p := 2) (i := i)) :
          ContDiff ℝ ∞ (fun z : CVec n ↦ z i)).contDiffOn).inv (fun z hz ↦ hz))

/-- Helper for Problem 4-5: if a homogeneous coordinate is nonzero at `z`, the quotient map is
smooth at `z` through the corresponding affine chart. -/
theorem complex_projective_quotient_map_contMDiffAt_of_nonzero_coord (n : ℕ)
    (i : Fin (n + 1)) (z : puncturedComplexEuclidean n) (hzi : (z : CVec n) i ≠ 0) :
    ContMDiffAt (Ipunct n) (Icp n) ∞ (fun w : puncturedComplexEuclidean n ↦ mk' ℂ w) z := by
  let ratio : EuclideanSpace ℂ (Fin (n + 1)) → EuclideanSpace ℂ (Fin n) :=
    fun w ↦ (EuclideanSpace.equiv (Fin n) ℂ).symm
      (fun j ↦ w (i.succAbove j) / w i)
  have hratio_at :
      ContDiffAt ℝ ∞ ratio (z : CVec n) := by
    -- The chart formula is smooth on the open nonvanishing-coordinate locus.
    exact (complex_projective_ratio_map_contDiffOn n i).contDiffAt <| by
      have hsOpen : IsOpen { w : CVec n | w i ≠ 0 } := by
        simpa using isOpen_ne_fun
          ((PiLp.continuous_apply 2 _ i) : Continuous fun w : CVec n ↦ w i)
          continuous_const
      exact hsOpen.mem_nhds hzi
  have hratio_subtype :
      ContMDiffAt (Ipunct n) (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ∞
        (fun w : puncturedComplexEuclidean n ↦ ratio w) z := by
    -- Passing from the punctured open subtype to the ambient vector space introduces no new
    -- smoothness issue.
    rw [contMDiffAt_subtype_iff (U := puncturedComplexEuclidean n) (f := ratio) (x := z)]
    exact hratio_at.contMDiffAt
  have hsymm :
      ContMDiffAt (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (Icp n) ∞
        (complexProjectiveChart n i).symm (ratio (z : CVec n)) := by
    have hmax := complex_projective_chart_mem_maximal_atlas n i
    -- The inverse affine chart is smooth on its Euclidean target.
    simpa [ratio] using
      contMDiffAt_symm_of_mem_maximalAtlas hmax
        (by simp : ratio (z : CVec n) ∈ Set.univ)
  have hcomp :
      ContMDiffAt (Ipunct n) (Icp n) ∞
        ((complexProjectiveChart n i).symm ∘ fun w : puncturedComplexEuclidean n ↦ ratio w) z := by
    -- Compose the smooth ratio map with the smooth inverse affine chart.
    exact hsymm.comp z hratio_subtype
  have hEq :
      (fun w : puncturedComplexEuclidean n ↦ mk' ℂ w) =ᶠ[nhds z]
        ((complexProjectiveChart n i).symm ∘ fun w : puncturedComplexEuclidean n ↦ ratio w) := by
    have hsOpen : IsOpen { w : puncturedComplexEuclidean n | (w : CVec n) i ≠ 0 } := by
      simpa using isOpen_ne_fun
        (((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val) :
          Continuous fun w : puncturedComplexEuclidean n ↦ (w : CVec n) i)
        continuous_const
    have hsNhds : { w : puncturedComplexEuclidean n | (w : CVec n) i ≠ 0 } ∈ nhds z :=
      hsOpen.mem_nhds hzi
    filter_upwards [hsNhds] with w hw
    have hwDomain : mk' ℂ w ∈ complexProjectiveChartDomain n i :=
      complex_projective_quotient_mem_chart_domain n i w hw
    have hleft := OpenPartialHomeomorph.left_inv (complexProjectiveChart n i) hwDomain
    -- Route correction: instead of fighting chart transport directly, identify the quotient map
    -- locally with the inverse affine chart applied to the explicit ratio map.
    rw [complex_projective_quotient_map_restricted_chart_formula n i w hw] at hleft
    simpa [Function.comp, ratio] using hleft.symm
  exact hcomp.congr_of_eventuallyEq hEq

/-- Helper for Problem 4-5: on each punctured vector, choose a nonzero homogeneous coordinate and
apply the corresponding affine-chart smoothness lemma. -/
theorem complex_projective_quotient_map_cont_mdiff (n : ℕ) :
    ContMDiff (Ipunct n) (Icp n) ∞ (fun z : puncturedComplexEuclidean n ↦ mk' ℂ z) := by
  intro z
  -- A nonzero homogeneous vector lies in some standard affine chart, and that chart gives the
  -- smooth local expression for the quotient map.
  rcases punctured_complex_euclidean_exists_nonzero_coord n z with ⟨i, hzi⟩
  exact complex_projective_quotient_map_contMDiffAt_of_nonzero_coord n i z hzi

/-- Problem 4-5 (2): the canonical quotient map `π : ℂ^(n+1) \ {0} → ℂPⁿ` is a smooth
submersion. -/
theorem complexProjectiveQuotientMap_isSmoothSubmersion (n : ℕ) :
    Manifold.IsSmoothSubmersion (Ipunct n) (Icp n)
      (fun z : puncturedComplexEuclidean n ↦ mk' ℂ z) := by
  refine ⟨complex_projective_quotient_map_cont_mdiff n, ?_⟩
  -- Apply the local-section criterion using the affine chart through a nonzero coordinate of `z`.
  have hsections :
      ∀ z : puncturedComplexEuclidean n,
        ∃ U : TopologicalSpace.Opens (ℂP[n]), ∃ hzU : mk' ℂ z ∈ U, ∃ σ : U → puncturedComplexEuclidean n,
          Manifold.IsSmoothLocalSection (Ipunct n) (Icp n)
            (fun w : puncturedComplexEuclidean n ↦ mk' ℂ w) U σ ∧
            σ ⟨mk' ℂ z, hzU⟩ = z := by
    intro z
    rcases punctured_complex_euclidean_exists_nonzero_coord n z with ⟨i, hzi⟩
    let U : TopologicalSpace.Opens (ℂP[n]) :=
      ⟨complexProjectiveChartDomain n i, complexProjectiveChartDomain_isOpen n i⟩
    let σ : U → puncturedComplexEuclidean n :=
      complexProjectiveScaledChartSection n i ((z : CVec n) i) hzi
    have hzU : mk' ℂ z ∈ U := complex_projective_quotient_mem_chart_domain n i z hzi
    refine ⟨U, hzU, σ, ?_, ?_⟩
    · -- This chartwise section is smooth by construction.
      exact complex_projective_scaled_chart_section_is_smooth_local_section n i ((z : CVec n) i) hzi
    · -- Choosing the scale factor from `z` makes the local section pass through `z`.
      exact complex_projective_scaled_chart_section_through_point n i z hzi
  exact
    (Manifold.smooth_submersion_iff_exists_smooth_local_section_through_every_point
      (complex_projective_quotient_map_cont_mdiff n)).2 hsections

/-- Helper for Problem 4-5: identify the unique complex affine coordinate of `ℂP¹` with the real
plane `ℝ²`. -/
def complexCoordinateAsPlane (z : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (Complex.equivRealProd z))

/-- Helper for Problem 4-5: recover the complex affine coordinate from its `ℝ²` image. -/
def planeCoordinateAsComplex (u : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  Complex.equivRealProd.symm
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
      ((EuclideanSpace.equiv (Fin 2) ℝ) u))

/-- Helper for Problem 4-5: the `ℂ ≃ ℝ²` adapter is inverted by `planeCoordinateAsComplex`. -/
theorem planeCoordinateAsComplex_complexCoordinateAsPlane (z : ℂ) :
    planeCoordinateAsComplex (complexCoordinateAsPlane z) = z := by
  -- Unfold both adapters and simplify the two inverse linear equivalences.
  simp [planeCoordinateAsComplex, complexCoordinateAsPlane]

/-- Helper for Problem 4-5: `planeCoordinateAsComplex` is a left inverse to the real-plane
adapter. -/
theorem complexCoordinateAsPlane_planeCoordinateAsComplex (u : EuclideanSpace ℝ (Fin 2)) :
    complexCoordinateAsPlane (planeCoordinateAsComplex u) = u := by
  -- Unfold both adapters and simplify the two inverse linear equivalences.
  ext i
  fin_cases i <;> simp [planeCoordinateAsComplex, complexCoordinateAsPlane]

/-- Helper for Problem 4-5: the real-plane adapter reads the real part in coordinate `0`. -/
theorem complexCoordinateAsPlane_apply_zero (z : ℂ) :
    complexCoordinateAsPlane z 0 = z.re := by
  -- Unfold the fixed `ℂ ≃ ℝ²` adapter and read off the first coordinate.
  simp [complexCoordinateAsPlane]

/-- Helper for Problem 4-5: the real-plane adapter reads the imaginary part in coordinate `1`. -/
theorem complexCoordinateAsPlane_apply_one (z : ℂ) :
    complexCoordinateAsPlane z 1 = z.im := by
  -- Unfold the fixed `ℂ ≃ ℝ²` adapter and read off the second coordinate.
  simp [complexCoordinateAsPlane]

/-- Helper for Problem 4-5: `planeCoordinateAsComplex` recovers the first real coordinate as the
real part. -/
theorem planeCoordinateAsComplex_re (u : EuclideanSpace ℝ (Fin 2)) :
    (planeCoordinateAsComplex u).re = u 0 := by
  -- Unfold the inverse adapter and read off the real part.
  simp [planeCoordinateAsComplex]

/-- Helper for Problem 4-5: `planeCoordinateAsComplex` recovers the second real coordinate as the
imaginary part. -/
theorem planeCoordinateAsComplex_im (u : EuclideanSpace ℝ (Fin 2)) :
    (planeCoordinateAsComplex u).im = u 1 := by
  -- Unfold the inverse adapter and read off the imaginary part.
  simp [planeCoordinateAsComplex]

/-- Helper for Problem 4-5: converting a real scalar multiple in `ℝ²` back to `ℂ` multiplies by
the corresponding real complex scalar. -/
theorem planeCoordinateAsComplex_real_smul (a : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeCoordinateAsComplex (a • u) = (a : ℂ) * planeCoordinateAsComplex u := by
  -- Compare real and imaginary parts after transporting the real scalar through the adapter.
  refine Complex.ext_iff.2 ?_
  constructor <;> simp [planeCoordinateAsComplex_re, planeCoordinateAsComplex_im, Complex.mul_re,
    Complex.mul_im]

/-- Helper for Problem 4-5: the `ℂ ≃ ℝ²` adapter preserves the squared norm. -/
theorem complexCoordinateAsPlane_norm_sq (z : ℂ) :
    ‖complexCoordinateAsPlane z‖ ^ 2 = Complex.normSq z := by
  -- Expand both sides into the sum of squares of the real and imaginary coordinates.
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [complexCoordinateAsPlane_apply_zero, complexCoordinateAsPlane_apply_one,
    Complex.normSq_apply]
  ring

/-- Helper for Problem 4-5: inserting the unique complex affine coordinate into
`EuclideanSpace ℂ (Fin 1)` is smooth. -/
theorem complex_projective_line_single_contDiff :
    ContDiff ℝ ∞
      (fun z : ℂ ↦ (EuclideanSpace.single (0 : Fin 1) z : EuclideanSpace ℂ (Fin 1))) := by
  -- Rewrite the insertion map as scalar multiplication by the fixed basis vector.
  have hsingle_eq :
      (fun z : ℂ ↦ (EuclideanSpace.single (0 : Fin 1) z : EuclideanSpace ℂ (Fin 1))) =
        fun z : ℂ ↦ z • EuclideanSpace.single (0 : Fin 1) (1 : ℂ) := by
    funext z
    ext i
    fin_cases i
    simp
  rw [hsingle_eq]
  exact contDiff_id.smul
    (contDiff_const : ContDiff ℝ ∞ fun _ : ℂ ↦
      (EuclideanSpace.single (0 : Fin 1) (1 : ℂ) : EuclideanSpace ℂ (Fin 1)))

/-- Helper for Problem 4-5: the fixed real-linear identification `ℂ → ℝ²` is smooth. -/
theorem complexCoordinateAsPlane_contDiff :
    ContDiff ℝ ∞ complexCoordinateAsPlane := by
  -- Prove smoothness coordinatewise using the real and imaginary coordinate projections.
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simpa [complexCoordinateAsPlane_apply_zero] using Complex.reCLM.contDiff
  · simpa [complexCoordinateAsPlane_apply_one] using Complex.imCLM.contDiff

/-- Helper for Problem 4-5: the inverse identification `ℝ² → ℂ` is smooth. -/
theorem planeCoordinateAsComplex_contDiff :
    ContDiff ℝ ∞ planeCoordinateAsComplex := by
  -- Rewrite the inverse adapter into the explicit affine-linear complex formula.
  have hformula :
      planeCoordinateAsComplex =
        fun u : EuclideanSpace ℝ (Fin 2) ↦ (u 0 : ℂ) + (u 1 : ℂ) * Complex.I := by
    funext u
    apply Complex.ext <;> simp [planeCoordinateAsComplex]
  rw [hformula]
  -- Each real coordinate projection becomes a smooth complex-valued map via `Complex.ofRealCLM`.
  have hzero :
      ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 2) ↦ (u 0 : ℂ)) := by
    simpa [Function.comp] using
      Complex.ofRealCLM.contDiff.comp
        ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))) :
          ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 2) ↦ u 0))
  have hone :
      ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 2) ↦ (u 1 : ℂ)) := by
    simpa [Function.comp] using
      Complex.ofRealCLM.contDiff.comp
        ((contDiff_piLp_apply (p := 2) (i := (1 : Fin 2))) :
          ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 2) ↦ u 1))
  -- The explicit formula is a sum of two smooth complex-valued coordinate expressions.
  exact hzero.add <| hone.mul
    (contDiff_const : ContDiff ℝ ∞ fun _ : EuclideanSpace ℝ (Fin 2) ↦ (Complex.I : ℂ))

/-- Helper for Problem 4-5: the south-chart model map reads the unique complex coordinate and
converts it to `ℝ²`. -/
def complex_projective_line_model_forward :
    EuclideanSpace ℂ (Fin 1) → EuclideanSpace ℝ (Fin 2) :=
  fun u ↦ complexCoordinateAsPlane (u 0)

/-- Helper for Problem 4-5: the inverse south-chart model map inserts a complex coordinate back
into `EuclideanSpace ℂ (Fin 1)`. -/
def complex_projective_line_model_inverse :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℂ (Fin 1) :=
  fun v ↦ EuclideanSpace.single 0 (planeCoordinateAsComplex v)

/-- Helper for Problem 4-5: the south-chart model map is inverted by the insertion map. -/
theorem complex_projective_line_model_left_inv (u : EuclideanSpace ℂ (Fin 1)) :
    complex_projective_line_model_inverse (complex_projective_line_model_forward u) = u := by
  -- Recover the unique complex coordinate and then use extensionality on `Fin 1`.
  ext i
  fin_cases i
  simp [complex_projective_line_model_forward, complex_projective_line_model_inverse,
    planeCoordinateAsComplex_complexCoordinateAsPlane]

/-- Helper for Problem 4-5: inserting a complex coordinate and then reading it back gives the
identity on `ℝ²`. -/
theorem complex_projective_line_model_right_inv (v : EuclideanSpace ℝ (Fin 2)) :
    complex_projective_line_model_forward (complex_projective_line_model_inverse v) = v := by
  -- The adapter pair `ℂ ↔ ℝ²` is already known to be inverse.
  simpa [complex_projective_line_model_forward, complex_projective_line_model_inverse] using
    complexCoordinateAsPlane_planeCoordinateAsComplex v

/-- Helper for Problem 4-5: the south-chart model map is smooth. -/
theorem complex_projective_line_model_forward_contMDiff :
    ContMDiff (Icp 1) (𝓡 2) ∞ complex_projective_line_model_forward := by
  -- Compose the smooth coordinate projection with the fixed `ℂ ≃ ℝ²` adapter.
  rw [contMDiff_iff_contDiff]
  simpa [complex_projective_line_model_forward, Function.comp] using
    complexCoordinateAsPlane_contDiff.comp
      ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 1))) :
        ContDiff ℝ ∞ (fun u : EuclideanSpace ℂ (Fin 1) ↦ u 0))

/-- Helper for Problem 4-5: the inverse south-chart model map is smooth. -/
theorem complex_projective_line_model_inverse_contMDiff :
    ContMDiff (𝓡 2) (Icp 1) ∞ complex_projective_line_model_inverse := by
  -- First recover the complex coordinate from `ℝ²`, then reinsert it into `ℂ¹`.
  rw [contMDiff_iff_contDiff]
  simpa [complex_projective_line_model_inverse, Function.comp] using
    complex_projective_line_single_contDiff.comp planeCoordinateAsComplex_contDiff

/-- Helper for Problem 4-5: the south-chart affine model is a diffeomorphism
`ℂ¹ ≃ ℝ²`. -/
def complex_projective_line_model_diffeomorph :
    EuclideanSpace ℂ (Fin 1) ≃ₘ⟮Icp 1, 𝓡 2⟯ EuclideanSpace ℝ (Fin 2) where
  toEquiv :=
    { toFun := complex_projective_line_model_forward
      invFun := complex_projective_line_model_inverse
      left_inv := complex_projective_line_model_left_inv
      right_inv := complex_projective_line_model_right_inv }
  contMDiff_toFun := complex_projective_line_model_forward_contMDiff
  contMDiff_invFun := complex_projective_line_model_inverse_contMDiff

/-- Helper for Problem 4-5: the conjugation model on `ℂ¹` reads the unique affine coordinate,
complex-conjugates it, and reinserts it. -/
def complex_projective_line_conj_forward :
    EuclideanSpace ℂ (Fin 1) → EuclideanSpace ℂ (Fin 1) :=
  fun u ↦ EuclideanSpace.single 0 (star (u 0))

/-- Helper for Problem 4-5: the conjugation model is its own inverse. -/
def complex_projective_line_conj_inverse :
    EuclideanSpace ℂ (Fin 1) → EuclideanSpace ℂ (Fin 1) :=
  complex_projective_line_conj_forward

/-- Helper for Problem 4-5: the conjugation model on `ℂ¹` is involutive. -/
theorem complex_projective_line_conj_left_inv (u : EuclideanSpace ℂ (Fin 1)) :
    complex_projective_line_conj_inverse (complex_projective_line_conj_forward u) = u := by
  -- Complex conjugation is involutive on the unique affine coordinate.
  ext i
  fin_cases i
  simp [complex_projective_line_conj_forward, complex_projective_line_conj_inverse]

/-- Helper for Problem 4-5: the conjugation model on `ℂ¹` is also a right inverse to itself. -/
theorem complex_projective_line_conj_right_inv (u : EuclideanSpace ℂ (Fin 1)) :
    complex_projective_line_conj_forward (complex_projective_line_conj_inverse u) = u := by
  -- The same involutivity argument closes the other inverse identity.
  simpa [complex_projective_line_conj_inverse] using complex_projective_line_conj_left_inv u

/-- Helper for Problem 4-5: the conjugation model on `ℂ¹` is smooth. -/
theorem complex_projective_line_conj_forward_contMDiff :
    ContMDiff (Icp 1) (Icp 1) ∞ complex_projective_line_conj_forward := by
  -- Compose the smooth coordinate projection with complex conjugation and then reinsert it.
  rw [contMDiff_iff_contDiff]
  simpa [complex_projective_line_conj_forward, Function.comp] using
    complex_projective_line_single_contDiff.comp
      (Complex.conjCLE.contDiff.comp
        ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 1))) :
          ContDiff ℝ ∞ (fun u : EuclideanSpace ℂ (Fin 1) ↦ u 0)))

/-- Helper for Problem 4-5: the conjugation model inverse is smooth for the same reason. -/
theorem complex_projective_line_conj_inverse_contMDiff :
    ContMDiff (Icp 1) (Icp 1) ∞ complex_projective_line_conj_inverse := by
  -- The inverse is definitionally the same conjugation map.
  simpa [complex_projective_line_conj_inverse] using complex_projective_line_conj_forward_contMDiff

/-- Helper for Problem 4-5: conjugation on the unique affine coordinate is a diffeomorphism of
`ℂ¹`. -/
def complex_projective_line_conj_diffeomorph :
    EuclideanSpace ℂ (Fin 1) ≃ₘ⟮Icp 1, Icp 1⟯ EuclideanSpace ℂ (Fin 1) where
  toEquiv :=
    { toFun := complex_projective_line_conj_forward
      invFun := complex_projective_line_conj_inverse
      left_inv := complex_projective_line_conj_left_inv
      right_inv := complex_projective_line_conj_right_inv }
  contMDiff_toFun := complex_projective_line_conj_forward_contMDiff
  contMDiff_invFun := complex_projective_line_conj_inverse_contMDiff

/-- Helper for Problem 4-5: the north-chart affine model is conjugation followed by the standard
`ℂ¹ ≃ ℝ²` identification. -/
def complex_projective_line_north_model_diffeomorph :
    EuclideanSpace ℂ (Fin 1) ≃ₘ⟮Icp 1, 𝓡 2⟯ EuclideanSpace ℝ (Fin 2) :=
  complex_projective_line_conj_diffeomorph.trans complex_projective_line_model_diffeomorph

/-- Helper for Problem 4-5: a smooth open partial homeomorphism packages to a manifold
partial diffeomorphism. -/
def partialDiffeomorphOfOpenPartialHomeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin 1)) M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    {I : ModelWithCorners ℝ (EuclideanSpace ℂ (Fin 1)) (EuclideanSpace ℂ (Fin 1))}
    {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))}
    (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn I J ∞ e e.source)
    (he_symm : ContMDiffOn J I ∞ e.symm e.target) :
    PartialDiffeomorph I J M N ∞ :=
  { toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := he_symm }

/-- Helper for Problem 4-5: every point of `ℂP¹` lies in either the south affine chart or the
north affine chart. -/
theorem complex_projective_line_mem_south_or_north_chart (x : ℂP[1]) :
    x ∈ complexProjectiveChartDomain 1 (Fin.last 1) ∨ x ∈ complexProjectiveChartDomain 1 0 := by
  rcases complex_projective_space_has_standard_chart 1 x with ⟨i, hi⟩
  fin_cases i
  · exact Or.inr hi
  · exact Or.inl hi

/-- Helper for Problem 4-5: if a point of `ℂP¹` is not in the south affine chart, it must lie in
the north affine chart. -/
theorem complex_projective_line_mem_north_chart_of_not_mem_south_chart
    {x : ℂP[1]} (hx : x ∉ complexProjectiveChartDomain 1 (Fin.last 1)) :
    x ∈ complexProjectiveChartDomain 1 0 := by
  rcases complex_projective_line_mem_south_or_north_chart x with hs | hn
  · exact False.elim (hx hs)
  · exact hn

/-- Helper for Problem 4-5: the chartwise candidate map from `ℂP¹` to `S²`. -/
def complex_projective_line_to_sphere : ℂP[1] → unitSphere2 :=
  fun x ↦
    if x ∈ complexProjectiveChartDomain 1 (Fin.last 1) then
      -- On the south affine chart `[z : 1]`, use the inverse north-pole stereographic chart.
      stereographicNorthInv 2
        (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0))
    else
      -- Route correction: the complementary branch uses the north affine chart, so the source
      -- proof still glues two chartwise inverses rather than switching to a global formula.
      stereographicSouthInv 2
        (complexCoordinateAsPlane (star ((complexProjectiveChart 1 0 x) 0)))

/-- Helper for Problem 4-5: on the south affine chart, the global candidate agrees with the
north-pole stereographic inverse branch. -/
theorem complex_projective_line_to_sphere_eq_south_branch {x : ℂP[1]}
    (hx : x ∈ complexProjectiveChartDomain 1 (Fin.last 1)) :
    complex_projective_line_to_sphere x =
      stereographicNorthInv 2
        (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0)) := by
  -- On the south chart, the defining `if` chooses the north-pole stereographic branch.
  unfold complex_projective_line_to_sphere
  rw [if_pos hx]

/-- Helper for Problem 4-5: off the south affine chart, the global candidate agrees with the
south-pole stereographic inverse branch coming from the north affine chart. -/
theorem complex_projective_line_to_sphere_eq_north_branch {x : ℂP[1]}
    (hx : x ∉ complexProjectiveChartDomain 1 (Fin.last 1)) :
    complex_projective_line_to_sphere x =
      stereographicSouthInv 2
        (complexCoordinateAsPlane (star ((complexProjectiveChart 1 0 x) 0))) := by
  -- Away from the south chart, the complementary north-chart branch is the one used globally.
  unfold complex_projective_line_to_sphere
  rw [if_neg hx]

/-- Helper for Problem 4-5: on the overlap of the two affine charts on `ℂP¹`, the north-chart
coordinate is the inverse of the south-chart coordinate. -/
theorem complex_projective_line_chart_coords_inv_on_overlap {x : ℂP[1]}
    (hS : x ∈ complexProjectiveChartDomain 1 (Fin.last 1))
    (hN : x ∈ complexProjectiveChartDomain 1 0) :
    ((complexProjectiveChart 1 0 x) 0) =
      (((complexProjectiveChart 1 (Fin.last 1) x) 0)⁻¹) := by
  -- Read both chart coordinates from the fixed representative `x.rep`, then cancel the common
  -- nonzero homogeneous coordinates.
  have hmkS :
      mk ℂ x.rep x.rep_nonzero ∈ complexProjectiveChartDomain 1 (Fin.last 1) := by
    simpa [x.mk_rep] using hS
  have hmkN :
      mk ℂ x.rep x.rep_nonzero ∈ complexProjectiveChartDomain 1 0 := by
    simpa [x.mk_rep] using hN
  have hrep1 : x.rep 1 ≠ 0 := by
    exact (complexProjectiveChartDomain_mk 1 (Fin.last 1) x.rep x.rep_nonzero).1 hmkS
  have hrep0 : x.rep 0 ≠ 0 := by
    exact (complexProjectiveChartDomain_mk 1 0 x.rep x.rep_nonzero).1 hmkN
  have hchart0 :
      ((complexProjectiveChart 1 0 x) 0) = x.rep 1 / x.rep 0 := by
    rw [← x.mk_rep, complexProjectiveChart_mk]
    simp
  have hchart1 :
      ((complexProjectiveChart 1 (Fin.last 1) x) 0) = x.rep 0 / x.rep 1 := by
    rw [← x.mk_rep, complexProjectiveChart_mk]
    simp
  rw [hchart0, hchart1]
  field_simp [hrep0, hrep1]

/-- Helper for Problem 4-5: after identifying `ℂ` with `ℝ²`, the complex scalar `star (z⁻¹)` is
real inversion by `‖z‖²`. -/
theorem complexCoordinateAsPlane_star_inv (z : ℂ) (hz : z ≠ 0) :
    complexCoordinateAsPlane (star (z⁻¹)) =
      (‖complexCoordinateAsPlane z‖ ^ 2)⁻¹ • complexCoordinateAsPlane z := by
  -- Route correction: after isolating the coordinate and norm-square adapters, the clean proof is
  -- coordinatewise in `ℝ²`.
  ext i
  fin_cases i
  · -- In the first coordinate, both sides are `re z / Complex.normSq z`.
    simp [complexCoordinateAsPlane_apply_zero, Complex.conj_re, Complex.inv_re,
      complexCoordinateAsPlane_norm_sq, div_eq_mul_inv, mul_comm]
  · -- In the second coordinate, conjugation flips the sign twice, so the same scalar remains.
    simp [complexCoordinateAsPlane_apply_one, Complex.conj_im, Complex.inv_im,
      complexCoordinateAsPlane_norm_sq, div_eq_mul_inv, mul_comm]

/-- Helper for Problem 4-5: the temporary two-chart stereographic sphere structure has the same
smooth maximal atlas as the standard sphere structure. -/
theorem stereographic_two_chart_maximalAtlas_eq_standard :
    (letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) unitSphere2 :=
        stereographicSphereChartedSpace 2
      ; IsManifold.maximalAtlas (𝓡 2) ∞ unitSphere2) =
      IsManifold.maximalAtlas (𝓡 2) ∞ unitSphere2 := by
  -- Route correction: isolate the charted-space transport once, then reuse it for both
  -- stereographic atlas-membership lemmas and the branch smoothness proofs.
  simpa [IsManifold.maximalAtlas] using stereographic_two_chart_same_smooth_structure 2

/-- Helper for Problem 4-5: the north stereographic chart belongs to the standard smooth maximal
atlas of `S²`. -/
theorem stereographicNorthChart_mem_maximalAtlas :
    stereographicNorthChart 2 ∈ IsManifold.maximalAtlas (𝓡 2) ∞ unitSphere2 := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) unitSphere2 := stereographicSphereChartedSpace 2
  letI : IsManifold (𝓡 2) ∞ unitSphere2 := stereographic_two_chart_isManifold 2
  have hAtlas : stereographicNorthChart 2 ∈ atlas (EuclideanSpace ℝ (Fin 2)) unitSphere2 := by
    -- In the temporary two-chart structure, the north chart is one of the generating charts.
    change stereographicNorthChart 2 ∈
      {f | f = stereographicNorthChart 2 ∨ f = stereographicSouthChart 2}
    exact Or.inl rfl
  have hTemp : stereographicNorthChart 2 ∈ IsManifold.maximalAtlas (𝓡 2) ∞ unitSphere2 := by
    -- Any chart in the temporary atlas lies in its maximal smooth atlas.
    exact IsManifold.subset_maximalAtlas hAtlas
  -- Transport membership from the temporary stereographic owner to the standard sphere owner.
  exact stereographic_two_chart_maximalAtlas_eq_standard ▸ hTemp

/-- Helper for Problem 4-5: the south stereographic chart belongs to the standard smooth maximal
atlas of `S²`. -/
theorem stereographicSouthChart_mem_maximalAtlas :
    stereographicSouthChart 2 ∈ IsManifold.maximalAtlas (𝓡 2) ∞ unitSphere2 := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) unitSphere2 := stereographicSphereChartedSpace 2
  letI : IsManifold (𝓡 2) ∞ unitSphere2 := stereographic_two_chart_isManifold 2
  have hAtlas : stereographicSouthChart 2 ∈ atlas (EuclideanSpace ℝ (Fin 2)) unitSphere2 := by
    -- The south chart is the second generator of the temporary two-chart atlas.
    change stereographicSouthChart 2 ∈
      {f | f = stereographicNorthChart 2 ∨ f = stereographicSouthChart 2}
    exact Or.inr rfl
  have hTemp : stereographicSouthChart 2 ∈ IsManifold.maximalAtlas (𝓡 2) ∞ unitSphere2 := by
    -- Atlas membership upgrades to maximal-atlas membership in the temporary sphere structure.
    exact IsManifold.subset_maximalAtlas hAtlas
  -- Transport the temporary maximal-atlas membership to the standard sphere smooth structure.
  exact stereographic_two_chart_maximalAtlas_eq_standard ▸ hTemp

/-- Helper for Problem 4-5: the south-chart branch is the composition of the south projective
chart, the affine model diffeomorphism, and the inverse north stereographic chart. -/
def complex_projective_line_south_branch : OpenPartialHomeomorph ℂP[1] unitSphere2 :=
  ((complexProjectiveChart 1 (Fin.last 1)).trans
    (complex_projective_line_model_diffeomorph.toHomeomorph.toOpenPartialHomeomorph)).trans
    (stereographicNorthChart 2).symm

/-- Helper for Problem 4-5: the north-chart branch is the composition of the north projective
chart, the conjugated affine model diffeomorphism, and the inverse south stereographic chart. -/
def complex_projective_line_north_branch : OpenPartialHomeomorph ℂP[1] unitSphere2 :=
  ((complexProjectiveChart 1 0).trans
    (complex_projective_line_north_model_diffeomorph.toHomeomorph.toOpenPartialHomeomorph)).trans
    (stereographicSouthChart 2).symm

/-- Helper for Problem 4-5: the south branch has exactly the south projective chart as source and
the north-pole complement as target. -/
theorem complex_projective_line_south_branch_source_target :
    complex_projective_line_south_branch.source =
      complexProjectiveChartDomain 1 (Fin.last 1) ∧
    complex_projective_line_south_branch.target = northPoleComplement 2 := by
  constructor
  · -- Normalize the iterated source of the branch composition by removing the global middle chart.
    ext x
    simp [complex_projective_line_south_branch, complexProjectiveChart, stereographicNorthChart]
  · -- Normalize the target by observing that the final inverse stereographic chart has target
    -- exactly the north-pole complement.
    ext y
    simp [complex_projective_line_south_branch, complexProjectiveChart, stereographicNorthChart]

/-- Helper for Problem 4-5: the north branch has exactly the north projective chart as source and
the south-pole complement as target. -/
theorem complex_projective_line_north_branch_source_target :
    complex_projective_line_north_branch.source = complexProjectiveChartDomain 1 0 ∧
    complex_projective_line_north_branch.target = southPoleComplement 2 := by
  constructor
  · -- Normalize the iterated source of the north branch in the same way.
    ext x
    simp [complex_projective_line_north_branch, complexProjectiveChart, stereographicSouthChart]
  · -- The terminal inverse stereographic chart contributes the south-pole complement as target.
    ext y
    simp [complex_projective_line_north_branch, complexProjectiveChart, stereographicSouthChart]

/-- Helper for Problem 4-5: the south-chart branch is smooth on its source. -/
theorem complex_projective_line_south_branch_contMDiffOn :
    ContMDiffOn (Icp 1) (𝓡 2) ∞ complex_projective_line_south_branch
      complex_projective_line_south_branch.source := by
  have hChart :
      ContMDiffOn (Icp 1) (Icp 1) ∞
        (complexProjectiveChart 1 (Fin.last 1))
        (complexProjectiveChart 1 (Fin.last 1)).source := by
    -- The south affine chart is already a maximal-atlas chart on `ℂP¹`.
    exact contMDiffOn_of_mem_maximalAtlas
      (complex_projective_chart_mem_maximal_atlas 1 (Fin.last 1))
  have hModel :
      ContMDiffOn (Icp 1) (𝓡 2) ∞ complex_projective_line_model_diffeomorph Set.univ := by
    -- The middle affine model map is a global diffeomorphism, hence smooth on all of `ℂ¹`.
    exact complex_projective_line_model_diffeomorph.contMDiff_toFun.contMDiffOn
  have hStereo :
      ContMDiffOn (𝓡 2) (𝓡 2) ∞
        (stereographicNorthChart 2).symm
        (stereographicNorthChart 2).target := by
    -- The inverse north stereographic chart is smooth on its target because the chart is maximal.
    exact contMDiffOn_symm_of_mem_maximalAtlas stereographicNorthChart_mem_maximalAtlas
  have hChartModel :
      ContMDiffOn (Icp 1) (𝓡 2) ∞
        (complex_projective_line_model_diffeomorph ∘ complexProjectiveChart 1 (Fin.last 1))
        (complexProjectiveChart 1 (Fin.last 1)).source := by
    -- Compose the south projective chart with the affine `ℂ¹ ≃ ℝ²` identification.
    exact hModel.comp hChart (by intro x hx; simp)
  have hBranch :
      ContMDiffOn (Icp 1) (𝓡 2) ∞
        ((stereographicNorthChart 2).symm ∘
          (complex_projective_line_model_diffeomorph ∘ complexProjectiveChart 1 (Fin.last 1)))
        (complexProjectiveChart 1 (Fin.last 1)).source := by
    -- The final inverse stereographic chart is defined on all of `ℝ²`, so one more composition
    -- closes the south branch.
    exact hStereo.comp hChartModel (by intro x hx; simp [stereographicNorthChart])
  -- Rewrite the branch source back to the packaged `OpenPartialHomeomorph`.
  rw [(complex_projective_line_south_branch_source_target).1]
  simpa [complex_projective_line_south_branch, Function.comp]
    using hBranch

/-- Helper for Problem 4-5: the south-chart branch inverse is smooth on its target. -/
theorem complex_projective_line_south_branch_symm_contMDiffOn :
    ContMDiffOn (𝓡 2) (Icp 1) ∞ complex_projective_line_south_branch.symm
      complex_projective_line_south_branch.target := by
  have hStereo :
      ContMDiffOn (𝓡 2) (𝓡 2) ∞
        (stereographicNorthChart 2)
        (stereographicNorthChart 2).source := by
    -- Start with the forward north stereographic chart on the north-pole complement.
    exact contMDiffOn_of_mem_maximalAtlas stereographicNorthChart_mem_maximalAtlas
  have hModel :
      ContMDiffOn (𝓡 2) (Icp 1) ∞
        complex_projective_line_model_diffeomorph.symm Set.univ := by
    -- The inverse affine model map is globally smooth.
    exact complex_projective_line_model_diffeomorph.contMDiff_invFun.contMDiffOn
  have hChartSymm :
      ContMDiffOn (Icp 1) (Icp 1) ∞
        (complexProjectiveChart 1 (Fin.last 1)).symm
        (complexProjectiveChart 1 (Fin.last 1)).target := by
    -- The inverse south affine chart is smooth on all affine coordinates.
    exact contMDiffOn_symm_of_mem_maximalAtlas
      (complex_projective_chart_mem_maximal_atlas 1 (Fin.last 1))
  have hStereoModel :
      ContMDiffOn (𝓡 2) (Icp 1) ∞
        (complex_projective_line_model_diffeomorph.symm ∘ stereographicNorthChart 2)
        (stereographicNorthChart 2).source := by
    -- Reverse the Euclidean part of the south branch.
    exact hModel.comp hStereo (by intro x hx; simp)
  have hBranch :
      ContMDiffOn (𝓡 2) (Icp 1) ∞
        ((complexProjectiveChart 1 (Fin.last 1)).symm ∘
          (complex_projective_line_model_diffeomorph.symm ∘ stereographicNorthChart 2))
        (stereographicNorthChart 2).source := by
    -- Finish by applying the inverse projective chart.
    exact hChartSymm.comp hStereoModel (by intro x hx; simp [complexProjectiveChart])
  -- Rewrite the target to the north-pole complement of the south branch.
  rw [(complex_projective_line_south_branch_source_target).2]
  simpa [complex_projective_line_south_branch, Function.comp]
    using hBranch

/-- Helper for Problem 4-5: the north-chart branch is smooth on its source. -/
theorem complex_projective_line_north_branch_contMDiffOn :
    ContMDiffOn (Icp 1) (𝓡 2) ∞ complex_projective_line_north_branch
      complex_projective_line_north_branch.source := by
  have hChart :
      ContMDiffOn (Icp 1) (Icp 1) ∞
        (complexProjectiveChart 1 0)
        (complexProjectiveChart 1 0).source := by
    -- The north affine chart is likewise a maximal-atlas chart on `ℂP¹`.
    exact contMDiffOn_of_mem_maximalAtlas (complex_projective_chart_mem_maximal_atlas 1 0)
  have hModel :
      ContMDiffOn (Icp 1) (𝓡 2) ∞ complex_projective_line_north_model_diffeomorph Set.univ := by
    -- The conjugated affine model is a global diffeomorphism from `ℂ¹` to `ℝ²`.
    exact complex_projective_line_north_model_diffeomorph.contMDiff_toFun.contMDiffOn
  have hStereo :
      ContMDiffOn (𝓡 2) (𝓡 2) ∞
        (stereographicSouthChart 2).symm
        (stereographicSouthChart 2).target := by
    -- The inverse south stereographic chart is smooth on its full Euclidean target.
    exact contMDiffOn_symm_of_mem_maximalAtlas stereographicSouthChart_mem_maximalAtlas
  have hChartModel :
      ContMDiffOn (Icp 1) (𝓡 2) ∞
        (complex_projective_line_north_model_diffeomorph ∘ complexProjectiveChart 1 0)
        (complexProjectiveChart 1 0).source := by
    -- Compose the north projective chart with the conjugated affine model.
    exact hModel.comp hChart (by intro x hx; simp)
  have hBranch :
      ContMDiffOn (Icp 1) (𝓡 2) ∞
        ((stereographicSouthChart 2).symm ∘
          (complex_projective_line_north_model_diffeomorph ∘ complexProjectiveChart 1 0))
        (complexProjectiveChart 1 0).source := by
    -- The final south stereographic inverse closes the north branch.
    exact hStereo.comp hChartModel (by intro x hx; simp [stereographicSouthChart])
  -- Rewrite the packaged branch source to the normalized north chart source.
  rw [(complex_projective_line_north_branch_source_target).1]
  simpa [complex_projective_line_north_branch, Function.comp]
    using hBranch

/-- Helper for Problem 4-5: the north-chart branch inverse is smooth on its target. -/
theorem complex_projective_line_north_branch_symm_contMDiffOn :
    ContMDiffOn (𝓡 2) (Icp 1) ∞ complex_projective_line_north_branch.symm
      complex_projective_line_north_branch.target := by
  have hStereo :
      ContMDiffOn (𝓡 2) (𝓡 2) ∞
        (stereographicSouthChart 2)
        (stereographicSouthChart 2).source := by
    -- Start from the forward south stereographic chart on the south-pole complement.
    exact contMDiffOn_of_mem_maximalAtlas stereographicSouthChart_mem_maximalAtlas
  have hModel :
      ContMDiffOn (𝓡 2) (Icp 1) ∞
        complex_projective_line_north_model_diffeomorph.symm Set.univ := by
    -- The inverse conjugated affine model is globally smooth as well.
    exact complex_projective_line_north_model_diffeomorph.contMDiff_invFun.contMDiffOn
  have hChartSymm :
      ContMDiffOn (Icp 1) (Icp 1) ∞
        (complexProjectiveChart 1 0).symm
        (complexProjectiveChart 1 0).target := by
    -- The inverse north affine chart is smooth on all affine coordinates.
    exact contMDiffOn_symm_of_mem_maximalAtlas
      (complex_projective_chart_mem_maximal_atlas 1 0)
  have hStereoModel :
      ContMDiffOn (𝓡 2) (Icp 1) ∞
        (complex_projective_line_north_model_diffeomorph.symm ∘ stereographicSouthChart 2)
        (stereographicSouthChart 2).source := by
    -- Reverse the Euclidean part of the north branch.
    exact hModel.comp hStereo (by intro x hx; simp)
  have hBranch :
      ContMDiffOn (𝓡 2) (Icp 1) ∞
        ((complexProjectiveChart 1 0).symm ∘
          (complex_projective_line_north_model_diffeomorph.symm ∘ stereographicSouthChart 2))
        (stereographicSouthChart 2).source := by
    -- Finish by re-entering `ℂP¹` through the inverse north affine chart.
    exact hChartSymm.comp hStereoModel (by intro x hx; simp [complexProjectiveChart])
  -- Rewrite the target to the south-pole complement of the north branch.
  rw [(complex_projective_line_north_branch_source_target).2]
  simpa [complex_projective_line_north_branch, Function.comp]
    using hBranch

/-- Helper for Problem 4-5: the south-chart branch packages to a `PartialDiffeomorph`. -/
def complex_projective_line_south_partialDiffeomorph :
    PartialDiffeomorph (Icp 1) (𝓡 2) ℂP[1] unitSphere2 ∞ :=
  partialDiffeomorphOfOpenPartialHomeomorph complex_projective_line_south_branch
    complex_projective_line_south_branch_contMDiffOn
    complex_projective_line_south_branch_symm_contMDiffOn

/-- Helper for Problem 4-5: the north-chart branch packages to a `PartialDiffeomorph`. -/
def complex_projective_line_north_partialDiffeomorph :
    PartialDiffeomorph (Icp 1) (𝓡 2) ℂP[1] unitSphere2 ∞ :=
  partialDiffeomorphOfOpenPartialHomeomorph complex_projective_line_north_branch
    complex_projective_line_north_branch_contMDiffOn
    complex_projective_line_north_branch_symm_contMDiffOn

/-- Helper for Problem 4-5: on the south chart, the explicit branch partial diffeomorphism agrees
with the textbook south-branch formula. -/
theorem complex_projective_line_south_partialDiffeomorph_eqOn :
    Set.EqOn complex_projective_line_south_partialDiffeomorph
      (fun x : ℂP[1] ↦
        stereographicNorthInv 2
          (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0)))
      complex_projective_line_south_partialDiffeomorph.source := by
  intro x _hx
  -- Unfold the packaged partial diffeomorphism back to the three chart factors.
  rfl

/-- Helper for Problem 4-5: on the north chart, the explicit branch partial diffeomorphism agrees
with the repaired north-branch formula. -/
theorem complex_projective_line_north_partialDiffeomorph_eqOn :
    Set.EqOn complex_projective_line_north_partialDiffeomorph
      (fun x : ℂP[1] ↦
        stereographicSouthInv 2
          (complexCoordinateAsPlane (star ((complexProjectiveChart 1 0 x) 0))))
      complex_projective_line_north_partialDiffeomorph.source := by
  intro x _hx
  -- Unfold the packaged north branch back to the explicit conjugated chart formula.
  rfl

/-- Helper for Problem 4-5: on the chart overlap, the repaired north branch matches the south
branch through the stereographic transition formula. -/
theorem complex_projective_line_branch_transition_matches_stereographic {x : ℂP[1]}
    (hS : x ∈ complexProjectiveChartDomain 1 (Fin.last 1))
    (hN : x ∈ complexProjectiveChartDomain 1 0) :
    stereographicNorthInv 2
        (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0)) =
      stereographicSouthInv 2
        (complexCoordinateAsPlane (star ((complexProjectiveChart 1 0 x) 0))) := by
  let u : EuclideanSpace ℝ (Fin 2) :=
    complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0)
  have hmkS :
      mk ℂ x.rep x.rep_nonzero ∈ complexProjectiveChartDomain 1 (Fin.last 1) := by
    simpa [x.mk_rep] using hS
  have hmkN :
      mk ℂ x.rep x.rep_nonzero ∈ complexProjectiveChartDomain 1 0 := by
    simpa [x.mk_rep] using hN
  have hsouth_coord_ne :
      ((complexProjectiveChart 1 (Fin.last 1) x) 0) ≠ 0 := by
    have hrep1 : x.rep 1 ≠ 0 := by
      exact (complexProjectiveChartDomain_mk 1 (Fin.last 1) x.rep x.rep_nonzero).1 hmkS
    have hrep0 : x.rep 0 ≠ 0 := by
      exact (complexProjectiveChartDomain_mk 1 0 x.rep x.rep_nonzero).1 hmkN
    have hchart :
        ((complexProjectiveChart 1 (Fin.last 1) x) 0) = x.rep 0 / x.rep 1 := by
      rw [← x.mk_rep, complexProjectiveChart_mk]
      simp
    rw [hchart]
    exact div_ne_zero hrep0 hrep1
  have hu : u ≠ 0 := by
    intro hu
    apply hsouth_coord_ne
    have hcomplex := congrArg planeCoordinateAsComplex hu
    simpa [u, planeCoordinateAsComplex_complexCoordinateAsPlane] using hcomplex
  have hnotSouth :
      stereographicNorthInv 2 u ∈ (southPoleComplement 2 : Set unitSphere2) := by
    -- The north inverse of a nonzero coordinate cannot be the south pole because
    -- `stereographicNorthMap` sends the south pole to `0`.
    rw [southPoleComplement]
    intro hsouth
    have hzero : stereographicNorthMap 2 (southPolePoint 2) = 0 := by
      ext i
      fin_cases i <;> simp [stereographicNorthMap, southPolePoint, southPoleVec, Fin.snoc]
    have hmap' : stereographicNorthMap 2 (stereographicNorthInv 2 u) = 0 := by
      simpa [hsouth] using hzero
    exact hu <| by simpa [stereographicNorth_right_inv 2 u] using hmap'
  -- Apply the explicit transition formula, then rewrite the north-chart coordinate by the
  -- projective overlap identity.
  calc
    stereographicNorthInv 2 u =
        stereographicSouthInv 2 (stereographicSouthMap 2 (stereographicNorthInv 2 u)) := by
          symm
          exact stereographicSouth_left_inv 2 hnotSouth
    _ = stereographicSouthInv 2 ((‖u‖ ^ 2)⁻¹ • u) := by
          rw [stereographic_transition 2 u hu]
    _ = stereographicSouthInv 2
          (complexCoordinateAsPlane
            (star ((complexProjectiveChart 1 0 x) 0))) := by
          congr 1
          rw [complex_projective_line_chart_coords_inv_on_overlap hS hN]
          simpa [u] using
            (complexCoordinateAsPlane_star_inv
              (((complexProjectiveChart 1 (Fin.last 1) x) 0)) hsouth_coord_ne).symm

/-- Helper for Problem 4-5: on the north chart, the global `ℂP¹ -> S²` map agrees with the
repaired south-pole stereographic branch. -/
theorem complex_projective_line_to_sphere_eqOn_north_chart :
    Set.EqOn complex_projective_line_to_sphere
      (fun x : ℂP[1] ↦
        stereographicSouthInv 2
          (complexCoordinateAsPlane (star ((complexProjectiveChart 1 0 x) 0))))
      (complexProjectiveChartDomain 1 0) := by
  intro x hx
  by_cases hS : x ∈ complexProjectiveChartDomain 1 (Fin.last 1)
  · -- On the overlap, compare the two chart branches through the transition identity.
    rw [complex_projective_line_to_sphere_eq_south_branch hS]
    exact complex_projective_line_branch_transition_matches_stereographic hS hx
  · -- Off the south chart, the global definition already chooses the repaired north branch.
    exact complex_projective_line_to_sphere_eq_north_branch hS

/-- Helper for Problem 4-5: the point outside the south affine chart is the chart-`0` origin, i.e.
the point at infinity. -/
theorem complex_projective_line_eq_infinity_of_not_mem_south_chart
    (x : ℂP[1]) (hx : x ∉ complexProjectiveChartDomain 1 (Fin.last 1)) :
    x = (complexProjectiveChart 1 0).symm 0 := by
  -- A point outside the south chart has vanishing second homogeneous coordinate.
  have hrep1 : x.rep 1 = 0 := by
    by_contra h1
    apply hx
    simpa [x.mk_rep] using
      (complexProjectiveChartDomain_mk 1 (Fin.last 1) x.rep x.rep_nonzero).2 h1
  -- Its first homogeneous coordinate must then be nonzero because the representative is nonzero.
  have hrep0 : x.rep 0 ≠ 0 := by
    intro h0
    apply x.rep_nonzero
    ext i
    fin_cases i
    · simp [h0]
    · simp [hrep1]
  -- Compare `x` directly with the projective class of the vector `[1, 0]`.
  rw [complexProjectiveChart_symm_apply]
  rw [← x.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ x.rep_nonzero
    (complexProjectiveChartInvVector_ne_zero 1 0 0)).2
  refine ⟨x.rep 0, ?_⟩
  ext i
  fin_cases i
  · simp [complexProjectiveChartInvVector]
  · simp [complexProjectiveChartInvVector, hrep1]

/-- Helper for Problem 4-5: the south-pole stereographic inverse sends the origin to the north
pole. -/
theorem stereographicSouthInv_zero_eq_northPole :
    stereographicSouthInv 2 (0 : EuclideanSpace ℝ (Fin 2)) = northPolePoint 2 := by
  -- Both points are represented by the same explicit sphere vector `(0, 0, 1)`.
  apply Subtype.ext
  ext i
  fin_cases i
  · simp [stereographicSouthInv, stereographicSouthInvVector, northPolePoint, northPoleVec, Fin.snoc]
  · simp [stereographicSouthInv, stereographicSouthInvVector, northPolePoint, northPoleVec, Fin.snoc]
  · simp [stereographicSouthInv, stereographicSouthInvVector, northPolePoint, northPoleVec, Fin.snoc]

/-- Helper for Problem 4-5: the point at infinity is sent to the north pole. -/
theorem complex_projective_line_to_sphere_eq_northPole_of_not_mem_south_chart
    {x : ℂP[1]} (hx : x ∉ complexProjectiveChartDomain 1 (Fin.last 1)) :
    complex_projective_line_to_sphere x = northPolePoint 2 := by
  -- Replace `x` by the unique point outside the south chart and evaluate the repaired north
  -- branch there.
  have hnotSouthInfinity :
      (complexProjectiveChart 1 0).symm (0 : EuclideanSpace ℂ (Fin 1)) ∉
        complexProjectiveChartDomain 1 (Fin.last 1) := by
    rw [complexProjectiveChart_symm_apply, complexProjectiveChartDomain_mk]
    simp [complexProjectiveChartInvVector]
  have hchart0 :
      complexProjectiveChart 1 0
        ((complexProjectiveChart 1 0).symm (0 : EuclideanSpace ℂ (Fin 1))) = 0 := by
    exact OpenPartialHomeomorph.right_inv (complexProjectiveChart 1 0) (Set.mem_univ _)
  rw [complex_projective_line_eq_infinity_of_not_mem_south_chart x hx]
  rw [complex_projective_line_to_sphere_eq_north_branch hnotSouthInfinity]
  rw [hchart0]
  have hcoordZero :
      complexCoordinateAsPlane (star ((0 : EuclideanSpace ℂ (Fin 1)) 0)) =
        (0 : EuclideanSpace ℝ (Fin 2)) := by
    simp [complexCoordinateAsPlane]
  rw [hcoordZero]
  exact stereographicSouthInv_zero_eq_northPole

/-- Helper for Problem 4-5: on the south affine chart, the global candidate agrees with the
explicit south-branch partial diffeomorphism. -/
theorem complex_projective_line_south_branch_isLocalDiffeomorphAt {x : ℂP[1]}
    (hx : x ∈ complexProjectiveChartDomain 1 (Fin.last 1)) :
    IsLocalDiffeomorphAt (Icp 1) (𝓡 2) ∞ complex_projective_line_to_sphere x := by
  -- The packaged south branch is a local diffeomorphism on its source.
  refine ⟨complex_projective_line_south_partialDiffeomorph, ?_, ?_⟩
  · -- Normalize the branch source to the south affine chart domain.
    change x ∈ complex_projective_line_south_branch.source
    simpa [complex_projective_line_south_branch_source_target.1] using hx
  · intro y hy
    -- On that source, both the global map and the packaged branch equal the same textbook formula.
    have hySouth : y ∈ complexProjectiveChartDomain 1 (Fin.last 1) := by
      change y ∈ complex_projective_line_south_branch.source at hy
      simpa [complex_projective_line_south_branch_source_target.1] using hy
    rw [complex_projective_line_to_sphere_eq_south_branch hySouth]
    symm
    exact complex_projective_line_south_partialDiffeomorph_eqOn hy

/-- Helper for Problem 4-5: on the north affine chart, the global candidate agrees with the
explicit north-branch partial diffeomorphism. -/
theorem complex_projective_line_north_branch_isLocalDiffeomorphAt {x : ℂP[1]}
    (hx : x ∈ complexProjectiveChartDomain 1 0) :
    IsLocalDiffeomorphAt (Icp 1) (𝓡 2) ∞ complex_projective_line_to_sphere x := by
  -- The packaged north branch is a local diffeomorphism on its source.
  refine ⟨complex_projective_line_north_partialDiffeomorph, ?_, ?_⟩
  · -- Normalize the branch source to the north affine chart domain.
    change x ∈ complex_projective_line_north_branch.source
    simpa [complex_projective_line_north_branch_source_target.1] using hx
  · intro y hy
    -- On the north chart, both maps agree with the repaired south-pole stereographic branch.
    have hyNorth : y ∈ complexProjectiveChartDomain 1 0 := by
      change y ∈ complex_projective_line_north_branch.source at hy
      simpa [complex_projective_line_north_branch_source_target.1] using hy
    rw [complex_projective_line_to_sphere_eqOn_north_chart hyNorth]
    symm
    exact complex_projective_line_north_partialDiffeomorph_eqOn hy

/-- Helper for Problem 4-5: the chartwise candidate map `ℂP¹ → S²` is a smooth local
diffeomorphism. -/
theorem complex_projective_line_to_sphere_isLocalDiffeomorph :
    IsLocalDiffeomorph (Icp 1) (𝓡 2) ∞ complex_projective_line_to_sphere := by
  intro x
  -- Split by the two standard affine charts covering `ℂP¹`.
  rcases complex_projective_line_mem_south_or_north_chart x with hxSouth | hxNorth
  · exact complex_projective_line_south_branch_isLocalDiffeomorphAt hxSouth
  · exact complex_projective_line_north_branch_isLocalDiffeomorphAt hxNorth

/-- Helper for Problem 4-5: the chartwise candidate map `ℂP¹ → S²` is bijective. -/
theorem complex_projective_line_to_sphere_bijective :
    Function.Bijective complex_projective_line_to_sphere := by
  constructor
  · intro x y hxy
    by_cases hx : x ∈ complexProjectiveChartDomain 1 (Fin.last 1)
    · by_cases hy : y ∈ complexProjectiveChartDomain 1 (Fin.last 1)
      · -- On the south chart, apply stereographic projection from the north pole to compare the
        -- affine coordinates.
        have hxBranch := complex_projective_line_to_sphere_eq_south_branch hx
        have hyBranch := complex_projective_line_to_sphere_eq_south_branch hy
        have hplane :
            complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0) =
              complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) y) 0) := by
          calc
            complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0) =
                stereographicNorthMap 2
                  (stereographicNorthInv 2
                    (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0))) := by
                      symm
                      exact stereographicNorth_right_inv 2
                        (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0))
            _ = stereographicNorthMap 2 (complex_projective_line_to_sphere x) := by rw [hxBranch]
            _ = stereographicNorthMap 2 (complex_projective_line_to_sphere y) := by rw [hxy]
            _ = stereographicNorthMap 2
                  (stereographicNorthInv 2
                    (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) y) 0))) := by
                      rw [hyBranch]
            _ = complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) y) 0) := by
                      exact stereographicNorth_right_inv 2
                        (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) y) 0))
        have hcoord0 :
            ((complexProjectiveChart 1 (Fin.last 1) x) 0) =
              ((complexProjectiveChart 1 (Fin.last 1) y) 0) := by
          have hcomplex := congrArg planeCoordinateAsComplex hplane
          simpa [planeCoordinateAsComplex_complexCoordinateAsPlane] using hcomplex
        have hchart :
            complexProjectiveChart 1 (Fin.last 1) x =
              complexProjectiveChart 1 (Fin.last 1) y := by
          ext j
          fin_cases j
          simpa using hcoord0
        calc
          x = (complexProjectiveChart 1 (Fin.last 1)).symm
              (complexProjectiveChart 1 (Fin.last 1) x) := by
                symm
                exact OpenPartialHomeomorph.left_inv (complexProjectiveChart 1 (Fin.last 1)) hx
          _ = (complexProjectiveChart 1 (Fin.last 1)).symm
              (complexProjectiveChart 1 (Fin.last 1) y) := by rw [hchart]
          _ = y := by
                exact OpenPartialHomeomorph.left_inv (complexProjectiveChart 1 (Fin.last 1)) hy
      · -- A south-chart point cannot map to the north pole, whereas a non-south-chart point does.
        have hxNotNorth :
            complex_projective_line_to_sphere x ≠ northPolePoint 2 := by
          rw [complex_projective_line_to_sphere_eq_south_branch hx]
          exact stereographicNorthInv_ne_northPole 2
            (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) x) 0))
        have hyNorth :
            complex_projective_line_to_sphere y = northPolePoint 2 :=
          complex_projective_line_to_sphere_eq_northPole_of_not_mem_south_chart hy
        exact False.elim (hxNotNorth (hxy.trans hyNorth))
    · have hxInf : x = (complexProjectiveChart 1 0).symm 0 :=
        complex_projective_line_eq_infinity_of_not_mem_south_chart x hx
      by_cases hy : y ∈ complexProjectiveChartDomain 1 (Fin.last 1)
      · -- Symmetric to the previous mixed-chart case.
        have hyNotNorth :
            complex_projective_line_to_sphere y ≠ northPolePoint 2 := by
          rw [complex_projective_line_to_sphere_eq_south_branch hy]
          exact stereographicNorthInv_ne_northPole 2
            (complexCoordinateAsPlane ((complexProjectiveChart 1 (Fin.last 1) y) 0))
        have hxNorth :
            complex_projective_line_to_sphere x = northPolePoint 2 :=
          complex_projective_line_to_sphere_eq_northPole_of_not_mem_south_chart hx
        exact False.elim (hyNotNorth (hxy.symm.trans hxNorth))
      · -- Both points are the unique point outside the south chart.
        rw [hxInf, complex_projective_line_eq_infinity_of_not_mem_south_chart y hy]
  · intro y
    by_cases hy : y = northPolePoint 2
    · -- The north pole is the image of the unique point at infinity.
      refine ⟨(complexProjectiveChart 1 0).symm 0, ?_⟩
      simpa [hy] using complex_projective_line_to_sphere_eq_northPole_of_not_mem_south_chart
        (x := (complexProjectiveChart 1 0).symm 0)
        (by
          rw [complexProjectiveChart_symm_apply, complexProjectiveChartDomain_mk]
          simp [complexProjectiveChartInvVector])
    · -- Away from the north pole, use the south affine chart together with the inverse of
      -- north-pole stereographic projection.
      let u : EuclideanSpace ℝ (Fin 2) := stereographicNorthMap 2 y
      let z : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 (planeCoordinateAsComplex u)
      refine ⟨(complexProjectiveChart 1 (Fin.last 1)).symm z, ?_⟩
      have hzSouth :
          (complexProjectiveChart 1 (Fin.last 1)).symm z ∈
            complexProjectiveChartDomain 1 (Fin.last 1) :=
        complexProjectiveChart_symm_mem_domain 1 (Fin.last 1) z
      rw [complex_projective_line_to_sphere_eq_south_branch hzSouth]
      have hchart :
          complexProjectiveChart 1 (Fin.last 1)
            ((complexProjectiveChart 1 (Fin.last 1)).symm z) = z := by
        exact OpenPartialHomeomorph.right_inv (complexProjectiveChart 1 (Fin.last 1))
          (Set.mem_univ z)
      rw [hchart]
      change stereographicNorthInv 2 (complexCoordinateAsPlane (planeCoordinateAsComplex u)) = y
      rw [complexCoordinateAsPlane_planeCoordinateAsComplex]
      exact stereographicNorth_left_inv 2 hy

/-- Problem 4-5 (3): `ℂP¹` is diffeomorphic to `S²`. -/
theorem complexProjectiveLine_diffeomorphic_sphere :
    Nonempty (ℂP[1] ≃ₘ⟮Icp 1, 𝓡 2⟯ unitSphere2) := by
  -- TODO: once the candidate map is known to be a bijective local diffeomorphism, package it as
  -- a global diffeomorphism.
  exact
    ⟨complex_projective_line_to_sphere_isLocalDiffeomorph.diffeomorphOfBijective
      complex_projective_line_to_sphere_bijective⟩
