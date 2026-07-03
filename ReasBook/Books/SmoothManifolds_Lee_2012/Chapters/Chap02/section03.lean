import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Sphere

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_2_3 (from Chap02/Sec02_08) -/
universe uE uH uM

open Set ChartedSpace IsManifold
open scoped ContDiff Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Proof sketch: use the canonical source-chart bridge
-- `contMDiffOn_iff_source_of_mem_maximalAtlas` on the domain `e.source`, then convert the
-- Euclidean `ContMDiffOn` conclusion to `ContDiffOn`.
/-- Exercise 2.3: if `f : M → ℝ^k` is smooth, then for every smooth chart `e` on `M`, the
chart-written expression `f ∘ (e.extend I).symm` is smooth on the chart image
`e.extend I '' e.source`. This is the manifold-with-corners form of the textbook statement that
`f ∘ φ⁻¹` is smooth on `φ(U)`. -/
theorem smooth_chart_representation_of_contMDiff
    {k : ℕ} {f : M → EuclideanSpace ℝ (Fin k)} {e : OpenPartialHomeomorph M H}
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ f)
    (he : e ∈ maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (f ∘ (e.extend I).symm) (e.extend I '' e.source) := by
  have hwritten :
      ContMDiffOn
        𝓘(ℝ, E)
        𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        ∞
        (f ∘ (e.extend I).symm)
        (e.extend I '' e.source) :=
    (contMDiffOn_iff_source_of_mem_maximalAtlas he Subset.rfl).1 <| hf.contMDiffOn.mono Subset.rfl
  exact hwritten.contDiffOn

/-! ### Problem_2_3 (from Chap02/Sec02_12) -/
open scoped Manifold ContDiff RealInnerProductSpace
open Complex Metric ComplexConjugate

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Local API note: semantic `lean_leansearch` was unavailable in this session; the sphere-valued
-- smoothness statements below use mathlib's `Instances.Sphere` API directly.

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C2" => WithLp 2 (ℂ × ℂ)
local notation "unitSphere3" => sphere (0 : C2) 1
local notation "unitSphere2" => sphere (0 : R3) 1

/-- The integer power map on the complex unit circle. -/
def circle_zpow_map (n : ℤ) : Circle → Circle :=
  fun z ↦ z ^ n

-- Proof sketch: use that `Circle` is an analytic Lie group, so multiplication, inversion, and
-- hence every integer power map are smooth.
/-- Problem 2-3 (1): the nth power map `p_n(z) = z^n` on `S¹ ⊆ ℂ` is smooth for every integer
`n`. -/
theorem circle_zpow_map_smooth (n : ℤ) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (circle_zpow_map n) := sorry

/- Recall for the middle clause of Problem 2-3: the antipodal map `x ↦ -x` on the
unit sphere `S^n` is smooth. -/
recall contMDiff_neg_sphere {m : ℕ∞ω} {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] :
    CMDiff m fun x : sphere (0 : E) 1 ↦ -x

-- Proof sketch: combine `Complex.finrank_real_complex_fact` with the standard formula for the
-- real dimension of a finite product.
/-- The real vector space `ℂ × ℂ` has dimension `4`. -/
theorem finrank_real_complex_prod_fact : Fact (Module.finrank ℝ C2 = 3 + 1) := sorry

/-- The standard sphere in `ℂ²` uses the real-dimension-four sphere manifold structure. -/
local instance complex_pair_finrank_fact : Fact (Module.finrank ℝ C2 = 3 + 1) :=
  finrank_real_complex_prod_fact

/-- The unit sphere in `ℂ²` carries the standard charted-space structure of the `3`-sphere. -/
local instance unitSphere3_chartedSpace : ChartedSpace R3 unitSphere3 :=
  EuclideanSpace.instChartedSpaceSphere (E := C2) (n := 3)

-- Proof sketch: unfold `R3 = EuclideanSpace ℝ (Fin 3)` and use the standard finrank formula for
-- Euclidean space.
/-- The Euclidean space `ℝ³` has real dimension `3`. -/
theorem finrank_real_r3_fact : Fact (Module.finrank ℝ R3 = 2 + 1) := sorry

/-- The standard sphere in `ℝ³` uses the real-dimension-three sphere manifold structure. -/
local instance r3_finrank_fact : Fact (Module.finrank ℝ R3 = 2 + 1) :=
  finrank_real_r3_fact

/-- The ambient quadratic formula defining the map `S^3 → S^2` in Problem 2-3(c). -/
def hopf_map_aux : C2 → R3 :=
  fun p ↦
    let w := p.fst
    let z := p.snd
    WithLp.toLp 2
      ![Complex.re (z * conj w + w * conj z),
        Complex.re (Complex.I * w * conj z - Complex.I * z * conj w),
        Complex.re (z * conj z - w * conj w)]

-- Proof sketch: write the squared norm of the displayed vector, use the sphere relation
-- `‖w‖^2 + ‖z‖^2 = 1`, and simplify the resulting polynomial identity.
/-- The quadratic coordinate formula in Problem 2-3(c) sends `S^3 ⊆ ℂ²` into `S^2 ⊆ ℝ³`. -/
theorem hopf_map_aux_mem_unit_sphere2 (p : unitSphere3) :
    hopf_map_aux p ∈ unitSphere2 := sorry

/-- The sphere-valued map `F : S^3 → S^2` from Problem 2-3(c). -/
def hopf_map : unitSphere3 → unitSphere2 :=
  fun p ↦ ⟨hopf_map_aux p, hopf_map_aux_mem_unit_sphere2 p⟩

-- Proof sketch: each coordinate of `hopf_map_aux` is a polynomial expression in the real and
-- imaginary parts of `w` and `z`, so the ambient map `ℂ² → ℝ³` is smooth; then restrict the
-- domain to `S^3` and codomain to `S^2` using the manifold structure on spheres.
/-- Problem 2-3 (2): the map `F : S^3 → S^2` with coordinates
`(z\bar{w} + w\bar{z}, iw\bar{z} - iz\bar{w}, z\bar{z} - w\bar{w})` is smooth. -/
theorem hopf_map_smooth :
    ContMDiff (𝓡 3) (𝓡 2) ∞ hopf_map := sorry
