import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.LinearAlgebra.BilinearForm.Properties
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_4

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {C : Set 𝕜} {f : 𝕜 → 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 4.5 is the Hessian characterization of convexity for a twice
  differentiable scalar-valued function on a convex domain.
- `core/canonical`: the statement owner is `ConvexOn 𝕜 C f`, and the second-order owner is the
  canonical set-local bilinear second derivative `bilinearIteratedFDerivWithinTwo 𝕜 f C`.
- `bridge/view`: the primary statement is intrinsic/relative, using `intrinsicInterior 𝕜 C`;
  the ambient-open textbook form is a derived corollary.

Scalar/ambient note:
- The intrinsic-owner shift is kept on theorem surfaces.
- The scalar/ambient layer is one-dimensional over an ordered normed field `𝕜`; the theorem is
  expressed on the intrinsic owner route through `IsOpen.convexOn_iff_nonneg_deriv2` from
  Theorem 4.4.
-/

lemma differentiableOn_deriv_of_differentiableOn_fderivWithin
    (hC_open : IsOpen C) (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C) :
    DifferentiableOn 𝕜 (deriv f) C := by
  intro x hx
  have hc : DifferentiableAt 𝕜 (fderivWithin 𝕜 f C) x :=
    (hf' x hx).differentiableAt (hC_open.mem_nhds hx)
  have hfun : (fun y : 𝕜 ↦ (fderivWithin 𝕜 f C y) 1) = derivWithin f C := by
    funext y
    exact fderivWithin_derivWithin (𝕜 := 𝕜) (f := f) (s := C) (x := y)
  have hdwAt : DifferentiableAt 𝕜 (derivWithin f C) x := by
    simpa [hfun] using hc.clm_apply (differentiableAt_const (1 : 𝕜))
  have hdw_eq : derivWithin f C =ᶠ[nhds x] deriv f := by
    filter_upwards [hC_open.mem_nhds hx] with y hy
    exact derivWithin_of_isOpen hC_open hy
  exact ((hdw_eq.differentiableAt_iff).1 hdwAt).differentiableWithinAt

lemma bilinForm_eq_mul_mul (B : LinearMap.BilinForm 𝕜 𝕜) (x y : 𝕜) :
    B x y = x * y * B 1 1 := by
  calc
    B x y = B (x • (1 : 𝕜)) (y • (1 : 𝕜)) := by simp
    _ = x * B 1 (y • (1 : 𝕜)) := by simpa using B.smul_left x (1 : 𝕜) (y • (1 : 𝕜))
    _ = x * (y * B 1 1) := by
      have hy1 : B 1 (y • (1 : 𝕜)) = y * B 1 1 := by
        simpa using B.smul_right y (1 : 𝕜) (1 : 𝕜)
      rw [hy1]
    _ = x * y * B 1 1 := by ring

lemma bilinForm_isSymm (B : LinearMap.BilinForm 𝕜 𝕜) : B.IsSymm := by
  refine ⟨?_⟩
  intro x y
  calc
    B x y = x * y * B 1 1 := bilinForm_eq_mul_mul B x y
    _ = y * x * B 1 1 := by ring
    _ = B y x := by
      symm
      exact bilinForm_eq_mul_mul B y x

lemma hessianWithin_apply_one_one_eq_derivWithin2
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    (bilinearIteratedFDerivWithinTwo 𝕜 f C x) 1 1 = derivWithin (derivWithin f C) C x := by
  have hc : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f C) C x := hf' x hx
  unfold bilinearIteratedFDerivWithinTwo
  change ((fderivWithin 𝕜 (fderivWithin 𝕜 f C) C x) 1) 1 = derivWithin (derivWithin f C) C x
  rw [fderivWithin_derivWithin (𝕜 := 𝕜) (f := fderivWithin 𝕜 f C) (s := C) (x := x)]
  have hfun : (fun y : 𝕜 ↦ (fderivWithin 𝕜 f C y) 1) = derivWithin f C := by
    funext y
    exact fderivWithin_derivWithin (𝕜 := 𝕜) (f := f) (s := C) (x := y)
  have happlyWithin :=
    derivWithin_clm_apply (s := C) (c := fun y : 𝕜 ↦ fderivWithin 𝕜 f C y)
      (u := fun _ : 𝕜 ↦ (1 : 𝕜)) (x := x) hc
      (differentiableWithinAt_const (s := C) (c := (1 : 𝕜)))
  have happlyWithin' :
      derivWithin (derivWithin f C) C x =
        (derivWithin (fun y : 𝕜 ↦ fderivWithin 𝕜 f C y) C x) 1 := by
    simpa [hfun] using happlyWithin
  simp [happlyWithin']

lemma hessianWithin_apply_one_one_eq_deriv2
    (hC_open : IsOpen C) (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    (bilinearIteratedFDerivWithinTwo 𝕜 f C x) 1 1 = deriv^[2] f x := by
  rw [hessianWithin_apply_one_one_eq_derivWithin2 (hf' := hf') hx]
  simpa using hC_open.derivWithin2_eq_deriv2 (f := f) hx

section Ordered

variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]

omit [OrderTopology 𝕜] [DenselyOrdered 𝕜] in
lemma hessianWithin_posSemidef_iff_nonneg_derivWithin2
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef ↔
      0 ≤ derivWithin (derivWithin f C) C x := by
  let B : LinearMap.BilinForm 𝕜 𝕜 := bilinearIteratedFDerivWithinTwo 𝕜 f C x
  have hB11 : B 1 1 = derivWithin (derivWithin f C) C x := by
    simpa [B] using hessianWithin_apply_one_one_eq_derivWithin2
      (hf' := hf') hx
  constructor
  · intro hpos
    have h11_nonneg : 0 ≤ B 1 1 := hpos.isNonneg.nonneg 1
    simpa [hB11] using h11_nonneg
  · intro hderivWithin2_nonneg
    have h11_nonneg : 0 ≤ B 1 1 := by simpa [hB11] using hderivWithin2_nonneg
    have hnonneg : B.IsNonneg := by
      refine ⟨?_⟩
      intro z
      have hzdiag : B z z = z * z * B 1 1 := bilinForm_eq_mul_mul B z z
      have hzsq_nonneg : 0 ≤ z * z := by nlinarith [sq_nonneg z]
      have : 0 ≤ z * z * B 1 1 := mul_nonneg hzsq_nonneg h11_nonneg
      simpa [hzdiag] using this
    have hpsdB : LinearMap.IsPosSemidef B :=
      (LinearMap.BilinForm.isPosSemidef_iff).1 ⟨bilinForm_isSymm B, hnonneg⟩
    simpa [B] using hpsdB

omit [OrderTopology 𝕜] [DenselyOrdered 𝕜] in
lemma hessianWithin_posSemidef_iff_nonneg_deriv2
    (hC_open : IsOpen C) (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C)
    {x : 𝕜} (hx : x ∈ C) :
    ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef ↔
      0 ≤ deriv^[2] f x := by
  rw [hessianWithin_posSemidef_iff_nonneg_derivWithin2 (hf' := hf') hx]
  simp [hC_open.derivWithin2_eq_deriv2 (f := f) hx]

/-- Textbook open-set bridge for Theorem 4.5 on the scalar-generic reusable layer (`𝕜 → 𝕜`):
on an open convex domain, convexity is equivalent to set-local Hessian positive semidefiniteness
at every point of the domain. -/
theorem convexOn_iff_hessianWithin_posSemidef_of_isOpen
    {C : Set 𝕜} {f : 𝕜 → 𝕜}
    (hC_open : IsOpen C) (hC_convex : Convex 𝕜 C) (hf : DifferentiableOn 𝕜 f C)
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C) :
    ConvexOn 𝕜 C f ↔
      ∀ x ∈ C,
        ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef := by
  have hderiv : DifferentiableOn 𝕜 (deriv f) C :=
    differentiableOn_deriv_of_differentiableOn_fderivWithin hC_open hf'
  have hconv_iff_nonneg : ConvexOn 𝕜 C f ↔
      ∀ x ∈ C, 0 ≤ derivWithin (derivWithin f C) C x := by
    simpa using hC_open.convexOn_iff_nonneg_derivWithin2
      (s := C) (f := f) hC_convex hf hderiv
  constructor
  · intro hconv x hx
    exact (hessianWithin_posSemidef_iff_nonneg_derivWithin2
      (hf' := hf') hx).2 ((hconv_iff_nonneg.mp hconv) x hx)
  · intro hpsd
    refine hconv_iff_nonneg.mpr ?_
    intro x hx
    exact (hessianWithin_posSemidef_iff_nonneg_derivWithin2
      (hf' := hf') hx).1 (hpsd x hx)

/-- Theorem 4.5 at the intrinsic/relative-topology owner layer (on the currently available
upstream scalar/ambient layer `𝕜 → 𝕜`): on an open convex domain, convexity is equivalent to
set-local Hessian positive semidefiniteness on `intrinsicInterior 𝕜 C`. -/
theorem convexOn_iff_hessianWithin_posSemidef
    {C : Set 𝕜} {f : 𝕜 → 𝕜}
    (hC_open : IsOpen C) (hC_convex : Convex 𝕜 C) (hf : DifferentiableOn 𝕜 f C)
    (hf' : DifferentiableOn 𝕜 (fderivWithin 𝕜 f C) C) :
    ConvexOn 𝕜 C f ↔
      ∀ x ∈ intrinsicInterior 𝕜 C,
        ((bilinearIteratedFDerivWithinTwo 𝕜 f C x : LinearMap.BilinForm 𝕜 𝕜)).IsPosSemidef := by
  have hC_intrinsicInterior : intrinsicInterior 𝕜 C = C := by
    refine subset_antisymm intrinsicInterior_subset ?_
    simpa [hC_open.interior_eq] using
      (interior_subset_intrinsicInterior : interior C ⊆ intrinsicInterior 𝕜 C)
  simpa [hC_intrinsicInterior] using
    (convexOn_iff_hessianWithin_posSemidef_of_isOpen
      hC_open hC_convex hf hf')

end Ordered

end
