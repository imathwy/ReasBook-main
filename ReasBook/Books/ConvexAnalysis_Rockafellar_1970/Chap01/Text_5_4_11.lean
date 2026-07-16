import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_7
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Rockafellar
open scoped Pointwise
open Function

section

variable {E : Type*} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/- Text 5.4.11 studies the source function `x ↦ δ[𝕜](x | C) + 1`. -/
/-- The right scalar multiple of `x ↦ δ[𝕜](x | C) + 1` is
`x ↦ δ[𝕜](x | λ • C) + λ`. -/
theorem rightScalarMul_indicator_add_one
    (C : Set E) (lam : 𝕜≥0) :
    lam •ʳ (δ[𝕜](· | C) + 1) =
      fun x ↦ δ[𝕜](x | (lam : 𝕜) • C) + (lam : 𝕜) := by
  funext x
  by_cases hC_nonempty : C.Nonempty
  · by_cases hlam : (lam : 𝕜) = 0
    · have hlam_eq : lam = ⟨0, le_rfl⟩ := Subtype.ext hlam
      obtain ⟨y, hy⟩ := hC_nonempty
      -- At `λ = 0`, the scaled epigraph collapses to the origin indicator because `epi (δ + 1)`
      -- is nonempty whenever `C` is nonempty.
      have hepi : (epi (fun z : E ↦ δ[𝕜](z | C) + 1)).Nonempty := by
        refine ⟨(y, 1), ?_⟩
        simp [hy]
      calc
        (lam •ʳ (δ[𝕜](· | C) + 1)) x =
            ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ (δ[𝕜](· | C) + 1)) x := by rw [hlam_eq]
        _ = δ[𝕜](x | ({0} : Set E)) :=
          rightScalarMul_zero_apply_eq_origin_indicator_of_epi_nonempty
            (f := fun z : E ↦ δ[𝕜](z | C) + 1) (hepi := hepi) x
        _ = δ[𝕜](x | (lam : 𝕜) • C) + (lam : 𝕜) := by
          rw [hlam, Set.zero_smul_set ⟨y, hy⟩, ← Set.singleton_zero]
          simp
    · have hlam_pos : 0 < (lam : 𝕜) := lt_of_le_of_ne lam.2 (Ne.symm hlam)
      have hlam_sub :
          (⟨(lam : 𝕜), hlam_pos.le⟩ : 𝕜≥0) = lam := Subtype.ext rfl
      -- For a positive scalar, use the explicit rescaling formula from Text 5.4.3.
      calc
        (lam •ʳ (δ[𝕜](· | C) + 1)) x =
            ((⟨(lam : 𝕜), hlam_pos.le⟩ : 𝕜≥0) •ʳ (δ[𝕜](· | C) + 1)) x := by rw [hlam_sub]
        _ = ((lam : 𝕜) : WithTopBot 𝕜) *
              (δ[𝕜]((lam : 𝕜)⁻¹ • x | C) + 1) :=
          rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
            (f := fun z : E ↦ δ[𝕜](z | C) + 1) (a := (lam : 𝕜)) hlam_pos x
        _ = δ[𝕜](x | (lam : 𝕜) • C) + (lam : 𝕜) := by
          by_cases hx : x ∈ (lam : 𝕜) • C
          · have hxC : (lam : 𝕜)⁻¹ • x ∈ C := by
              exact (Set.mem_smul_set_iff_inv_smul_mem₀ hlam C x).mp hx
            rw [indicator_of_mem C hxC, indicator_of_mem ((lam : 𝕜) • C) hx]
            simp
          · have hxC : (lam : 𝕜)⁻¹ • x ∉ C := by
              exact mt (Set.mem_smul_set_iff_inv_smul_mem₀ hlam C x).mpr hx
            rw [indicator_of_notMem C hxC,
              indicator_of_notMem ((lam : 𝕜) • C) hx]
            apply WithTop.mul_top
            exact_mod_cast hlam
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    by_cases hlam : (lam : 𝕜) = 0
    · have hlam_eq : lam = ⟨0, le_rfl⟩ := Subtype.ext hlam
      subst lam
      -- If `C = ∅`, then `δ[𝕜](· | C) + 1` is identically `⊤`, so the zero scalar leaves it unchanged.
      have hf_top : (fun z : E ↦ δ[𝕜](z | C) + 1) = (⊤ : E → WithTopBot 𝕜) := by
        funext z
        simp [hC_empty]
      rw [rightScalarMul_zero_eq_self_of_eq_top (f := fun z : E ↦ δ[𝕜](z | C) + 1) hf_top]
      simp [hC_empty]
    · have hlam_pos : 0 < (lam : 𝕜) := lt_of_le_of_ne lam.2 (Ne.symm hlam)
      have hlam_sub :
          (⟨(lam : 𝕜), hlam_pos.le⟩ : 𝕜≥0) = lam := Subtype.ext rfl
      -- The positive-scalar formula again reduces the empty-set case to the `⊤` branch.
      calc
        (lam •ʳ (δ[𝕜](· | C) + 1)) x =
            ((⟨(lam : 𝕜), hlam_pos.le⟩ : 𝕜≥0) •ʳ (δ[𝕜](· | C) + 1)) x := by rw [hlam_sub]
        _ = ((lam : 𝕜) : WithTopBot 𝕜) *
              (δ[𝕜]((lam : 𝕜)⁻¹ • x | C) + 1) :=
          rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
            (f := fun z : E ↦ δ[𝕜](z | C) + 1) (a := (lam : 𝕜)) hlam_pos x
        _ = δ[𝕜](x | (lam : 𝕜) • C) + (lam : 𝕜) := by
          rw [indicator_of_notMem C (by simp [hC_empty]),
            indicator_of_notMem ((lam : 𝕜) • C) (by simp [hC_empty])]
          apply WithTop.mul_top
          exact_mod_cast hlam

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Preorder 𝕜] [Zero 𝕜]
variable [SMul 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- Nonnegative scalars whose dilates of `C` contain `x`. -/
def nonnegDilates (C : Set E) (x : E) : Set 𝕜≥0 :=
  {c : 𝕜≥0 | x ∈ (c : 𝕜) • C}

/-- The `WithTopBot 𝕜` image of `nonnegDilates C x`. -/
def nonnegDilateValues (C : Set E) (x : E) : Set (WithTopBot 𝕜) :=
  (fun c : 𝕜≥0 ↦ ((c : 𝕜) : WithTopBot 𝕜)) '' nonnegDilates C x

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [SMul 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- The pointwise infimum of the dilated indicator-shift terms in the ordered
`WithTopBot 𝕜` codomain. -/
private theorem iInf_indicator_dilate_add_eq_sInf_nonneg_dilates
    (C : Set E) (x : E) :
    (⨅ a : 𝕜≥0, δ[𝕜](x | (a : 𝕜) • C) + (a : 𝕜)) =
      sInf (nonnegDilateValues C x) := by
  -- Rewrite the set-level target as an image infimum, then simplify each term by the indicator formula.
  rw [nonnegDilateValues, sInf_image]
  refine iInf_congr fun a ↦ ?_
  change
    (if x ∈ (a : 𝕜) • C then (0 : WithTopBot 𝕜) else ⊤) +
        ((a : 𝕜) : WithTopBot 𝕜) =
      ⨅ (_ : x ∈ (a : 𝕜) • C), ((a : 𝕜) : WithTopBot 𝕜)
  split <;> simp_all

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- For the empty set, the generated sublinear hull of `x ↦ δ[𝕜](x | C) + 1` takes the value `0`
at the origin. -/
theorem sublinearHull_indicator_add_one_empty_zero :
    sublinearHull (fun y : E ↦ δ[𝕜](y | (∅ : Set E)) + 1) (0 : E) = 0 := by
  change (sublinearHull
      (fun y : E ↦ (δ[𝕜](y | (∅ : Set E)) : WithTopBot 𝕜) + ((1 : 𝕜) : WithTopBot 𝕜))
      (0 : E) : WithTopBot 𝕜) = 0
  rw [sublinearHull_eq_sInf_verticalHeights]
  have hepi :
      epi (fun y : E ↦ (δ[𝕜](y | (∅ : Set E)) : WithTopBot 𝕜) + ((1 : 𝕜) : WithTopBot 𝕜)) =
        (∅ : Set (E × 𝕜)) := by
    ext p
    rcases p with ⟨y, a⟩
    constructor
    · intro h
      have : ((⊤ : WithTopBot 𝕜) + ((1 : 𝕜) : WithTopBot 𝕜)) ≤ a := by
        simp at h
      simpa using this
    · simp
  rw [hepi]
  simp [Function.verticalHeights, Function.verticalSection]

end

section

variable {E : Type*} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- Helper for Text 5.4.11: the indicator-shift function `x ↦ δ[𝕜](x | C) + 1` is convex
whenever `C` is convex. -/
private theorem indicator_add_one_isConvex
    (C : Set E) (hC_convex : Convex 𝕜 C) :
    (fun y ↦ δ[𝕜](y | C) + 1).IsConvex 𝕜 := by
  change Convex 𝕜 (epi (fun y : E ↦ δ[𝕜](y | C) + 1))
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, μx⟩
  rcases q with ⟨y, μy⟩
  rw [mem_epi_iff] at hp hq ⊢
  -- Membership in the epigraph forces both base points to lie in `C`.
  have hxC : x ∈ C := by
    by_cases hx : x ∈ C
    · exact hx
    · simp [indicator_def, hx] at hp
  have hyC : y ∈ C := by
    by_cases hy : y ∈ C
    · exact hy
    · simp [indicator_def, hy] at hq
  have hxyC : a • x + b • y ∈ C := hC_convex hxC hyC ha hb hab
  -- The finite-height parts of the epigraph inequalities reduce to lower bounds by `1`.
  have hx_one : (1 : 𝕜) ≤ μx := by
    simpa [indicator_def, hxC] using hp
  have hy_one : (1 : 𝕜) ≤ μy := by
    simpa [indicator_def, hyC] using hq
  have hone :
      (1 : 𝕜) ≤ a • μx + b • μy := by
    have hlin :
        a • (1 : 𝕜) + b • (1 : 𝕜) ≤ a • μx + b • μy :=
      add_le_add
        (smul_le_smul_of_nonneg_left hx_one ha)
        (smul_le_smul_of_nonneg_left hy_one hb)
    simpa [smul_eq_mul, hab] using hlin
  simp only [Prod.smul_mk, Prod.mk_add_mk]
  rw [indicator_of_mem (α := 𝕜) (C := C) hxyC]
  simpa [smul_eq_mul] using
    (WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr hone) :
      ((1 : 𝕜) : WithTopBot 𝕜) ≤
        ((a • μx + b • μy : 𝕜) : WithTopBot 𝕜))

/-- The positively homogeneous convex function generated by `x ↦ δ[𝕜](x | C) + 1`
is the pointwise infimum of the nonnegative right scalar multiples when `C` is nonempty and
convex. -/
theorem sublinearHull_indicator_add_one_eq_iInf_rightScalarMul
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    sublinearHull (fun y ↦ δ[𝕜](y | C) + 1) =
      fun x ↦ ⨅ a : 𝕜≥0, (a •ʳ (δ[𝕜](· | C) + 1)) x := by
  funext x
  -- Text 5.4.9 applies once we package convexity and rule out the identically `⊤` case.
  have h_convex : (fun y : E ↦ δ[𝕜](y | C) + 1).IsConvex 𝕜 :=
    indicator_add_one_isConvex (C := C) hC_convex
  have h_ne_top : (fun y : E ↦ δ[𝕜](y | C) + 1) ≠ (⊤ : E → WithTopBot 𝕜) := by
    obtain ⟨y, hy⟩ := hC_nonempty
    intro htop
    have : (((1 : 𝕜) : WithTopBot 𝕜)) = ⊤ := by
      simpa [indicator_def, hy] using congrFun htop y
    simpa using this
  exact Function.sublinearHull_eq_iInf_rightScalarMul
    (h := fun y : E ↦ δ[𝕜](y | C) + 1)
    (h_convex := h_convex) (x := x) (hx := Or.inr h_ne_top)

/-- Bridge form of `sublinearHull_indicator_add_one_eq_iInf_rightScalarMul`: the right scalar
multiple terms are rewritten as dilated indicator-shift expressions. -/
theorem sublinearHull_indicator_add_one_eq_iInf_dilate_add
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    sublinearHull (fun y ↦ δ[𝕜](y | C) + 1) =
      fun x ↦ ⨅ a : 𝕜≥0, δ[𝕜](x | (a : 𝕜) • C) + (a : 𝕜) := by
  funext x
  rw [sublinearHull_indicator_add_one_eq_iInf_rightScalarMul
      (C := C) (hC_convex := hC_convex) (hC_nonempty := hC_nonempty)]
  refine iInf_congr (fun a : 𝕜≥0 ↦ ?_)
  simpa using congrFun (rightScalarMul_indicator_add_one (C := C) (lam := a)) x

/-- Canonical codomain-level endpoint: the generated positively homogeneous convex function of
`x ↦ δ[𝕜](x | C) + 1` is the nonnegative-dilate infimum in `WithTopBot 𝕜` when `C` is nonempty and
convex. -/
theorem sublinearHull_indicator_add_one_eq_sInf_nonneg_dilates
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    sublinearHull (fun y ↦ δ[𝕜](y | C) + 1) =
      fun x ↦
        sInf (nonnegDilateValues C x) := by
  funext x
  rw [sublinearHull_indicator_add_one_eq_iInf_dilate_add
      (C := C) (hC_convex := hC_convex) (hC_nonempty := hC_nonempty)]
  simpa using iInf_indicator_dilate_add_eq_sInf_nonneg_dilates (C := C) (x := x)

end
