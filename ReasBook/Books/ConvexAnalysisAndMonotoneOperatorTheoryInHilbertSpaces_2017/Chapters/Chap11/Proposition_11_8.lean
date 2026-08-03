import Mathlib
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap10.Definition_10_27
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Proposition_11_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u}

section StrictQuasiconvex

variable [AddCommMonoid H] [Module ℝ H]

/-- A strictly quasiconvex objective has at most one global minimizer. -/
theorem argmin_subsingleton_of_strictlyQuasiconvex
    {f : H → EReal} (hstrict : StrictlyQuasiconvex f) :
    (Argmin f).Subsingleton := by
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  have hxmin : ∀ z, f x ≤ f z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hx)
  have hymin : ∀ z, f y ≤ f z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hy)
  rcases hstrict.isProper.2 with ⟨z, hz_dom⟩
  have hx_dom : x ∈ dom f := by
    rw [mem_dom_iff_ne_top]
    intro hxtop
    have : (⊤ : EReal) ≤ f z := by simpa [hxtop] using hxmin z
    exact (not_lt_of_ge this) ((mem_dom_iff f z).mp hz_dom)
  have hy_dom : y ∈ dom f := by
    rw [mem_dom_iff_ne_top]
    intro hytop
    have : (⊤ : EReal) ≤ f z := by simpa [hytop] using hymin z
    exact (not_lt_of_ge this) ((mem_dom_iff f z).mp hz_dom)
  let z : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hstrict_z : f z < max (f x) (f y) :=
    hstrict.ineq hx_dom hy_dom hxy (by norm_num) (by norm_num)
  have hx_z : f x ≤ f z := hxmin z
  have hy_z : f y ≤ f z := hymin z
  have hmax_z : max (f x) (f y) ≤ f z := max_le hx_z hy_z
  exact (not_lt_of_ge hmax_z hstrict_z).elim

/-- Proposition 11 8 (1): if the indicator-augmented function `f + ι_C` is strictly
quasiconvex, then `f` has at most one minimizer on `C`. -/
-- Proof sketch: strict quasiconvexity of `f + ι[C]` already makes
-- `f + ι_C` proper, so any two constrained
-- minimizers lie in its domain. Applying the strict midpoint inequality to two distinct
-- minimizers contradicts minimality.
theorem argminOn_subsingleton_of_indicator_strictlyQuasiconvex
    {f : H → EReal} {C : Set H}
    (hstrict : StrictlyQuasiconvex (f + (ι[C]).asEReal)) :
    (Argmin[C] f).Subsingleton := by
  have hbot : ∀ x ∉ C, f x ≠ ⊥ := by
    intro x hxC hfx
    have hg : (f + (ι[C]).asEReal) x ≠ ⊥ := hstrict.isProper.1 x
    exact hg <| by simp [hxC, hfx]
  rw [argminOn_eq_inter_argmin_add_indicator f C hbot]
  exact (argmin_subsingleton_of_strictlyQuasiconvex hstrict).anti Set.inter_subset_right

end StrictQuasiconvex

section ConvexMinimizer

section

/-- Helper for Proposition 11 8: any constrained minimizer is finite once the constraint set
contains one point of the effective domain. -/
private theorem mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {x : H}
    (hx : x ∈ Argmin[C] f.asEReal) (hfeas : (C ∩ effectiveDomain f).Nonempty) :
    x ∈ effectiveDomain f := by
  rcases mem_argminOn_iff.mp hx with ⟨hxC, hxmin⟩
  rcases hfeas with ⟨z, hzC, hz_dom⟩
  -- Compare the minimizer value against one feasible finite point.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt ((isMinOn_iff.mp hxmin) z hzC) (mem_effectiveDomain_iff.mp hz_dom)

end

section

variable [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

/-- Helper for Proposition 11 8: distinct feasible points of a strictly convex set have their
midpoint in the interior. -/
private theorem strict_midpoint_mem_interior
    {C : Set H} {x y : H} (hstrictC : StrictConvex ℝ C)
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) ∈ interior C := by
  -- Apply strict convexity with the textbook midpoint coefficients.
  exact hstrictC hx hy hxy (by norm_num) (by norm_num) (by norm_num)

end

section

variable [AddCommGroup H] [Module ℝ H]

/-- Helper for Proposition 11 8: convexity on the effective domain keeps the textbook midpoint
finite. -/
private theorem strict_midpoint_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hconv : ConvexOn f (effectiveDomain f))
    (hx_dom : x ∈ effectiveDomain f) (hy_dom : y ∈ effectiveDomain f) :
    ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) ∈ effectiveDomain f := by
  -- The source proof first keeps the midpoint inside the effective domain before using value
  -- comparisons there.
  simpa using
    hconv.convex_effectiveDomain hx_dom hy_dom (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ 1 - (1 / 2 : ℝ)) (by norm_num)

end

section

variable [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
variable [ContinuousSMul ℝ H]

/-- Helper for Proposition 11 8: convexity on the effective domain makes the midpoint of two
constrained minimizers another constrained minimizer. -/
private theorem strict_midpoint_mem_argminOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {x y : H}
    (hconv : ConvexOn f (effectiveDomain f)) (hstrictC : StrictConvex ℝ C)
    (hx : x ∈ Argmin[C] f.asEReal) (hy : y ∈ Argmin[C] f.asEReal)
    (hx_dom : x ∈ effectiveDomain f) (hy_dom : y ∈ effectiveDomain f) :
    ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) ∈ Argmin[C] f.asEReal := by
  rcases mem_argminOn_iff.mp hx with ⟨hxC, hxmin⟩
  rcases mem_argminOn_iff.mp hy with ⟨hyC, hymin⟩
  let m : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hmC : m ∈ C := by
    -- Strict convexity supplies convexity, so the midpoint stays feasible.
    simpa [m] using
      hstrictC.convex hxC hyC (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : 0 ≤ 1 - (1 / 2 : ℝ)) (by norm_num)
  have hm_dom : m ∈ effectiveDomain f := by
    -- Reuse the midpoint finiteness bridge before applying convexity inequalities.
    simpa [m] using strict_midpoint_mem_effectiveDomain hconv hx_dom hy_dom
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hxy_val : (f x : EReal) = (f y : EReal) := by
    -- Minimality in both directions identifies the endpoint values.
    exact le_antisymm ((isMinOn_iff.mp hxmin) y hyC) ((isMinOn_iff.mp hymin) x hxC)
  have hxy_val_real : (f x : EReal).toReal = (f y : EReal).toReal := by
    -- Finite endpoint values can be compared in `ℝ`.
    exact EReal.coe_eq_coe_iff.mp <| by
      simpa [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot] using hxy_val
  have hm_le_avg :
      (f m : EReal) ≤
        (1 / 2 : EReal) * (f x : EReal) + (1 - (1 / 2 : ℝ) : EReal) * (f y : EReal) := by
    -- Jensen's inequality on the effective domain controls the midpoint value.
    simpa [m] using hconv.ineq hx_dom hy_dom (by norm_num) (by norm_num)
  have hm_le_x : (f m : EReal) ≤ (f x : EReal) := by
    -- The equal endpoint values collapse the average back to the common minimum value.
    have hone_sub_half : (1 - (1 / 2 : ℝ) : EReal) = ((1 / 2 : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) (by norm_num : (1 - (1 / 2 : ℝ) : ℝ) = (1 / 2 : ℝ))
    have hrhs :
        (1 / 2 : EReal) * (f x : EReal) + (1 - (1 / 2 : ℝ) : EReal) * (f y : EReal) =
          (f x : EReal) := by
      rw [hone_sub_half, show (1 / 2 : EReal) = ((1 / 2 : ℝ) : EReal) by rfl,
        ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_toReal hx_top hx_bot]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
        rw [hxy_val_real]
        simp
        ring
    calc
      (f m : EReal) ≤
          (1 / 2 : EReal) * (f x : EReal) + (1 - (1 / 2 : ℝ) : EReal) * (f y : EReal) :=
        hm_le_avg
      _ = (f x : EReal) := hrhs
  refine mem_argminOn_iff.mpr ⟨hmC, ?_⟩
  -- Compare every feasible point to `x`, then insert the midpoint estimate.
  rw [isMinOn_iff]
  intro z hzC
  calc
    (f m : EReal) ≤ (f x : EReal) := hm_le_x
    _ ≤ (f z : EReal) := (isMinOn_iff.mp hxmin) z hzC

end

variable [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
variable [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

/-- Proposition 11 8 (2): if `f` is convex on its effective domain, `C` is disjoint from
`Argmin f`, `C ∩ effectiveDomain f` is nonempty, and `C` is strictly convex, then `f` has at
most one minimizer on `C`. -/
-- Proof sketch: if two distinct points of `C` both minimize `f`, strict convexity of `C` places
-- the open segment between them in `interior C`, so in particular their midpoint lies in
-- `interior C`. The feasibility hypothesis provides one point of `C ∩ effectiveDomain f`, and
-- comparing against that feasible point shows any constrained minimizer of `f` on `C` already
-- lies in `effectiveDomain f`. Convexity on `effectiveDomain f` then shows that this midpoint is
-- also a constrained minimizer, and Proposition 11.5 upgrades it to a global minimizer,
-- contradicting the disjointness from `Argmin f`.
theorem argminOn_subsingleton_of_strictConvex
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hconv : ConvexOn f (effectiveDomain f))
    (hdisjoint : Disjoint C (Argmin f.asEReal))
    (hC_dom : (C ∩ effectiveDomain f).Nonempty)
    (hstrictC : StrictConvex ℝ C) :
    (Argmin[C] f.asEReal).Subsingleton := by
  -- Route correction: keep the source midpoint contradiction, then upgrade the midpoint
  -- constrained minimizer to a global minimizer via Proposition 11.5.
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  have hx_dom : x ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain hx hC_dom
  have hy_dom : y ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain hy hC_dom
  let m : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hm_argminOn : m ∈ Argmin[C] f.asEReal := by
    -- The midpoint remains a constrained minimizer by convexity of `f`.
    simpa [m] using strict_midpoint_mem_argminOn hconv hstrictC hx hy hx_dom hy_dom
  have hm_int : m ∈ interior C := by
    -- Distinct endpoints in a strictly convex set push the midpoint into the interior.
    simpa [m] using
      strict_midpoint_mem_interior hstrictC (mem_of_mem_argminOn hx) (mem_of_mem_argminOn hy) hxy
  have hm_dom : m ∈ effectiveDomain f := by
    -- The midpoint is finite directly from convexity on the effective domain.
    simpa [m] using strict_midpoint_mem_effectiveDomain hconv hx_dom hy_dom
  have hm_argmin : m ∈ Argmin f.asEReal := by
    -- An interior constrained minimizer of a convex function is already a global minimizer.
    exact mem_argmin_of_mem_argminOn_of_mem_interior_of_convexOn_effectiveDomain
      f hconv hm_dom hm_argminOn hm_int
  have hmC : m ∈ C := interior_subset hm_int
  -- This global minimizer lies in `C`, contradicting the disjointness hypothesis.
  exact False.elim <| Set.disjoint_left.mp hdisjoint hmC hm_argmin

end ConvexMinimizer

end ERealFunction
