import Mathlib
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Proposition_16_27

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open Lean Elab Term
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Corollary 16.49 (1) is Proposition 16.27. -/
#check interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero

-- Proof sketch: rewrite the continuity set using Proposition 16.27, then use convexity of
-- `effectiveDomain f` from `hf` together with the Chapter 6 fact that the interior of a convex set
-- is contained in its strong relative interior.
/-- Corollary 16 49 (2): for `f ∈ Γ₀(H)`, every continuity point on the effective domain belongs to
the strong relative interior of the effective domain. -/
theorem continuitySet_subset_strongRelativeInterior_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    {x : H | ContinuousAtOnEffectiveDomain f x} ⊆ sri (effectiveDomain f) := by
  rw [← interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero hf]
  by_cases hinter : (interior (effectiveDomain f)).Nonempty
  · rw [interior_eq_strongRelativeInterior_of_convex_nonempty_interior
      hf.2.convex_effectiveDomain hinter]
  · simp [Set.not_nonempty_iff_eq_empty.mp hinter]

/-- Helper for Corollary 16 49: subtracting the zero singleton does not change a set. -/
private theorem sub_singleton_zero_eq_self {E : Type*} [AddGroup E] (C : Set E) :
    C - ({0} : Set E) = C := by
  -- Rewrite set subtraction through the explicit witness `0`.
  ext x
  constructor
  · intro hx
    rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, hyz⟩
    have hz0 : z = 0 := by
      simpa using hz
    subst z
    have hxy : x = y := by
      simpa using hyz.symm
    simpa [hxy] using hy
  · intro hx
    refine Set.mem_sub.mpr ?_
    have hzero_mem : (0 : E) ∈ ({0} : Set E) := by
      simp
    have hx_sub : x - 0 = x := sub_zero x
    exact ⟨x, hx, 0, hzero_mem, hx_sub⟩

omit [CompleteSpace H] in
/-- Helper for Corollary 16 49: translating a strong-relative-interior point to the origin turns
the regularity set into the difference with the singleton base point. -/
private theorem zero_mem_strongRelativeInterior_sub_singleton_of_mem_strongRelativeInterior
    {C : Set H} {y : H} (hy : y ∈ sri C) :
    (0 : H) ∈ sri (C - ({y} : Set H)) := by
  -- Unfold the strong-relative-interior hypothesis at `y` and reuse the same cone identity after
  -- translating the base point to `0`.
  rcases Set.mem_strongRelativeInterior_iff.mp hy with ⟨hyC, hcone⟩
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨?_, ?_⟩
  · refine Set.mem_sub.mpr ?_
    exact ⟨y, hyC, y, by simp, sub_self y⟩
  · simpa [sub_singleton_zero_eq_self] using hcone

omit [CompleteSpace H] in
/-- Helper for Corollary 16 49: the singleton indicator belongs to `Γ₀(H)`. -/
private theorem singleton_indicator_mem_gammaZero (y : H) :
    ι[({y} : Set H)] ∈ Γ₀(H) := by
  -- The singleton indicator is lower semicontinuous, proper, and convex because its effective
  -- domain is the convex singleton `{y}`.
  have hindicator_lsc :
      LowerSemicontinuous (fun z ↦ ((ι[({y} : Set H)]) z : EReal)) := by
    simpa using
      (lowerSemicontinuous_indicator_compl_top_iff_isClosed ({y} : Set H)).2 isClosed_singleton
  have hy_mem : y ∈ effectiveDomain (ι[({y} : Set H)]) := by
    simp [effectiveDomain_indicator]
  have hy_dom_nonempty : (effectiveDomain (ι[({y} : Set H)])).Nonempty := ⟨y, hy_mem⟩
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨hy_dom_nonempty, fun _ hz ↦ hz, ?_⟩
  intro x hx z hz a ha0 ha1
  have hx' : x = y := by
    simpa using hx
  have hz' : z = y := by
    simpa using hz
  subst x
  subst z
  simp

elab "compositeDualAttainment" : term => do
  let theoremName :=
    Name.str
      (Name.mkSimple "ERealFunction")
      ("exists_mem_argmin_compositeDualObjective_eq_neg_" ++
        "compositePrimalOptimalValue_of_zero_mem_sri_sub_" ++
        "image_effectiveDomain")
  elabTerm (mkIdent theoremName) none

-- Proof sketch: fix `y ∈ sri (effectiveDomain f)` and constrain `f` by the singleton indicator
-- at `y`. The verified prefix below builds the source-faithful regularity witness
-- `0 ∈ sri (effectiveDomain f - {y})`, packages the singleton indicator as a `Γ₀` function, and
-- shows that the constrained objective has the trivial subgradient `0` at `y`. The remaining step
-- is the exact subdifferential splitting from the attained dual formula for the singleton
-- perturbation.
/-- Corollary 16.49 (3): for `f ∈ Γ₀(H)`, the strong relative interior of the effective domain is
contained in the subdifferentiability domain. -/
theorem strongRelativeInterior_effectiveDomain_subset_subdifferentiabilityDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    sri (effectiveDomain f) ⊆ {x : H | SubdifferentiableAt f x} := by
  intro y hy
  -- Read the strong-relative-interior hypothesis as effective-domain membership at the active
  -- singleton-constraint point.
  rcases Set.mem_strongRelativeInterior_iff.mp hy with ⟨hy_dom, _⟩
  have hsri :
      (0 : H) ∈
        sri (effectiveDomain f -
          (ContinuousLinearMap.id ℝ H) '' effectiveDomain (ι[({y} : Set H)])) := by
    simpa [effectiveDomain_indicator] using
      (zero_mem_strongRelativeInterior_sub_singleton_of_mem_strongRelativeInterior hy)
  obtain ⟨u, _, hu_eq⟩ :=
    compositeDualAttainment
      (ι[({y} : Set H)])
      (singleton_indicator_mem_gammaZero y)
      f
      hf
      (ContinuousLinearMap.id ℝ H)
      hsri
  have hprimal :
      compositePrimalOptimalValue (ι[({y} : Set H)]) f (ContinuousLinearMap.id ℝ H) =
        (f y : EReal) := by
    rw [compositePrimalOptimalValue, primalOptimalValue_eq_iInf_primalObjective]
    apply le_antisymm
    · simpa [primalObjective, hy_dom] using
        (iInf_le
          (fun x : H ↦ primalObjective (ι[({y} : Set H)])
            (f ∘ (ContinuousLinearMap.id ℝ H)) x) y)
    · refine le_iInf ?_
      intro x
      by_cases hx : x = y
      · subst hx
        simp [primalObjective]
      · have htop :
            primalObjective (ι[({y} : Set H)]) (f ∘ (ContinuousLinearMap.id ℝ H)) x = ⊤ := by
          have hfx_ne_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
          simp [primalObjective, hx, EReal.top_add_of_ne_bot hfx_ne_bot]
        rw [htop]
        exact le_top
  have hdual :
      compositeDualObjective (ι[({y} : Set H)]) f (ContinuousLinearMap.id ℝ H) u =
        -(f y : EReal) := by
    have hneg := congrArg Neg.neg hu_eq
    simpa [hprimal] using hneg.symm
  have hconj_indicator :
      ((ι[({y} : Set H)]).asEReal)∗ (-u) = (((-⟪y, u⟫_ℝ : ℝ) : EReal)) := by
    rw [conjugate_indicator_eq_supportFunction, supportFunction_eq_sSup_image]
    simp
  have hdual_explicit :
      (((-⟪y, u⟫_ℝ : ℝ) : EReal)) + f.asEReal∗ u = -(f y : EReal) := by
    have hdual_id :
        ((ι[({y} : Set H)]).asEReal)∗ (-u) + f.asEReal∗ u = -(f y : EReal) := by
      simpa [compositeDualObjective_apply] using hdual
    calc
      (((-⟪y, u⟫_ℝ : ℝ) : EReal)) + f.asEReal∗ u
          = ((ι[({y} : Set H)]).asEReal)∗ (-u) + f.asEReal∗ u := by rw [hconj_indicator]
      _ = -(f y : EReal) := hdual_id
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hconj_bot : f.asEReal∗ u ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty u
  have hconj_top : f.asEReal∗ u ≠ ⊤ := by
    intro htop
    have hsum_top :
        (((-⟪y, u⟫_ℝ : ℝ) : EReal)) + f.asEReal∗ u = ⊤ := by
      rw [htop, EReal.coe_add_top]
    have hright_top : -(f y : EReal) = ⊤ := by
      calc
        -(f y : EReal) = (((-⟪y, u⟫_ℝ : ℝ) : EReal)) + f.asEReal∗ u := hdual_explicit.symm
        _ = ⊤ := hsum_top
    have hright_ne_top : -(f y : EReal) ≠ ⊤ := by
      simpa [EReal.coe_toReal hy_top hy_bot] using
        (EReal.coe_ne_top (-(f y : EReal).toReal))
    exact hright_ne_top hright_top
  have hdual_toReal :
      -⟪y, u⟫_ℝ + (f.asEReal∗ u).toReal = -(f y : EReal).toReal := by
    have hinner_top : (-((⟪y, u⟫_ℝ : ℝ) : EReal)) ≠ ⊤ := by
      simp
    have hinner_bot : (-((⟪y, u⟫_ℝ : ℝ) : EReal)) ≠ ⊥ := by
      simp
    have htoReal :
        ((((-⟪y, u⟫_ℝ : ℝ) : EReal)) + f.asEReal∗ u).toReal = (-((f y : EReal))).toReal :=
      congrArg EReal.toReal hdual_explicit
    have htoReal' :
        -⟪y, u⟫_ℝ + (f.asEReal∗ u).toReal = (-((f y : EReal))).toReal := by
      have htoReal'' := htoReal
      have hinner_cast :
          (((-⟪y, u⟫_ℝ : ℝ) : EReal)) = -((⟪y, u⟫_ℝ : ℝ) : EReal) := by
        simp
      rw [hinner_cast] at htoReal''
      rw [EReal.toReal_add hinner_top hinner_bot hconj_top hconj_bot] at htoReal''
      simpa using htoReal''
    simpa using htoReal'
  have hfy_toReal :
      (f y : EReal).toReal + (f.asEReal∗ u).toReal = ⟪y, u⟫_ℝ := by
    linarith
  have hleft_top :
      (f y : EReal) + f.asEReal∗ u ≠ ⊤ :=
    EReal.add_ne_top hy_top hconj_top
  have hleft_bot :
      (f y : EReal) + f.asEReal∗ u ≠ ⊥ := by
    rw [EReal.add_ne_bot_iff]
    exact ⟨hy_bot, hconj_bot⟩
  have hfy :
      (f y : EReal) + f.asEReal∗ u = ((⟪y, u⟫_ℝ : ℝ) : EReal) := by
    have hleft_toReal :
        ((f y : EReal) + f.asEReal∗ u).toReal = ⟪y, u⟫_ℝ := by
      rw [EReal.toReal_add hy_top hy_bot hconj_top hconj_bot]
      exact hfy_toReal
    exact
      (EReal.toReal_eq_toReal hleft_top hleft_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
        hleft_toReal
  have hsub : u ∈ (∂ f) y :=
    (ERealFunction.mem_subdifferential_iff_fenchel_young_eq f y u).2 hfy
  change SubdifferentiableAt f y
  rw [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff]
  exact ⟨u, hsub⟩

/- Corollary 16.49 (4) is Proposition 16.4 (1). -/
#check subdifferential_domain_subset_effectiveDomain

end SubdifferentialCalculus

end ERealFunction
