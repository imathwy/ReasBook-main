import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap06.Definition_6_22
import BauschkeLean.Chap06.Proposition_6_19
import BauschkeLean.Chap06.Proposition_6_24
import BauschkeLean.Chap06.Proposition_6_35
import BauschkeLean.Chap06.Theorem_6_37
import BauschkeLean.Chap07.Corollary_7_19
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap12.Example_12_3
import BauschkeLean.Chap12.Proposition_12_36
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise translate

universe u v

namespace Set

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15.31: the preimage of a cone under a continuous linear map is again a
cone. -/
private theorem preimage_isCone_of_isCone
    (D : Set K) (L : H →L[ℝ] K) (hD_cone : IsCone D) :
    IsCone (L ⁻¹' D) := by
  -- Pull the positive-scalar closure of `D` back along `L`.
  rw [isCone_iff] at hD_cone ⊢
  refine Subset.antisymm ?_ ?_
  · intro x hx
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · rintro x hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    have hmem : a • L y ∈ D := by
      exact hD_cone.symm ▸ Set.mem_smul.mpr ⟨a, ha, L y, hy, rfl⟩
    simpa using hmem

omit [CompleteSpace H] in
/-- Helper for Corollary 15.31: the intersection of two cones is again a cone. -/
private theorem inter_isCone_of_isCone
    (A B : Set H) (hA_cone : IsCone A) (hB_cone : IsCone B) :
    IsCone (A ∩ B) := by
  -- Intersect the two positive-scalar invariance statements componentwise.
  rw [isCone_iff] at hA_cone hB_cone ⊢
  refine Subset.antisymm ?_ ?_
  · intro x hx
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · rintro x hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    rcases hy with ⟨hyA, hyB⟩
    refine ⟨?_, ?_⟩
    · exact hA_cone.symm ▸ Set.mem_smul.mpr ⟨a, ha, y, hyA, rfl⟩
    · exact hB_cone.symm ▸ Set.mem_smul.mpr ⟨a, ha, y, hyB, rfl⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 15.31: taking the closure after replacing the second summand by its
closure does not change the final sum closure. -/
private theorem closure_add_closure_right_eq_closure_add
    (A B : Set H) :
    closure (A + closure B) = closure (A + B) := by
  refine Subset.antisymm ?_ (closure_mono ?_)
  · -- Move each `a + b` with `b ∈ closure B` into `closure (A + B)` by continuity of translation.
    refine closure_minimal ?_ isClosed_closure
    intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
    have htranslate :
        (fun y : H ↦ a + y) '' closure B ⊆ closure ((fun y : H ↦ a + y) '' B) :=
      image_closure_subset_closure_image (continuous_const.add continuous_id)
    have hmem_translate : a + b ∈ closure ((fun y : H ↦ a + y) '' B) :=
      htranslate ⟨b, hb, rfl⟩
    have hsubset : (fun y : H ↦ a + y) '' B ⊆ A + B := by
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      exact Set.mem_add.mpr ⟨a, ha, z, hz, rfl⟩
    exact closure_mono hsubset hmem_translate
  · -- The reverse inclusion is immediate because `B ⊆ closure B`.
    intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
    exact Set.mem_add.mpr ⟨a, ha, b, subset_closure hb, rfl⟩

omit [CompleteSpace K] in
/-- Helper for Corollary 15.31: a nonempty closed convex cone can be packaged as a `ProperCone`.
-/
private theorem exists_properCone_of_nonempty_isClosed_convex_isCone
    (D : Set K) (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D) :
    ∃ Kp : ProperCone ℝ K, (Kp : Set K) = D := by
  let coneD : ConvexCone ℝ K := hD_convex.toCone D
  have hconeD_set : (coneD : Set K) = D := by
    ext y
    constructor
    · intro hy
      rcases hD_convex.mem_toCone.mp hy with ⟨c, hc, z, hz, rfl⟩
      rw [isCone_iff] at hD_cone
      exact hD_cone.symm ▸ Set.mem_smul.mpr ⟨c, hc, z, hz, rfl⟩
    · intro hy
      exact hD_convex.subset_toCone hy
  have hconeD_nonempty : (coneD : Set K).Nonempty := by
    simpa [hconeD_set] using hD_nonempty
  have hconeD_closed : IsClosed (coneD : Set K) := by
    simpa [hconeD_set] using hD_closed
  classical
  let hDp : ∃ C : ProperCone ℝ K, (C : ConvexCone ℝ K) = coneD :=
    CanLift.prf coneD ⟨hconeD_nonempty, hconeD_closed⟩
  let Kp : ProperCone ℝ K := Classical.choose hDp
  refine ⟨Kp, ?_⟩
  ext y
  change y ∈ (((Kp : ProperCone ℝ K) : ConvexCone ℝ K) : Set K) ↔ y ∈ D
  rw [Classical.choose_spec hDp, hconeD_set]

/-- Helper for Corollary 15.31: the fiberwise dual minimand at `u` is
`v ↦ f^*(u - L^* v) + g^*(v)`. -/
private noncomputable def shiftedCompositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) : K → EReal :=
  fun v ↦ f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v

/-- Helper for Corollary 15.31: evaluating the shifted dual minimand exposes the explicit
adjoint-shifted conjugate sum. -/
@[simp] private theorem shiftedCompositeDualObjective_apply
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) (v : K) :
    shiftedCompositeDualObjective f g L u v =
      f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v :=
  rfl

omit [CompleteSpace H] in
/-- Helper for Corollary 15.31: the linear tilt `x ↦ -⟪x, u⟫` belongs to `Γ₀(H)`. -/
private theorem negativeInnerToEReal_mem_gammaZero
    (u : H) :
    (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity follows from continuity of the linear functional.
    have hcont :
        Continuous (fun x : H ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) := by
      simpa using continuous_coe_real_ereal.comp ((continuous_id.inner continuous_const).neg)
    exact hcont.lowerSemicontinuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The linear tilt is finite everywhere, in particular at the origin.
      refine ⟨0, ?_⟩
      simp
    · -- Jensen convexity is equality because the tilt is affine.
      intro x _hx y _hy a ha0 ha1
      have hreal :
          -⟪a • x + (1 - a) • y, u⟫_ℝ =
            a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      simp only [Function.toEReal_apply, EReal.coe_neg, mul_neg, ge_iff_le]
      have hcast :
          (((-⟪a • x + (1 - a) • y, u⟫_ℝ : ℝ) : EReal)) =
            (((a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
      simpa [EReal.coe_add, EReal.coe_mul] using le_of_eq hcast

/-- Helper for Corollary 15.31: the indicator of `C` tilted by `x ↦ -⟪x, u⟫` stays in `Γ₀(H)`.
-/
private theorem indicatorLinearTilt_mem_gammaZero
    (C : Set H) (u : H) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) := by
  have hGammaC : ι[C] ∈ Γ₀(H) :=
    ERealFunction.indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
      hC_nonempty hC_closed hC_convex
  have hGammaLinear : (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) :=
    negativeInnerToEReal_mem_gammaZero u
  rcases hC_nonempty with ⟨x, hx⟩
  refine pointwiseAdd_mem_gammaZero (ι[C]) ((fun x : H ↦ -⟪x, u⟫_ℝ).toEReal)
    hGammaC hGammaLinear ?_
  refine ⟨x, ?_, ?_⟩
  · simpa [mem_effectiveDomain_iff, ERealFunction.indicator_apply] using hx
  · simp

omit [CompleteSpace H] in
/-- Helper for Corollary 15.31: adding the linear tilt does not change the effective domain of the
indicator. -/
private theorem effectiveDomain_indicatorLinearTilt_eq
    (C : Set H) (u : H) :
    effectiveDomain (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) = C := by
  ext x
  by_cases hx : x ∈ C
  · constructor
    · intro _hx
      exact hx
    · intro _
      simpa [mem_effectiveDomain_iff, ERealFunction.indicator_apply, hx] using
        (EReal.coe_lt_top (-⟪x, u⟫_ℝ))
  · simp [mem_effectiveDomain_iff, ERealFunction.indicator_apply, hx]

omit [CompleteSpace H] in
/-- Helper for Corollary 15.31: evaluating a conjugate at `0` is the negative of the indexed
infimum. -/
private theorem conjugate_zero_eq_neg_iInf_local
    (φ : H → EReal) :
    φ∗ 0 = - (⨅ x : H, φ x) := by
  calc
    φ∗ 0 = ⨆ x : H, -φ x := by
      simp [conjugate_apply]
    _ = - (⨅ x : H, φ x) := by
      have hneg : (-(⨅ x : H, φ x) : EReal) = ⨆ x : H, -φ x := by
        exact OrderIso.map_iInf EReal.negOrderIso (fun x : H ↦ φ x)
      rw [hneg]

set_option linter.style.longLine false in
/-- Helper for Corollary 15.31: Theorem 15.23 gives dual attainment in the `sri` branch. -/
private theorem existsCompositeDualArgminOfZeroMemSri
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
  exact
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      (f := f) (hf := hf) (g := g) (hg := hg) (L := L) hsri

/-- Helper for Corollary 15.31: the dual objective of the tilted indicator problem is exactly the
shifted minimand used in formula `(15.43)`. -/
private theorem compositeDualObjective_indicatorLinearTilt_eq_shifted
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) (u : H) :
    compositeDualObjective (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L =
      shiftedCompositeDualObjective (ι[C]) (ι[D]) L u := by
  funext v
  rw [compositeDualObjective_apply, shiftedCompositeDualObjective_apply]
  have hconj :=
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := (ι[C]).asEReal) (y := (0 : H)) (v := -u) (β := 0))
      (-(L.adjoint v))
  have hconj' :
      ((Function.asEReal (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal))∗)
          (-(L.adjoint v)) =
        ((Function.asEReal ι[C])∗) (u - L.adjoint v) := by
    simpa [translate_apply, pointwiseAdd_apply, Function.toEReal_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
      using hconj
  rw [hconj']

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15.31: tilting `ι[C]` by `x ↦ -⟪x, u⟫` tilts the composite primal owner
by the same affine term. -/
private theorem compositePrimalObjective_indicatorLinearTilt_eq_tilted
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) (u : H) :
    compositePrimalObjective (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L =
      fun x : H ↦
        compositePrimalObjective (ι[C]) (ι[D]) L x + (((⟪x, -u⟫_ℝ : ℝ) : EReal)) := by
  funext x
  simp [compositePrimalObjective_apply, Function.toEReal_apply, add_assoc, add_comm]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15.31: negating the tilted primal optimal value recovers the conjugate of
the original composite primal objective at `u`. -/
private theorem neg_compositePrimalOptimalValue_indicatorLinearTilt_eq_conjugate
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) (u : H) :
    -compositePrimalOptimalValue
        (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L =
      (compositePrimalObjective (ι[C]) (ι[D]) L)∗ u := by
  have hzero :
      (compositePrimalObjective
          (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L)∗ 0 =
        -compositePrimalOptimalValue
          (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L := by
    rw [conjugate_zero_eq_neg_iInf_local, compositePrimalOptimalValue_def, sInf_range]
  calc
    -compositePrimalOptimalValue
        (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L =
        (compositePrimalObjective
          (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L)∗ 0 := hzero.symm
    _ = (fun x : H ↦
          compositePrimalObjective (ι[C]) (ι[D]) L x +
            (((⟪x, -u⟫_ℝ : ℝ) : EReal)))∗ 0 := by
          rw [compositePrimalObjective_indicatorLinearTilt_eq_tilted]
    _ = (τ (-u) ((compositePrimalObjective (ι[C]) (ι[D]) L)∗)) 0 := by
          have hconj :=
            congrFun
              (conjugate_translate_add_inner_add_const
                (f := compositePrimalObjective (ι[C]) (ι[D]) L)
                (y := (0 : H)) (v := -u) (β := 0))
              0
          simpa [translate_apply, add_assoc] using hconj
    _ = (compositePrimalObjective (ι[C]) (ι[D]) L)∗ u := by
          simp [translate_apply]

/-- Helper for Corollary 15.31: under the `sri` regularity hypothesis on `D - L '' C`, the
shifted indicator dual minimand is attained and computes the conjugate value. -/
private theorem
    exists_mem_argmin_shiftedCompositeDualObjective_indicator_eq_conjugate_of_zero_mem_sri_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hsri : (0 : K) ∈ sri (D - L '' C))
    (u : H) :
    ∃ v ∈ Argmin (shiftedCompositeDualObjective (ι[C]) (ι[D]) L u),
      (compositePrimalObjective (ι[C]) (ι[D]) L)∗ u =
        shiftedCompositeDualObjective (ι[C]) (ι[D]) L u v := by
  have hGammaD : ι[D] ∈ Γ₀(K) :=
    ERealFunction.indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
      hD_nonempty hD_closed hD_convex
  have hTilt :
      ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal ∈ Γ₀(H) :=
    indicatorLinearTilt_mem_gammaZero C u hC_nonempty hC_closed hC_convex
  have hsri_tilt :
      (0 : K) ∈
        sri
          (effectiveDomain (ι[D]) -
            L '' effectiveDomain (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal)) := by
    simpa [effectiveDomain_indicatorLinearTilt_eq] using hsri
  obtain ⟨v, hvArg, hvEq⟩ :=
    existsCompositeDualArgminOfZeroMemSri
      (f := ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal)
      (hf := hTilt)
      (g := ι[D])
      (hg := hGammaD)
      (L := L)
      hsri_tilt
  have hshift :
      compositeDualObjective
          (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L =
        shiftedCompositeDualObjective (ι[C]) (ι[D]) L u :=
    compositeDualObjective_indicatorLinearTilt_eq_shifted C D L u
  have hvShift :
      compositeDualObjective
          (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L v =
        shiftedCompositeDualObjective (ι[C]) (ι[D]) L u v := by
    simpa [hshift] using congrArg (fun ψ : K → EReal ↦ ψ v) hshift
  have hshift' :
      ((Function.asEReal (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal))∗ᵛ ∘ L.adjoint +
          (Function.asEReal ι[D])∗) =
        shiftedCompositeDualObjective (ι[C]) (ι[D]) L u := by
    simpa [compositeDualObjective_eq_add_reflectedConjugates] using hshift
  refine ⟨v, ?_, ?_⟩
  · simpa [hshift'] using hvArg
  · have hneg := congrArg Neg.neg hvEq
    calc
      (compositePrimalObjective (ι[C]) (ι[D]) L)∗ u =
          compositeDualObjective
            (ι[C] + (fun x : H ↦ -⟪x, u⟫_ℝ).toEReal) (ι[D]) L v := by
              simpa
                [neg_compositePrimalOptimalValue_indicatorLinearTilt_eq_conjugate]
                using hneg
      _ = shiftedCompositeDualObjective (ι[C]) (ι[D]) L u v := hvShift

-- Proof sketch: apply Proposition 6.35 to the closed convex cones `C` and `L ⁻¹' D`. The
-- preimage cone is again nonempty, closed, convex, and a cone because both cones contain `0`.
-- Then identify `(L ⁻¹' D)ᵒ⊖` with `closure (L.adjoint '' (Dᵒ⊖))` via Theorem 6.37(1), and absorb
-- the extra closure inside the outer closure of the sum.
/-- Part (1) of Corollary 15.31: the polar cone of `C ∩ L ⁻¹' D` is the closure of the sum of the polar
cone of `C` and the adjoint image of the polar cone of `D`. -/
theorem polarCone_inter_preimage_eq_closure_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D) :
    (C ∩ L ⁻¹' D)ᵒ⊖ = closure (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := by
  have hzeroD : (0 : K) ∈ D :=
    zero_mem_of_nonempty_of_isClosed_of_isCone hD_nonempty hD_closed hD_cone
  have hpre_nonempty : (L ⁻¹' D).Nonempty := by
    refine ⟨0, ?_⟩
    simpa using hzeroD
  have hpre_convex : Convex ℝ (L ⁻¹' D) := by
    simpa using hD_convex.linear_preimage L.toLinearMap
  have hpre_cone : IsCone (L ⁻¹' D) :=
    preimage_isCone_of_isCone D L hD_cone
  rcases
      exists_properCone_of_nonempty_isClosed_convex_isCone
        D hD_nonempty hD_closed hD_convex hD_cone with
    ⟨Dp, hDp_set⟩
  have hprepolar : (L ⁻¹' D)ᵒ⊖ = closure (L.adjoint '' (Dᵒ⊖)) := by
    simpa [hDp_set] using
      polarCone_preimage_eq_closure_adjoint_image_polarCone (L := L) (K := Dp)
  -- First polarize the intersection, then rewrite the preimage polar by Theorem 6.37.
  calc
    (C ∩ L ⁻¹' D)ᵒ⊖ = closure (Cᵒ⊖ + (L ⁻¹' D)ᵒ⊖) := by
      simpa [hC_closed, hD_closed.preimage L.continuous] using
        polarCone_inter_closure_eq_closure_add_polarCone
          hC_nonempty hC_convex hC_cone hpre_nonempty hpre_convex hpre_cone
    _ = closure (Cᵒ⊖ + closure (L.adjoint '' (Dᵒ⊖))) := by
      rw [hprepolar]
    _ = closure (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := by
      exact closure_add_closure_right_eq_closure_add
        (Cᵒ⊖) (L.adjoint '' (Dᵒ⊖))

/-- Helper for Corollary 15.31: a closed linear-subspace description of `D - L '' C` gives the
strong-relative-interior regularity needed for the Chapter 15 duality theorem. -/
private theorem zero_mem_sri_sub_image_of_closed_subspace_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    (0 : K) ∈ sri (D - L '' C) := by
  -- Feed the closed-subspace branch directly into Proposition 6.19.
  have hregular : strongRelativeInteriorSubImageRegularity C D L := by
    dsimp [strongRelativeInteriorSubImageRegularity]
    left
    refine ⟨hsubspace, ?_⟩
    have hclosedSpan : IsClosed ((Submodule.span ℝ (D - L '' C) : Set K)) := by
      rw [← hsubspace]
      exact hsubspace_closed
    simpa using hclosedSpan
  exact
    zero_mem_strongRelativeInterior_sub_image_of_regularity
      hC_nonempty hD_nonempty hC_convex hD_convex L hregular

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15.31: the composite primal objective of the two indicators is the
indicator of `C ∩ L ⁻¹' D`. -/
private theorem compositePrimalObjective_indicator_eq_indicator_inter_preimage
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) :
    ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L =
      (ι[C ∩ L ⁻¹' D]).asEReal := by
  ext x
  -- Expand both indicators and split on the two feasibility tests.
  by_cases hC : x ∈ C <;> by_cases hD : L x ∈ D <;>
    simp [ERealFunction.compositePrimalObjective_apply, ERealFunction.indicator_apply, hC, hD,
      Set.mem_inter_iff]

/-- Helper for Corollary 15.31: pointwise, the indicator of the polar cone of
`C ∩ L ⁻¹' D` agrees with the indicator of `Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` under the closed-subspace
hypothesis on `D - L '' C`. -/
private theorem
    indicator_polar_inter_eq_indicator_polar_sum_of_closed_subspace_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C))
    (u : H) :
    ((ι[(C ∩ L ⁻¹' D)ᵒ⊖]).asEReal) u =
      (ι[Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)]).asEReal u := by
  have hzeroC : (0 : H) ∈ C :=
    zero_mem_of_nonempty_of_isClosed_of_isCone hC_nonempty hC_closed hC_cone
  have hzeroD : (0 : K) ∈ D :=
    zero_mem_of_nonempty_of_isClosed_of_isCone hD_nonempty hD_closed hD_cone
  have hzero_pre : (0 : H) ∈ L ⁻¹' D := by
    simpa using hzeroD
  have hinter_nonempty : (C ∩ L ⁻¹' D).Nonempty := ⟨0, hzeroC, hzero_pre⟩
  have hinter_cone : IsCone (C ∩ L ⁻¹' D) := by
    exact
      inter_isCone_of_isCone C (L ⁻¹' D) hC_cone
        (preimage_isCone_of_isCone D L hD_cone)
  have hsri : (0 : K) ∈ sri (D - L '' C) :=
    zero_mem_sri_sub_image_of_closed_subspace_sub_image
      C D L hC_nonempty hD_nonempty hC_convex hD_convex hsubspace hsubspace_closed
  obtain ⟨v, hvArg, hvEq⟩ :=
    exists_mem_argmin_shiftedCompositeDualObjective_indicator_eq_conjugate_of_zero_mem_sri_sub_image
      C D L hC_nonempty hC_closed hC_convex hD_nonempty hD_closed hD_convex hsri u
  have hpolar_conj :
      ((ι[(C ∩ L ⁻¹' D)ᵒ⊖]).asEReal) u =
        ((ι[C ∩ L ⁻¹' D]).asEReal)∗ u := by
    simpa using
      (congrFun
        (conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone
          (C ∩ L ⁻¹' D) hinter_nonempty hinter_cone) u).symm
  have hconj_inter :
      ((ι[(C ∩ L ⁻¹' D)ᵒ⊖]).asEReal) u =
        (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u := by
    calc
      ((ι[(C ∩ L ⁻¹' D)ᵒ⊖]).asEReal) u =
          ((ι[C ∩ L ⁻¹' D]).asEReal)∗ u := hpolar_conj
      _ = (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u := by
          rw [← compositePrimalObjective_indicator_eq_indicator_inter_preimage C D L]
  have hshift_indicator :
      shiftedCompositeDualObjective (ι[C]) (ι[D]) L u =
        fun w : K ↦ ((ι[Cᵒ⊖]).asEReal) (u - L.adjoint w) + ((ι[Dᵒ⊖]).asEReal) w := by
    funext w
    rw [shiftedCompositeDualObjective_apply,
      conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone C hC_nonempty hC_cone,
      conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone D hD_nonempty hD_cone]
  by_cases hu : u ∈ Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)
  · rcases Set.mem_add.mp hu with ⟨a, ha, b, hb, hub⟩
    rcases hb with ⟨w, hw, rfl⟩
    have hcandidate : shiftedCompositeDualObjective (ι[C]) (ι[D]) L u w = 0 := by
      have hu_sub : u - L.adjoint w = a := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (congrArg (fun z : H ↦ z - L.adjoint w) hub).symm
      rw [hshift_indicator]
      simp [hu_sub, ERealFunction.indicator_apply, ha, hw]
    have hvalue :
        (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u =
          sInf (Set.range (shiftedCompositeDualObjective (ι[C]) (ι[D]) L u)) := by
      calc
        (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u =
            shiftedCompositeDualObjective (ι[C]) (ι[D]) L u v := hvEq
        _ = sInf (Set.range (shiftedCompositeDualObjective (ι[C]) (ι[D]) L u)) := by
            exact (mem_argmin_iff_eq_sInf.mp hvArg)
    have hnonneg :
        (0 : EReal) ≤ (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u := by
      rw [hvEq, hshift_indicator]
      by_cases hvD : v ∈ Dᵒ⊖ <;> by_cases hvC : u - L.adjoint v ∈ Cᵒ⊖ <;>
        simp [ERealFunction.indicator_apply, hvD, hvC]
    have hcomp_zero :
        (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u = 0 := by
      refine le_antisymm ?_ hnonneg
      calc
        (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u =
            sInf (Set.range (shiftedCompositeDualObjective (ι[C]) (ι[D]) L u)) := hvalue
        _ ≤ shiftedCompositeDualObjective (ι[C]) (ι[D]) L u w := by
            exact sInf_le ⟨w, rfl⟩
        _ = 0 := hcandidate
    calc
      ((ι[(C ∩ L ⁻¹' D)ᵒ⊖]).asEReal) u =
          (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u := hconj_inter
      _ = 0 := hcomp_zero
      _ = (ι[Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)]).asEReal u := by
          simp [ERealFunction.indicator_apply, hu]
  · have htop_every :
        ∀ w : K, shiftedCompositeDualObjective (ι[C]) (ι[D]) L u w = ⊤ := by
      intro w
      rw [hshift_indicator]
      by_cases hw : w ∈ Dᵒ⊖
      · have hnotC : u - L.adjoint w ∉ Cᵒ⊖ := by
          intro hmem
          exact hu <|
            Set.mem_add.mpr ⟨u - L.adjoint w, hmem, L.adjoint w, ⟨w, hw, rfl⟩, by abel⟩
        simp [ERealFunction.indicator_apply, hnotC, hw]
      · by_cases hCmem : u - L.adjoint w ∈ Cᵒ⊖
        · simp [ERealFunction.indicator_apply, hw, hCmem]
        · simp [ERealFunction.indicator_apply, hw, hCmem]
    have hcomp_top :
        (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u = ⊤ := by
      calc
        (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u =
            shiftedCompositeDualObjective (ι[C]) (ι[D]) L u v := hvEq
        _ = ⊤ := htop_every v
    calc
      ((ι[(C ∩ L ⁻¹' D)ᵒ⊖]).asEReal) u =
          (ERealFunction.compositePrimalObjective (ι[C]) (ι[D]) L)∗ u := hconj_inter
      _ = ⊤ := hcomp_top
      _ = (ι[Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)]).asEReal u := by
          simp [ERealFunction.indicator_apply, hu]

-- Proof sketch: use Proposition 6.19 to turn the closed-linear-subspace hypothesis on
-- `D - L '' C` into `0 ∈ sri (D - L '' C)`. Apply Example 13.3(ii) and Theorem 15.27 to the
-- indicator functions of `C` and `D`, then rewrite the resulting exact infimal-convolution formula
-- as the displayed equality of polar cones.
/-- Corollary 15.31: if `D - L '' C` is a closed linear subspace, then the closure in part `(1)`
is unnecessary. -/
theorem polarCone_inter_preimage_eq_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    (C ∩ L ⁻¹' D)ᵒ⊖ = Cᵒ⊖ + L.adjoint '' (Dᵒ⊖) := by
  -- Convert the pointwise indicator identity back to equality of the underlying sets.
  ext u
  have hpoint :=
    indicator_polar_inter_eq_indicator_polar_sum_of_closed_subspace_sub_image
      C D L hC_nonempty hC_closed hC_convex hC_cone
      hD_nonempty hD_closed hD_convex hD_cone hsubspace hsubspace_closed u
  constructor
  · intro hu
    by_contra hu'
    simp [ERealFunction.indicator_apply, hu, hu'] at hpoint
  · intro hu
    by_contra hu'
    simp [ERealFunction.indicator_apply, hu, hu'] at hpoint

-- Proof sketch: both polar cones contain `0`, and the adjoint sends `0` to `0`, so the pointwise
-- sum also contains `0`.
/-- Part (3) of Corollary 15.31: under the closed-linear-subspace hypothesis, the sum
`Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is nonempty. -/
theorem nonempty_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)).Nonempty := by
  -- Rewrite to the polar cone of `C ∩ L ⁻¹' D`, whose nonemptiness is automatic.
  rw [← polarCone_inter_preimage_eq_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    C D L hC_nonempty hC_closed hC_convex hC_cone
    hD_nonempty hD_closed hD_convex hD_cone hsubspace hsubspace_closed]
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_nonempty (C ∩ L ⁻¹' D)

-- Proof sketch: combine clause `(2)` with Proposition 6.24(ii), which says that every polar cone
-- is closed.
/-- Part (4) of Corollary 15.31: under the closed-linear-subspace hypothesis, the sum
`Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is closed. -/
theorem isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    IsClosed (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := by
  -- Rewrite to the polar cone of `C ∩ L ⁻¹' D` and use the Chapter 6 closedness theorem.
  rw [← polarCone_inter_preimage_eq_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    C D L hC_nonempty hC_closed hC_convex hC_cone
    hD_nonempty hD_closed hD_convex hD_cone hsubspace hsubspace_closed]
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_isClosed (C ∩ L ⁻¹' D)

-- Proof sketch: Proposition 6.24(ii) makes each polar cone convex, continuous linear maps preserve
-- convexity, and pointwise sums of convex sets are convex.
/-- Part (5) of Corollary 15.31: under the closed-linear-subspace hypothesis, the sum
`Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is convex. -/
theorem convex_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    Convex ℝ (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := by
  -- Rewrite to the polar cone of `C ∩ L ⁻¹' D` and use the Chapter 6 convexity theorem.
  rw [← polarCone_inter_preimage_eq_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    C D L hC_nonempty hC_closed hC_convex hC_cone
    hD_nonempty hD_closed hD_convex hD_cone hsubspace hsubspace_closed]
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_convex (C ∩ L ⁻¹' D)

-- Proof sketch: Proposition 6.24(ii) makes each polar cone a cone, the adjoint image of a cone is
-- again a cone, and the pointwise sum of two cones is a cone.
/-- Part (6) of Corollary 15.31: under the closed-linear-subspace hypothesis, the sum
`Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is a cone. -/
theorem isCone_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    IsCone (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := by
  -- Rewrite to the polar cone of `C ∩ L ⁻¹' D` and use the Chapter 6 cone theorem.
  rw [← polarCone_inter_preimage_eq_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    C D L hC_nonempty hC_closed hC_convex hC_cone
    hD_nonempty hD_closed hD_convex hD_cone hsubspace hsubspace_closed]
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_isCone (C ∩ L ⁻¹' D)

end

end Set
