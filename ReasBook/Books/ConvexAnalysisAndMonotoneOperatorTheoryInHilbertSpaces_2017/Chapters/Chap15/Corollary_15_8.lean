import Mathlib
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap15.Proposition_15_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

open InfimalConvolutionRegularity

section AttouchBrezisTheorem

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: evaluating the product-space conjugate of a lifted function at a
zero second dual coordinate removes the second pairing term. -/
theorem conjugate_apply_prod_zeroSecond_local
    (F : (H × K) × K → EReal) (u : H × K) :
    F∗ (u, (0 : K)) =
      ⨆ p : (H × K) × K, (((⟪p.1, u⟫_ℝ : ℝ) : EReal) - F p) := by
  -- Expand the lifted conjugate and cancel the zero second-coordinate pairing.
  rw [conjugate_apply]
  congr with p
  congr 1
  change (((⟪p.1, u⟫_ℝ + ⟪p.2, (0 : K)⟫_ℝ : ℝ) : EReal)) =
    (((⟪p.1, u⟫_ℝ : ℝ) : EReal))
  simp

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: each second-variable slice of a lifted function is bounded above by
subtracting the fiber infimum. -/
theorem iSup_second_slice_le_pairing_sub_partialInf_local
    (F : (H × K) × K → EReal) (u x : H × K) :
    (⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (x, y))) ≤
      (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, F (x, y)) := by
  -- The map `t ↦ a - t` is antitone, so it sends the fiber infimum to an upper bound.
  let a : EReal := ((⟪x, u⟫_ℝ : ℝ) : EReal)
  have h_antitone : Antitone (fun t : EReal ↦ a - t) := by
    intro s t hst
    exact EReal.sub_le_sub le_rfl hst
  simpa [a] using (Antitone.le_map_iInf h_antitone (s := fun y : K ↦ F (x, y)))

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: subtracting the fiber infimum of a lifted function is bounded above
by the supremum of the corresponding second-variable slices. -/
theorem pairing_sub_partialInf_le_iSup_second_slice_local
    (F : (H × K) × K → EReal) (u x : H × K) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, F (x, y)) ≤
      (⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (x, y))) := by
  -- Rewrite the infimum as an `sInf`, then use a near-minimizer in the fiber.
  let a : EReal := ((⟪x, u⟫_ℝ : ℝ) : EReal)
  let s : Set EReal := Set.range (fun y : K ↦ F (x, y))
  have hs : (⨅ y : K, F (x, y)) = sInf s := by
    simpa [s] using (sInf_range (f := fun y : K ↦ F (x, y))).symm
  rw [hs]
  refine le_of_forall_lt fun c hc ↦ ?_
  have hsInf_ne_top : sInf s ≠ ⊤ := by
    intro hsInf_top
    have : ¬ c < (⊥ : EReal) := by simp
    simp [hsInf_top] at hc
  have hc_ne_top : c ≠ ⊤ := hc.ne_top
  have hc_add : c + sInf s < a := by
    exact
      (EReal.lt_sub_iff_add_lt (b := sInf s) (c := c) (Or.inr hc_ne_top) (Or.inl hsInf_ne_top)).1
        hc
  have hs_lt : sInf s < a - c := by
    exact
      (EReal.lt_sub_iff_add_lt (b := c) (c := sInf s) (Or.inr hsInf_ne_top) (Or.inl hc_ne_top)).2
        (by simpa [add_comm] using hc_add)
  obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hs_lt
  rcases hzmem with ⟨y, rfl⟩
  have hlt : c < a - F (x, y) := by
    have hz_add : F (x, y) + c < a := by
      exact EReal.add_lt_of_lt_sub hzlt
    exact
      (EReal.lt_sub_iff_add_lt (b := F (x, y)) (c := c) (Or.inr hc_ne_top) (Or.inl hzlt.ne_top)).2
        (by simpa [add_comm] using hz_add)
  exact lt_of_lt_of_le hlt (le_iSup (fun y : K ↦ a - F (x, y)) y)

/-
  `CompleteSpace` is not used in this local order-theoretic identity.
-/
omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: fiberwise, subtracting the second-variable infimum of a lifted
function equals the supremum of the corresponding second-variable slices. -/
theorem pairing_sub_partialInf_eq_iSup_second_slice_local
    (F : (H × K) × K → EReal) (u x : H × K) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, F (x, y)) =
      (⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (x, y))) := by
  -- Combine the antitone upper bound with the near-minimizer reverse inequality.
  refine le_antisymm
    (pairing_sub_partialInf_le_iSup_second_slice_local F u x)
    (iSup_second_slice_le_pairing_sub_partialInf_local F u x)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Corollary 15 8: specializing the first-projection infimal postcomposition on
`((H × K) × K)` recovers the partial infimum over the final `K` coordinate. -/
theorem infimalPostcomposition_fst_apply_local
    (F : (H × K) × K → EReal) (x : H × K) :
    (Prod.fst ▷ F) x = ⨅ y : K, F (x, y) := by
  -- Rewrite the first-projection fiber as the range of the last-coordinate parametrization.
  change sInf (F '' (Prod.fst ⁻¹' ({x} : Set (H × K))) ) = _
  rw [show F '' (Prod.fst ⁻¹' ({x} : Set (H × K))) = Set.range (fun y : K ↦ F (x, y)) by
    ext z
    constructor
    · rintro ⟨⟨a, b⟩, ha, rfl⟩
      refine ⟨b, ?_⟩
      simp at ha
      simp [ha]
    · rintro ⟨y, rfl⟩
      exact ⟨(x, y), by simp, rfl⟩]
  exact sInf_range

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: the conjugate of a first-projection infimal postcomposition equals
the lifted conjugate evaluated on the zero second dual slice. -/
theorem conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_local
    (F : (H × K) × K → EReal) :
    (Prod.fst ▷ F)∗ =
      fun u : H × K ↦ F∗ (u, (0 : K)) := by
  ext u
  -- Expand both conjugates and rewrite the first-projection infimal postcomposition fiberwise.
  rw [conjugate_apply]
  simp_rw [infimalPostcomposition_fst_apply_local]
  rw [conjugate_apply_prod_zeroSecond_local]
  -- Replace each fixed-`x` slice by the supremum over the last coordinate, then reindex by pairs.
  calc
    (⨆ x : H × K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - ⨅ y : K, F (x, y))) =
        (⨆ x : H × K, ⨆ y : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (x, y))) := by
          refine iSup_congr fun x ↦ ?_
          exact pairing_sub_partialInf_eq_iSup_second_slice_local F u x
    _ = ⨆ p : (H × K) × K, (((⟪p.1, u⟫_ℝ : ℝ) : EReal) - F p) := by
          rw [iSup_prod']

/- Source/core/bridge triage:
- `source-facing`: this corollary is the textbook second-variable fiberwise infimal-convolution
  formula on the Hilbert product `H × K`, written with ordinary pair syntax.
- `core/canonical`: the owner abstractions are the Chapter 12 infimal postcomposition and
  infimal-convolution operators together with the Chapter 13 raw-product `ℓ²` Hilbert structure
  and the Chapter 15 Attouch--Brézis conjugation theorem.
- `bridge/view`: `WithLp 2 (H × K)` is only an internal model for the `ℓ²` product geometry, so
  the public statement should stay on raw pairs and let the local instances supply that geometry. -/

/-- Helper for Corollary 15 8: precomposing a `Γ₀` function with a continuous linear map preserves
`Γ₀` membership when the range meets the effective domain. -/
theorem comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
    {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (g : F → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(F))
    (L : E →L[ℝ] F)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    g ∘ L ∈ Γ₀(E) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · simpa using hg.1.comp L.continuous
  · refine
      ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : L x ∈ effectiveDomain g := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hx
    have hy' : L y ∈ effectiveDomain g := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hg.2.ineq hx' hy' hα hα_lt_one

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Corollary 15 8: the source-facing fiberwise infimal convolution is the canonical
first-projection infimal postcomposition of the lifted separable sum on `((H × K) × K)`. -/
theorem secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted
    (φ ψ : H × K → Set.Ioi (⊥ : EReal)) :
    (fun p : H × K ↦
      ((fun z : K ↦ (φ (p.1, z) : EReal)) □
        fun z ↦ (ψ (p.1, z) : EReal)) p.2) =
      Prod.fst ▷
        (fun q : ((H × K) × K) ↦
          (φ (q.1.1, q.2) : EReal) + (ψ (q.1.1, q.1.2 - q.2) : EReal)) := by
  funext p
  -- Rewrite the lifted partial infimum and identify the remaining fiber formula with the
  -- textbook second-variable infimal convolution at `(p.1, p.2)`.
  rw [infimalPostcomposition_fst_apply_local]
  simp [infimalConvolution_apply]

omit [InnerProductSpace ℝ H] [CompleteSpace H] [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Corollary 15 8: the lifted domain difference is exactly the first-coordinate
difference set together with two free `K` coordinates. -/
theorem lifted_difference_eq_firstProjection_product_univ
    (φ ψ : H × K → Set.Ioi (⊥ : EReal)) :
    effectiveDomain
        (φ ∘ fun q : ((H × K) × K) ↦ (q.1.1, q.2)) -
      effectiveDomain
        (ψ ∘ fun q : ((H × K) × K) ↦ (q.1.1, q.1.2 - q.2)) =
        ((((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
          (Set.univ : Set K)) : Set (H × K)) ×ˢ (Set.univ : Set K)) := by
  ext q
  constructor
  · intro hq
    rcases Set.mem_sub.mp hq with ⟨p, hp, r, hr, hpr⟩
    have hp_dom : (p.1.1, p.2) ∈ effectiveDomain φ := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hp
    have hr_dom : (r.1.1, r.1.2 - r.2) ∈ effectiveDomain ψ := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hr
    have hfirst : p.1.1 - r.1.1 = q.1.1 := by
      simpa using congrArg (fun s : ((H × K) × K) ↦ s.1.1) hpr
    -- Project the lifted difference to the first coordinate; the other two coordinates are free.
    refine ⟨?_, by simp⟩
    refine ⟨?_, by simp⟩
    refine ⟨(p.1.1, p.2) - (r.1.1, r.1.2 - r.2), ?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨(p.1.1, p.2), hp_dom, (r.1.1, r.1.2 - r.2), hr_dom, rfl⟩
    · simp [hfirst]
  · intro hq
    have hfirst : q.1.1 ∈ Prod.fst '' (effectiveDomain φ - effectiveDomain ψ) := by
      simpa using hq
    rcases hfirst with ⟨d, hd, hdq⟩
    rcases Set.mem_sub.mp hd with ⟨u, hu, v, hv, huv⟩
    let p : ((H × K) × K) := ((u.1, q.1.2 + v.2 + u.2 - q.2), u.2)
    let r : ((H × K) × K) := ((v.1, v.2 + u.2 - q.2), u.2 - q.2)
    have hp_dom :
        p ∈ effectiveDomain (φ ∘ fun q : ((H × K) × K) ↦ (q.1.1, q.2)) := by
      simpa [p, Function.comp, mem_effectiveDomain_iff] using hu
    have hr_dom :
        r ∈ effectiveDomain (ψ ∘ fun q : ((H × K) × K) ↦ (q.1.1, q.1.2 - q.2)) := by
      simpa [r, Function.comp, mem_effectiveDomain_iff] using hv
    have hcoord : u.1 - v.1 = q.1.1 := by
      calc
        u.1 - v.1 = Prod.fst d := by
          simpa using congrArg Prod.fst huv
        _ = q.1.1 := hdq
    -- Use the explicit witness reconstruction from the source proof to realize any free pair
    -- of `K`-coordinates inside the lifted difference set.
    refine Set.mem_sub.mpr ⟨p, hp_dom, r, hr_dom, ?_⟩
    ext <;> simp [p, r, hcoord]

/-- Helper for Corollary 15 8: the first lifted linear map keeps the first coordinate and moves
the free variable into the second coordinate. -/
abbrev firstLastPullbackMap : ((H × K) × K) →L[ℝ] (H × K) :=
  (((ContinuousLinearMap.fst ℝ H K).comp (ContinuousLinearMap.fst ℝ (H × K) K)).prod
    (ContinuousLinearMap.snd ℝ (H × K) K))

/-- Helper for Corollary 15 8: the second lifted linear map keeps the first coordinate and
records the difference `y - z` in the second coordinate. -/
abbrev firstDifferencePullbackMap : ((H × K) × K) →L[ℝ] (H × K) :=
  (((ContinuousLinearMap.fst ℝ H K).comp (ContinuousLinearMap.fst ℝ (H × K) K)).prod
    ((ContinuousLinearMap.snd ℝ H K).comp (ContinuousLinearMap.fst ℝ (H × K) K) -
      ContinuousLinearMap.snd ℝ (H × K) K))

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: evaluating `firstLastPullbackMap` recovers `(x, z)`. -/
@[simp] theorem firstLastPullbackMap_apply (q : ((H × K) × K)) :
    firstLastPullbackMap q = (q.1.1, q.2) := by
  rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: evaluating `firstDifferencePullbackMap` recovers `(x, y - z)`. -/
@[simp] theorem firstDifferencePullbackMap_apply (q : ((H × K) × K)) :
    firstDifferencePullbackMap q = (q.1.1, q.1.2 - q.2) := by
  rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: the first lifted pullback map is surjective. -/
theorem range_firstLastPullbackMap :
    Set.range (firstLastPullbackMap (H := H) (K := K)) = Set.univ := by
  ext q
  constructor
  · intro _
    simp
  · intro _
    refine ⟨((q.1, 0), q.2), ?_⟩
    ext <;> rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: the second lifted pullback map is surjective. -/
theorem range_firstDifferencePullbackMap :
    Set.range (firstDifferencePullbackMap (H := H) (K := K)) = Set.univ := by
  ext q
  constructor
  · intro _
    simp
  · intro _
    refine ⟨((q.1, q.2), 0), ?_⟩
    ext <;> simp [firstDifferencePullbackMap]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: pulling back `φ` along the first-last projection preserves
`Γ₀`. -/
theorem firstLastPullback_mem_gammaZero
    (φ : H × K → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H × K)) :
    φ ∘ firstLastPullbackMap ∈ Γ₀(((H × K) × K)) := by
  refine comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
    φ hφ firstLastPullbackMap ?_
  rw [range_firstLastPullbackMap, Set.univ_inter]
  exact hφ.2.nonempty

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: pulling back `ψ` along the first-difference projection preserves
`Γ₀`. -/
theorem firstDifferencePullback_mem_gammaZero
    (ψ : H × K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(H × K)) :
    ψ ∘ firstDifferencePullbackMap ∈ Γ₀(((H × K) × K)) := by
  refine comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
    ψ hψ firstDifferencePullbackMap ?_
  rw [range_firstDifferencePullbackMap, Set.univ_inter]
  exact hψ.2.nonempty

/-- Helper for Corollary 15 8: taking the product with `univ` preserves strong relative interior
at the origin. -/
theorem zero_mem_sri_prod_univ_of_zero_mem_sri
    {S : Set H} (hS_convex : Convex ℝ S) (hsri : (0 : H) ∈ sri S) :
    (0 : H × K) ∈ sri (S ×ˢ (Set.univ : Set K)) := by
  have hzeroS : (0 : H) ∈ S := (Set.mem_strongRelativeInterior_iff.mp hsri).1
  have hS_nonempty : S.Nonempty := ⟨0, hzeroS⟩
  have hconeS :
      cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
    exact
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        hS_nonempty hS_convex).1 hsri
  have hcone_prod :
      cone (S ×ˢ (Set.univ : Set K)) = cone S ×ˢ (Set.univ : Set K) := by
    rw [cone_eq_toCone_of_convex (hS_convex.prod convex_univ)]
    ext p
    constructor
    · intro hp
      rcases (Convex.mem_toCone (hS_convex.prod convex_univ)).1 hp with ⟨a, ha, q, hq, rfl⟩
      rcases hq with ⟨hqS, -⟩
      refine ⟨?_, by simp⟩
      rw [cone_eq_toCone_of_convex hS_convex]
      exact (Convex.mem_toCone hS_convex).2 ⟨a, ha, q.1, hqS, rfl⟩
    · rintro ⟨hp, -⟩
      rw [cone_eq_toCone_of_convex hS_convex] at hp
      rcases (Convex.mem_toCone hS_convex).1 hp with ⟨a, ha, x, hx, hax⟩
      refine (Convex.mem_toCone (hS_convex.prod convex_univ)).2 ?_
      refine ⟨a, ha, (x, a⁻¹ • p.2), ?_, ?_⟩
      · exact ⟨hx, by simp⟩
      · ext <;> simp [hax, ha.ne', smul_smul]
  have hspan_le :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) ≤
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) := by
    simpa [Submodule.span_univ] using
      (Submodule.span_prod_le (R := ℝ) S (Set.univ : Set K))
  have hspan_ge :
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) ≤
        Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) := by
    have hsubset :
        LinearMap.inl ℝ H K '' S ∪ LinearMap.inr ℝ H K '' (Set.univ : Set K) ⊆
          S ×ˢ (Set.univ : Set K) := by
      intro p hp
      rcases hp with hp | hp
      · rcases hp with ⟨x, hx, rfl⟩
        exact ⟨hx, by simp⟩
      · rcases hp with ⟨y, -, rfl⟩
        exact ⟨hzeroS, by simp⟩
    calc
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) =
          Submodule.span ℝ
            (LinearMap.inl ℝ H K '' S ∪ LinearMap.inr ℝ H K '' (Set.univ : Set K)) := by
              symm
              simpa [Submodule.span_univ] using
                (LinearMap.span_inl_union_inr (R := ℝ) (M := H) (M₂ := K)
                  (s := S) (t := (Set.univ : Set K)))
      _ ≤ Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) := Submodule.span_mono hsubset
  have hspan_eq :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) =
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) := by
    exact le_antisymm hspan_le hspan_ge
  have hclosure_prod :
      ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure : Set (H × K)) =
        (((Submodule.span ℝ S).topologicalClosure : Set H) ×ˢ (Set.univ : Set K)) := by
    rw [hspan_eq]
    change closure (((Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) : Set (H × K))) =
      (((Submodule.span ℝ S).topologicalClosure : Set H) ×ˢ (Set.univ : Set K))
    have hprod_set :
        (((Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) : Set (H × K))) =
          ((Submodule.span ℝ S : Set H) ×ˢ (Set.univ : Set K)) := by
      rfl
    rw [hprod_set]
    rw [closure_prod_eq]
    simp
  have hcone_eq :
      cone (S ×ˢ (Set.univ : Set K)) =
        ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure : Set (H × K)) := by
    calc
      cone (S ×ˢ (Set.univ : Set K)) = cone S ×ˢ (Set.univ : Set K) := hcone_prod
      _ = (((Submodule.span ℝ S).topologicalClosure : Set H) ×ˢ (Set.univ : Set K)) := by
            rw [hconeS]
      _ = ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure : Set (H × K)) := by
            symm
            exact hclosure_prod
  exact
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      ⟨(0 : H × K), by simp [hzeroS]⟩
      (hS_convex.prod convex_univ)).2 hcone_eq

/-- Helper for Corollary 15 8: the Attouch--Brézis regularity hypothesis lifts from the first
coordinate difference set to the pulled-back domain difference on `((H × K) × K)`. -/
theorem zero_mem_sri_lifted_difference_of_zero_mem_sri_firstProjection_difference
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))) :
    (0 : ((H × K) × K)) ∈
      sri
        (effectiveDomain
            (φ ∘ firstLastPullbackMap) -
          effectiveDomain
            (ψ ∘ firstDifferencePullbackMap)) := by
  -- Rewrite the pulled-back domain difference as two free `K` coordinates over the first
  -- projection difference, then lift the original `sri` witness through each product.
  have hproj_convex :
      Convex ℝ (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) := by
    have hdiff_convex :
        Convex ℝ (effectiveDomain φ - effectiveDomain ψ) :=
      hφ.2.convex_effectiveDomain.sub hψ.2.convex_effectiveDomain
    simpa using hdiff_convex.linear_image (ContinuousLinearMap.fst ℝ H K).toLinearMap
  have hsri_prod :
      (0 : H × K) ∈
        sri ((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
          (Set.univ : Set K)) :=
    zero_mem_sri_prod_univ_of_zero_mem_sri (K := K) hproj_convex hsri
  have hsri_lifted :
      (0 : ((H × K) × K)) ∈
        sri ((((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
            (Set.univ : Set K)) : Set (H × K)) ×ˢ (Set.univ : Set K)) :=
    zero_mem_sri_prod_univ_of_zero_mem_sri
      (H := H × K) (K := K)
      (S := ((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
        (Set.univ : Set K)))
      (hproj_convex.prod convex_univ) hsri_prod
  have hset :
      effectiveDomain (φ ∘ firstLastPullbackMap) -
          effectiveDomain (ψ ∘ firstDifferencePullbackMap) =
        ((((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
            (Set.univ : Set K)) : Set (H × K)) ×ˢ (Set.univ : Set K)) := by
    simpa [Function.comp, firstLastPullbackMap_apply, firstDifferencePullbackMap_apply] using
      lifted_difference_eq_firstProjection_product_univ (φ := φ) (ψ := ψ)
  rw [hset]
  exact hsri_lifted

omit [CompleteSpace K] in
/-- Helper for Corollary 15 8: along a nonzero ray, the middle-coordinate pairing term dominates
any fixed finite constant and sends the supremum to `⊤`. -/
theorem iSup_pairing_middle_eq_top_of_ne_zero
    (b : K) (hb : b ≠ 0) (c : EReal)
    (hc_top : c ≠ ⊤) (hc_bot : c ≠ ⊥) :
    (⨆ y : K, (((⟪y, b⟫_ℝ : ℝ) : EReal) + c)) = ⊤ := by
  have hc : c = (((c.toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal hc_top hc_bot).symm
  have hnorm_sq_pos : 0 < ‖b‖ ^ 2 := by
    positivity
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  let t : ℝ := (M - c.toReal + 1) / (‖b‖ ^ 2)
  have hinner :
      ⟪t • b, b⟫_ℝ + c.toReal = M + 1 := by
    dsimp [t]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [hnorm_sq_pos.ne']
    ring
  have hlt_real : M < ⟪t • b, b⟫_ℝ + c.toReal := by
    calc
      M < M + 1 := by linarith
      _ = ⟪t • b, b⟫_ℝ + c.toReal := hinner.symm
  have hlt :
      ((M : ℝ) : EReal) <
        (((⟪t • b, b⟫_ℝ : ℝ) : EReal) + c) := by
    rw [hc, ← EReal.coe_add]
    exact_mod_cast hlt_real
  exact lt_of_lt_of_le hlt <|
    le_iSup (fun y : K ↦ (((⟪y, b⟫_ℝ : ℝ) : EReal) + c)) (t • b)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: on the literal zero middle slice, the first-last pullback conjugate
collapses to the ordinary conjugate of `φ`. -/
theorem conjugate_firstLastPullback_apply_zeroSlice
    (φ : H × K → Set.Ioi (⊥ : EReal)) (u : H) (v : K) :
    ((φ ∘ firstLastPullbackMap).asEReal∗) (((u, (0 : K)), v)) = φ.asEReal∗ (u, v) := by
  rw [conjugate_apply]
  calc
    (⨆ p : ((H × K) × K),
      (((⟪p, (((u, (0 : K)), v))⟫_ℝ : ℝ) : EReal) -
        ((φ ∘ firstLastPullbackMap) p : EReal))) =
        (⨆ x : H, ⨆ _y : K, ⨆ z : K,
          (((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal))) := by
          have hpair :
              (⨆ p : ((H × K) × K),
                (((⟪p, (((u, (0 : K)), v))⟫_ℝ : ℝ) : EReal) -
                  ((φ ∘ firstLastPullbackMap) p : EReal))) =
                (⨆ p : ((H × K) × K),
                  (((⟪p.1.1, u⟫_ℝ + ⟪p.2, v⟫_ℝ : ℝ) : EReal) - (φ (p.1.1, p.2) : EReal))) := by
                refine iSup_congr fun p ↦ ?_
                change (((⟪p.1, (u, (0 : K))⟫_ℝ + ⟪p.2, v⟫_ℝ : ℝ) : EReal) -
                    (φ (p.1.1, p.2) : EReal)) =
                  (((⟪p.1.1, u⟫_ℝ + ⟪p.2, v⟫_ℝ : ℝ) : EReal) - (φ (p.1.1, p.2) : EReal))
                have hinner :
                    (⟪p.1, (u, (0 : K))⟫_ℝ : ℝ) = ⟪p.1.1, u⟫_ℝ := by
                  calc
                    (⟪p.1, (u, (0 : K))⟫_ℝ : ℝ) =
                        ⟪p.1.1, u⟫_ℝ + ⟪p.1.2, (0 : K)⟫_ℝ := by
                          rfl
                    _ = ⟪p.1.1, u⟫_ℝ := by
                          simp
                exact congrArg
                  (fun t : ℝ ↦ ((t : EReal) + ((⟪p.2, v⟫_ℝ : ℝ) : EReal)) -
                    (φ (p.1.1, p.2) : EReal))
                  hinner
          have hsplit₁ :
              (⨆ p : ((H × K) × K),
                (((⟪p.1.1, u⟫_ℝ + ⟪p.2, v⟫_ℝ : ℝ) : EReal) - (φ (p.1.1, p.2) : EReal))) =
                (⨆ xy : H × K, ⨆ z : K,
                  (((⟪xy.1, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (xy.1, z) : EReal))) := by
                simpa using
                  (iSup_prod' (f := fun xy : H × K => fun z : K =>
                    (((⟪xy.1, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (xy.1, z) : EReal)))).symm
          have hsplit₂ :
              (⨆ x : H, ⨆ y : K, ⨆ z : K,
                (((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal))) =
                (⨆ xy : H × K, ⨆ z : K,
                  (((⟪xy.1, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (xy.1, z) : EReal))) := by
                simpa using
                  (iSup_prod' (f := fun x : H => fun y : K =>
                    ⨆ z : K, (((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal))))
          exact hpair.trans (hsplit₁.trans hsplit₂.symm)
    _ = (⨆ x : H, ⨆ z : K,
          (((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal))) := by
          refine iSup_congr fun x ↦ ?_
          simp
    _ = φ.asEReal∗ (u, v) := by
          rw [conjugate_apply]
          have hsplit :
              (⨆ x : H, ⨆ z : K,
                (((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal))) =
                (⨆ p : H × K, (((⟪p, (u, v)⟫_ℝ : ℝ) : EReal) - (φ p : EReal))) := by
                simpa using
                  (iSup_prod' (f := fun x : H => fun z : K =>
                    (((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal))))
          exact hsplit

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: off the zero middle slice, the first-last pullback conjugate is
forced to `⊤` by the free middle coordinate. -/
theorem conjugate_firstLastPullback_apply_top_of_ne_zero
    (φ : H × K → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H × K))
    (u : H) (b v : K) (hb : b ≠ 0) :
    ((φ ∘ firstLastPullbackMap).asEReal∗) (((u, b), v)) = ⊤ := by
  rcases hφ.2.nonempty with ⟨p, hp⟩
  rcases p with ⟨x, z⟩
  have hφxz_top : (φ (x, z) : EReal) ≠ ⊤ := by
    exact (mem_effectiveDomain_iff.mp hp).ne
  have hφxz_bot : (φ (x, z) : EReal) ≠ ⊥ := by
    exact ne_of_gt (φ (x, z)).2
  let c : EReal := ((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ - (φ (x, z) : EReal).toReal : ℝ) : EReal)
  have hconst :
      (((⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal)) = c := by
    -- Rewrite the fixed source value as a finite real constant before applying the ray lemma.
    rw [show (φ (x, z) : EReal) = (((φ (x, z) : EReal).toReal : ℝ) : EReal) by
      exact (EReal.coe_toReal hφxz_top hφxz_bot).symm]
    simp [c, sub_eq_add_neg, add_assoc]
  have hsup :
      (⨆ y : K, (((⟪y, b⟫_ℝ : ℝ) : EReal) + c)) = ⊤ :=
    iSup_pairing_middle_eq_top_of_ne_zero
      b
      hb
      c
      (by
        simpa [c] using
          (EReal.coe_ne_top
            (⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ - (φ (x, z) : EReal).toReal)))
      (by
        simpa [c] using
          (EReal.coe_ne_bot
            (⟪x, u⟫_ℝ + ⟪z, v⟫_ℝ - (φ (x, z) : EReal).toReal)))
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro M
  have hM : M < ⨆ y : K, (((⟪y, b⟫_ℝ : ℝ) : EReal) + c) := by
    simp [hsup]
  rcases lt_iSup_iff.mp hM with ⟨y, hy⟩
  refine lt_of_lt_of_le hy ?_
  refine le_iSup_of_le (((x, y), z)) ?_
  -- Keep the source witness fixed and move only along the free middle coordinate.
  suffices
      (((⟪y, b⟫_ℝ : ℝ) : EReal) + c) ≤
        (((⟪x, u⟫_ℝ + ⟪y, b⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal)) by
    simpa only [Function.asEReal_apply, Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
      using this
  have hEq :
      (((⟪y, b⟫_ℝ : ℝ) : EReal) + c) =
        (((⟪x, u⟫_ℝ + ⟪y, b⟫_ℝ + ⟪z, v⟫_ℝ : ℝ) : EReal) - (φ (x, z) : EReal)) := by
    rw [show (φ (x, z) : EReal) = (((φ (x, z) : EReal).toReal : ℝ) : EReal) by
      exact (EReal.coe_toReal hφxz_top hφxz_bot).symm]
    simp [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  exact hEq.le

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: the conjugate of the first-last pullback is finite exactly on the
zero middle-coordinate slice. -/
theorem conjugate_firstLastPullback_apply
    [DecidableEq K]
    (φ : H × K → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H × K))
    (u : H) (b v : K) :
    ((φ ∘ firstLastPullbackMap).asEReal∗) (((u, b), v)) =
      if b = 0 then φ.asEReal∗ (u, v) else ⊤ := by
  by_cases hb : b = 0
  · -- On the zero slice, the lifted conjugate just sees the source pair `(u, v)`.
    subst b
    simpa using conjugate_firstLastPullback_apply_zeroSlice (φ := φ) u v
  · -- Off the zero slice, the free middle coordinate drives the conjugate to `⊤`.
    simpa [hb] using
      conjugate_firstLastPullback_apply_top_of_ne_zero (φ := φ) hφ u b v hb

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: on the branch `c = -b`, the first-difference pullback conjugate
collapses to the ordinary conjugate of `ψ` at `(u, b)`. -/
theorem conjugate_firstDifferencePullback_apply_negSlice
    (ψ : H × K → Set.Ioi (⊥ : EReal)) (u : H) (b : K) :
    ((ψ ∘ firstDifferencePullbackMap).asEReal∗) (((u, b), -b)) = ψ.asEReal∗ (u, b) := by
  rw [conjugate_apply, conjugate_apply]
  calc
    (⨆ p : ((H × K) × K),
      (((⟪p, (((u, b), -b))⟫_ℝ : ℝ) : EReal) -
        ((ψ ∘ firstDifferencePullbackMap) p : EReal))) =
        (⨆ x : H, ⨆ y : K, ⨆ z : K,
          (((⟪x, u⟫_ℝ + ⟪y - z, b⟫_ℝ : ℝ) : EReal) - (ψ (x, y - z) : EReal))) := by
            have hpair :
                (⨆ p : ((H × K) × K),
                  (((⟪p, (((u, b), -b))⟫_ℝ : ℝ) : EReal) -
                    ((ψ ∘ firstDifferencePullbackMap) p : EReal))) =
                  (⨆ p : ((H × K) × K),
                    (((⟪p.1.1, u⟫_ℝ + ⟪p.1.2 - p.2, b⟫_ℝ : ℝ) : EReal) -
                      (ψ (p.1.1, p.1.2 - p.2) : EReal))) := by
                  refine iSup_congr fun p ↦ ?_
                  change (((⟪p.1, (u, b)⟫_ℝ + ⟪p.2, -b⟫_ℝ : ℝ) : EReal) -
                      (ψ (p.1.1, p.1.2 - p.2) : EReal)) =
                    (((⟪p.1.1, u⟫_ℝ + ⟪p.1.2 - p.2, b⟫_ℝ : ℝ) : EReal) -
                      (ψ (p.1.1, p.1.2 - p.2) : EReal))
                  have hinner :
                      (⟪p.1, (u, b)⟫_ℝ + ⟪p.2, -b⟫_ℝ : ℝ) =
                        ⟪p.1.1, u⟫_ℝ + ⟪p.1.2 - p.2, b⟫_ℝ := by
                    rw [show ⟪p.1, (u, b)⟫_ℝ = ⟪p.1.1, u⟫_ℝ + ⟪p.1.2, b⟫_ℝ by rfl]
                    rw [inner_sub_left, inner_neg_right]
                    ring
                  exact congrArg
                    (fun t : ℝ ↦ ((t : EReal) - (ψ (p.1.1, p.1.2 - p.2) : EReal)))
                    hinner
            have hsplit₁ :
                (⨆ p : ((H × K) × K),
                  (((⟪p.1.1, u⟫_ℝ + ⟪p.1.2 - p.2, b⟫_ℝ : ℝ) : EReal) -
                    (ψ (p.1.1, p.1.2 - p.2) : EReal))) =
                  (⨆ xy : H × K, ⨆ z : K,
                    (((⟪xy.1, u⟫_ℝ + ⟪xy.2 - z, b⟫_ℝ : ℝ) : EReal) -
                      (ψ (xy.1, xy.2 - z) : EReal))) := by
                  simpa using
                    (iSup_prod' (f := fun xy : H × K => fun z : K =>
                      (((⟪xy.1, u⟫_ℝ + ⟪xy.2 - z, b⟫_ℝ : ℝ) : EReal) -
                        (ψ (xy.1, xy.2 - z) : EReal)))).symm
            have hsplit₂ :
                (⨆ x : H, ⨆ y : K, ⨆ z : K,
                  (((⟪x, u⟫_ℝ + ⟪y - z, b⟫_ℝ : ℝ) : EReal) -
                    (ψ (x, y - z) : EReal))) =
                  (⨆ xy : H × K, ⨆ z : K,
                    (((⟪xy.1, u⟫_ℝ + ⟪xy.2 - z, b⟫_ℝ : ℝ) : EReal) -
                      (ψ (xy.1, xy.2 - z) : EReal))) := by
                  simpa using
                    (iSup_prod' (f := fun x : H => fun y : K =>
                      ⨆ z : K, (((⟪x, u⟫_ℝ + ⟪y - z, b⟫_ℝ : ℝ) : EReal) -
                        (ψ (x, y - z) : EReal))))
            exact hpair.trans (hsplit₁.trans hsplit₂.symm)
    _ = (⨆ x : H, ⨆ w : K,
          (((⟪x, u⟫_ℝ + ⟪w, b⟫_ℝ : ℝ) : EReal) - (ψ (x, w) : EReal))) := by
          refine iSup_congr fun x ↦ ?_
          apply le_antisymm
          · refine iSup_le fun y ↦ ?_
            refine iSup_le fun z ↦ ?_
            exact le_iSup (fun w : K ↦ (((⟪x, u⟫_ℝ + ⟪w, b⟫_ℝ : ℝ) : EReal) -
              (ψ (x, w) : EReal))) (y - z)
          · refine iSup_le fun w ↦ ?_
            exact le_iSup_of_le w <| le_iSup_of_le (0 : K) <| by simp
    _ = ψ.asEReal∗ (u, b) := by
          rw [conjugate_apply]
          have hsplit :
              (⨆ x : H, ⨆ w : K,
                (((⟪x, u⟫_ℝ + ⟪w, b⟫_ℝ : ℝ) : EReal) - (ψ (x, w) : EReal))) =
                (⨆ p : H × K, (((⟪p, (u, b)⟫_ℝ : ℝ) : EReal) - (ψ p : EReal))) := by
                simpa using
                  (iSup_prod' (f := fun x : H => fun w : K =>
                    (((⟪x, u⟫_ℝ + ⟪w, b⟫_ℝ : ℝ) : EReal) - (ψ (x, w) : EReal))))
          exact hsplit

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: off the branch `c = -b`, the first-difference pullback conjugate is
forced to `⊤` by the free last coordinate. -/
theorem conjugate_firstDifferencePullback_apply_top_of_ne_neg
    (ψ : H × K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(H × K))
    (u : H) (b c : K) (hc : c ≠ -b) :
    ((ψ ∘ firstDifferencePullbackMap).asEReal∗) (((u, b), c)) = ⊤ := by
  rcases hψ.2.nonempty with ⟨p, hp⟩
  rcases p with ⟨x, w⟩
  have hψxw_top : (ψ (x, w) : EReal) ≠ ⊤ := by
    exact (mem_effectiveDomain_iff.mp hp).ne
  have hψxw_bot : (ψ (x, w) : EReal) ≠ ⊥ := by
    exact ne_of_gt (ψ (x, w)).2
  have hbc_ne_zero : b + c ≠ 0 := by
    intro hbc
    apply hc
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hbc)
  let d : EReal := ((⟪x, u⟫_ℝ + ⟪w, b⟫_ℝ - (ψ (x, w) : EReal).toReal : ℝ) : EReal)
  have hsup :
      (⨆ z : K, (((⟪z, b + c⟫_ℝ : ℝ) : EReal) + d)) = ⊤ :=
    iSup_pairing_middle_eq_top_of_ne_zero
      (b + c)
      hbc_ne_zero
      d
      (by
        simpa [d] using
          (EReal.coe_ne_top
            (⟪x, u⟫_ℝ + ⟪w, b⟫_ℝ - (ψ (x, w) : EReal).toReal)))
      (by
        simpa [d] using
          (EReal.coe_ne_bot
            (⟪x, u⟫_ℝ + ⟪w, b⟫_ℝ - (ψ (x, w) : EReal).toReal)))
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro M
  have hM : M < ⨆ z : K, (((⟪z, b + c⟫_ℝ : ℝ) : EReal) + d) := by
    simp [hsup]
  rcases lt_iSup_iff.mp hM with ⟨z, hz⟩
  refine lt_of_lt_of_le hz ?_
  refine le_iSup_of_le (((x, w + z), z)) ?_
  -- Keep the source witness fixed and move only along the free last coordinate.
  suffices
      (((⟪z, b + c⟫_ℝ : ℝ) : EReal) + d) ≤
        (((⟪x, u⟫_ℝ + ⟪w + z, b⟫_ℝ + ⟪z, c⟫_ℝ : ℝ) : EReal) -
          (ψ (x, w) : EReal)) by
    simpa only [Function.asEReal_apply, Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_snd', Pi.sub_apply, add_sub_cancel_right] using this
  have hEq :
      (((⟪z, b + c⟫_ℝ : ℝ) : EReal) + d) =
        (((⟪x, u⟫_ℝ + ⟪w + z, b⟫_ℝ + ⟪z, c⟫_ℝ : ℝ) : EReal) - (ψ (x, w) : EReal)) := by
    rw [show (ψ (x, w) : EReal) = (((ψ (x, w) : EReal).toReal : ℝ) : EReal) by
      exact (EReal.coe_toReal hψxw_top hψxw_bot).symm]
    rw [sub_eq_add_neg, inner_add_left, inner_add_right]
    repeat rw [← EReal.coe_add]
    congr 1
    ring
  exact hEq.le

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: the conjugate of the first-difference pullback is finite exactly
when the last coordinate is the negative of the middle one. -/
theorem conjugate_firstDifferencePullback_apply
    [DecidableEq K]
    (ψ : H × K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(H × K))
    (u : H) (b c : K) :
    ((ψ ∘ firstDifferencePullbackMap).asEReal∗) (((u, b), c)) =
      if c = -b then ψ.asEReal∗ (u, b) else ⊤ := by
  by_cases hc : c = -b
  · -- On the finite branch, reindex by `w = y - z`.
    subst c
    simpa using conjugate_firstDifferencePullback_apply_negSlice (ψ := ψ) u b
  · -- Off the finite branch, the free last coordinate drives the conjugate to `⊤`.
    simpa [hc] using
      conjugate_firstDifferencePullback_apply_top_of_ne_neg (ψ := ψ) hψ u b c hc

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 15 8: evaluating the lifted dual infimal convolution on the zero second
dual coordinate forces the middle coordinate to vanish and the last coordinate to equal `q.2`. -/
theorem zeroSecond_lifted_dualInfimalConvolution_eq_firstVariableInfimalConvolution
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (q : H × K) :
    (((φ ∘ firstLastPullbackMap).asEReal∗ □
        (ψ ∘ firstDifferencePullbackMap).asEReal∗) (q, (0 : K))) =
      ((fun u : H ↦ φ.asEReal∗ (u, q.2)) □
        fun u ↦ ψ.asEReal∗ (u, q.2)) q.1 := by
  classical
  rw [infimalConvolution_apply, infimalConvolution_apply]
  apply le_antisymm
  · -- Use the split point `((u, 0), q.2)` to realize every first-variable decomposition.
    refine le_iInf fun u ↦ ?_
    refine iInf_le_of_le (((u, (0 : K)), q.2)) ?_
    have hsub : (q, (0 : K)) - ((u, (0 : K)), q.2) = ((q.1 - u, q.2), -q.2) := by
      ext <;> simp [sub_eq_add_neg]
    rw [conjugate_firstLastPullback_apply (φ := φ) hφ u 0 q.2]
    rw [hsub]
    rw [conjugate_firstDifferencePullback_apply (ψ := ψ) hψ (q.1 - u) q.2 (-q.2)]
    simp
  · -- Any lifted split either lands on the finite branch or gives value `⊤`.
    refine le_iInf fun r ↦ ?_
    rcases r with ⟨⟨u, b⟩, v⟩
    by_cases hb : b = 0
    · subst b
      by_cases hneg : -v = -(q.2 : K)
      · have hv : v = q.2 := by
          simpa using congrArg Neg.neg hneg
        have hsub : (q, (0 : K)) - ((u, (0 : K)), v) = ((q.1 - u, q.2), -v) := by
          ext <;> simp [sub_eq_add_neg]
        rw [conjugate_firstLastPullback_apply (φ := φ) hφ u 0 v]
        rw [hsub]
        rw [conjugate_firstDifferencePullback_apply (ψ := ψ) hψ (q.1 - u) q.2 (-v)]
        subst v
        simpa using
          (iInf_le
            (fun u' : H ↦ φ.asEReal∗ (u', q.2) + ψ.asEReal∗ (q.1 - u', q.2))
            u)
      · rw [conjugate_firstLastPullback_apply (φ := φ) hφ u 0 v]
        have hsub : (q, (0 : K)) - ((u, (0 : K)), v) = ((q.1 - u, q.2), -v) := by
          ext <;> simp [sub_eq_add_neg]
        rw [hsub]
        rw [conjugate_firstDifferencePullback_apply (ψ := ψ) hψ (q.1 - u) q.2 (-v)]
        have hleft_ne_bot : φ.asEReal∗ (u, v) ≠ ⊥ :=
          conjugate_ne_bot_of_effectiveDomain_nonempty hφ.2.nonempty (u, v)
        have hsum_top :
            ((⨆ x, (((⟪x, (u, v)⟫_ℝ : ℝ) : EReal) - (φ x : EReal))) + ⊤ : EReal) = ⊤ := by
          simpa [conjugate_apply] using EReal.add_top_of_ne_bot hleft_ne_bot
        simp [hneg, hsum_top]
    · have hsub : (q, (0 : K)) - ((u, b), v) = ((q.1 - u, q.2 - b), -v) := by
        ext <;> simp [sub_eq_add_neg]
      rw [conjugate_firstLastPullback_apply (φ := φ) hφ u b v]
      rw [hsub]
      rw [conjugate_firstDifferencePullback_apply (ψ := ψ) hψ (q.1 - u) (q.2 - b) (-v)]
      have hright_ne_bot : ψ.asEReal∗ (q.1 - u, q.2 - b) ≠ ⊥ :=
        conjugate_ne_bot_of_effectiveDomain_nonempty hψ.2.nonempty (q.1 - u, q.2 - b)
      have hbranch_ne_bot :
          (if -v = b - q.2 then
              (⨆ x, (((⟪x, (q.1 - u, q.2 - b)⟫_ℝ : ℝ) : EReal) - (ψ x : EReal)))
            else ⊤) ≠ ⊥ := by
        by_cases hcase : -v = b - q.2
        · simpa [hcase] using hright_ne_bot
        · simp [hcase]
      have hsum_top :
          (⊤ + if -v = b - q.2 then
              (⨆ x, (((⟪x, (q.1 - u, q.2 - b)⟫_ℝ : ℝ) : EReal) - (ψ x : EReal)))
            else ⊤ : EReal) = ⊤ := by
        exact EReal.top_add_of_ne_bot hbranch_ne_bot
      simp [hb, conjugate_apply, hsum_top]

/-- Helper for Corollary 15 8: after rewriting the primal function as a lifted partial infimum,
the remaining zero-slice conjugate of the lifted sum is the first-variable infimal convolution of
the conjugate slices. -/
theorem lifted_sum_conjugate_zeroSecond_eq_infimalConvolution_conjugateSlices
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)))
    (q : H × K) :
    (fun r : ((H × K) × K) ↦
      (φ (r.1.1, r.2) : EReal) + (ψ (r.1.1, r.1.2 - r.2) : EReal))∗ (q, (0 : K)) =
      ((fun u : H ↦ φ.asEReal∗ (u, q.2)) □
        fun u ↦ ψ.asEReal∗ (u, q.2)) q.1 := by
  classical
  have hconj :=
    congrFun
      (
        conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
        (φ ∘ firstLastPullbackMap)
        (ψ ∘ firstDifferencePullbackMap)
        (firstLastPullback_mem_gammaZero φ hφ)
        (firstDifferencePullback_mem_gammaZero ψ hψ)
        (zero_mem_sri_lifted_difference_of_zero_mem_sri_firstProjection_difference
          φ ψ hφ hψ hsri)
      )
      (q, (0 : K))
  calc
    (fun r : ((H × K) × K) ↦
      (φ (r.1.1, r.2) : EReal) + (ψ (r.1.1, r.1.2 - r.2) : EReal))∗ (q, (0 : K)) =
        (((φ ∘ firstLastPullbackMap).asEReal∗ □
          (ψ ∘ firstDifferencePullbackMap).asEReal∗) (q, (0 : K))) := by
            -- The lifted separable sum is exactly the pointwise sum of the two pullbacks.
            simpa [Pi.add_apply, Function.comp, firstLastPullbackMap_apply,
              firstDifferencePullbackMap_apply] using hconj
    _ = ((fun u : H ↦ φ.asEReal∗ (u, q.2)) □
          fun u ↦ ψ.asEReal∗ (u, q.2)) q.1 := by
          simpa using
            zeroSecond_lifted_dualInfimalConvolution_eq_firstVariableInfimalConvolution
              φ ψ hφ hψ q

-- Proof sketch: write the function
-- `p ↦ ((z ↦ φ(x, z)) □ (z ↦ ψ(x, z))) y` with `p = (x, y)` in `H × K`
-- as the infimal postcomposition of the separable sum `(x, y₁, y₂) ↦ φ(x, y₁) + ψ(x, y₂)` along
-- `(x, y₁, y₂) ↦ (x, y₁ + y₂)`. Apply the Attouch--Brézis conjugation theorem on the product
-- Hilbert product `H × K` under the hypothesis
-- `0 ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))`, then evaluate the
-- resulting conjugate identity on slices with the second dual variable fixed.
/-- Corollary 15 8: if `φ, ψ ∈ Γ₀(H × K)` and
`0 ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))`, then the Fenchel
conjugate of the second-variable fiberwise infimal convolution
`p ↦ ((z ↦ φ(x, z)) □ (z ↦ ψ(x, z))) y`, where `p = (x, y)` in `H × K`,
is obtained by taking the infimal convolution in the first variable of the conjugate slices with
the second dual variable fixed. -/
theorem conjugate_secondVariableFiberwiseInfimalConvolution_eq_infimalConvolution_conjugateSlices
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))) :
    (fun p : H × K ↦
      ((fun z : K ↦ (φ (p.1, z) : EReal)) □
        fun z ↦ (ψ (p.1, z) : EReal)) p.2)∗ =
      fun q : H × K ↦
        ((fun u : H ↦ φ.asEReal∗ (u, q.2)) □
          fun u ↦ ψ.asEReal∗ (u, q.2)) q.1 := by
  let F : ((H × K) × K) → EReal := fun r ↦
    (φ (r.1.1, r.2) : EReal) + (ψ (r.1.1, r.1.2 - r.2) : EReal)
  have hrewrite :
      (fun p : H × K ↦
        ((fun z : K ↦ (φ (p.1, z) : EReal)) □
          fun z ↦ (ψ (p.1, z) : EReal)) p.2) =
        Prod.fst ▷ F := by
    simpa [F] using
      secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted φ ψ
  funext q
  calc
    (fun p : H × K ↦
      ((fun z : K ↦ (φ (p.1, z) : EReal)) □
        fun z ↦ (ψ (p.1, z) : EReal)) p.2)∗ q =
        (Prod.fst ▷ F)∗ q := by
          simp [hrewrite]
    _ = F∗ (q, (0 : K)) := by
          simpa [F] using
            congrFun (conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_local F) q
    _ = ((fun u : H ↦ φ.asEReal∗ (u, q.2)) □
          fun u ↦ ψ.asEReal∗ (u, q.2)) q.1 := by
          simpa [F] using
            lifted_sum_conjugate_zeroSecond_eq_infimalConvolution_conjugateSlices
              φ ψ hφ hψ hsri q

/-- Evaluating Corollary 15.8 at `(x, y)` recovers the textbook raw-pair formula. -/
theorem
    conjugate_secondVariableFiberwiseInfimalConvolution_eq_infimalConvolution_conjugateSlices_apply
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈ sri (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)))
    (x : H) (y : K) :
    (fun p : H × K ↦
      ((fun z : K ↦ (φ (p.1, z) : EReal)) □
        fun z ↦ (ψ (p.1, z) : EReal)) p.2)∗ (x, y) =
      ((fun u : H ↦ φ.asEReal∗ (u, y)) □
        fun u ↦ ψ.asEReal∗ (u, y)) x := by
  simpa using
    congrFun
      (conjugate_secondVariableFiberwiseInfimalConvolution_eq_infimalConvolution_conjugateSlices
        φ ψ hφ hψ hsri)
      (x, y)

end AttouchBrezisTheorem

end ERealFunction
