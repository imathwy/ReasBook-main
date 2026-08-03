import Mathlib
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Definition_12_34

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section FiberwiseDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Helper for Theorem 25.2: the lifted domain difference is exactly the first-coordinate
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
    -- Project the lifted difference to the first coordinate; the remaining coordinates are free.
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
    -- Rebuild lifted witnesses from the source-domain witnesses and the free coordinates.
    refine Set.mem_sub.mpr ⟨p, hp_dom, r, hr_dom, ?_⟩
    ext <;> simp [p, r, hcoord]

/-- Helper for Theorem 25.2: the lifted map `(x, y, z) ↦ (x, z)` used in the local product-space
regularity bridge. -/
abbrev firstLastPullbackMap : ((H × K) × K) →L[ℝ] (H × K) :=
  (((ContinuousLinearMap.fst ℝ H K).comp (ContinuousLinearMap.fst ℝ (H × K) K)).prod
    (ContinuousLinearMap.snd ℝ (H × K) K))

/-- Helper for Theorem 25.2: the lifted map `(x, y, z) ↦ (x, y - z)` used in the local
product-space regularity bridge. -/
abbrev firstDifferencePullbackMap : ((H × K) × K) →L[ℝ] (H × K) :=
  (((ContinuousLinearMap.fst ℝ H K).comp (ContinuousLinearMap.fst ℝ (H × K) K)).prod
    ((ContinuousLinearMap.snd ℝ H K).comp (ContinuousLinearMap.fst ℝ (H × K) K) -
      ContinuousLinearMap.snd ℝ (H × K) K))

/-- Helper for Theorem 25.2: evaluating `firstLastPullbackMap` recovers `(x, z)`. -/
@[simp] theorem firstLastPullbackMap_apply (q : ((H × K) × K)) :
    firstLastPullbackMap q = (q.1.1, q.2) := by
  rfl

/-- Helper for Theorem 25.2: evaluating `firstDifferencePullbackMap` recovers `(x, y - z)`. -/
@[simp] theorem firstDifferencePullbackMap_apply (q : ((H × K) × K)) :
    firstDifferencePullbackMap q = (q.1.1, q.1.2 - q.2) := by
  rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 25.2: evaluating a lifted conjugate on the zero second dual slice removes
the second pairing term. -/
theorem conjugate_apply_prod_zeroSecond_local
    (F : (H × K) × K → EReal) (u : H × K) :
    F∗ (u, (0 : K)) =
      ⨆ p : (H × K) × K, (((⟪p.1, u⟫_ℝ : ℝ) : EReal) - F p) := by
  -- Expand the conjugate and cancel the zero contribution from the second dual coordinate.
  rw [conjugate_apply]
  congr with p
  congr 1
  change (((⟪p.1, u⟫_ℝ + ⟪p.2, (0 : K)⟫_ℝ : ℝ) : EReal)) =
    (((⟪p.1, u⟫_ℝ : ℝ) : EReal))
  simp

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 25.2: each fixed first-variable slice is bounded above by subtracting the
fiber infimum. -/
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
/-- Helper for Theorem 25.2: subtracting the fiber infimum is bounded above by the supremum of
the corresponding slices. -/
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

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 25.2: fiberwise, subtracting the infimum equals taking the supremum of the
corresponding slices. -/
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
/-- Helper for Theorem 25.2: specializing first-projection infimal postcomposition on
`((H × K) × K)` recovers the partial infimum over the last coordinate. -/
theorem infimalPostcomposition_fst_apply_local
    (F : (H × K) × K → EReal) (x : H × K) :
    (Prod.fst ▷ F) x = ⨅ y : K, F (x, y) := by
  -- Rewrite the first-projection fiber as the range of the last-coordinate parametrization.
  change sInf (F '' (Prod.fst ⁻¹' ({x} : Set (H × K)))) = _
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
/-- Helper for Theorem 25.2: the conjugate of a first-projection infimal postcomposition equals
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

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Theorem 25.2: the source-facing fiberwise infimal convolution is the canonical
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
  -- Rewrite the lifted partial infimum and identify it with the textbook fiberwise formula.
  rw [infimalPostcomposition_fst_apply_local]
  simp [infimalConvolution_apply]

/-- Helper for Theorem 25.2: taking the product with `univ` preserves strong relative interior at
the origin. -/
theorem zero_mem_sri_prod_univ_of_zero_mem_sri
    {S : Set H} (hS_convex : Convex ℝ S) (hsri : (0 : H) ∈ sri S) :
    (0 : H × K) ∈ sri (S ×ˢ (Set.univ : Set K)) := by
  -- Reuse the Chapter 15 cone/closure-span argument in the theorem-local support file.
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

/-- Helper for Theorem 25.2: the projected `sri` hypothesis lifts to the pulled-back domain
difference on `((H × K) × K)`. -/
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
  -- Rewrite the lifted difference as two free `K` coordinates over the projected difference.
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

end FiberwiseDuality

end ERealFunction
